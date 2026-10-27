// Lean compiler output
// Module: Lean.Server.References
// Imports: public import Lean.Data.Lsp.Internal public import Lean.Server.Utils public import Lean.Elab.Import
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Lsp_instOrdRefIdent_ord(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object*);
uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Lsp_instHashableRange_hash(lean_object*);
uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqRefIdent_beq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t l_Lean_Lsp_instHashableRefIdent_hash(lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_Range_toLspRange(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_DeclInfo_range(lean_object*);
lean_object* l_Lean_Lsp_DeclInfo_selectionRange(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_IO_throwServerError___redArg(lean_object*);
lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
lean_object* lean_compacted_region_read(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ImportInfo_ofImport(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_collectImports_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_collectImports_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_collectImports(lean_object*);
static const lean_array_object l_Lean_Server_RefInfo_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_RefInfo_empty___closed__0 = (const lean_object*)&l_Lean_Server_RefInfo_empty___closed__0_value;
static const lean_ctor_object l_Lean_Server_RefInfo_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_RefInfo_empty___closed__0_value)}};
static const lean_object* l_Lean_Server_RefInfo_empty___closed__1 = (const lean_object*)&l_Lean_Server_RefInfo_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_RefInfo_empty = (const lean_object*)&l_Lean_Server_RefInfo_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_addRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_toLspRefInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_toLspRefInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_addRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_RefInfo_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_RefInfo_empty___closed__0 = (const lean_object*)&l_Lean_Lsp_RefInfo_empty___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_RefInfo_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_RefInfo_empty___closed__0_value)}};
static const lean_object* l_Lean_Lsp_RefInfo_empty___closed__1 = (const lean_object*)&l_Lean_Lsp_RefInfo_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_RefInfo_empty = (const lean_object*)&l_Lean_Lsp_RefInfo_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_merge(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_findReferenceLocation_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_RefInfo_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_ModuleRefs_findAt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_ModuleRefs_findAt___closed__0 = (const lean_object*)&l_Lean_Lsp_ModuleRefs_findAt___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Expected list of length 8, not length "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Expected list"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__1_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__1_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Expected list of length 4 or 5, not "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "usages"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Expected array, got other JSON type"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__0 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__0_value;
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__1 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__1_value;
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__2 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__2_value;
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Ilean"};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__3 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Server_instFromJsonIlean_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_instFromJsonIlean_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_instFromJsonIlean_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 170, 53, 225, 48, 57, 13, 173)}};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__4 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__5;
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__6 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__7;
static const lean_ctor_object l_Lean_Server_instFromJsonIlean_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__8 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__9;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__10;
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__11 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__12;
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__13 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_Server_instFromJsonIlean_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__14 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__15;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__16;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__17;
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "directImports"};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__18 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__18_value;
static const lean_ctor_object l_Lean_Server_instFromJsonIlean_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__18_value),LEAN_SCALAR_PTR_LITERAL(113, 107, 65, 139, 239, 150, 173, 242)}};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__19 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__19_value;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__20;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__21;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__22;
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "references"};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__23 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__23_value;
static const lean_ctor_object l_Lean_Server_instFromJsonIlean_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__23_value),LEAN_SCALAR_PTR_LITERAL(52, 234, 189, 66, 81, 216, 208, 197)}};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__24 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__24_value;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__25;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__26;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__27;
static const lean_string_object l_Lean_Server_instFromJsonIlean_fromJson___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decls"};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__28 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__28_value;
static const lean_ctor_object l_Lean_Server_instFromJsonIlean_fromJson___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__28_value),LEAN_SCALAR_PTR_LITERAL(44, 160, 58, 0, 137, 124, 237, 95)}};
static const lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__29 = (const lean_object*)&l_Lean_Server_instFromJsonIlean_fromJson___closed__29_value;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__30;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__31;
static lean_once_cell_t l_Lean_Server_instFromJsonIlean_fromJson___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instFromJsonIlean_fromJson___closed__32;
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonIlean_fromJson(lean_object*);
static const lean_closure_object l_Lean_Server_instFromJsonIlean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instFromJsonIlean_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instFromJsonIlean___closed__0 = (const lean_object*)&l_Lean_Server_instFromJsonIlean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instFromJsonIlean = (const lean_object*)&l_Lean_Server_instFromJsonIlean___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_instToJsonIlean_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_instToJsonIlean_toJson___closed__0 = (const lean_object*)&l_Lean_Server_instToJsonIlean_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonIlean_toJson(lean_object*);
static const lean_closure_object l_Lean_Server_instToJsonIlean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_instToJsonIlean_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instToJsonIlean___closed__0 = (const lean_object*)&l_Lean_Server_instToJsonIlean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instToJsonIlean = (const lean_object*)&l_Lean_Server_instToJsonIlean___closed__0_value;
static const lean_string_object l_Lean_Server_Ilean_compactedExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ilean.mmap"};
static const lean_object* l_Lean_Server_Ilean_compactedExt___closed__0 = (const lean_object*)&l_Lean_Server_Ilean_compactedExt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_Ilean_compactedExt = (const lean_object*)&l_Lean_Server_Ilean_compactedExt___closed__0_value;
static const lean_array_object l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Ilean_loadCompacted_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ilean"};
static const lean_object* l_Lean_Server_Ilean_loadCompacted_x3f___closed__0 = (const lean_object*)&l_Lean_Server_Ilean_loadCompacted_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Server_Ilean_loadCompacted_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_Ilean_loadCompacted_x3f___closed__0_value)}};
static const lean_object* l_Lean_Server_Ilean_loadCompacted_x3f___closed__1 = (const lean_object*)&l_Lean_Server_Ilean_loadCompacted_x3f___closed__1_value;
static const lean_string_object l_Lean_Server_Ilean_loadCompacted_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Ilean.loadCompacted\?: '"};
static const lean_object* l_Lean_Server_Ilean_loadCompacted_x3f___closed__2 = (const lean_object*)&l_Lean_Server_Ilean_loadCompacted_x3f___closed__2_value;
static const lean_string_object l_Lean_Server_Ilean_loadCompacted_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "' not an .ilean"};
static const lean_object* l_Lean_Server_Ilean_loadCompacted_x3f___closed__3 = (const lean_object*)&l_Lean_Server_Ilean_loadCompacted_x3f___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_loadCompacted_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_loadCompacted_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_Ilean_load___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Failed to load ilean at "};
static const lean_object* l_Lean_Server_Ilean_load___closed__0 = (const lean_object*)&l_Lean_Server_Ilean_load___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_identOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_identOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Elab.InfoTree.Util.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Util"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_findReferences(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_findReferences___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_combineIdents___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_combineIdents___closed__0;
static lean_once_cell_t l_Lean_Server_combineIdents___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_combineIdents___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_dedupReferences___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_dedupReferences___closed__0;
static lean_once_cell_t l_Lean_Server_dedupReferences___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_dedupReferences___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_instInhabitedModuleImport_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_instInhabitedModuleImport_default___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedModuleImport_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedModuleImport_default = (const lean_object*)&l_Lean_Server_instInhabitedModuleImport_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedModuleImport = (const lean_object*)&l_Lean_Server_instInhabitedModuleImport_default___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_instEmptyCollectionDirectImports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_instEmptyCollectionDirectImports___closed__0 = (const lean_object*)&l_Lean_Server_instEmptyCollectionDirectImports___closed__0_value;
static const lean_ctor_object l_Lean_Server_instEmptyCollectionDirectImports___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instEmptyCollectionDirectImports___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Server_instEmptyCollectionDirectImports___closed__1 = (const lean_object*)&l_Lean_Server_instEmptyCollectionDirectImports___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instEmptyCollectionDirectImports = (const lean_object*)&l_Lean_Server_instEmptyCollectionDirectImports___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0;
static lean_once_cell_t l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_DirectImports_convertImportInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_DirectImports_convertImportInfos___closed__0 = (const lean_object*)&l_Lean_Server_DirectImports_convertImportInfos___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object*);
static const lean_ctor_object l_Lean_Server_instInhabitedReferences_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Server_instInhabitedReferences_default___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedReferences_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedReferences_default = (const lean_object*)&l_Lean_Server_instInhabitedReferences_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_instInhabitedReferences = (const lean_object*)&l_Lean_Server_instInhabitedReferences_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_References_empty = (const lean_object*)&l_Lean_Server_instInhabitedReferences_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_References_updateWorkerRefs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_References_updateWorkerRefs___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_References_updateWorkerRefs___closed__0 = (const lean_object*)&l_Lean_Server_References_updateWorkerRefs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_References_allRefsFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_References_allRefsFor___closed__0 = (const lean_object*)&l_Lean_Server_References_allRefsFor___closed__0_value;
static const lean_array_object l_Lean_Server_References_allRefsFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_References_allRefsFor___closed__1 = (const lean_object*)&l_Lean_Server_References_allRefsFor___closed__1_value;
static const lean_array_object l_Lean_Server_References_allRefsFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_References_allRefsFor___closed__2 = (const lean_object*)&l_Lean_Server_References_allRefsFor___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_References_referringTo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_References_referringTo___closed__0 = (const lean_object*)&l_Lean_Server_References_referringTo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_References_definitionsMatching___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_References_definitionsMatching___redArg___closed__0 = (const lean_object*)&l_Lean_Server_References_definitionsMatching___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Server_References_definitionsMatching___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_References_definitionsMatching___redArg___closed__0_value)}};
static const lean_object* l_Lean_Server_References_definitionsMatching___redArg___closed__1 = (const lean_object*)&l_Lean_Server_References_definitionsMatching___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_ImportInfo_ofImport(lean_object* v_i_1_){
_start:
{
lean_object* v_module_2_; uint8_t v_importAll_3_; uint8_t v_isExported_4_; uint8_t v_isMeta_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_18_; 
v_module_2_ = lean_ctor_get(v_i_1_, 0);
v_importAll_3_ = lean_ctor_get_uint8(v_i_1_, sizeof(void*)*1);
v_isExported_4_ = lean_ctor_get_uint8(v_i_1_, sizeof(void*)*1 + 1);
v_isMeta_5_ = lean_ctor_get_uint8(v_i_1_, sizeof(void*)*1 + 2);
v_isSharedCheck_18_ = !lean_is_exclusive(v_i_1_);
if (v_isSharedCheck_18_ == 0)
{
v___x_7_ = v_i_1_;
v_isShared_8_ = v_isSharedCheck_18_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_module_2_);
lean_dec(v_i_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_18_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
uint8_t v___x_9_; lean_object* v___x_10_; 
v___x_9_ = 1;
v___x_10_ = l_Lean_Name_toString(v_module_2_, v___x_9_);
if (v_isExported_4_ == 0)
{
lean_object* v___x_12_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 0, v___x_10_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_10_);
lean_ctor_set_uint8(v_reuseFailAlloc_13_, sizeof(void*)*1 + 2, v_isMeta_5_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*1, v___x_9_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*1 + 1, v_importAll_3_);
return v___x_12_;
}
}
else
{
uint8_t v___x_14_; lean_object* v___x_16_; 
v___x_14_ = 0;
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 0, v___x_10_);
v___x_16_ = v___x_7_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_10_);
lean_ctor_set_uint8(v_reuseFailAlloc_17_, sizeof(void*)*1 + 2, v_isMeta_5_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*1, v___x_14_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*1 + 1, v_importAll_3_);
return v___x_16_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_collectImports_spec__0(size_t v_sz_19_, size_t v_i_20_, lean_object* v_bs_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = lean_usize_dec_lt(v_i_20_, v_sz_19_);
if (v___x_22_ == 0)
{
return v_bs_21_;
}
else
{
lean_object* v_v_23_; lean_object* v___x_24_; lean_object* v_bs_x27_25_; lean_object* v___x_26_; size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; 
v_v_23_ = lean_array_uget(v_bs_21_, v_i_20_);
v___x_24_ = lean_unsigned_to_nat(0u);
v_bs_x27_25_ = lean_array_uset(v_bs_21_, v_i_20_, v___x_24_);
v___x_26_ = l_Lean_Server_ImportInfo_ofImport(v_v_23_);
v___x_27_ = ((size_t)1ULL);
v___x_28_ = lean_usize_add(v_i_20_, v___x_27_);
v___x_29_ = lean_array_uset(v_bs_x27_25_, v_i_20_, v___x_26_);
v_i_20_ = v___x_28_;
v_bs_21_ = v___x_29_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_collectImports_spec__0___boxed(lean_object* v_sz_31_, lean_object* v_i_32_, lean_object* v_bs_33_){
_start:
{
size_t v_sz_boxed_34_; size_t v_i_boxed_35_; lean_object* v_res_36_; 
v_sz_boxed_34_ = lean_unbox_usize(v_sz_31_);
lean_dec(v_sz_31_);
v_i_boxed_35_ = lean_unbox_usize(v_i_32_);
lean_dec(v_i_32_);
v_res_36_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_collectImports_spec__0(v_sz_boxed_34_, v_i_boxed_35_, v_bs_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_collectImports(lean_object* v_headerStx_37_){
_start:
{
uint8_t v___x_38_; lean_object* v___x_39_; size_t v_sz_40_; size_t v___x_41_; lean_object* v___x_42_; 
v___x_38_ = 0;
v___x_39_ = l_Lean_Elab_HeaderSyntax_imports(v_headerStx_37_, v___x_38_);
v_sz_40_ = lean_array_size(v___x_39_);
v___x_41_ = ((size_t)0ULL);
v___x_42_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_collectImports_spec__0(v_sz_40_, v___x_41_, v___x_39_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_addRef(lean_object* v_i_49_, lean_object* v_ref_50_){
_start:
{
lean_object* v_definition_51_; lean_object* v_usages_52_; 
v_definition_51_ = lean_ctor_get(v_i_49_, 0);
v_usages_52_ = lean_ctor_get(v_i_49_, 1);
if (lean_obj_tag(v_definition_51_) == 0)
{
lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_64_; 
lean_inc(v_definition_51_);
lean_inc_ref(v_usages_52_);
v_isSharedCheck_64_ = !lean_is_exclusive(v_i_49_);
if (v_isSharedCheck_64_ == 0)
{
lean_object* v_unused_65_; lean_object* v_unused_66_; 
v_unused_65_ = lean_ctor_get(v_i_49_, 1);
lean_dec(v_unused_65_);
v_unused_66_ = lean_ctor_get(v_i_49_, 0);
lean_dec(v_unused_66_);
v___x_57_ = v_i_49_;
v_isShared_58_ = v_isSharedCheck_64_;
goto v_resetjp_56_;
}
else
{
lean_dec(v_i_49_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_64_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
uint8_t v_isBinder_59_; 
v_isBinder_59_ = lean_ctor_get_uint8(v_ref_50_, sizeof(void*)*6);
if (v_isBinder_59_ == 0)
{
lean_del_object(v___x_57_);
goto v___jp_53_;
}
else
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v_ref_50_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_60_);
v___x_62_ = v___x_57_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_usages_52_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
else
{
uint8_t v_isBinder_67_; 
v_isBinder_67_ = lean_ctor_get_uint8(v_ref_50_, sizeof(void*)*6);
if (v_isBinder_67_ == 0)
{
lean_inc_ref(v_definition_51_);
lean_inc_ref(v_usages_52_);
lean_dec_ref(v_i_49_);
goto v___jp_53_;
}
else
{
lean_dec_ref(v_ref_50_);
return v_i_49_;
}
}
v___jp_53_:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_array_push(v_usages_52_, v_ref_50_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v_definition_51_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(lean_object* v_k_68_, lean_object* v_v_69_, lean_object* v_t_70_){
_start:
{
if (lean_obj_tag(v_t_70_) == 0)
{
lean_object* v_size_71_; lean_object* v_k_72_; lean_object* v_v_73_; lean_object* v_l_74_; lean_object* v_r_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_355_; 
v_size_71_ = lean_ctor_get(v_t_70_, 0);
v_k_72_ = lean_ctor_get(v_t_70_, 1);
v_v_73_ = lean_ctor_get(v_t_70_, 2);
v_l_74_ = lean_ctor_get(v_t_70_, 3);
v_r_75_ = lean_ctor_get(v_t_70_, 4);
v_isSharedCheck_355_ = !lean_is_exclusive(v_t_70_);
if (v_isSharedCheck_355_ == 0)
{
v___x_77_ = v_t_70_;
v_isShared_78_ = v_isSharedCheck_355_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_r_75_);
lean_inc(v_l_74_);
lean_inc(v_v_73_);
lean_inc(v_k_72_);
lean_inc(v_size_71_);
lean_dec(v_t_70_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_355_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint8_t v___x_79_; 
v___x_79_ = lean_string_compare(v_k_68_, v_k_72_);
switch(v___x_79_)
{
case 0:
{
lean_object* v_impl_80_; lean_object* v___x_81_; 
lean_dec(v_size_71_);
v_impl_80_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_68_, v_v_69_, v_l_74_);
v___x_81_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_75_) == 0)
{
lean_object* v_size_82_; lean_object* v_size_83_; lean_object* v_k_84_; lean_object* v_v_85_; lean_object* v_l_86_; lean_object* v_r_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_size_82_ = lean_ctor_get(v_r_75_, 0);
v_size_83_ = lean_ctor_get(v_impl_80_, 0);
v_k_84_ = lean_ctor_get(v_impl_80_, 1);
v_v_85_ = lean_ctor_get(v_impl_80_, 2);
v_l_86_ = lean_ctor_get(v_impl_80_, 3);
v_r_87_ = lean_ctor_get(v_impl_80_, 4);
lean_inc(v_r_87_);
v___x_88_ = lean_unsigned_to_nat(3u);
v___x_89_ = lean_nat_mul(v___x_88_, v_size_82_);
v___x_90_ = lean_nat_dec_lt(v___x_89_, v_size_83_);
lean_dec(v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
lean_dec(v_r_87_);
v___x_91_ = lean_nat_add(v___x_81_, v_size_83_);
v___x_92_ = lean_nat_add(v___x_91_, v_size_82_);
lean_dec(v___x_91_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 3, v_impl_80_);
lean_ctor_set(v___x_77_, 0, v___x_92_);
v___x_94_ = v___x_77_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_95_, 3, v_impl_80_);
lean_ctor_set(v_reuseFailAlloc_95_, 4, v_r_75_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
else
{
lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_161_; 
lean_inc(v_l_86_);
lean_inc(v_v_85_);
lean_inc(v_k_84_);
lean_inc(v_size_83_);
v_isSharedCheck_161_ = !lean_is_exclusive(v_impl_80_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; lean_object* v_unused_163_; lean_object* v_unused_164_; lean_object* v_unused_165_; lean_object* v_unused_166_; 
v_unused_162_ = lean_ctor_get(v_impl_80_, 4);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_impl_80_, 3);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_impl_80_, 2);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_impl_80_, 1);
lean_dec(v_unused_165_);
v_unused_166_ = lean_ctor_get(v_impl_80_, 0);
lean_dec(v_unused_166_);
v___x_97_ = v_impl_80_;
v_isShared_98_ = v_isSharedCheck_161_;
goto v_resetjp_96_;
}
else
{
lean_dec(v_impl_80_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_161_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v_size_99_; lean_object* v_size_100_; lean_object* v_k_101_; lean_object* v_v_102_; lean_object* v_l_103_; lean_object* v_r_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_size_99_ = lean_ctor_get(v_l_86_, 0);
v_size_100_ = lean_ctor_get(v_r_87_, 0);
v_k_101_ = lean_ctor_get(v_r_87_, 1);
v_v_102_ = lean_ctor_get(v_r_87_, 2);
v_l_103_ = lean_ctor_get(v_r_87_, 3);
v_r_104_ = lean_ctor_get(v_r_87_, 4);
v___x_105_ = lean_unsigned_to_nat(2u);
v___x_106_ = lean_nat_mul(v___x_105_, v_size_99_);
v___x_107_ = lean_nat_dec_lt(v_size_100_, v___x_106_);
lean_dec(v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_136_; 
lean_inc(v_r_104_);
lean_inc(v_l_103_);
lean_inc(v_v_102_);
lean_inc(v_k_101_);
v_isSharedCheck_136_ = !lean_is_exclusive(v_r_87_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; lean_object* v_unused_138_; lean_object* v_unused_139_; lean_object* v_unused_140_; lean_object* v_unused_141_; 
v_unused_137_ = lean_ctor_get(v_r_87_, 4);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_r_87_, 3);
lean_dec(v_unused_138_);
v_unused_139_ = lean_ctor_get(v_r_87_, 2);
lean_dec(v_unused_139_);
v_unused_140_ = lean_ctor_get(v_r_87_, 1);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_r_87_, 0);
lean_dec(v_unused_141_);
v___x_109_ = v_r_87_;
v_isShared_110_ = v_isSharedCheck_136_;
goto v_resetjp_108_;
}
else
{
lean_dec(v_r_87_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_136_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___y_114_; lean_object* v___y_115_; lean_object* v___y_116_; lean_object* v___x_124_; lean_object* v___y_126_; 
v___x_111_ = lean_nat_add(v___x_81_, v_size_83_);
lean_dec(v_size_83_);
v___x_112_ = lean_nat_add(v___x_111_, v_size_82_);
lean_dec(v___x_111_);
v___x_124_ = lean_nat_add(v___x_81_, v_size_99_);
if (lean_obj_tag(v_l_103_) == 0)
{
lean_object* v_size_134_; 
v_size_134_ = lean_ctor_get(v_l_103_, 0);
lean_inc(v_size_134_);
v___y_126_ = v_size_134_;
goto v___jp_125_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(0u);
v___y_126_ = v___x_135_;
goto v___jp_125_;
}
v___jp_113_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_117_ = lean_nat_add(v___y_114_, v___y_116_);
lean_dec(v___y_116_);
lean_dec(v___y_114_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v_r_75_);
lean_ctor_set(v___x_109_, 3, v_r_104_);
lean_ctor_set(v___x_109_, 2, v_v_73_);
lean_ctor_set(v___x_109_, 1, v_k_72_);
lean_ctor_set(v___x_109_, 0, v___x_117_);
v___x_119_ = v___x_109_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_123_, 3, v_r_104_);
lean_ctor_set(v_reuseFailAlloc_123_, 4, v_r_75_);
v___x_119_ = v_reuseFailAlloc_123_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v___x_119_);
lean_ctor_set(v___x_97_, 3, v___y_115_);
lean_ctor_set(v___x_97_, 2, v_v_102_);
lean_ctor_set(v___x_97_, 1, v_k_101_);
lean_ctor_set(v___x_97_, 0, v___x_112_);
v___x_121_ = v___x_97_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_k_101_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v_v_102_);
lean_ctor_set(v_reuseFailAlloc_122_, 3, v___y_115_);
lean_ctor_set(v_reuseFailAlloc_122_, 4, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_nat_add(v___x_124_, v___y_126_);
lean_dec(v___y_126_);
lean_dec(v___x_124_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_l_103_);
lean_ctor_set(v___x_77_, 3, v_l_86_);
lean_ctor_set(v___x_77_, 2, v_v_85_);
lean_ctor_set(v___x_77_, 1, v_k_84_);
lean_ctor_set(v___x_77_, 0, v___x_127_);
v___x_129_ = v___x_77_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_k_84_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_v_85_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v_l_86_);
lean_ctor_set(v_reuseFailAlloc_133_, 4, v_l_103_);
v___x_129_ = v_reuseFailAlloc_133_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; 
v___x_130_ = lean_nat_add(v___x_81_, v_size_82_);
if (lean_obj_tag(v_r_104_) == 0)
{
lean_object* v_size_131_; 
v_size_131_ = lean_ctor_get(v_r_104_, 0);
lean_inc(v_size_131_);
v___y_114_ = v___x_130_;
v___y_115_ = v___x_129_;
v___y_116_ = v_size_131_;
goto v___jp_113_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___y_114_ = v___x_130_;
v___y_115_ = v___x_129_;
v___y_116_ = v___x_132_;
goto v___jp_113_;
}
}
}
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
lean_del_object(v___x_77_);
v___x_142_ = lean_nat_add(v___x_81_, v_size_83_);
lean_dec(v_size_83_);
v___x_143_ = lean_nat_add(v___x_142_, v_size_82_);
lean_dec(v___x_142_);
v___x_144_ = lean_nat_add(v___x_81_, v_size_82_);
v___x_145_ = lean_nat_add(v___x_144_, v_size_100_);
lean_dec(v___x_144_);
lean_inc_ref(v_r_75_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v_r_75_);
lean_ctor_set(v___x_97_, 3, v_r_87_);
lean_ctor_set(v___x_97_, 2, v_v_73_);
lean_ctor_set(v___x_97_, 1, v_k_72_);
lean_ctor_set(v___x_97_, 0, v___x_145_);
v___x_147_ = v___x_97_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v_r_87_);
lean_ctor_set(v_reuseFailAlloc_160_, 4, v_r_75_);
v___x_147_ = v_reuseFailAlloc_160_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_isSharedCheck_154_ = !lean_is_exclusive(v_r_75_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; lean_object* v_unused_159_; 
v_unused_155_ = lean_ctor_get(v_r_75_, 4);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_r_75_, 3);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_r_75_, 2);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_r_75_, 1);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_r_75_, 0);
lean_dec(v_unused_159_);
v___x_149_ = v_r_75_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_r_75_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 4, v___x_147_);
lean_ctor_set(v___x_149_, 3, v_l_86_);
lean_ctor_set(v___x_149_, 2, v_v_85_);
lean_ctor_set(v___x_149_, 1, v_k_84_);
lean_ctor_set(v___x_149_, 0, v___x_143_);
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_k_84_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v_v_85_);
lean_ctor_set(v_reuseFailAlloc_153_, 3, v_l_86_);
lean_ctor_set(v_reuseFailAlloc_153_, 4, v___x_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_167_; 
v_l_167_ = lean_ctor_get(v_impl_80_, 3);
if (lean_obj_tag(v_l_167_) == 0)
{
lean_object* v_r_168_; lean_object* v_k_169_; lean_object* v_v_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_181_; 
lean_inc_ref(v_l_167_);
v_r_168_ = lean_ctor_get(v_impl_80_, 4);
v_k_169_ = lean_ctor_get(v_impl_80_, 1);
v_v_170_ = lean_ctor_get(v_impl_80_, 2);
v_isSharedCheck_181_ = !lean_is_exclusive(v_impl_80_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; lean_object* v_unused_183_; 
v_unused_182_ = lean_ctor_get(v_impl_80_, 3);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_impl_80_, 0);
lean_dec(v_unused_183_);
v___x_172_ = v_impl_80_;
v_isShared_173_ = v_isSharedCheck_181_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_r_168_);
lean_inc(v_v_170_);
lean_inc(v_k_169_);
lean_dec(v_impl_80_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_181_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_168_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 3, v_r_168_);
lean_ctor_set(v___x_172_, 2, v_v_73_);
lean_ctor_set(v___x_172_, 1, v_k_72_);
lean_ctor_set(v___x_172_, 0, v___x_81_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_180_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_180_, 3, v_r_168_);
lean_ctor_set(v_reuseFailAlloc_180_, 4, v_r_168_);
v___x_176_ = v_reuseFailAlloc_180_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_176_);
lean_ctor_set(v___x_77_, 3, v_l_167_);
lean_ctor_set(v___x_77_, 2, v_v_170_);
lean_ctor_set(v___x_77_, 1, v_k_169_);
lean_ctor_set(v___x_77_, 0, v___x_174_);
v___x_178_ = v___x_77_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_l_167_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_object* v_r_184_; 
v_r_184_ = lean_ctor_get(v_impl_80_, 4);
lean_inc(v_r_184_);
if (lean_obj_tag(v_r_184_) == 0)
{
lean_object* v_k_185_; lean_object* v_v_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_209_; 
lean_inc(v_l_167_);
v_k_185_ = lean_ctor_get(v_impl_80_, 1);
v_v_186_ = lean_ctor_get(v_impl_80_, 2);
v_isSharedCheck_209_ = !lean_is_exclusive(v_impl_80_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; 
v_unused_210_ = lean_ctor_get(v_impl_80_, 4);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_impl_80_, 3);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_impl_80_, 0);
lean_dec(v_unused_212_);
v___x_188_ = v_impl_80_;
v_isShared_189_ = v_isSharedCheck_209_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_v_186_);
lean_inc(v_k_185_);
lean_dec(v_impl_80_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_209_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_k_190_; lean_object* v_v_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_205_; 
v_k_190_ = lean_ctor_get(v_r_184_, 1);
v_v_191_ = lean_ctor_get(v_r_184_, 2);
v_isSharedCheck_205_ = !lean_is_exclusive(v_r_184_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; 
v_unused_206_ = lean_ctor_get(v_r_184_, 4);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_r_184_, 3);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_r_184_, 0);
lean_dec(v_unused_208_);
v___x_193_ = v_r_184_;
v_isShared_194_ = v_isSharedCheck_205_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_v_191_);
lean_inc(v_k_190_);
lean_dec(v_r_184_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_205_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(3u);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 4, v_l_167_);
lean_ctor_set(v___x_193_, 3, v_l_167_);
lean_ctor_set(v___x_193_, 2, v_v_186_);
lean_ctor_set(v___x_193_, 1, v_k_185_);
lean_ctor_set(v___x_193_, 0, v___x_81_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_k_185_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_v_186_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_l_167_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_l_167_);
v___x_197_ = v_reuseFailAlloc_204_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 4, v_l_167_);
lean_ctor_set(v___x_188_, 2, v_v_73_);
lean_ctor_set(v___x_188_, 1, v_k_72_);
lean_ctor_set(v___x_188_, 0, v___x_81_);
v___x_199_ = v___x_188_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_l_167_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v_l_167_);
v___x_199_ = v_reuseFailAlloc_203_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_199_);
lean_ctor_set(v___x_77_, 3, v___x_197_);
lean_ctor_set(v___x_77_, 2, v_v_191_);
lean_ctor_set(v___x_77_, 1, v_k_190_);
lean_ctor_set(v___x_77_, 0, v___x_195_);
v___x_201_ = v___x_77_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_k_190_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_v_191_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_unsigned_to_nat(2u);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_r_184_);
lean_ctor_set(v___x_77_, 3, v_impl_80_);
lean_ctor_set(v___x_77_, 0, v___x_213_);
v___x_215_ = v___x_77_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v_impl_80_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v_r_184_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
case 1:
{
lean_object* v___x_218_; 
lean_dec(v_v_73_);
lean_dec(v_k_72_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 2, v_v_69_);
lean_ctor_set(v___x_77_, 1, v_k_68_);
v___x_218_ = v___x_77_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_size_71_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_r_75_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
default: 
{
lean_object* v_impl_220_; lean_object* v___x_221_; 
lean_dec(v_size_71_);
v_impl_220_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_68_, v_v_69_, v_r_75_);
v___x_221_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_74_) == 0)
{
lean_object* v_size_222_; lean_object* v_size_223_; lean_object* v_k_224_; lean_object* v_v_225_; lean_object* v_l_226_; lean_object* v_r_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_size_222_ = lean_ctor_get(v_l_74_, 0);
v_size_223_ = lean_ctor_get(v_impl_220_, 0);
v_k_224_ = lean_ctor_get(v_impl_220_, 1);
v_v_225_ = lean_ctor_get(v_impl_220_, 2);
v_l_226_ = lean_ctor_get(v_impl_220_, 3);
lean_inc(v_l_226_);
v_r_227_ = lean_ctor_get(v_impl_220_, 4);
v___x_228_ = lean_unsigned_to_nat(3u);
v___x_229_ = lean_nat_mul(v___x_228_, v_size_222_);
v___x_230_ = lean_nat_dec_lt(v___x_229_, v_size_223_);
lean_dec(v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
lean_dec(v_l_226_);
v___x_231_ = lean_nat_add(v___x_221_, v_size_222_);
v___x_232_ = lean_nat_add(v___x_231_, v_size_223_);
lean_dec(v___x_231_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_impl_220_);
lean_ctor_set(v___x_77_, 0, v___x_232_);
v___x_234_ = v___x_77_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_impl_220_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
else
{
lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_299_; 
lean_inc(v_r_227_);
lean_inc(v_v_225_);
lean_inc(v_k_224_);
lean_inc(v_size_223_);
v_isSharedCheck_299_ = !lean_is_exclusive(v_impl_220_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; 
v_unused_300_ = lean_ctor_get(v_impl_220_, 4);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_impl_220_, 3);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_impl_220_, 2);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_impl_220_, 1);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_impl_220_, 0);
lean_dec(v_unused_304_);
v___x_237_ = v_impl_220_;
v_isShared_238_ = v_isSharedCheck_299_;
goto v_resetjp_236_;
}
else
{
lean_dec(v_impl_220_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_299_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_size_239_; lean_object* v_k_240_; lean_object* v_v_241_; lean_object* v_l_242_; lean_object* v_r_243_; lean_object* v_size_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_size_239_ = lean_ctor_get(v_l_226_, 0);
v_k_240_ = lean_ctor_get(v_l_226_, 1);
v_v_241_ = lean_ctor_get(v_l_226_, 2);
v_l_242_ = lean_ctor_get(v_l_226_, 3);
v_r_243_ = lean_ctor_get(v_l_226_, 4);
v_size_244_ = lean_ctor_get(v_r_227_, 0);
v___x_245_ = lean_unsigned_to_nat(2u);
v___x_246_ = lean_nat_mul(v___x_245_, v_size_244_);
v___x_247_ = lean_nat_dec_lt(v_size_239_, v___x_246_);
lean_dec(v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_275_; 
lean_inc(v_r_243_);
lean_inc(v_l_242_);
lean_inc(v_v_241_);
lean_inc(v_k_240_);
v_isSharedCheck_275_ = !lean_is_exclusive(v_l_226_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; lean_object* v_unused_277_; lean_object* v_unused_278_; lean_object* v_unused_279_; lean_object* v_unused_280_; 
v_unused_276_ = lean_ctor_get(v_l_226_, 4);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_l_226_, 3);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_l_226_, 2);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_l_226_, 1);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_l_226_, 0);
lean_dec(v_unused_280_);
v___x_249_ = v_l_226_;
v_isShared_250_ = v_isSharedCheck_275_;
goto v_resetjp_248_;
}
else
{
lean_dec(v_l_226_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_275_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_265_; 
v___x_251_ = lean_nat_add(v___x_221_, v_size_222_);
v___x_252_ = lean_nat_add(v___x_251_, v_size_223_);
lean_dec(v_size_223_);
if (lean_obj_tag(v_l_242_) == 0)
{
lean_object* v_size_273_; 
v_size_273_ = lean_ctor_get(v_l_242_, 0);
lean_inc(v_size_273_);
v___y_265_ = v_size_273_;
goto v___jp_264_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___y_265_ = v___x_274_;
goto v___jp_264_;
}
v___jp_253_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = lean_nat_add(v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec(v___y_255_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 4, v_r_227_);
lean_ctor_set(v___x_249_, 3, v_r_243_);
lean_ctor_set(v___x_249_, 2, v_v_225_);
lean_ctor_set(v___x_249_, 1, v_k_224_);
lean_ctor_set(v___x_249_, 0, v___x_257_);
v___x_259_ = v___x_249_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_k_224_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_v_225_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v_r_243_);
lean_ctor_set(v_reuseFailAlloc_263_, 4, v_r_227_);
v___x_259_ = v_reuseFailAlloc_263_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_261_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 4, v___x_259_);
lean_ctor_set(v___x_237_, 3, v___y_254_);
lean_ctor_set(v___x_237_, 2, v_v_241_);
lean_ctor_set(v___x_237_, 1, v_k_240_);
lean_ctor_set(v___x_237_, 0, v___x_252_);
v___x_261_ = v___x_237_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_k_240_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_v_241_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v___y_254_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_nat_add(v___x_251_, v___y_265_);
lean_dec(v___y_265_);
lean_dec(v___x_251_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_l_242_);
lean_ctor_set(v___x_77_, 0, v___x_266_);
v___x_268_ = v___x_77_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v_l_242_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; 
v___x_269_ = lean_nat_add(v___x_221_, v_size_244_);
if (lean_obj_tag(v_r_243_) == 0)
{
lean_object* v_size_270_; 
v_size_270_ = lean_ctor_get(v_r_243_, 0);
lean_inc(v_size_270_);
v___y_254_ = v___x_268_;
v___y_255_ = v___x_269_;
v___y_256_ = v_size_270_;
goto v___jp_253_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_unsigned_to_nat(0u);
v___y_254_ = v___x_268_;
v___y_255_ = v___x_269_;
v___y_256_ = v___x_271_;
goto v___jp_253_;
}
}
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
lean_del_object(v___x_77_);
v___x_281_ = lean_nat_add(v___x_221_, v_size_222_);
v___x_282_ = lean_nat_add(v___x_281_, v_size_223_);
lean_dec(v_size_223_);
v___x_283_ = lean_nat_add(v___x_281_, v_size_239_);
lean_dec(v___x_281_);
lean_inc_ref(v_l_74_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 4, v_l_226_);
lean_ctor_set(v___x_237_, 3, v_l_74_);
lean_ctor_set(v___x_237_, 2, v_v_73_);
lean_ctor_set(v___x_237_, 1, v_k_72_);
lean_ctor_set(v___x_237_, 0, v___x_283_);
v___x_285_ = v___x_237_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_l_226_);
v___x_285_ = v_reuseFailAlloc_298_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_isSharedCheck_292_ = !lean_is_exclusive(v_l_74_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; 
v_unused_293_ = lean_ctor_get(v_l_74_, 4);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v_l_74_, 3);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_l_74_, 2);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_l_74_, 1);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_l_74_, 0);
lean_dec(v_unused_297_);
v___x_287_ = v_l_74_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_l_74_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 4, v_r_227_);
lean_ctor_set(v___x_287_, 3, v___x_285_);
lean_ctor_set(v___x_287_, 2, v_v_225_);
lean_ctor_set(v___x_287_, 1, v_k_224_);
lean_ctor_set(v___x_287_, 0, v___x_282_);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_224_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_225_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_r_227_);
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
}
}
else
{
lean_object* v_l_305_; 
v_l_305_ = lean_ctor_get(v_impl_220_, 3);
lean_inc(v_l_305_);
if (lean_obj_tag(v_l_305_) == 0)
{
lean_object* v_r_306_; lean_object* v_k_307_; lean_object* v_v_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_331_; 
v_r_306_ = lean_ctor_get(v_impl_220_, 4);
v_k_307_ = lean_ctor_get(v_impl_220_, 1);
v_v_308_ = lean_ctor_get(v_impl_220_, 2);
v_isSharedCheck_331_ = !lean_is_exclusive(v_impl_220_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; lean_object* v_unused_333_; 
v_unused_332_ = lean_ctor_get(v_impl_220_, 3);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_impl_220_, 0);
lean_dec(v_unused_333_);
v___x_310_ = v_impl_220_;
v_isShared_311_ = v_isSharedCheck_331_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_r_306_);
lean_inc(v_v_308_);
lean_inc(v_k_307_);
lean_dec(v_impl_220_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_331_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_k_312_; lean_object* v_v_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_327_; 
v_k_312_ = lean_ctor_get(v_l_305_, 1);
v_v_313_ = lean_ctor_get(v_l_305_, 2);
v_isSharedCheck_327_ = !lean_is_exclusive(v_l_305_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; 
v_unused_328_ = lean_ctor_get(v_l_305_, 4);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_l_305_, 3);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_l_305_, 0);
lean_dec(v_unused_330_);
v___x_315_ = v_l_305_;
v_isShared_316_ = v_isSharedCheck_327_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_v_313_);
lean_inc(v_k_312_);
lean_dec(v_l_305_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_327_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_306_, 2);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 4, v_r_306_);
lean_ctor_set(v___x_315_, 3, v_r_306_);
lean_ctor_set(v___x_315_, 2, v_v_73_);
lean_ctor_set(v___x_315_, 1, v_k_72_);
lean_ctor_set(v___x_315_, 0, v___x_221_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_r_306_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_r_306_);
v___x_319_ = v_reuseFailAlloc_326_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_321_; 
lean_inc(v_r_306_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 3, v_r_306_);
lean_ctor_set(v___x_310_, 0, v___x_221_);
v___x_321_ = v___x_310_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_k_307_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_v_308_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v_r_306_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_r_306_);
v___x_321_ = v_reuseFailAlloc_325_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_321_);
lean_ctor_set(v___x_77_, 3, v___x_319_);
lean_ctor_set(v___x_77_, 2, v_v_313_);
lean_ctor_set(v___x_77_, 1, v_k_312_);
lean_ctor_set(v___x_77_, 0, v___x_317_);
v___x_323_ = v___x_77_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_k_312_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_v_313_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
}
else
{
lean_object* v_r_334_; 
v_r_334_ = lean_ctor_get(v_impl_220_, 4);
lean_inc(v_r_334_);
if (lean_obj_tag(v_r_334_) == 0)
{
lean_object* v_k_335_; lean_object* v_v_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_347_; 
v_k_335_ = lean_ctor_get(v_impl_220_, 1);
v_v_336_ = lean_ctor_get(v_impl_220_, 2);
v_isSharedCheck_347_ = !lean_is_exclusive(v_impl_220_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; lean_object* v_unused_349_; lean_object* v_unused_350_; 
v_unused_348_ = lean_ctor_get(v_impl_220_, 4);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_impl_220_, 3);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_impl_220_, 0);
lean_dec(v_unused_350_);
v___x_338_ = v_impl_220_;
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_v_336_);
lean_inc(v_k_335_);
lean_dec(v_impl_220_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = lean_unsigned_to_nat(3u);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 4, v_l_305_);
lean_ctor_set(v___x_338_, 2, v_v_73_);
lean_ctor_set(v___x_338_, 1, v_k_72_);
lean_ctor_set(v___x_338_, 0, v___x_221_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_l_305_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_l_305_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_r_334_);
lean_ctor_set(v___x_77_, 3, v___x_342_);
lean_ctor_set(v___x_77_, 2, v_v_336_);
lean_ctor_set(v___x_77_, 1, v_k_335_);
lean_ctor_set(v___x_77_, 0, v___x_340_);
v___x_344_ = v___x_77_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_k_335_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_v_336_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v_r_334_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_unsigned_to_nat(2u);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_impl_220_);
lean_ctor_set(v___x_77_, 3, v_r_334_);
lean_ctor_set(v___x_77_, 0, v___x_351_);
v___x_353_ = v___x_77_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_r_334_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_impl_220_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
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
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_k_68_);
lean_ctor_set(v___x_357_, 2, v_v_69_);
lean_ctor_set(v___x_357_, 3, v_t_70_);
lean_ctor_set(v___x_357_, 4, v_t_70_);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1(size_t v_sz_358_, size_t v_i_359_, lean_object* v_bs_360_, lean_object* v___y_361_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_bs_360_);
lean_ctor_set(v___x_364_, 1, v___y_361_);
return v___x_364_;
}
else
{
lean_object* v_v_365_; lean_object* v_ci_366_; lean_object* v_range_367_; lean_object* v_toCommandContextInfo_368_; lean_object* v_parentDecl_x3f_369_; lean_object* v___x_370_; lean_object* v_bs_x27_371_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_387_; 
v_v_365_ = lean_array_uget_borrowed(v_bs_360_, v_i_359_);
v_ci_366_ = lean_ctor_get(v_v_365_, 4);
v_range_367_ = lean_ctor_get(v_v_365_, 2);
lean_inc_ref(v_range_367_);
v_toCommandContextInfo_368_ = lean_ctor_get(v_ci_366_, 0);
lean_inc_ref(v_toCommandContextInfo_368_);
v_parentDecl_x3f_369_ = lean_ctor_get(v_ci_366_, 1);
lean_inc(v_parentDecl_x3f_369_);
v___x_370_ = lean_unsigned_to_nat(0u);
v_bs_x27_371_ = lean_array_uset(v_bs_360_, v_i_359_, v___x_370_);
if (lean_obj_tag(v_parentDecl_x3f_369_) == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_box(0);
v___y_387_ = v___x_407_;
goto v___jp_386_;
}
else
{
lean_object* v_val_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_val_408_ = lean_ctor_get(v_parentDecl_x3f_369_, 0);
lean_inc(v_val_408_);
v___x_409_ = l_Lean_Name_toString(v_val_408_, v___x_363_);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
v___y_387_ = v___x_410_;
goto v___jp_386_;
}
v___jp_372_:
{
lean_object* v___x_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v___x_375_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_367_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v_range_367_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_359_, v___x_376_);
v___x_378_ = lean_array_uset(v_bs_x27_371_, v_i_359_, v___x_375_);
v_i_359_ = v___x_377_;
v_bs_360_ = v___x_378_;
v___y_361_ = v___y_374_;
goto _start;
}
v___jp_380_:
{
if (lean_obj_tag(v___y_381_) == 1)
{
if (lean_obj_tag(v___y_382_) == 1)
{
lean_object* v_val_383_; lean_object* v_val_384_; lean_object* v___x_385_; 
v_val_383_ = lean_ctor_get(v___y_381_, 0);
v_val_384_ = lean_ctor_get(v___y_382_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v___y_382_, 1);
lean_inc(v_val_383_);
v___x_385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_val_383_, v_val_384_, v___y_361_);
v___y_373_ = v___y_381_;
v___y_374_ = v___x_385_;
goto v___jp_372_;
}
else
{
lean_dec(v___y_382_);
v___y_373_ = v___y_381_;
v___y_374_ = v___y_361_;
goto v___jp_372_;
}
}
else
{
lean_dec(v___y_382_);
v___y_373_ = v___y_381_;
v___y_374_ = v___y_361_;
goto v___jp_372_;
}
}
v___jp_386_:
{
lean_object* v_cmdEnv_x3f_388_; 
v_cmdEnv_x3f_388_ = lean_ctor_get(v_toCommandContextInfo_368_, 1);
lean_inc(v_cmdEnv_x3f_388_);
lean_dec_ref(v_toCommandContextInfo_368_);
if (lean_obj_tag(v_cmdEnv_x3f_388_) == 0)
{
lean_object* v___x_389_; 
lean_dec(v_parentDecl_x3f_369_);
v___x_389_ = lean_box(0);
v___y_381_ = v___y_387_;
v___y_382_ = v___x_389_;
goto v___jp_380_;
}
else
{
if (lean_obj_tag(v_parentDecl_x3f_369_) == 0)
{
lean_object* v___x_390_; 
lean_dec_ref_known(v_cmdEnv_x3f_388_, 1);
v___x_390_ = lean_box(0);
v___y_381_ = v___y_387_;
v___y_382_ = v___x_390_;
goto v___jp_380_;
}
else
{
lean_object* v_val_391_; lean_object* v_val_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; 
v_val_391_ = lean_ctor_get(v_cmdEnv_x3f_388_, 0);
lean_inc(v_val_391_);
lean_dec_ref_known(v_cmdEnv_x3f_388_, 1);
v_val_392_ = lean_ctor_get(v_parentDecl_x3f_369_, 0);
lean_inc(v_val_392_);
lean_dec_ref_known(v_parentDecl_x3f_369_, 1);
v___x_393_ = l_Lean_declRangeExt;
v___x_394_ = lean_box(1);
v___x_395_ = 0;
v___x_396_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_393_, v_val_391_, v_val_392_, v___x_394_, v___x_395_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v___x_397_; 
v___x_397_ = lean_box(0);
v___y_381_ = v___y_387_;
v___y_382_ = v___x_397_;
goto v___jp_380_;
}
else
{
lean_object* v_val_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_val_398_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v___x_396_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_val_398_);
lean_dec(v___x_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_val_398_);
lean_dec(v_val_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
v___y_381_ = v___y_387_;
v___y_382_ = v___x_404_;
goto v___jp_380_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1___boxed(lean_object* v_sz_411_, lean_object* v_i_412_, lean_object* v_bs_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
size_t v_sz_boxed_416_; size_t v_i_boxed_417_; lean_object* v_res_418_; 
v_sz_boxed_416_ = lean_unbox_usize(v_sz_411_);
lean_dec(v_sz_411_);
v_i_boxed_417_ = lean_unbox_usize(v_i_412_);
lean_dec(v_i_412_);
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1(v_sz_boxed_416_, v_i_boxed_417_, v_bs_413_, v___y_414_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_toLspRefInfo(lean_object* v_i_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_definition_422_; lean_object* v_usages_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_494_; 
v_definition_422_ = lean_ctor_get(v_i_419_, 0);
v_usages_423_ = lean_ctor_get(v_i_419_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_i_419_);
if (v_isSharedCheck_494_ == 0)
{
v___x_425_ = v_i_419_;
v_isShared_426_ = v_isSharedCheck_494_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_usages_423_);
lean_inc(v_definition_422_);
lean_dec(v_i_419_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_494_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_fst_428_; lean_object* v_snd_429_; 
if (lean_obj_tag(v_definition_422_) == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_box(0);
v_fst_428_ = v___x_445_;
v_snd_429_ = v_a_420_;
goto v___jp_427_;
}
else
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_493_; 
v_val_446_ = lean_ctor_get(v_definition_422_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_definition_422_);
if (v_isSharedCheck_493_ == 0)
{
v___x_448_ = v_definition_422_;
v_isShared_449_ = v_isSharedCheck_493_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v_definition_422_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_493_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v_range_450_; lean_object* v_ci_451_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v_toCommandContextInfo_465_; lean_object* v_parentDecl_x3f_466_; lean_object* v___y_468_; 
v_range_450_ = lean_ctor_get(v_val_446_, 2);
lean_inc_ref(v_range_450_);
v_ci_451_ = lean_ctor_get(v_val_446_, 4);
lean_inc_ref(v_ci_451_);
lean_dec(v_val_446_);
v_toCommandContextInfo_465_ = lean_ctor_get(v_ci_451_, 0);
lean_inc_ref(v_toCommandContextInfo_465_);
v_parentDecl_x3f_466_ = lean_ctor_get(v_ci_451_, 1);
lean_inc(v_parentDecl_x3f_466_);
lean_dec_ref(v_ci_451_);
if (lean_obj_tag(v_parentDecl_x3f_466_) == 0)
{
lean_object* v___x_488_; 
v___x_488_ = lean_box(0);
v___y_468_ = v___x_488_;
goto v___jp_467_;
}
else
{
lean_object* v_val_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_val_489_ = lean_ctor_get(v_parentDecl_x3f_466_, 0);
v___x_490_ = 1;
lean_inc(v_val_489_);
v___x_491_ = l_Lean_Name_toString(v_val_489_, v___x_490_);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
v___y_468_ = v___x_492_;
goto v___jp_467_;
}
v___jp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_450_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v_range_450_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_455_);
v___x_457_ = v___x_448_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
v_fst_428_ = v___x_457_;
v_snd_429_ = v___y_454_;
goto v___jp_427_;
}
}
v___jp_459_:
{
if (lean_obj_tag(v___y_460_) == 1)
{
if (lean_obj_tag(v___y_461_) == 1)
{
lean_object* v_val_462_; lean_object* v_val_463_; lean_object* v___x_464_; 
v_val_462_ = lean_ctor_get(v___y_460_, 0);
v_val_463_ = lean_ctor_get(v___y_461_, 0);
lean_inc(v_val_463_);
lean_dec_ref_known(v___y_461_, 1);
lean_inc(v_val_462_);
v___x_464_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_val_462_, v_val_463_, v_a_420_);
v___y_453_ = v___y_460_;
v___y_454_ = v___x_464_;
goto v___jp_452_;
}
else
{
lean_dec(v___y_461_);
v___y_453_ = v___y_460_;
v___y_454_ = v_a_420_;
goto v___jp_452_;
}
}
else
{
lean_dec(v___y_461_);
v___y_453_ = v___y_460_;
v___y_454_ = v_a_420_;
goto v___jp_452_;
}
}
v___jp_467_:
{
lean_object* v_cmdEnv_x3f_469_; 
v_cmdEnv_x3f_469_ = lean_ctor_get(v_toCommandContextInfo_465_, 1);
lean_inc(v_cmdEnv_x3f_469_);
lean_dec_ref(v_toCommandContextInfo_465_);
if (lean_obj_tag(v_cmdEnv_x3f_469_) == 0)
{
lean_object* v___x_470_; 
lean_dec(v_parentDecl_x3f_466_);
v___x_470_ = lean_box(0);
v___y_460_ = v___y_468_;
v___y_461_ = v___x_470_;
goto v___jp_459_;
}
else
{
if (lean_obj_tag(v_parentDecl_x3f_466_) == 0)
{
lean_object* v___x_471_; 
lean_dec_ref_known(v_cmdEnv_x3f_469_, 1);
v___x_471_ = lean_box(0);
v___y_460_ = v___y_468_;
v___y_461_ = v___x_471_;
goto v___jp_459_;
}
else
{
lean_object* v_val_472_; lean_object* v_val_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; 
v_val_472_ = lean_ctor_get(v_cmdEnv_x3f_469_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v_cmdEnv_x3f_469_, 1);
v_val_473_ = lean_ctor_get(v_parentDecl_x3f_466_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v_parentDecl_x3f_466_, 1);
v___x_474_ = l_Lean_declRangeExt;
v___x_475_ = lean_box(1);
v___x_476_ = 0;
v___x_477_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_474_, v_val_472_, v_val_473_, v___x_475_, v___x_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(0);
v___y_460_ = v___y_468_;
v___y_461_ = v___x_478_;
goto v___jp_459_;
}
else
{
lean_object* v_val_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v_val_479_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_477_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_val_479_);
lean_dec(v___x_477_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_val_479_);
lean_dec(v_val_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
v___y_460_ = v___y_468_;
v___y_461_ = v___x_485_;
goto v___jp_459_;
}
}
}
}
}
}
}
}
v___jp_427_:
{
size_t v_sz_430_; size_t v___x_431_; lean_object* v___x_432_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_444_; 
v_sz_430_ = lean_array_size(v_usages_423_);
v___x_431_ = ((size_t)0ULL);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1(v_sz_430_, v___x_431_, v_usages_423_, v_snd_429_);
v_fst_433_ = lean_ctor_get(v___x_432_, 0);
v_snd_434_ = lean_ctor_get(v___x_432_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_444_ == 0)
{
v___x_436_ = v___x_432_;
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snd_434_);
lean_inc(v_fst_433_);
lean_dec(v___x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v_fst_433_);
lean_ctor_set(v___x_425_, 0, v_fst_428_);
v___x_439_ = v___x_425_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_fst_428_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_fst_433_);
v___x_439_ = v_reuseFailAlloc_443_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_snd_434_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_toLspRefInfo___boxed(lean_object* v_i_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Server_RefInfo_toLspRefInfo(v_i_495_, v_a_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0(lean_object* v_00_u03b2_499_, lean_object* v_k_500_, lean_object* v_v_501_, lean_object* v_t_502_, lean_object* v_hl_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_500_, v_v_501_, v_t_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(lean_object* v_ref_505_, lean_object* v_x_506_){
_start:
{
if (lean_obj_tag(v_x_506_) == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = ((lean_object*)(l_Lean_Server_RefInfo_empty));
v___x_508_ = l_Lean_Server_RefInfo_addRef(v___x_507_, v_ref_505_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_val_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_val_510_ = lean_ctor_get(v_x_506_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_506_);
if (v_isSharedCheck_518_ == 0)
{
v___x_512_ = v_x_506_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_val_510_);
lean_dec(v_x_506_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = l_Lean_Server_RefInfo_addRef(v_val_510_, v_ref_505_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(lean_object* v_ref_519_, lean_object* v_k_520_, lean_object* v_t_521_){
_start:
{
if (lean_obj_tag(v_t_521_) == 0)
{
lean_object* v_size_522_; lean_object* v_k_523_; lean_object* v_v_524_; lean_object* v_l_525_; lean_object* v_r_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_541_; 
v_size_522_ = lean_ctor_get(v_t_521_, 0);
v_k_523_ = lean_ctor_get(v_t_521_, 1);
v_v_524_ = lean_ctor_get(v_t_521_, 2);
v_l_525_ = lean_ctor_get(v_t_521_, 3);
v_r_526_ = lean_ctor_get(v_t_521_, 4);
v_isSharedCheck_541_ = !lean_is_exclusive(v_t_521_);
if (v_isSharedCheck_541_ == 0)
{
v___x_528_ = v_t_521_;
v_isShared_529_ = v_isSharedCheck_541_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_r_526_);
lean_inc(v_l_525_);
lean_inc(v_v_524_);
lean_inc(v_k_523_);
lean_inc(v_size_522_);
lean_dec(v_t_521_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_541_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
uint8_t v___x_530_; 
v___x_530_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_520_, v_k_523_);
switch(v___x_530_)
{
case 0:
{
lean_object* v_impl_531_; lean_object* v___x_532_; 
lean_del_object(v___x_528_);
lean_dec(v_size_522_);
v_impl_531_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_519_, v_k_520_, v_l_525_);
v___x_532_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_523_, v_v_524_, v_impl_531_, v_r_526_);
return v___x_532_;
}
case 1:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_val_535_; lean_object* v___x_537_; 
lean_dec(v_k_523_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v_v_524_);
v___x_534_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(v_ref_519_, v___x_533_);
v_val_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_val_535_);
lean_dec(v___x_534_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 2, v_val_535_);
lean_ctor_set(v___x_528_, 1, v_k_520_);
v___x_537_ = v___x_528_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_size_522_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_k_520_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_val_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_l_525_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_r_526_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
default: 
{
lean_object* v_impl_539_; lean_object* v___x_540_; 
lean_del_object(v___x_528_);
lean_dec(v_size_522_);
v_impl_539_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_519_, v_k_520_, v_r_526_);
v___x_540_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_523_, v_v_524_, v_l_525_, v_impl_539_);
return v___x_540_;
}
}
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_val_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_542_ = lean_box(0);
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(v_ref_519_, v___x_542_);
v_val_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_val_544_);
lean_dec(v___x_543_);
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v_k_520_);
lean_ctor_set(v___x_546_, 2, v_val_544_);
lean_ctor_set(v___x_546_, 3, v_t_521_);
lean_ctor_set(v___x_546_, 4, v_t_521_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_addRef(lean_object* v_self_547_, lean_object* v_ref_548_){
_start:
{
lean_object* v_ident_549_; lean_object* v___x_550_; 
v_ident_549_ = lean_ctor_get(v_ref_548_, 0);
lean_inc_ref(v_ident_549_);
v___x_550_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_548_, v_ident_549_, v_self_547_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0(lean_object* v_ref_551_, lean_object* v_k_552_, lean_object* v_t_553_, lean_object* v_hl_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_551_, v_k_552_, v_t_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(lean_object* v_k_556_, lean_object* v_v_557_, lean_object* v_t_558_){
_start:
{
if (lean_obj_tag(v_t_558_) == 0)
{
lean_object* v_size_559_; lean_object* v_k_560_; lean_object* v_v_561_; lean_object* v_l_562_; lean_object* v_r_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_843_; 
v_size_559_ = lean_ctor_get(v_t_558_, 0);
v_k_560_ = lean_ctor_get(v_t_558_, 1);
v_v_561_ = lean_ctor_get(v_t_558_, 2);
v_l_562_ = lean_ctor_get(v_t_558_, 3);
v_r_563_ = lean_ctor_get(v_t_558_, 4);
v_isSharedCheck_843_ = !lean_is_exclusive(v_t_558_);
if (v_isSharedCheck_843_ == 0)
{
v___x_565_ = v_t_558_;
v_isShared_566_ = v_isSharedCheck_843_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_r_563_);
lean_inc(v_l_562_);
lean_inc(v_v_561_);
lean_inc(v_k_560_);
lean_inc(v_size_559_);
lean_dec(v_t_558_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_843_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
uint8_t v___x_567_; 
v___x_567_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_556_, v_k_560_);
switch(v___x_567_)
{
case 0:
{
lean_object* v_impl_568_; lean_object* v___x_569_; 
lean_dec(v_size_559_);
v_impl_568_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_556_, v_v_557_, v_l_562_);
v___x_569_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_563_) == 0)
{
lean_object* v_size_570_; lean_object* v_size_571_; lean_object* v_k_572_; lean_object* v_v_573_; lean_object* v_l_574_; lean_object* v_r_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_size_570_ = lean_ctor_get(v_r_563_, 0);
v_size_571_ = lean_ctor_get(v_impl_568_, 0);
v_k_572_ = lean_ctor_get(v_impl_568_, 1);
v_v_573_ = lean_ctor_get(v_impl_568_, 2);
v_l_574_ = lean_ctor_get(v_impl_568_, 3);
v_r_575_ = lean_ctor_get(v_impl_568_, 4);
lean_inc(v_r_575_);
v___x_576_ = lean_unsigned_to_nat(3u);
v___x_577_ = lean_nat_mul(v___x_576_, v_size_570_);
v___x_578_ = lean_nat_dec_lt(v___x_577_, v_size_571_);
lean_dec(v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec(v_r_575_);
v___x_579_ = lean_nat_add(v___x_569_, v_size_571_);
v___x_580_ = lean_nat_add(v___x_579_, v_size_570_);
lean_dec(v___x_579_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 3, v_impl_568_);
lean_ctor_set(v___x_565_, 0, v___x_580_);
v___x_582_ = v___x_565_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_impl_568_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v_r_563_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
else
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_649_; 
lean_inc(v_l_574_);
lean_inc(v_v_573_);
lean_inc(v_k_572_);
lean_inc(v_size_571_);
v_isSharedCheck_649_ = !lean_is_exclusive(v_impl_568_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; lean_object* v_unused_653_; lean_object* v_unused_654_; 
v_unused_650_ = lean_ctor_get(v_impl_568_, 4);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_impl_568_, 3);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_impl_568_, 2);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v_impl_568_, 1);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_impl_568_, 0);
lean_dec(v_unused_654_);
v___x_585_ = v_impl_568_;
v_isShared_586_ = v_isSharedCheck_649_;
goto v_resetjp_584_;
}
else
{
lean_dec(v_impl_568_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_649_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_size_587_; lean_object* v_size_588_; lean_object* v_k_589_; lean_object* v_v_590_; lean_object* v_l_591_; lean_object* v_r_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_size_587_ = lean_ctor_get(v_l_574_, 0);
v_size_588_ = lean_ctor_get(v_r_575_, 0);
v_k_589_ = lean_ctor_get(v_r_575_, 1);
v_v_590_ = lean_ctor_get(v_r_575_, 2);
v_l_591_ = lean_ctor_get(v_r_575_, 3);
v_r_592_ = lean_ctor_get(v_r_575_, 4);
v___x_593_ = lean_unsigned_to_nat(2u);
v___x_594_ = lean_nat_mul(v___x_593_, v_size_587_);
v___x_595_ = lean_nat_dec_lt(v_size_588_, v___x_594_);
lean_dec(v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_624_; 
lean_inc(v_r_592_);
lean_inc(v_l_591_);
lean_inc(v_v_590_);
lean_inc(v_k_589_);
v_isSharedCheck_624_ = !lean_is_exclusive(v_r_575_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; lean_object* v_unused_626_; lean_object* v_unused_627_; lean_object* v_unused_628_; lean_object* v_unused_629_; 
v_unused_625_ = lean_ctor_get(v_r_575_, 4);
lean_dec(v_unused_625_);
v_unused_626_ = lean_ctor_get(v_r_575_, 3);
lean_dec(v_unused_626_);
v_unused_627_ = lean_ctor_get(v_r_575_, 2);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_r_575_, 1);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_r_575_, 0);
lean_dec(v_unused_629_);
v___x_597_ = v_r_575_;
v_isShared_598_ = v_isSharedCheck_624_;
goto v_resetjp_596_;
}
else
{
lean_dec(v_r_575_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_624_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___x_612_; lean_object* v___y_614_; 
v___x_599_ = lean_nat_add(v___x_569_, v_size_571_);
lean_dec(v_size_571_);
v___x_600_ = lean_nat_add(v___x_599_, v_size_570_);
lean_dec(v___x_599_);
v___x_612_ = lean_nat_add(v___x_569_, v_size_587_);
if (lean_obj_tag(v_l_591_) == 0)
{
lean_object* v_size_622_; 
v_size_622_ = lean_ctor_get(v_l_591_, 0);
lean_inc(v_size_622_);
v___y_614_ = v_size_622_;
goto v___jp_613_;
}
else
{
lean_object* v___x_623_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___y_614_ = v___x_623_;
goto v___jp_613_;
}
v___jp_601_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_nat_add(v___y_602_, v___y_604_);
lean_dec(v___y_604_);
lean_dec(v___y_602_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 4, v_r_563_);
lean_ctor_set(v___x_597_, 3, v_r_592_);
lean_ctor_set(v___x_597_, 2, v_v_561_);
lean_ctor_set(v___x_597_, 1, v_k_560_);
lean_ctor_set(v___x_597_, 0, v___x_605_);
v___x_607_ = v___x_597_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_r_592_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_r_563_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 4, v___x_607_);
lean_ctor_set(v___x_585_, 3, v___y_603_);
lean_ctor_set(v___x_585_, 2, v_v_590_);
lean_ctor_set(v___x_585_, 1, v_k_589_);
lean_ctor_set(v___x_585_, 0, v___x_600_);
v___x_609_ = v___x_585_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v___y_603_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
v___jp_613_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_nat_add(v___x_612_, v___y_614_);
lean_dec(v___y_614_);
lean_dec(v___x_612_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v_l_591_);
lean_ctor_set(v___x_565_, 3, v_l_574_);
lean_ctor_set(v___x_565_, 2, v_v_573_);
lean_ctor_set(v___x_565_, 1, v_k_572_);
lean_ctor_set(v___x_565_, 0, v___x_615_);
v___x_617_ = v___x_565_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_k_572_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_v_573_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_l_574_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_l_591_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; 
v___x_618_ = lean_nat_add(v___x_569_, v_size_570_);
if (lean_obj_tag(v_r_592_) == 0)
{
lean_object* v_size_619_; 
v_size_619_ = lean_ctor_get(v_r_592_, 0);
lean_inc(v_size_619_);
v___y_602_ = v___x_618_;
v___y_603_ = v___x_617_;
v___y_604_ = v_size_619_;
goto v___jp_601_;
}
else
{
lean_object* v___x_620_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___y_602_ = v___x_618_;
v___y_603_ = v___x_617_;
v___y_604_ = v___x_620_;
goto v___jp_601_;
}
}
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
lean_del_object(v___x_565_);
v___x_630_ = lean_nat_add(v___x_569_, v_size_571_);
lean_dec(v_size_571_);
v___x_631_ = lean_nat_add(v___x_630_, v_size_570_);
lean_dec(v___x_630_);
v___x_632_ = lean_nat_add(v___x_569_, v_size_570_);
v___x_633_ = lean_nat_add(v___x_632_, v_size_588_);
lean_dec(v___x_632_);
lean_inc_ref(v_r_563_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 4, v_r_563_);
lean_ctor_set(v___x_585_, 3, v_r_575_);
lean_ctor_set(v___x_585_, 2, v_v_561_);
lean_ctor_set(v___x_585_, 1, v_k_560_);
lean_ctor_set(v___x_585_, 0, v___x_633_);
v___x_635_ = v___x_585_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_r_575_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v_r_563_);
v___x_635_ = v_reuseFailAlloc_648_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_isSharedCheck_642_ = !lean_is_exclusive(v_r_563_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; lean_object* v_unused_646_; lean_object* v_unused_647_; 
v_unused_643_ = lean_ctor_get(v_r_563_, 4);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_r_563_, 3);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_r_563_, 2);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_r_563_, 1);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_r_563_, 0);
lean_dec(v_unused_647_);
v___x_637_ = v_r_563_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_dec(v_r_563_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 4, v___x_635_);
lean_ctor_set(v___x_637_, 3, v_l_574_);
lean_ctor_set(v___x_637_, 2, v_v_573_);
lean_ctor_set(v___x_637_, 1, v_k_572_);
lean_ctor_set(v___x_637_, 0, v___x_631_);
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_k_572_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_v_573_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_l_574_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v___x_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_655_; 
v_l_655_ = lean_ctor_get(v_impl_568_, 3);
if (lean_obj_tag(v_l_655_) == 0)
{
lean_object* v_r_656_; lean_object* v_k_657_; lean_object* v_v_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_669_; 
lean_inc_ref(v_l_655_);
v_r_656_ = lean_ctor_get(v_impl_568_, 4);
v_k_657_ = lean_ctor_get(v_impl_568_, 1);
v_v_658_ = lean_ctor_get(v_impl_568_, 2);
v_isSharedCheck_669_ = !lean_is_exclusive(v_impl_568_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; 
v_unused_670_ = lean_ctor_get(v_impl_568_, 3);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_impl_568_, 0);
lean_dec(v_unused_671_);
v___x_660_ = v_impl_568_;
v_isShared_661_ = v_isSharedCheck_669_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_r_656_);
lean_inc(v_v_658_);
lean_inc(v_k_657_);
lean_dec(v_impl_568_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_669_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_656_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 3, v_r_656_);
lean_ctor_set(v___x_660_, 2, v_v_561_);
lean_ctor_set(v___x_660_, 1, v_k_560_);
lean_ctor_set(v___x_660_, 0, v___x_569_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_r_656_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_r_656_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v___x_664_);
lean_ctor_set(v___x_565_, 3, v_l_655_);
lean_ctor_set(v___x_565_, 2, v_v_658_);
lean_ctor_set(v___x_565_, 1, v_k_657_);
lean_ctor_set(v___x_565_, 0, v___x_662_);
v___x_666_ = v___x_565_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_k_657_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_v_658_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_l_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_r_672_; 
v_r_672_ = lean_ctor_get(v_impl_568_, 4);
lean_inc(v_r_672_);
if (lean_obj_tag(v_r_672_) == 0)
{
lean_object* v_k_673_; lean_object* v_v_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_697_; 
lean_inc(v_l_655_);
v_k_673_ = lean_ctor_get(v_impl_568_, 1);
v_v_674_ = lean_ctor_get(v_impl_568_, 2);
v_isSharedCheck_697_ = !lean_is_exclusive(v_impl_568_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_698_ = lean_ctor_get(v_impl_568_, 4);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_impl_568_, 3);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_impl_568_, 0);
lean_dec(v_unused_700_);
v___x_676_ = v_impl_568_;
v_isShared_677_ = v_isSharedCheck_697_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_v_674_);
lean_inc(v_k_673_);
lean_dec(v_impl_568_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_697_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_k_678_; lean_object* v_v_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_693_; 
v_k_678_ = lean_ctor_get(v_r_672_, 1);
v_v_679_ = lean_ctor_get(v_r_672_, 2);
v_isSharedCheck_693_ = !lean_is_exclusive(v_r_672_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_694_ = lean_ctor_get(v_r_672_, 4);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_r_672_, 3);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_r_672_, 0);
lean_dec(v_unused_696_);
v___x_681_ = v_r_672_;
v_isShared_682_ = v_isSharedCheck_693_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_v_679_);
lean_inc(v_k_678_);
lean_dec(v_r_672_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_693_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_unsigned_to_nat(3u);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 4, v_l_655_);
lean_ctor_set(v___x_681_, 3, v_l_655_);
lean_ctor_set(v___x_681_, 2, v_v_674_);
lean_ctor_set(v___x_681_, 1, v_k_673_);
lean_ctor_set(v___x_681_, 0, v___x_569_);
v___x_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_673_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_674_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_l_655_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_l_655_);
v___x_685_ = v_reuseFailAlloc_692_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 4, v_l_655_);
lean_ctor_set(v___x_676_, 2, v_v_561_);
lean_ctor_set(v___x_676_, 1, v_k_560_);
lean_ctor_set(v___x_676_, 0, v___x_569_);
v___x_687_ = v___x_676_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_l_655_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v_l_655_);
v___x_687_ = v_reuseFailAlloc_691_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v___x_687_);
lean_ctor_set(v___x_565_, 3, v___x_685_);
lean_ctor_set(v___x_565_, 2, v_v_679_);
lean_ctor_set(v___x_565_, 1, v_k_678_);
lean_ctor_set(v___x_565_, 0, v___x_683_);
v___x_689_ = v___x_565_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_k_678_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_v_679_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(2u);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v_r_672_);
lean_ctor_set(v___x_565_, 3, v_impl_568_);
lean_ctor_set(v___x_565_, 0, v___x_701_);
v___x_703_ = v___x_565_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_impl_568_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v_r_672_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
case 1:
{
lean_object* v___x_706_; 
lean_dec(v_v_561_);
lean_dec(v_k_560_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 2, v_v_557_);
lean_ctor_set(v___x_565_, 1, v_k_556_);
v___x_706_ = v___x_565_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_size_559_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_k_556_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_v_557_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_l_562_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_r_563_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
default: 
{
lean_object* v_impl_708_; lean_object* v___x_709_; 
lean_dec(v_size_559_);
v_impl_708_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_556_, v_v_557_, v_r_563_);
v___x_709_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_562_) == 0)
{
lean_object* v_size_710_; lean_object* v_size_711_; lean_object* v_k_712_; lean_object* v_v_713_; lean_object* v_l_714_; lean_object* v_r_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_size_710_ = lean_ctor_get(v_l_562_, 0);
v_size_711_ = lean_ctor_get(v_impl_708_, 0);
v_k_712_ = lean_ctor_get(v_impl_708_, 1);
v_v_713_ = lean_ctor_get(v_impl_708_, 2);
v_l_714_ = lean_ctor_get(v_impl_708_, 3);
lean_inc(v_l_714_);
v_r_715_ = lean_ctor_get(v_impl_708_, 4);
v___x_716_ = lean_unsigned_to_nat(3u);
v___x_717_ = lean_nat_mul(v___x_716_, v_size_710_);
v___x_718_ = lean_nat_dec_lt(v___x_717_, v_size_711_);
lean_dec(v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
lean_dec(v_l_714_);
v___x_719_ = lean_nat_add(v___x_709_, v_size_710_);
v___x_720_ = lean_nat_add(v___x_719_, v_size_711_);
lean_dec(v___x_719_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v_impl_708_);
lean_ctor_set(v___x_565_, 0, v___x_720_);
v___x_722_ = v___x_565_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_l_562_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_impl_708_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_787_; 
lean_inc(v_r_715_);
lean_inc(v_v_713_);
lean_inc(v_k_712_);
lean_inc(v_size_711_);
v_isSharedCheck_787_ = !lean_is_exclusive(v_impl_708_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; lean_object* v_unused_792_; 
v_unused_788_ = lean_ctor_get(v_impl_708_, 4);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_impl_708_, 3);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_impl_708_, 2);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_impl_708_, 1);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_impl_708_, 0);
lean_dec(v_unused_792_);
v___x_725_ = v_impl_708_;
v_isShared_726_ = v_isSharedCheck_787_;
goto v_resetjp_724_;
}
else
{
lean_dec(v_impl_708_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_787_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_size_727_; lean_object* v_k_728_; lean_object* v_v_729_; lean_object* v_l_730_; lean_object* v_r_731_; lean_object* v_size_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_size_727_ = lean_ctor_get(v_l_714_, 0);
v_k_728_ = lean_ctor_get(v_l_714_, 1);
v_v_729_ = lean_ctor_get(v_l_714_, 2);
v_l_730_ = lean_ctor_get(v_l_714_, 3);
v_r_731_ = lean_ctor_get(v_l_714_, 4);
v_size_732_ = lean_ctor_get(v_r_715_, 0);
v___x_733_ = lean_unsigned_to_nat(2u);
v___x_734_ = lean_nat_mul(v___x_733_, v_size_732_);
v___x_735_ = lean_nat_dec_lt(v_size_727_, v___x_734_);
lean_dec(v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_763_; 
lean_inc(v_r_731_);
lean_inc(v_l_730_);
lean_inc(v_v_729_);
lean_inc(v_k_728_);
v_isSharedCheck_763_ = !lean_is_exclusive(v_l_714_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; 
v_unused_764_ = lean_ctor_get(v_l_714_, 4);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_l_714_, 3);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_l_714_, 2);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_l_714_, 1);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_l_714_, 0);
lean_dec(v_unused_768_);
v___x_737_ = v_l_714_;
v_isShared_738_ = v_isSharedCheck_763_;
goto v_resetjp_736_;
}
else
{
lean_dec(v_l_714_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_763_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_753_; 
v___x_739_ = lean_nat_add(v___x_709_, v_size_710_);
v___x_740_ = lean_nat_add(v___x_739_, v_size_711_);
lean_dec(v_size_711_);
if (lean_obj_tag(v_l_730_) == 0)
{
lean_object* v_size_761_; 
v_size_761_ = lean_ctor_get(v_l_730_, 0);
lean_inc(v_size_761_);
v___y_753_ = v_size_761_;
goto v___jp_752_;
}
else
{
lean_object* v___x_762_; 
v___x_762_ = lean_unsigned_to_nat(0u);
v___y_753_ = v___x_762_;
goto v___jp_752_;
}
v___jp_741_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = lean_nat_add(v___y_742_, v___y_744_);
lean_dec(v___y_744_);
lean_dec(v___y_742_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 4, v_r_715_);
lean_ctor_set(v___x_737_, 3, v_r_731_);
lean_ctor_set(v___x_737_, 2, v_v_713_);
lean_ctor_set(v___x_737_, 1, v_k_712_);
lean_ctor_set(v___x_737_, 0, v___x_745_);
v___x_747_ = v___x_737_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_k_712_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_v_713_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_r_731_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_r_715_);
v___x_747_ = v_reuseFailAlloc_751_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 4, v___x_747_);
lean_ctor_set(v___x_725_, 3, v___y_743_);
lean_ctor_set(v___x_725_, 2, v_v_729_);
lean_ctor_set(v___x_725_, 1, v_k_728_);
lean_ctor_set(v___x_725_, 0, v___x_740_);
v___x_749_ = v___x_725_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_k_728_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_v_729_);
lean_ctor_set(v_reuseFailAlloc_750_, 3, v___y_743_);
lean_ctor_set(v_reuseFailAlloc_750_, 4, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = lean_nat_add(v___x_739_, v___y_753_);
lean_dec(v___y_753_);
lean_dec(v___x_739_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v_l_730_);
lean_ctor_set(v___x_565_, 0, v___x_754_);
v___x_756_ = v___x_565_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_l_562_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v_l_730_);
v___x_756_ = v_reuseFailAlloc_760_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; 
v___x_757_ = lean_nat_add(v___x_709_, v_size_732_);
if (lean_obj_tag(v_r_731_) == 0)
{
lean_object* v_size_758_; 
v_size_758_ = lean_ctor_get(v_r_731_, 0);
lean_inc(v_size_758_);
v___y_742_ = v___x_757_;
v___y_743_ = v___x_756_;
v___y_744_ = v_size_758_;
goto v___jp_741_;
}
else
{
lean_object* v___x_759_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___y_742_ = v___x_757_;
v___y_743_ = v___x_756_;
v___y_744_ = v___x_759_;
goto v___jp_741_;
}
}
}
}
}
else
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_del_object(v___x_565_);
v___x_769_ = lean_nat_add(v___x_709_, v_size_710_);
v___x_770_ = lean_nat_add(v___x_769_, v_size_711_);
lean_dec(v_size_711_);
v___x_771_ = lean_nat_add(v___x_769_, v_size_727_);
lean_dec(v___x_769_);
lean_inc_ref(v_l_562_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 4, v_l_714_);
lean_ctor_set(v___x_725_, 3, v_l_562_);
lean_ctor_set(v___x_725_, 2, v_v_561_);
lean_ctor_set(v___x_725_, 1, v_k_560_);
lean_ctor_set(v___x_725_, 0, v___x_771_);
v___x_773_ = v___x_725_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_l_562_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_l_714_);
v___x_773_ = v_reuseFailAlloc_786_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_isSharedCheck_780_ = !lean_is_exclusive(v_l_562_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_781_ = lean_ctor_get(v_l_562_, 4);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_l_562_, 3);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_l_562_, 2);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_l_562_, 1);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_l_562_, 0);
lean_dec(v_unused_785_);
v___x_775_ = v_l_562_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_dec(v_l_562_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 4, v_r_715_);
lean_ctor_set(v___x_775_, 3, v___x_773_);
lean_ctor_set(v___x_775_, 2, v_v_713_);
lean_ctor_set(v___x_775_, 1, v_k_712_);
lean_ctor_set(v___x_775_, 0, v___x_770_);
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_k_712_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_v_713_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_r_715_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_793_; 
v_l_793_ = lean_ctor_get(v_impl_708_, 3);
lean_inc(v_l_793_);
if (lean_obj_tag(v_l_793_) == 0)
{
lean_object* v_r_794_; lean_object* v_k_795_; lean_object* v_v_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_819_; 
v_r_794_ = lean_ctor_get(v_impl_708_, 4);
v_k_795_ = lean_ctor_get(v_impl_708_, 1);
v_v_796_ = lean_ctor_get(v_impl_708_, 2);
v_isSharedCheck_819_ = !lean_is_exclusive(v_impl_708_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_820_ = lean_ctor_get(v_impl_708_, 3);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_impl_708_, 0);
lean_dec(v_unused_821_);
v___x_798_ = v_impl_708_;
v_isShared_799_ = v_isSharedCheck_819_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_r_794_);
lean_inc(v_v_796_);
lean_inc(v_k_795_);
lean_dec(v_impl_708_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_819_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_k_800_; lean_object* v_v_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_815_; 
v_k_800_ = lean_ctor_get(v_l_793_, 1);
v_v_801_ = lean_ctor_get(v_l_793_, 2);
v_isSharedCheck_815_ = !lean_is_exclusive(v_l_793_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_816_ = lean_ctor_get(v_l_793_, 4);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_l_793_, 3);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_l_793_, 0);
lean_dec(v_unused_818_);
v___x_803_ = v_l_793_;
v_isShared_804_ = v_isSharedCheck_815_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_v_801_);
lean_inc(v_k_800_);
lean_dec(v_l_793_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_815_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_794_, 2);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 4, v_r_794_);
lean_ctor_set(v___x_803_, 3, v_r_794_);
lean_ctor_set(v___x_803_, 2, v_v_561_);
lean_ctor_set(v___x_803_, 1, v_k_560_);
lean_ctor_set(v___x_803_, 0, v___x_709_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_r_794_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_r_794_);
v___x_807_ = v_reuseFailAlloc_814_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
lean_inc(v_r_794_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 3, v_r_794_);
lean_ctor_set(v___x_798_, 0, v___x_709_);
v___x_809_ = v___x_798_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_795_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_796_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_r_794_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_r_794_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v___x_809_);
lean_ctor_set(v___x_565_, 3, v___x_807_);
lean_ctor_set(v___x_565_, 2, v_v_801_);
lean_ctor_set(v___x_565_, 1, v_k_800_);
lean_ctor_set(v___x_565_, 0, v___x_805_);
v___x_811_ = v___x_565_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_k_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_v_801_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
else
{
lean_object* v_r_822_; 
v_r_822_ = lean_ctor_get(v_impl_708_, 4);
lean_inc(v_r_822_);
if (lean_obj_tag(v_r_822_) == 0)
{
lean_object* v_k_823_; lean_object* v_v_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_835_; 
v_k_823_ = lean_ctor_get(v_impl_708_, 1);
v_v_824_ = lean_ctor_get(v_impl_708_, 2);
v_isSharedCheck_835_ = !lean_is_exclusive(v_impl_708_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_836_ = lean_ctor_get(v_impl_708_, 4);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_impl_708_, 3);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_impl_708_, 0);
lean_dec(v_unused_838_);
v___x_826_ = v_impl_708_;
v_isShared_827_ = v_isSharedCheck_835_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_v_824_);
lean_inc(v_k_823_);
lean_dec(v_impl_708_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_835_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_unsigned_to_nat(3u);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 4, v_l_793_);
lean_ctor_set(v___x_826_, 2, v_v_561_);
lean_ctor_set(v___x_826_, 1, v_k_560_);
lean_ctor_set(v___x_826_, 0, v___x_709_);
v___x_830_ = v___x_826_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v_l_793_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v_l_793_);
v___x_830_ = v_reuseFailAlloc_834_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v_r_822_);
lean_ctor_set(v___x_565_, 3, v___x_830_);
lean_ctor_set(v___x_565_, 2, v_v_824_);
lean_ctor_set(v___x_565_, 1, v_k_823_);
lean_ctor_set(v___x_565_, 0, v___x_828_);
v___x_832_ = v___x_565_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_k_823_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_v_824_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_r_822_);
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
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = lean_unsigned_to_nat(2u);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v_impl_708_);
lean_ctor_set(v___x_565_, 3, v_r_822_);
lean_ctor_set(v___x_565_, 0, v___x_839_);
v___x_841_ = v___x_565_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_r_822_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_impl_708_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
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
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v_k_556_);
lean_ctor_set(v___x_845_, 2, v_v_557_);
lean_ctor_set(v___x_845_, 3, v_t_558_);
lean_ctor_set(v___x_845_, 4, v_t_558_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(lean_object* v_init_846_, lean_object* v_x_847_, lean_object* v___y_848_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
lean_object* v_k_850_; lean_object* v_v_851_; lean_object* v_l_852_; lean_object* v_r_853_; lean_object* v___x_854_; lean_object* v_fst_855_; lean_object* v_snd_856_; lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_861_; 
v_k_850_ = lean_ctor_get(v_x_847_, 1);
lean_inc(v_k_850_);
v_v_851_ = lean_ctor_get(v_x_847_, 2);
lean_inc(v_v_851_);
v_l_852_ = lean_ctor_get(v_x_847_, 3);
lean_inc(v_l_852_);
v_r_853_ = lean_ctor_get(v_x_847_, 4);
lean_inc(v_r_853_);
lean_dec_ref_known(v_x_847_, 5);
v___x_854_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(v_init_846_, v_l_852_, v___y_848_);
v_fst_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_fst_855_);
v_snd_856_ = lean_ctor_get(v___x_854_, 1);
lean_inc(v_snd_856_);
lean_dec_ref(v___x_854_);
v_a_857_ = lean_ctor_get(v_fst_855_, 0);
lean_inc(v_a_857_);
lean_dec(v_fst_855_);
v___x_858_ = l_Lean_Server_RefInfo_toLspRefInfo(v_v_851_, v_snd_856_);
v_fst_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_fst_859_);
v_snd_860_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_snd_860_);
lean_dec_ref(v___x_858_);
v___x_861_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_850_, v_fst_859_, v_a_857_);
v_init_846_ = v___x_861_;
v_x_847_ = v_r_853_;
v___y_848_ = v_snd_860_;
goto _start;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_init_846_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___y_848_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1___boxed(lean_object* v_init_865_, lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(v_init_865_, v_x_866_, v___y_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object* v_refs_870_){
_start:
{
lean_object* v_refs_x27_872_; lean_object* v___x_873_; lean_object* v_fst_874_; lean_object* v_snd_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_885_; 
v_refs_x27_872_ = lean_box(1);
v___x_873_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(v_refs_x27_872_, v_refs_870_, v_refs_x27_872_);
v_fst_874_ = lean_ctor_get(v___x_873_, 0);
v_snd_875_ = lean_ctor_get(v___x_873_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_885_ == 0)
{
v___x_877_ = v___x_873_;
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_snd_875_);
lean_inc(v_fst_874_);
lean_dec(v___x_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_d_880_; lean_object* v_a_884_; 
v_a_884_ = lean_ctor_get(v_fst_874_, 0);
lean_inc(v_a_884_);
lean_dec(v_fst_874_);
v_d_880_ = v_a_884_;
goto v___jp_879_;
v___jp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v_d_880_);
v___x_882_ = v___x_877_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_d_880_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_snd_875_);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs___boxed(lean_object* v_refs_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v_refs_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0(lean_object* v_00_u03b2_889_, lean_object* v_k_890_, lean_object* v_v_891_, lean_object* v_t_892_, lean_object* v_hl_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_890_, v_v_891_, v_t_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_merge(lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
lean_object* v_definition_x3f_903_; lean_object* v_usages_904_; lean_object* v___y_906_; 
v_definition_x3f_903_ = lean_ctor_get(v_b_902_, 0);
lean_inc(v_definition_x3f_903_);
v_usages_904_ = lean_ctor_get(v_b_902_, 1);
lean_inc_ref(v_usages_904_);
lean_dec_ref(v_b_902_);
if (lean_obj_tag(v_definition_x3f_903_) == 0)
{
lean_object* v_definition_x3f_917_; 
v_definition_x3f_917_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_definition_x3f_917_);
v___y_906_ = v_definition_x3f_917_;
goto v___jp_905_;
}
else
{
v___y_906_ = v_definition_x3f_903_;
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v_usages_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_915_; 
v_usages_907_ = lean_ctor_get(v_a_901_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_a_901_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_a_901_, 0);
lean_dec(v_unused_916_);
v___x_909_ = v_a_901_;
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_usages_907_);
lean_dec(v_a_901_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = l_Array_append___redArg(v_usages_907_, v_usages_904_);
lean_dec_ref(v_usages_904_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_911_);
lean_ctor_set(v___x_909_, 0, v___y_906_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___y_906_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(uint8_t v_includeStop_918_, lean_object* v_range_919_, lean_object* v_pos_920_){
_start:
{
lean_object* v_start_921_; lean_object* v_end_922_; uint8_t v___x_923_; 
v_start_921_ = lean_ctor_get(v_range_919_, 0);
v_end_922_ = lean_ctor_get(v_range_919_, 1);
v___x_923_ = l_Lean_Lsp_instOrdPosition_ord(v_start_921_, v_pos_920_);
if (v___x_923_ == 2)
{
uint8_t v___x_924_; 
v___x_924_ = 0;
return v___x_924_;
}
else
{
if (v_includeStop_918_ == 0)
{
uint8_t v___x_925_; 
v___x_925_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_920_, v_end_922_);
if (v___x_925_ == 0)
{
uint8_t v___x_926_; 
v___x_926_ = 1;
return v___x_926_;
}
else
{
return v_includeStop_918_;
}
}
else
{
uint8_t v___x_927_; 
v___x_927_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_920_, v_end_922_);
if (v___x_927_ == 2)
{
uint8_t v___x_928_; 
v___x_928_ = 0;
return v___x_928_;
}
else
{
return v_includeStop_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains___boxed(lean_object* v_includeStop_929_, lean_object* v_range_930_, lean_object* v_pos_931_){
_start:
{
uint8_t v_includeStop_boxed_932_; uint8_t v_res_933_; lean_object* v_r_934_; 
v_includeStop_boxed_932_ = lean_unbox(v_includeStop_929_);
v_res_933_ = l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(v_includeStop_boxed_932_, v_range_930_, v_pos_931_);
lean_dec_ref(v_pos_931_);
lean_dec_ref(v_range_930_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(uint8_t v_includeStop_938_, lean_object* v_pos_939_, lean_object* v_as_940_, size_t v_sz_941_, size_t v_i_942_, lean_object* v_b_943_){
_start:
{
uint8_t v___x_944_; 
v___x_944_ = lean_usize_dec_lt(v_i_942_, v_sz_941_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v_b_943_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; lean_object* v_a_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
lean_dec_ref(v_b_943_);
v___x_946_ = lean_box(0);
v_a_947_ = lean_array_uget_borrowed(v_as_940_, v_i_942_);
v___x_948_ = l_Lean_Lsp_RefInfo_Location_range(v_a_947_);
v___x_949_ = l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(v_includeStop_938_, v___x_948_, v_pos_939_);
lean_dec_ref(v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; size_t v___x_951_; size_t v___x_952_; 
v___x_950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___closed__0));
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_942_, v___x_951_);
v_i_942_ = v___x_952_;
v_b_943_ = v___x_950_;
goto _start;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_inc(v_a_947_);
v___x_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_954_, 0, v_a_947_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_946_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___boxed(lean_object* v_includeStop_957_, lean_object* v_pos_958_, lean_object* v_as_959_, lean_object* v_sz_960_, lean_object* v_i_961_, lean_object* v_b_962_){
_start:
{
uint8_t v_includeStop_boxed_963_; size_t v_sz_boxed_964_; size_t v_i_boxed_965_; lean_object* v_res_966_; 
v_includeStop_boxed_963_ = lean_unbox(v_includeStop_957_);
v_sz_boxed_964_ = lean_unbox_usize(v_sz_960_);
lean_dec(v_sz_960_);
v_i_boxed_965_ = lean_unbox_usize(v_i_961_);
lean_dec(v_i_961_);
v_res_966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(v_includeStop_boxed_963_, v_pos_958_, v_as_959_, v_sz_boxed_964_, v_i_boxed_965_, v_b_962_);
lean_dec_ref(v_as_959_);
lean_dec_ref(v_pos_958_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(lean_object* v_self_967_, lean_object* v_pos_968_, uint8_t v_includeStop_969_){
_start:
{
lean_object* v_definition_x3f_970_; lean_object* v_usages_971_; 
v_definition_x3f_970_ = lean_ctor_get(v_self_967_, 0);
v_usages_971_ = lean_ctor_get(v_self_967_, 1);
if (lean_obj_tag(v_definition_x3f_970_) == 1)
{
lean_object* v_val_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_val_980_ = lean_ctor_get(v_definition_x3f_970_, 0);
v___x_981_ = l_Lean_Lsp_RefInfo_Location_range(v_val_980_);
v___x_982_ = l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(v_includeStop_969_, v___x_981_, v_pos_968_);
lean_dec_ref(v___x_981_);
if (v___x_982_ == 0)
{
goto v___jp_972_;
}
else
{
lean_inc_ref(v_definition_x3f_970_);
return v_definition_x3f_970_;
}
}
else
{
goto v___jp_972_;
}
v___jp_972_:
{
lean_object* v___x_973_; lean_object* v___x_974_; size_t v_sz_975_; size_t v___x_976_; lean_object* v___x_977_; 
v___x_973_ = lean_box(0);
v___x_974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___closed__0));
v_sz_975_ = lean_array_size(v_usages_971_);
v___x_976_ = ((size_t)0ULL);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(v_includeStop_969_, v_pos_968_, v_usages_971_, v_sz_975_, v___x_976_, v___x_974_);
if (lean_obj_tag(v___x_977_) == 0)
{
return v___x_973_;
}
else
{
lean_object* v_val_978_; lean_object* v_fst_979_; 
v_val_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v___x_977_, 1);
v_fst_979_ = lean_ctor_get(v_val_978_, 0);
lean_inc(v_fst_979_);
lean_dec(v_val_978_);
if (lean_obj_tag(v_fst_979_) == 0)
{
return v___x_973_;
}
else
{
return v_fst_979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_findReferenceLocation_x3f___boxed(lean_object* v_self_983_, lean_object* v_pos_984_, lean_object* v_includeStop_985_){
_start:
{
uint8_t v_includeStop_boxed_986_; lean_object* v_res_987_; 
v_includeStop_boxed_986_ = lean_unbox(v_includeStop_985_);
v_res_987_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_self_983_, v_pos_984_, v_includeStop_boxed_986_);
lean_dec_ref(v_pos_984_);
lean_dec_ref(v_self_983_);
return v_res_987_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_RefInfo_contains(lean_object* v_self_988_, lean_object* v_pos_989_, uint8_t v_includeStop_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_self_988_, v_pos_989_, v_includeStop_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
uint8_t v___x_992_; 
v___x_992_ = 0;
return v___x_992_;
}
else
{
uint8_t v___x_993_; 
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = 1;
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_contains___boxed(lean_object* v_self_994_, lean_object* v_pos_995_, lean_object* v_includeStop_996_){
_start:
{
uint8_t v_includeStop_boxed_997_; uint8_t v_res_998_; lean_object* v_r_999_; 
v_includeStop_boxed_997_ = lean_unbox(v_includeStop_996_);
v_res_998_ = l_Lean_Lsp_RefInfo_contains(v_self_994_, v_pos_995_, v_includeStop_boxed_997_);
lean_dec_ref(v_pos_995_);
lean_dec_ref(v_self_994_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(lean_object* v_pos_1000_, uint8_t v_includeStop_1001_, lean_object* v_init_1002_, lean_object* v_x_1003_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
lean_object* v_k_1004_; lean_object* v_v_1005_; lean_object* v_l_1006_; lean_object* v_r_1007_; lean_object* v___x_1008_; lean_object* v_a_1009_; uint8_t v___x_1010_; 
v_k_1004_ = lean_ctor_get(v_x_1003_, 1);
lean_inc(v_k_1004_);
v_v_1005_ = lean_ctor_get(v_x_1003_, 2);
lean_inc(v_v_1005_);
v_l_1006_ = lean_ctor_get(v_x_1003_, 3);
lean_inc(v_l_1006_);
v_r_1007_ = lean_ctor_get(v_x_1003_, 4);
lean_inc(v_r_1007_);
lean_dec_ref_known(v_x_1003_, 5);
v___x_1008_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1000_, v_includeStop_1001_, v_init_1002_, v_l_1006_);
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = l_Lean_Lsp_RefInfo_contains(v_v_1005_, v_pos_1000_, v_includeStop_1001_);
lean_dec(v_v_1005_);
if (v___x_1010_ == 0)
{
lean_dec(v_k_1004_);
v_init_1002_ = v_a_1009_;
v_x_1003_ = v_r_1007_;
goto _start;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_array_push(v_a_1009_, v_k_1004_);
v_init_1002_ = v___x_1012_;
v_x_1003_ = v_r_1007_;
goto _start;
}
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_init_1002_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0___boxed(lean_object* v_pos_1015_, lean_object* v_includeStop_1016_, lean_object* v_init_1017_, lean_object* v_x_1018_){
_start:
{
uint8_t v_includeStop_boxed_1019_; lean_object* v_res_1020_; 
v_includeStop_boxed_1019_ = lean_unbox(v_includeStop_1016_);
v_res_1020_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1015_, v_includeStop_boxed_1019_, v_init_1017_, v_x_1018_);
lean_dec_ref(v_pos_1015_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt(lean_object* v_self_1023_, lean_object* v_pos_1024_, uint8_t v_includeStop_1025_){
_start:
{
lean_object* v_result_1026_; lean_object* v___x_1027_; lean_object* v_a_1028_; 
v_result_1026_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_1027_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1024_, v_includeStop_1025_, v_result_1026_, v_self_1023_);
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref(v___x_1027_);
return v_a_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt___boxed(lean_object* v_self_1029_, lean_object* v_pos_1030_, lean_object* v_includeStop_1031_){
_start:
{
uint8_t v_includeStop_boxed_1032_; lean_object* v_res_1033_; 
v_includeStop_boxed_1032_ = lean_unbox(v_includeStop_1031_);
v_res_1033_ = l_Lean_Lsp_ModuleRefs_findAt(v_self_1029_, v_pos_1030_, v_includeStop_boxed_1032_);
lean_dec_ref(v_pos_1030_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(lean_object* v_pos_1037_, uint8_t v_includeStop_1038_, lean_object* v_init_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v_d_1042_; 
if (lean_obj_tag(v_x_1040_) == 0)
{
lean_object* v_v_1045_; lean_object* v_l_1046_; lean_object* v_r_1047_; lean_object* v___x_1048_; lean_object* v_val_1049_; 
v_v_1045_ = lean_ctor_get(v_x_1040_, 2);
v_l_1046_ = lean_ctor_get(v_x_1040_, 3);
v_r_1047_ = lean_ctor_get(v_x_1040_, 4);
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1037_, v_includeStop_1038_, v_init_1039_, v_l_1046_);
v_val_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_val_1049_);
lean_dec(v___x_1048_);
if (lean_obj_tag(v_val_1049_) == 0)
{
lean_object* v_a_1050_; 
v_a_1050_ = lean_ctor_get(v_val_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v_val_1049_, 1);
v_d_1042_ = v_a_1050_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec_ref_known(v_val_1049_, 1);
v___x_1051_ = lean_box(0);
v___x_1052_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_v_1045_, v_pos_1037_, v_includeStop_1038_);
if (lean_obj_tag(v___x_1052_) == 1)
{
lean_object* v_val_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1062_; 
v_val_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_val_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = l_Lean_Lsp_RefInfo_Location_range(v_val_1053_);
lean_dec(v_val_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___x_1051_);
v_d_1042_ = v___x_1060_;
goto v___jp_1041_;
}
}
}
else
{
lean_object* v___x_1063_; 
lean_dec(v___x_1052_);
v___x_1063_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0));
v_init_1039_ = v___x_1063_;
v_x_1040_ = v_r_1047_;
goto _start;
}
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_init_1039_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_d_1042_);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___boxed(lean_object* v_pos_1067_, lean_object* v_includeStop_1068_, lean_object* v_init_1069_, lean_object* v_x_1070_){
_start:
{
uint8_t v_includeStop_boxed_1071_; lean_object* v_res_1072_; 
v_includeStop_boxed_1071_ = lean_unbox(v_includeStop_1068_);
v_res_1072_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1067_, v_includeStop_boxed_1071_, v_init_1069_, v_x_1070_);
lean_dec(v_x_1070_);
lean_dec_ref(v_pos_1067_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f(lean_object* v_self_1073_, lean_object* v_pos_1074_, uint8_t v_includeStop_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v_val_1078_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v_val_1082_; lean_object* v_a_1083_; 
v___x_1076_ = lean_box(0);
v___x_1080_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0));
v___x_1081_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1074_, v_includeStop_1075_, v___x_1080_, v_self_1073_);
v_val_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_val_1082_);
lean_dec(v___x_1081_);
v_a_1083_ = lean_ctor_get(v_val_1082_, 0);
lean_inc(v_a_1083_);
lean_dec(v_val_1082_);
v_val_1078_ = v_a_1083_;
goto v___jp_1077_;
v___jp_1077_:
{
lean_object* v_fst_1079_; 
v_fst_1079_ = lean_ctor_get(v_val_1078_, 0);
lean_inc(v_fst_1079_);
lean_dec_ref(v_val_1078_);
if (lean_obj_tag(v_fst_1079_) == 0)
{
return v___x_1076_;
}
else
{
return v_fst_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f___boxed(lean_object* v_self_1084_, lean_object* v_pos_1085_, lean_object* v_includeStop_1086_){
_start:
{
uint8_t v_includeStop_boxed_1087_; lean_object* v_res_1088_; 
v_includeStop_boxed_1087_ = lean_unbox(v_includeStop_1086_);
v_res_1088_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_self_1084_, v_pos_1085_, v_includeStop_boxed_1087_);
lean_dec_ref(v_pos_1085_);
lean_dec(v_self_1084_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(lean_object* v_j_1089_, lean_object* v_k_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = l_Lean_Json_getObjValD(v_j_1089_, v_k_1090_);
v___x_1092_ = l_Lean_Json_getNat_x3f(v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0___boxed(lean_object* v_j_1093_, lean_object* v_k_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(v_j_1093_, v_k_1094_);
lean_dec_ref(v_k_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(lean_object* v_j_1096_, lean_object* v_k_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = l_Lean_Json_getObjValD(v_j_1096_, v_k_1097_);
v___x_1099_ = l_Lean_Name_fromJson_x3f(v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1___boxed(lean_object* v_j_1100_, lean_object* v_k_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(v_j_1100_, v_k_1101_);
lean_dec_ref(v_k_1101_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(lean_object* v_init_1107_, lean_object* v_x_1108_){
_start:
{
if (lean_obj_tag(v_x_1108_) == 0)
{
lean_object* v_k_1109_; lean_object* v_v_1110_; lean_object* v_l_1111_; lean_object* v_r_1112_; lean_object* v___x_1113_; 
v_k_1109_ = lean_ctor_get(v_x_1108_, 1);
lean_inc(v_k_1109_);
v_v_1110_ = lean_ctor_get(v_x_1108_, 2);
lean_inc(v_v_1110_);
v_l_1111_ = lean_ctor_get(v_x_1108_, 3);
lean_inc(v_l_1111_);
v_r_1112_ = lean_ctor_get(v_x_1108_, 4);
lean_inc(v_r_1112_);
lean_dec_ref_known(v_x_1108_, 5);
v___x_1113_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(v_init_1107_, v_l_1111_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec(v_r_1112_);
lean_dec(v_v_1110_);
lean_dec(v_k_1109_);
return v___x_1113_;
}
else
{
if (lean_obj_tag(v_v_1110_) == 4)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1228_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1228_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1228_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_elems_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_elems_1118_ = lean_ctor_get(v_v_1110_, 0);
lean_inc_ref(v_elems_1118_);
lean_dec_ref_known(v_v_1110_, 1);
v___x_1119_ = lean_array_get_size(v_elems_1118_);
v___x_1120_ = lean_unsigned_to_nat(8u);
v___x_1121_ = lean_nat_dec_eq(v___x_1119_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_dec_ref(v_elems_1118_);
lean_dec(v_a_1114_);
lean_dec(v_r_1112_);
lean_dec(v_k_1109_);
v___x_1122_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__0));
v___x_1123_ = l_Nat_reprFast(v___x_1119_);
v___x_1124_ = lean_string_append(v___x_1122_, v___x_1123_);
lean_dec_ref(v___x_1123_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1124_);
v___x_1126_ = v___x_1116_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_del_object(v___x_1116_);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = lean_array_get_borrowed(v___x_1128_, v_elems_1118_, v___x_1129_);
lean_inc(v___x_1130_);
v___x_1131_ = l_Lean_Json_getNat_x3f(v___x_1130_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_elems_1118_);
lean_dec(v_a_1114_);
lean_dec(v_r_1112_);
lean_dec(v_k_1109_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
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
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_a_1140_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_array_get_borrowed(v___x_1128_, v_elems_1118_, v___x_1141_);
lean_inc(v___x_1142_);
v___x_1143_ = l_Lean_Json_getNat_x3f(v___x_1142_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_a_1140_);
lean_dec_ref(v_elems_1118_);
lean_dec(v_a_1114_);
lean_dec(v_r_1112_);
lean_dec(v_k_1109_);
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_a_1152_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1153_ = lean_unsigned_to_nat(2u);
v___x_1154_ = lean_array_get_borrowed(v___x_1128_, v_elems_1118_, v___x_1153_);
lean_inc(v___x_1154_);
v___x_1155_ = l_Lean_Json_getNat_x3f(v___x_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_a_1152_);
lean_dec(v_a_1140_);
lean_dec_ref(v_elems_1118_);
lean_dec(v_a_1114_);
lean_dec(v_r_1112_);
lean_dec(v_k_1109_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_a_1164_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1165_ = lean_unsigned_to_nat(3u);
v___x_1166_ = lean_array_get_borrowed(v___x_1128_, v_elems_1118_, v___x_1165_);
lean_inc(v___x_1166_);
v___x_1167_ = l_Lean_Json_getNat_x3f(v___x_1166_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_a_1164_);
lean_dec(v_a_1152_);
lean_dec(v_a_1140_);
lean_dec_ref(v_elems_1118_);
lean_dec(v_a_1114_);
lean_dec(v_r_1112_);
lean_dec(v_k_1109_);
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_a_1176_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1177_ = lean_unsigned_to_nat(4u);
v___x_1178_ = lean_array_get_borrowed(v___x_1128_, v_elems_1118_, v___x_1177_);
lean_inc(v___x_1178_);
v___x_1179_ = l_Lean_Json_getNat_x3f(v___x_1178_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_a_1176_);
lean_dec(v_a_1164_);
lean_dec(v_a_1152_);
lean_dec(v_a_1140_);
lean_dec_ref(v_elems_1118_);
lean_dec(v_a_1114_);
lean_dec(v_r_1112_);
lean_dec(v_k_1109_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_a_1188_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1179_, 1);
v___x_1189_ = lean_unsigned_to_nat(5u);
v___x_1190_ = lean_array_get_borrowed(v___x_1128_, v_elems_1118_, v___x_1189_);
lean_inc(v___x_1190_);
v___x_1191_ = l_Lean_Json_getNat_x3f(v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v_a_1188_);
lean_dec(v_a_1176_);
lean_dec(v_a_1164_);
lean_dec(v_a_1152_);
lean_dec(v_a_1140_);
lean_dec_ref(v_elems_1118_);
lean_dec(v_a_1114_);
lean_dec(v_r_1112_);
lean_dec(v_k_1109_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_a_1200_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1201_ = lean_unsigned_to_nat(6u);
v___x_1202_ = lean_array_get_borrowed(v___x_1128_, v_elems_1118_, v___x_1201_);
lean_inc(v___x_1202_);
v___x_1203_ = l_Lean_Json_getNat_x3f(v___x_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_a_1200_);
lean_dec(v_a_1188_);
lean_dec(v_a_1176_);
lean_dec(v_a_1164_);
lean_dec(v_a_1152_);
lean_dec(v_a_1140_);
lean_dec_ref(v_elems_1118_);
lean_dec(v_a_1114_);
lean_dec(v_r_1112_);
lean_dec(v_k_1109_);
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_a_1212_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1203_, 1);
v___x_1213_ = lean_unsigned_to_nat(7u);
v___x_1214_ = lean_array_get(v___x_1128_, v_elems_1118_, v___x_1213_);
lean_dec_ref(v_elems_1118_);
v___x_1215_ = l_Lean_Json_getNat_x3f(v___x_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_a_1212_);
lean_dec(v_a_1200_);
lean_dec(v_a_1188_);
lean_dec(v_a_1176_);
lean_dec(v_a_1164_);
lean_dec(v_a_1152_);
lean_dec(v_a_1140_);
lean_dec(v_a_1114_);
lean_dec(v_r_1112_);
lean_dec(v_k_1109_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_a_1224_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1225_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1225_, 0, v_a_1140_);
lean_ctor_set(v___x_1225_, 1, v_a_1152_);
lean_ctor_set(v___x_1225_, 2, v_a_1164_);
lean_ctor_set(v___x_1225_, 3, v_a_1176_);
lean_ctor_set(v___x_1225_, 4, v_a_1188_);
lean_ctor_set(v___x_1225_, 5, v_a_1200_);
lean_ctor_set(v___x_1225_, 6, v_a_1212_);
lean_ctor_set(v___x_1225_, 7, v_a_1224_);
v___x_1226_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_1109_, v___x_1225_, v_a_1114_);
v_init_1107_ = v___x_1226_;
v_x_1108_ = v_r_1112_;
goto _start;
}
}
}
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
lean_object* v___x_1229_; 
lean_dec_ref_known(v___x_1113_, 1);
lean_dec(v_r_1112_);
lean_dec(v_v_1110_);
lean_dec(v_k_1109_);
v___x_1229_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__2));
return v___x_1229_;
}
}
}
else
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1230_, 0, v_init_1107_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(lean_object* v_j_1231_, lean_object* v_k_1232_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = l_Lean_Json_getObjValD(v_j_1231_, v_k_1232_);
v___x_1234_ = l_Lean_Json_getObj_x3f(v___x_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_a_1243_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1244_ = lean_box(1);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(v___x_1244_, v_a_1243_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4___boxed(lean_object* v_j_1246_, lean_object* v_k_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(v_j_1246_, v_k_1247_);
lean_dec_ref(v_k_1247_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(size_t v_sz_1249_, size_t v_i_1250_, lean_object* v_bs_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1250_, v_sz_1249_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_bs_1251_);
return v___x_1253_;
}
else
{
lean_object* v_v_1254_; lean_object* v___x_1255_; lean_object* v_bs_x27_1256_; size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v_v_1254_ = lean_array_uget(v_bs_1251_, v_i_1250_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v_bs_x27_1256_ = lean_array_uset(v_bs_1251_, v_i_1250_, v___x_1255_);
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = lean_usize_add(v_i_1250_, v___x_1257_);
v___x_1259_ = lean_array_uset(v_bs_x27_1256_, v_i_1250_, v_v_1254_);
v_i_1250_ = v___x_1258_;
v_bs_1251_ = v___x_1259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13___boxed(lean_object* v_sz_1261_, lean_object* v_i_1262_, lean_object* v_bs_1263_){
_start:
{
size_t v_sz_boxed_1264_; size_t v_i_boxed_1265_; lean_object* v_res_1266_; 
v_sz_boxed_1264_ = lean_unbox_usize(v_sz_1261_);
lean_dec(v_sz_1261_);
v_i_boxed_1265_ = lean_unbox_usize(v_i_1262_);
lean_dec(v_i_1262_);
v_res_1266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(v_sz_boxed_1264_, v_i_boxed_1265_, v_bs_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(lean_object* v_x_1269_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 4)
{
lean_object* v_elems_1270_; size_t v_sz_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v_elems_1270_ = lean_ctor_get(v_x_1269_, 0);
lean_inc_ref(v_elems_1270_);
lean_dec_ref_known(v_x_1269_, 1);
v_sz_1271_ = lean_array_size(v_elems_1270_);
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(v_sz_1271_, v___x_1272_, v_elems_1270_);
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1274_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1275_ = lean_unsigned_to_nat(80u);
v___x_1276_ = l_Lean_Json_pretty(v_x_1269_, v___x_1275_);
v___x_1277_ = lean_string_append(v___x_1274_, v___x_1276_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1279_ = lean_string_append(v___x_1277_, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(size_t v_sz_1281_, size_t v_i_1282_, lean_object* v_bs_1283_){
_start:
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_usize_dec_lt(v_i_1282_, v_sz_1281_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_bs_1283_);
return v___x_1285_;
}
else
{
lean_object* v_v_1286_; lean_object* v___x_1287_; 
v_v_1286_ = lean_array_uget_borrowed(v_bs_1283_, v_i_1282_);
lean_inc(v_v_1286_);
v___x_1287_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(v_v_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_bs_1283_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1297_; lean_object* v_bs_x27_1298_; size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v_a_1296_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1297_ = lean_unsigned_to_nat(0u);
v_bs_x27_1298_ = lean_array_uset(v_bs_1283_, v_i_1282_, v___x_1297_);
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1282_, v___x_1299_);
v___x_1301_ = lean_array_uset(v_bs_x27_1298_, v_i_1282_, v_a_1296_);
v_i_1282_ = v___x_1300_;
v_bs_1283_ = v___x_1301_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9___boxed(lean_object* v_sz_1303_, lean_object* v_i_1304_, lean_object* v_bs_1305_){
_start:
{
size_t v_sz_boxed_1306_; size_t v_i_boxed_1307_; lean_object* v_res_1308_; 
v_sz_boxed_1306_ = lean_unbox_usize(v_sz_1303_);
lean_dec(v_sz_1303_);
v_i_boxed_1307_ = lean_unbox_usize(v_i_1304_);
lean_dec(v_i_1304_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(v_sz_boxed_1306_, v_i_boxed_1307_, v_bs_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 4)
{
lean_object* v_elems_1310_; size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v_elems_1310_ = lean_ctor_get(v_x_1309_, 0);
lean_inc_ref(v_elems_1310_);
lean_dec_ref_known(v_x_1309_, 1);
v_sz_1311_ = lean_array_size(v_elems_1310_);
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(v_sz_1311_, v___x_1312_, v_elems_1310_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1314_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1315_ = lean_unsigned_to_nat(80u);
v___x_1316_ = l_Lean_Json_pretty(v_x_1309_, v___x_1315_);
v___x_1317_ = lean_string_append(v___x_1314_, v___x_1316_);
lean_dec_ref(v___x_1316_);
v___x_1318_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1319_ = lean_string_append(v___x_1317_, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(lean_object* v_j_1321_, lean_object* v_k_1322_){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = l_Lean_Json_getObjValD(v_j_1321_, v_k_1322_);
v___x_1324_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4___boxed(lean_object* v_j_1325_, lean_object* v_k_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(v_j_1325_, v_k_1326_);
lean_dec_ref(v_k_1326_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_bs_1332_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_lt(v_i_1331_, v_sz_1330_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_bs_1332_);
return v___x_1334_;
}
else
{
lean_object* v_v_1335_; lean_object* v___x_1336_; lean_object* v_bs_x27_1337_; lean_object* v_a_1339_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1410_; 
v_v_1335_ = lean_array_uget(v_bs_1332_, v_i_1331_);
v___x_1336_ = lean_unsigned_to_nat(0u);
v_bs_x27_1337_ = lean_array_uset(v_bs_1332_, v_i_1331_, v___x_1336_);
v___x_1344_ = lean_array_get_size(v_v_1335_);
v___x_1345_ = lean_unsigned_to_nat(4u);
v___x_1410_ = lean_nat_dec_eq(v___x_1344_, v___x_1345_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = lean_unsigned_to_nat(5u);
v___x_1412_ = lean_nat_dec_eq(v___x_1344_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec_ref(v_bs_x27_1337_);
lean_dec(v_v_1335_);
v___x_1413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1414_ = l_Nat_reprFast(v___x_1344_);
v___x_1415_ = lean_string_append(v___x_1413_, v___x_1414_);
lean_dec_ref(v___x_1414_);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
else
{
goto v___jp_1346_;
}
}
else
{
goto v___jp_1346_;
}
v___jp_1338_:
{
size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_add(v_i_1331_, v___x_1340_);
v___x_1342_ = lean_array_uset(v_bs_x27_1337_, v_i_1331_, v_a_1339_);
v_i_1331_ = v___x_1341_;
v_bs_1332_ = v___x_1342_;
goto _start;
}
v___jp_1346_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_array_fget_borrowed(v_v_1335_, v___x_1336_);
lean_inc(v___x_1347_);
v___x_1348_ = l_Lean_Json_getNat_x3f(v___x_1347_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_bs_x27_1337_);
lean_dec(v_v_1335_);
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_a_1357_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_array_fget_borrowed(v_v_1335_, v___x_1358_);
lean_inc(v___x_1359_);
v___x_1360_ = l_Lean_Json_getNat_x3f(v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_a_1357_);
lean_dec_ref(v_bs_x27_1337_);
lean_dec(v_v_1335_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_a_1369_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1370_ = lean_unsigned_to_nat(2u);
v___x_1371_ = lean_array_fget_borrowed(v_v_1335_, v___x_1370_);
lean_inc(v___x_1371_);
v___x_1372_ = l_Lean_Json_getNat_x3f(v___x_1371_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec(v_a_1369_);
lean_dec(v_a_1357_);
lean_dec_ref(v_bs_x27_1337_);
lean_dec(v_v_1335_);
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
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
lean_object* v_a_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1381_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1382_ = lean_unsigned_to_nat(3u);
v___x_1383_ = lean_array_fget_borrowed(v_v_1335_, v___x_1382_);
lean_inc(v___x_1383_);
v___x_1384_ = l_Lean_Json_getNat_x3f(v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_a_1381_);
lean_dec(v_a_1369_);
lean_dec(v_a_1357_);
lean_dec_ref(v_bs_x27_1337_);
lean_dec(v_v_1335_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_a_1393_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1394_ = lean_unsigned_to_nat(5u);
v___x_1395_ = lean_nat_dec_eq(v___x_1344_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec(v_v_1335_);
v___x_1396_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
v___x_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1397_, 0, v_a_1357_);
lean_ctor_set(v___x_1397_, 1, v_a_1369_);
lean_ctor_set(v___x_1397_, 2, v_a_1381_);
lean_ctor_set(v___x_1397_, 3, v_a_1393_);
lean_ctor_set(v___x_1397_, 4, v___x_1396_);
v_a_1339_ = v___x_1397_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_array_fget(v_v_1335_, v___x_1345_);
lean_dec(v_v_1335_);
v___x_1399_ = l_Lean_Json_getStr_x3f(v___x_1398_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_a_1393_);
lean_dec(v_a_1381_);
lean_dec(v_a_1369_);
lean_dec(v_a_1357_);
lean_dec_ref(v_bs_x27_1337_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
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
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1409_, 0, v_a_1357_);
lean_ctor_set(v___x_1409_, 1, v_a_1369_);
lean_ctor_set(v___x_1409_, 2, v_a_1381_);
lean_ctor_set(v___x_1409_, 3, v_a_1393_);
lean_ctor_set(v___x_1409_, 4, v_a_1408_);
v_a_1339_ = v___x_1409_;
goto v___jp_1338_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___boxed(lean_object* v_sz_1417_, lean_object* v_i_1418_, lean_object* v_bs_1419_){
_start:
{
size_t v_sz_boxed_1420_; size_t v_i_boxed_1421_; lean_object* v_res_1422_; 
v_sz_boxed_1420_ = lean_unbox_usize(v_sz_1417_);
lean_dec(v_sz_1417_);
v_i_boxed_1421_ = lean_unbox_usize(v_i_1418_);
lean_dec(v_i_1418_);
v_res_1422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_boxed_1420_, v_i_boxed_1421_, v_bs_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(lean_object* v_x_1425_){
_start:
{
if (lean_obj_tag(v_x_1425_) == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0));
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(v_x_1425_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1444_; 
v_a_1436_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1438_ = v___x_1427_;
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1427_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_a_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(lean_object* v_j_1445_, lean_object* v_k_1446_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = l_Lean_Json_getObjValD(v_j_1445_, v_k_1446_);
v___x_1448_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6___boxed(lean_object* v_j_1449_, lean_object* v_k_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_j_1449_, v_k_1450_);
lean_dec_ref(v_k_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(lean_object* v_init_1454_, lean_object* v_x_1455_){
_start:
{
if (lean_obj_tag(v_x_1455_) == 0)
{
lean_object* v_k_1456_; lean_object* v_v_1457_; lean_object* v_l_1458_; lean_object* v_r_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1619_; 
v_k_1456_ = lean_ctor_get(v_x_1455_, 1);
v_v_1457_ = lean_ctor_get(v_x_1455_, 2);
v_l_1458_ = lean_ctor_get(v_x_1455_, 3);
v_r_1459_ = lean_ctor_get(v_x_1455_, 4);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_x_1455_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; 
v_unused_1620_ = lean_ctor_get(v_x_1455_, 0);
lean_dec(v_unused_1620_);
v___x_1461_ = v_x_1455_;
v_isShared_1462_ = v_isSharedCheck_1619_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_r_1459_);
lean_inc(v_l_1458_);
lean_inc(v_v_1457_);
lean_inc(v_k_1456_);
lean_dec(v_x_1455_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1619_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v_init_1454_, v_l_1458_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
lean_dec(v_k_1456_);
return v___x_1463_;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1618_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1618_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1618_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Json_parse(v_k_1456_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1478_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1477_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v_definition_x3f_1489_; lean_object* v_a_1517_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_a_1487_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1521_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
lean_inc(v_v_1457_);
v___x_1522_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_v_1457_, v___x_1521_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_a_1487_);
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1617_; 
v_a_1531_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1533_ = v___x_1522_;
v_isShared_1534_ = v_isSharedCheck_1617_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1522_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1617_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
if (lean_obj_tag(v_a_1531_) == 0)
{
lean_object* v___x_1535_; 
lean_del_object(v___x_1533_);
lean_del_object(v___x_1466_);
lean_del_object(v___x_1461_);
v___x_1535_ = lean_box(0);
v_definition_x3f_1489_ = v___x_1535_;
goto v___jp_1488_;
}
else
{
lean_object* v_val_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1608_; 
v_val_1536_ = lean_ctor_get(v_a_1531_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v_a_1531_, 1);
v___x_1537_ = lean_array_get_size(v_val_1536_);
v___x_1538_ = lean_unsigned_to_nat(4u);
v___x_1608_ = lean_nat_dec_eq(v___x_1537_, v___x_1538_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = lean_unsigned_to_nat(5u);
v___x_1610_ = lean_nat_dec_eq(v___x_1537_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
lean_dec(v_val_1536_);
lean_dec(v_a_1487_);
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
v___x_1611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1612_ = l_Nat_reprFast(v___x_1537_);
v___x_1613_ = lean_string_append(v___x_1611_, v___x_1612_);
lean_dec_ref(v___x_1612_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set_tag(v___x_1533_, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1613_);
v___x_1615_ = v___x_1533_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
else
{
lean_del_object(v___x_1533_);
goto v___jp_1539_;
}
}
else
{
lean_del_object(v___x_1533_);
goto v___jp_1539_;
}
v___jp_1539_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_array_fget_borrowed(v_val_1536_, v___x_1540_);
lean_inc(v___x_1541_);
v___x_1542_ = l_Lean_Json_getNat_x3f(v___x_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v_val_1536_);
lean_dec(v_a_1487_);
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_a_1551_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_array_fget_borrowed(v_val_1536_, v___x_1552_);
lean_inc(v___x_1553_);
v___x_1554_ = l_Lean_Json_getNat_x3f(v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_a_1551_);
lean_dec(v_val_1536_);
lean_dec(v_a_1487_);
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_a_1563_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1564_ = lean_unsigned_to_nat(2u);
v___x_1565_ = lean_array_fget_borrowed(v_val_1536_, v___x_1564_);
lean_inc(v___x_1565_);
v___x_1566_ = l_Lean_Json_getNat_x3f(v___x_1565_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1563_);
lean_dec(v_a_1551_);
lean_dec(v_val_1536_);
lean_dec(v_a_1487_);
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_a_1575_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1576_ = lean_unsigned_to_nat(3u);
v___x_1577_ = lean_array_fget_borrowed(v_val_1536_, v___x_1576_);
lean_inc(v___x_1577_);
v___x_1578_ = l_Lean_Json_getNat_x3f(v___x_1577_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1575_);
lean_dec(v_a_1563_);
lean_dec(v_a_1551_);
lean_dec(v_val_1536_);
lean_dec(v_a_1487_);
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_a_1587_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1588_ = lean_unsigned_to_nat(5u);
v___x_1589_ = lean_nat_dec_eq(v___x_1537_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
lean_dec(v_val_1536_);
v___x_1590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 4, v___x_1590_);
lean_ctor_set(v___x_1461_, 3, v_a_1587_);
lean_ctor_set(v___x_1461_, 2, v_a_1575_);
lean_ctor_set(v___x_1461_, 1, v_a_1563_);
lean_ctor_set(v___x_1461_, 0, v_a_1551_);
v___x_1592_ = v___x_1461_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1551_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1563_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_a_1575_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_a_1587_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
v_a_1517_ = v___x_1592_;
goto v___jp_1516_;
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_array_fget(v_val_1536_, v___x_1538_);
lean_dec(v_val_1536_);
v___x_1595_ = l_Lean_Json_getStr_x3f(v___x_1594_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1587_);
lean_dec(v_a_1575_);
lean_dec(v_a_1563_);
lean_dec(v_a_1551_);
lean_dec(v_a_1487_);
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
lean_del_object(v___x_1461_);
lean_dec(v_r_1459_);
lean_dec(v_v_1457_);
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; 
v_a_1604_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1595_, 1);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 4, v_a_1604_);
lean_ctor_set(v___x_1461_, 3, v_a_1587_);
lean_ctor_set(v___x_1461_, 2, v_a_1575_);
lean_ctor_set(v___x_1461_, 1, v_a_1563_);
lean_ctor_set(v___x_1461_, 0, v_a_1551_);
v___x_1606_ = v___x_1461_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1551_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_a_1563_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_a_1575_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_a_1587_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_a_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
v_a_1517_ = v___x_1606_;
goto v___jp_1516_;
}
}
}
}
}
}
}
}
}
}
}
v___jp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v___x_1491_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(v_v_1457_, v___x_1490_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_definition_x3f_1489_);
lean_dec(v_a_1487_);
lean_dec(v_a_1464_);
lean_dec(v_r_1459_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1500_; size_t v_sz_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
v_a_1500_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1491_, 1);
v_sz_1501_ = lean_array_size(v_a_1500_);
v___x_1502_ = ((size_t)0ULL);
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_1501_, v___x_1502_, v_a_1500_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v_definition_x3f_1489_);
lean_dec(v_a_1487_);
lean_dec(v_a_1464_);
lean_dec(v_r_1459_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_a_1512_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_definition_x3f_1489_);
lean_ctor_set(v___x_1513_, 1, v_a_1512_);
v___x_1514_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_a_1487_, v___x_1513_, v_a_1464_);
v_init_1454_ = v___x_1514_;
v_x_1455_ = v_r_1459_;
goto _start;
}
}
}
v___jp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v_a_1517_);
v___x_1519_ = v___x_1466_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
v_definition_x3f_1489_ = v___x_1519_;
goto v___jp_1488_;
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
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_init_1454_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(lean_object* v_j_1622_, lean_object* v_k_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = l_Lean_Json_getObjValD(v_j_1622_, v_k_1623_);
v___x_1625_ = l_Lean_Json_getObj_x3f(v___x_1624_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1634_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1635_ = lean_box(1);
v___x_1636_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v___x_1635_, v_a_1634_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3___boxed(lean_object* v_j_1637_, lean_object* v_k_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_j_1637_, v_k_1638_);
lean_dec_ref(v_k_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1643_, size_t v_i_1644_, lean_object* v_bs_1645_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_usize_dec_lt(v_i_1644_, v_sz_1643_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_bs_1645_);
return v___x_1649_;
}
else
{
lean_object* v_v_1650_; 
v_v_1650_ = lean_array_uget_borrowed(v_bs_1645_, v_i_1644_);
if (lean_obj_tag(v_v_1650_) == 4)
{
lean_object* v_elems_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_elems_1651_ = lean_ctor_get(v_v_1650_, 0);
v___x_1652_ = lean_array_get_size(v_elems_1651_);
v___x_1653_ = lean_unsigned_to_nat(4u);
v___x_1654_ = lean_nat_dec_eq(v___x_1652_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_dec_ref(v_bs_1645_);
goto v___jp_1646_;
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = lean_unsigned_to_nat(0u);
v___x_1656_ = lean_array_fget_borrowed(v_elems_1651_, v___x_1655_);
lean_inc(v___x_1656_);
v___x_1657_ = l_Lean_Json_getStr_x3f(v___x_1656_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_bs_1645_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_a_1666_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_array_fget_borrowed(v_elems_1651_, v___x_1667_);
v___x_1669_ = l_Lean_Json_getBool_x3f(v___x_1668_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_a_1666_);
lean_dec_ref(v_bs_1645_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_a_1678_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1679_ = lean_unsigned_to_nat(2u);
v___x_1680_ = lean_array_fget_borrowed(v_elems_1651_, v___x_1679_);
v___x_1681_ = l_Lean_Json_getBool_x3f(v___x_1680_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_a_1678_);
lean_dec(v_a_1666_);
lean_dec_ref(v_bs_1645_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_a_1690_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1691_ = lean_unsigned_to_nat(3u);
v___x_1692_ = lean_array_fget_borrowed(v_elems_1651_, v___x_1691_);
v___x_1693_ = l_Lean_Json_getBool_x3f(v___x_1692_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_a_1690_);
lean_dec(v_a_1678_);
lean_dec(v_a_1666_);
lean_dec_ref(v_bs_1645_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v_bs_x27_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; uint8_t v___x_1706_; uint8_t v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1693_, 1);
v_bs_x27_1703_ = lean_array_uset(v_bs_1645_, v_i_1644_, v___x_1655_);
v___x_1704_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1704_, 0, v_a_1666_);
v___x_1705_ = lean_unbox(v_a_1678_);
lean_dec(v_a_1678_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*1, v___x_1705_);
v___x_1706_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*1 + 1, v___x_1706_);
v___x_1707_ = lean_unbox(v_a_1702_);
lean_dec(v_a_1702_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*1 + 2, v___x_1707_);
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_add(v_i_1644_, v___x_1708_);
v___x_1710_ = lean_array_uset(v_bs_x27_1703_, v_i_1644_, v___x_1704_);
v_i_1644_ = v___x_1709_;
v_bs_1645_ = v___x_1710_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1645_);
goto v___jp_1646_;
}
}
v___jp_1646_:
{
lean_object* v___x_1647_; 
v___x_1647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1));
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1712_, lean_object* v_i_1713_, lean_object* v_bs_1714_){
_start:
{
size_t v_sz_boxed_1715_; size_t v_i_boxed_1716_; lean_object* v_res_1717_; 
v_sz_boxed_1715_ = lean_unbox_usize(v_sz_1712_);
lean_dec(v_sz_1712_);
v_i_boxed_1716_ = lean_unbox_usize(v_i_1713_);
lean_dec(v_i_1713_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1715_, v_i_boxed_1716_, v_bs_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(lean_object* v_x_1718_){
_start:
{
if (lean_obj_tag(v_x_1718_) == 4)
{
lean_object* v_elems_1719_; size_t v_sz_1720_; size_t v___x_1721_; lean_object* v___x_1722_; 
v_elems_1719_ = lean_ctor_get(v_x_1718_, 0);
lean_inc_ref(v_elems_1719_);
lean_dec_ref_known(v_x_1718_, 1);
v_sz_1720_ = lean_array_size(v_elems_1719_);
v___x_1721_ = ((size_t)0ULL);
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_1720_, v___x_1721_, v_elems_1719_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1723_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1724_ = lean_unsigned_to_nat(80u);
v___x_1725_ = l_Lean_Json_pretty(v_x_1718_, v___x_1724_);
v___x_1726_ = lean_string_append(v___x_1723_, v___x_1725_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1728_ = lean_string_append(v___x_1726_, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(lean_object* v_j_1730_, lean_object* v_k_1731_){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = l_Lean_Json_getObjValD(v_j_1730_, v_k_1731_);
v___x_1733_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2___boxed(lean_object* v_j_1734_, lean_object* v_k_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_j_1734_, v_k_1735_);
lean_dec_ref(v_k_1735_);
return v_res_1736_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = 1;
v___x_1746_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__4));
v___x_1747_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1746_, v___x_1745_);
return v___x_1747_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__6));
v___x_1750_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__5, &l_Lean_Server_instFromJsonIlean_fromJson___closed__5_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5);
v___x_1751_ = lean_string_append(v___x_1750_, v___x_1749_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = 1;
v___x_1755_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__8));
v___x_1756_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1755_, v___x_1754_);
return v___x_1756_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__9, &l_Lean_Server_instFromJsonIlean_fromJson___closed__9_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9);
v___x_1758_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1759_ = lean_string_append(v___x_1758_, v___x_1757_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1762_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__10, &l_Lean_Server_instFromJsonIlean_fromJson___closed__10_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10);
v___x_1763_ = lean_string_append(v___x_1762_, v___x_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = 1;
v___x_1768_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__14));
v___x_1769_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1768_, v___x_1767_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__15, &l_Lean_Server_instFromJsonIlean_fromJson___closed__15_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15);
v___x_1771_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1772_ = lean_string_append(v___x_1771_, v___x_1770_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1774_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__16, &l_Lean_Server_instFromJsonIlean_fromJson___closed__16_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16);
v___x_1775_ = lean_string_append(v___x_1774_, v___x_1773_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = 1;
v___x_1780_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__19));
v___x_1781_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1780_, v___x_1779_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__20, &l_Lean_Server_instFromJsonIlean_fromJson___closed__20_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20);
v___x_1783_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1784_ = lean_string_append(v___x_1783_, v___x_1782_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1786_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__21, &l_Lean_Server_instFromJsonIlean_fromJson___closed__21_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21);
v___x_1787_ = lean_string_append(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = 1;
v___x_1792_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__24));
v___x_1793_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1792_, v___x_1791_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__25, &l_Lean_Server_instFromJsonIlean_fromJson___closed__25_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25);
v___x_1795_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1796_ = lean_string_append(v___x_1795_, v___x_1794_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1798_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__26, &l_Lean_Server_instFromJsonIlean_fromJson___closed__26_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26);
v___x_1799_ = lean_string_append(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30(void){
_start:
{
uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = 1;
v___x_1804_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__29));
v___x_1805_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__30, &l_Lean_Server_instFromJsonIlean_fromJson___closed__30_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30);
v___x_1807_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1808_ = lean_string_append(v___x_1807_, v___x_1806_);
return v___x_1808_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1810_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__31, &l_Lean_Server_instFromJsonIlean_fromJson___closed__31_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31);
v___x_1811_ = lean_string_append(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonIlean_fromJson(lean_object* v_json_1812_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
lean_inc(v_json_1812_);
v___x_1814_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(v_json_1812_, v___x_1813_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_json_1812_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1819_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__12, &l_Lean_Server_instFromJsonIlean_fromJson___closed__12_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12);
v___x_1820_ = lean_string_append(v___x_1819_, v_a_1815_);
lean_dec(v_a_1815_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1820_);
v___x_1822_ = v___x_1817_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_a_1825_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1826_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
lean_inc(v_json_1812_);
v___x_1827_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(v_json_1812_, v___x_1826_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1837_; 
lean_dec(v_a_1825_);
lean_dec(v_json_1812_);
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1837_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1837_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1832_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__17, &l_Lean_Server_instFromJsonIlean_fromJson___closed__17_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17);
v___x_1833_ = lean_string_append(v___x_1832_, v_a_1828_);
lean_dec(v_a_1828_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1833_);
v___x_1835_ = v___x_1830_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_a_1838_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1839_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
lean_inc(v_json_1812_);
v___x_1840_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_json_1812_, v___x_1839_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_a_1838_);
lean_dec(v_a_1825_);
lean_dec(v_json_1812_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1845_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__22, &l_Lean_Server_instFromJsonIlean_fromJson___closed__22_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22);
v___x_1846_ = lean_string_append(v___x_1845_, v_a_1841_);
lean_dec(v_a_1841_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1846_);
v___x_1848_ = v___x_1843_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_a_1851_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1852_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
lean_inc(v_json_1812_);
v___x_1853_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_json_1812_, v___x_1852_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v_a_1851_);
lean_dec(v_a_1838_);
lean_dec(v_a_1825_);
lean_dec(v_json_1812_);
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1858_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__27, &l_Lean_Server_instFromJsonIlean_fromJson___closed__27_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27);
v___x_1859_ = lean_string_append(v___x_1858_, v_a_1854_);
lean_dec(v_a_1854_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1859_);
v___x_1861_ = v___x_1856_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_a_1864_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1865_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_1866_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(v_json_1812_, v___x_1865_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1864_);
lean_dec(v_a_1851_);
lean_dec(v_a_1838_);
lean_dec(v_a_1825_);
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1876_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1876_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1871_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__32, &l_Lean_Server_instFromJsonIlean_fromJson___closed__32_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32);
v___x_1872_ = lean_string_append(v___x_1871_, v_a_1867_);
lean_dec(v_a_1867_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1872_);
v___x_1874_ = v___x_1869_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1885_; 
v_a_1877_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1879_ = v___x_1866_;
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1866_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1881_, 0, v_a_1825_);
lean_ctor_set(v___x_1881_, 1, v_a_1838_);
lean_ctor_set(v___x_1881_, 2, v_a_1851_);
lean_ctor_set(v___x_1881_, 3, v_a_1864_);
lean_ctor_set(v___x_1881_, 4, v_a_1877_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1881_);
v___x_1883_ = v___x_1879_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(size_t v_sz_1888_, size_t v_i_1889_, lean_object* v_bs_1890_){
_start:
{
uint8_t v___x_1891_; 
v___x_1891_ = lean_usize_dec_lt(v_i_1889_, v_sz_1888_);
if (v___x_1891_ == 0)
{
return v_bs_1890_;
}
else
{
lean_object* v_v_1892_; lean_object* v_module_1893_; uint8_t v_isPrivate_1894_; uint8_t v_isAll_1895_; uint8_t v_isMeta_1896_; lean_object* v___x_1897_; lean_object* v_bs_x27_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v_v_1892_ = lean_array_uget_borrowed(v_bs_1890_, v_i_1889_);
v_module_1893_ = lean_ctor_get(v_v_1892_, 0);
lean_inc_ref(v_module_1893_);
v_isPrivate_1894_ = lean_ctor_get_uint8(v_v_1892_, sizeof(void*)*1);
v_isAll_1895_ = lean_ctor_get_uint8(v_v_1892_, sizeof(void*)*1 + 1);
v_isMeta_1896_ = lean_ctor_get_uint8(v_v_1892_, sizeof(void*)*1 + 2);
v___x_1897_ = lean_unsigned_to_nat(0u);
v_bs_x27_1898_ = lean_array_uset(v_bs_1890_, v_i_1889_, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1899_, 0, v_module_1893_);
v___x_1900_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1900_, 0, v_isPrivate_1894_);
v___x_1901_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1901_, 0, v_isAll_1895_);
v___x_1902_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1902_, 0, v_isMeta_1896_);
v___x_1903_ = lean_unsigned_to_nat(4u);
v___x_1904_ = lean_mk_empty_array_with_capacity(v___x_1903_);
v___x_1905_ = lean_array_push(v___x_1904_, v___x_1899_);
v___x_1906_ = lean_array_push(v___x_1905_, v___x_1900_);
v___x_1907_ = lean_array_push(v___x_1906_, v___x_1901_);
v___x_1908_ = lean_array_push(v___x_1907_, v___x_1902_);
v___x_1909_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1889_, v___x_1910_);
v___x_1912_ = lean_array_uset(v_bs_x27_1898_, v_i_1889_, v___x_1909_);
v_i_1889_ = v___x_1911_;
v_bs_1890_ = v___x_1912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6___boxed(lean_object* v_sz_1914_, lean_object* v_i_1915_, lean_object* v_bs_1916_){
_start:
{
size_t v_sz_boxed_1917_; size_t v_i_boxed_1918_; lean_object* v_res_1919_; 
v_sz_boxed_1917_ = lean_unbox_usize(v_sz_1914_);
lean_dec(v_sz_1914_);
v_i_boxed_1918_ = lean_unbox_usize(v_i_1915_);
lean_dec(v_i_1915_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_boxed_1917_, v_i_boxed_1918_, v_bs_1916_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(lean_object* v_a_1920_){
_start:
{
size_t v_sz_1921_; size_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_sz_1921_ = lean_array_size(v_a_1920_);
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_1921_, v___x_1922_, v_a_1920_);
v___x_1924_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
if (lean_obj_tag(v_a_1925_) == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = l_List_reverse___redArg(v_a_1926_);
return v___x_1927_;
}
else
{
lean_object* v_head_1928_; lean_object* v_tail_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1939_; 
v_head_1928_ = lean_ctor_get(v_a_1925_, 0);
v_tail_1929_ = lean_ctor_get(v_a_1925_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_a_1925_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1931_ = v_a_1925_;
v_isShared_1932_ = v_isSharedCheck_1939_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_tail_1929_);
lean_inc(v_head_1928_);
lean_dec(v_a_1925_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1939_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1933_ = l_Lean_JsonNumber_fromNat(v_head_1928_);
v___x_1934_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 1, v_a_1926_);
lean_ctor_set(v___x_1931_, 0, v___x_1934_);
v___x_1936_ = v___x_1931_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_a_1926_);
v___x_1936_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
v_a_1925_ = v_tail_1929_;
v_a_1926_ = v___x_1936_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(size_t v_sz_1940_, size_t v_i_1941_, lean_object* v_bs_1942_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_lt(v_i_1941_, v_sz_1940_);
if (v___x_1943_ == 0)
{
return v_bs_1942_;
}
else
{
lean_object* v_v_1944_; lean_object* v___x_1945_; lean_object* v_bs_x27_1946_; size_t v___x_1947_; size_t v___x_1948_; lean_object* v___x_1949_; 
v_v_1944_ = lean_array_uget(v_bs_1942_, v_i_1941_);
v___x_1945_ = lean_unsigned_to_nat(0u);
v_bs_x27_1946_ = lean_array_uset(v_bs_1942_, v_i_1941_, v___x_1945_);
v___x_1947_ = ((size_t)1ULL);
v___x_1948_ = lean_usize_add(v_i_1941_, v___x_1947_);
v___x_1949_ = lean_array_uset(v_bs_x27_1946_, v_i_1941_, v_v_1944_);
v_i_1941_ = v___x_1948_;
v_bs_1942_ = v___x_1949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11___boxed(lean_object* v_sz_1951_, lean_object* v_i_1952_, lean_object* v_bs_1953_){
_start:
{
size_t v_sz_boxed_1954_; size_t v_i_boxed_1955_; lean_object* v_res_1956_; 
v_sz_boxed_1954_ = lean_unbox_usize(v_sz_1951_);
lean_dec(v_sz_1951_);
v_i_boxed_1955_ = lean_unbox_usize(v_i_1952_);
lean_dec(v_i_1952_);
v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_boxed_1954_, v_i_boxed_1955_, v_bs_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(lean_object* v_a_1957_){
_start:
{
size_t v_sz_1958_; size_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_sz_1958_ = lean_array_size(v_a_1957_);
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_1958_, v___x_1959_, v_a_1957_);
v___x_1961_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(lean_object* v_a_1962_){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_array_mk(v_a_1962_);
v___x_1964_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(v___x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(lean_object* v_x_1965_){
_start:
{
if (lean_obj_tag(v_x_1965_) == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_box(0);
return v___x_1966_;
}
else
{
lean_object* v_val_1967_; lean_object* v___x_1968_; 
v_val_1967_ = lean_ctor_get(v_x_1965_, 0);
lean_inc(v_val_1967_);
lean_dec_ref_known(v_x_1965_, 1);
v___x_1968_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_val_1967_);
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(size_t v_sz_1969_, size_t v_i_1970_, lean_object* v_bs_1971_){
_start:
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_usize_dec_lt(v_i_1970_, v_sz_1969_);
if (v___x_1972_ == 0)
{
return v_bs_1971_;
}
else
{
lean_object* v_v_1973_; lean_object* v_startPosLine_1974_; lean_object* v_startPosCharacter_1975_; lean_object* v_endPosLine_1976_; lean_object* v_endPosCharacter_1977_; lean_object* v___x_1978_; lean_object* v_bs_x27_1979_; lean_object* v___y_1981_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v_range_1991_; lean_object* v___x_1992_; 
v_v_1973_ = lean_array_uget(v_bs_1971_, v_i_1970_);
v_startPosLine_1974_ = lean_ctor_get(v_v_1973_, 0);
v_startPosCharacter_1975_ = lean_ctor_get(v_v_1973_, 1);
v_endPosLine_1976_ = lean_ctor_get(v_v_1973_, 2);
v_endPosCharacter_1977_ = lean_ctor_get(v_v_1973_, 3);
v___x_1978_ = lean_unsigned_to_nat(0u);
v_bs_x27_1979_ = lean_array_uset(v_bs_1971_, v_i_1970_, v___x_1978_);
v___x_1986_ = lean_box(0);
lean_inc(v_endPosCharacter_1977_);
v___x_1987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1987_, 0, v_endPosCharacter_1977_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
lean_inc(v_endPosLine_1976_);
v___x_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_endPosLine_1976_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
lean_inc(v_startPosCharacter_1975_);
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_startPosCharacter_1975_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
lean_inc(v_startPosLine_1974_);
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_startPosLine_1974_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v_range_1991_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_1990_, v___x_1986_);
v___x_1992_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_1973_);
lean_dec(v_v_1973_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = l_List_appendTR___redArg(v_range_1991_, v___x_1986_);
v___y_1981_ = v___x_1993_;
goto v___jp_1980_;
}
else
{
lean_object* v_val_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2003_; 
v_val_1994_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1996_ = v___x_1992_;
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_val_1994_);
lean_dec(v___x_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 3);
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_val_1994_);
v___x_1999_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v___x_1986_);
v___x_2001_ = l_List_appendTR___redArg(v_range_1991_, v___x_2000_);
v___y_1981_ = v___x_2001_;
goto v___jp_1980_;
}
}
}
v___jp_1980_:
{
size_t v___x_1982_; size_t v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_add(v_i_1970_, v___x_1982_);
v___x_1984_ = lean_array_uset(v_bs_x27_1979_, v_i_1970_, v___y_1981_);
v_i_1970_ = v___x_1983_;
v_bs_1971_ = v___x_1984_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2___boxed(lean_object* v_sz_2004_, lean_object* v_i_2005_, lean_object* v_bs_2006_){
_start:
{
size_t v_sz_boxed_2007_; size_t v_i_boxed_2008_; lean_object* v_res_2009_; 
v_sz_boxed_2007_ = lean_unbox_usize(v_sz_2004_);
lean_dec(v_sz_2004_);
v_i_boxed_2008_ = lean_unbox_usize(v_i_2005_);
lean_dec(v_i_2005_);
v_res_2009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_boxed_2007_, v_i_boxed_2008_, v_bs_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_bs_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
if (v___x_2013_ == 0)
{
return v_bs_2012_;
}
else
{
lean_object* v_v_2014_; lean_object* v___x_2015_; lean_object* v_bs_x27_2016_; lean_object* v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v_v_2014_ = lean_array_uget(v_bs_2012_, v_i_2011_);
v___x_2015_ = lean_unsigned_to_nat(0u);
v_bs_x27_2016_ = lean_array_uset(v_bs_2012_, v_i_2011_, v___x_2015_);
v___x_2017_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_v_2014_);
v___x_2018_ = ((size_t)1ULL);
v___x_2019_ = lean_usize_add(v_i_2011_, v___x_2018_);
v___x_2020_ = lean_array_uset(v_bs_x27_2016_, v_i_2011_, v___x_2017_);
v_i_2011_ = v___x_2019_;
v_bs_2012_ = v___x_2020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4___boxed(lean_object* v_sz_2022_, lean_object* v_i_2023_, lean_object* v_bs_2024_){
_start:
{
size_t v_sz_boxed_2025_; size_t v_i_boxed_2026_; lean_object* v_res_2027_; 
v_sz_boxed_2025_ = lean_unbox_usize(v_sz_2022_);
lean_dec(v_sz_2022_);
v_i_boxed_2026_ = lean_unbox_usize(v_i_2023_);
lean_dec(v_i_2023_);
v_res_2027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_boxed_2025_, v_i_boxed_2026_, v_bs_2024_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(lean_object* v_a_2028_){
_start:
{
size_t v_sz_2029_; size_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_sz_2029_ = lean_array_size(v_a_2028_);
v___x_2030_ = ((size_t)0ULL);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_2029_, v___x_2030_, v_a_2028_);
v___x_2032_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
if (lean_obj_tag(v_a_2033_) == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = l_List_reverse___redArg(v_a_2034_);
return v___x_2035_;
}
else
{
lean_object* v_head_2036_; lean_object* v_snd_2037_; lean_object* v_tail_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2107_; 
v_head_2036_ = lean_ctor_get(v_a_2033_, 0);
lean_inc(v_head_2036_);
v_snd_2037_ = lean_ctor_get(v_head_2036_, 1);
lean_inc(v_snd_2037_);
v_tail_2038_ = lean_ctor_get(v_a_2033_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_a_2033_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v_a_2033_, 0);
lean_dec(v_unused_2108_);
v___x_2040_ = v_a_2033_;
v_isShared_2041_ = v_isSharedCheck_2107_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_tail_2038_);
lean_dec(v_a_2033_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2107_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_fst_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2105_; 
v_fst_2042_ = lean_ctor_get(v_head_2036_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_head_2036_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v_head_2036_, 1);
lean_dec(v_unused_2106_);
v___x_2044_ = v_head_2036_;
v_isShared_2045_ = v_isSharedCheck_2105_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_fst_2042_);
lean_dec(v_head_2036_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2105_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_definition_x3f_2046_; lean_object* v_usages_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2104_; 
v_definition_x3f_2046_ = lean_ctor_get(v_snd_2037_, 0);
v_usages_2047_ = lean_ctor_get(v_snd_2037_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_snd_2037_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2049_ = v_snd_2037_;
v_isShared_2050_ = v_isSharedCheck_2104_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_usages_2047_);
lean_inc(v_definition_x3f_2046_);
lean_dec(v_snd_2037_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2104_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___y_2055_; lean_object* v___y_2078_; 
v___x_2051_ = l_Lean_Lsp_RefIdent_toJson(v_fst_2042_);
v___x_2052_ = l_Lean_Json_compress(v___x_2051_);
v___x_2053_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
if (lean_obj_tag(v_definition_x3f_2046_) == 0)
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_box(0);
v___y_2055_ = v___x_2080_;
goto v___jp_2054_;
}
else
{
lean_object* v_val_2081_; lean_object* v_startPosLine_2082_; lean_object* v_startPosCharacter_2083_; lean_object* v_endPosLine_2084_; lean_object* v_endPosCharacter_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v_range_2091_; lean_object* v___x_2092_; 
v_val_2081_ = lean_ctor_get(v_definition_x3f_2046_, 0);
lean_inc(v_val_2081_);
lean_dec_ref_known(v_definition_x3f_2046_, 1);
v_startPosLine_2082_ = lean_ctor_get(v_val_2081_, 0);
v_startPosCharacter_2083_ = lean_ctor_get(v_val_2081_, 1);
v_endPosLine_2084_ = lean_ctor_get(v_val_2081_, 2);
v_endPosCharacter_2085_ = lean_ctor_get(v_val_2081_, 3);
v___x_2086_ = lean_box(0);
lean_inc(v_endPosCharacter_2085_);
v___x_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2087_, 0, v_endPosCharacter_2085_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
lean_inc(v_endPosLine_2084_);
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_endPosLine_2084_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
lean_inc(v_startPosCharacter_2083_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v_startPosCharacter_2083_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
lean_inc(v_startPosLine_2082_);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v_startPosLine_2082_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v_range_2091_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_2090_, v___x_2086_);
v___x_2092_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_2081_);
lean_dec(v_val_2081_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = l_List_appendTR___redArg(v_range_2091_, v___x_2086_);
v___y_2078_ = v___x_2093_;
goto v___jp_2077_;
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2103_; 
v_val_2094_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2096_ = v___x_2092_;
v_isShared_2097_ = v_isSharedCheck_2103_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_val_2094_);
lean_dec(v___x_2092_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2103_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 3);
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_val_2094_);
v___x_2099_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v___x_2086_);
v___x_2101_ = l_List_appendTR___redArg(v_range_2091_, v___x_2100_);
v___y_2078_ = v___x_2101_;
goto v___jp_2077_;
}
}
}
}
v___jp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = l_Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(v___y_2055_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v___x_2056_);
lean_ctor_set(v___x_2044_, 0, v___x_2053_);
v___x_2058_ = v___x_2044_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; size_t v_sz_2060_; size_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2059_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v_sz_2060_ = lean_array_size(v_usages_2047_);
v___x_2061_ = ((size_t)0ULL);
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_2060_, v___x_2061_, v_usages_2047_);
v___x_2063_ = l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(v___x_2062_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v___x_2063_);
lean_ctor_set(v___x_2049_, 0, v___x_2059_);
v___x_2065_ = v___x_2049_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = lean_box(0);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 1, v___x_2066_);
lean_ctor_set(v___x_2040_, 0, v___x_2065_);
v___x_2068_ = v___x_2040_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2058_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = l_Lean_Json_mkObj(v___x_2069_);
lean_dec_ref_known(v___x_2069_, 2);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2052_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v_a_2034_);
v_a_2033_ = v_tail_2038_;
v_a_2034_ = v___x_2072_;
goto _start;
}
}
}
}
v___jp_2077_:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___y_2078_);
v___y_2055_ = v___x_2079_;
goto v___jp_2054_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(lean_object* v_init_2109_, lean_object* v_x_2110_){
_start:
{
if (lean_obj_tag(v_x_2110_) == 0)
{
lean_object* v_k_2111_; lean_object* v_v_2112_; lean_object* v_l_2113_; lean_object* v_r_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_k_2111_ = lean_ctor_get(v_x_2110_, 1);
v_v_2112_ = lean_ctor_get(v_x_2110_, 2);
v_l_2113_ = lean_ctor_get(v_x_2110_, 3);
v_r_2114_ = lean_ctor_get(v_x_2110_, 4);
v___x_2115_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2109_, v_r_2114_);
lean_inc(v_v_2112_);
lean_inc(v_k_2111_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v_k_2111_);
lean_ctor_set(v___x_2116_, 1, v_v_2112_);
v___x_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v___x_2115_);
v_init_2109_ = v___x_2117_;
v_x_2110_ = v_l_2113_;
goto _start;
}
else
{
return v_init_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5___boxed(lean_object* v_init_2119_, lean_object* v_x_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2119_, v_x_2120_);
lean_dec(v_x_2120_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
if (lean_obj_tag(v_a_2122_) == 0)
{
lean_object* v___x_2124_; 
v___x_2124_ = l_List_reverse___redArg(v_a_2123_);
return v___x_2124_;
}
else
{
lean_object* v_head_2125_; lean_object* v_snd_2126_; lean_object* v_tail_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2179_; 
v_head_2125_ = lean_ctor_get(v_a_2122_, 0);
lean_inc(v_head_2125_);
v_snd_2126_ = lean_ctor_get(v_head_2125_, 1);
lean_inc(v_snd_2126_);
v_tail_2127_ = lean_ctor_get(v_a_2122_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_a_2122_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; 
v_unused_2180_ = lean_ctor_get(v_a_2122_, 0);
lean_dec(v_unused_2180_);
v___x_2129_ = v_a_2122_;
v_isShared_2130_ = v_isSharedCheck_2179_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_tail_2127_);
lean_dec(v_a_2122_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2179_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_fst_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2177_; 
v_fst_2131_ = lean_ctor_get(v_head_2125_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_head_2125_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v_head_2125_, 1);
lean_dec(v_unused_2178_);
v___x_2133_ = v_head_2125_;
v_isShared_2134_ = v_isSharedCheck_2177_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_fst_2131_);
lean_dec(v_head_2125_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2177_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_rangeStartPosLine_2135_; lean_object* v_rangeStartPosCharacter_2136_; lean_object* v_rangeEndPosLine_2137_; lean_object* v_rangeEndPosCharacter_2138_; lean_object* v_selectionRangeStartPosLine_2139_; lean_object* v_selectionRangeStartPosCharacter_2140_; lean_object* v_selectionRangeEndPosLine_2141_; lean_object* v_selectionRangeEndPosCharacter_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v_rangeStartPosLine_2135_ = lean_ctor_get(v_snd_2126_, 0);
lean_inc(v_rangeStartPosLine_2135_);
v_rangeStartPosCharacter_2136_ = lean_ctor_get(v_snd_2126_, 1);
lean_inc(v_rangeStartPosCharacter_2136_);
v_rangeEndPosLine_2137_ = lean_ctor_get(v_snd_2126_, 2);
lean_inc(v_rangeEndPosLine_2137_);
v_rangeEndPosCharacter_2138_ = lean_ctor_get(v_snd_2126_, 3);
lean_inc(v_rangeEndPosCharacter_2138_);
v_selectionRangeStartPosLine_2139_ = lean_ctor_get(v_snd_2126_, 4);
lean_inc(v_selectionRangeStartPosLine_2139_);
v_selectionRangeStartPosCharacter_2140_ = lean_ctor_get(v_snd_2126_, 5);
lean_inc(v_selectionRangeStartPosCharacter_2140_);
v_selectionRangeEndPosLine_2141_ = lean_ctor_get(v_snd_2126_, 6);
lean_inc(v_selectionRangeEndPosLine_2141_);
v_selectionRangeEndPosCharacter_2142_ = lean_ctor_get(v_snd_2126_, 7);
lean_inc(v_selectionRangeEndPosCharacter_2142_);
lean_dec(v_snd_2126_);
v___x_2143_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_2135_);
v___x_2144_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
v___x_2145_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_2136_);
v___x_2146_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
v___x_2147_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_2137_);
v___x_2148_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
v___x_2149_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_2138_);
v___x_2150_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
v___x_2151_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_2139_);
v___x_2152_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
v___x_2153_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_2140_);
v___x_2154_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
v___x_2155_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_2141_);
v___x_2156_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
v___x_2157_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_2142_);
v___x_2158_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
v___x_2159_ = lean_unsigned_to_nat(8u);
v___x_2160_ = lean_mk_empty_array_with_capacity(v___x_2159_);
v___x_2161_ = lean_array_push(v___x_2160_, v___x_2144_);
v___x_2162_ = lean_array_push(v___x_2161_, v___x_2146_);
v___x_2163_ = lean_array_push(v___x_2162_, v___x_2148_);
v___x_2164_ = lean_array_push(v___x_2163_, v___x_2150_);
v___x_2165_ = lean_array_push(v___x_2164_, v___x_2152_);
v___x_2166_ = lean_array_push(v___x_2165_, v___x_2154_);
v___x_2167_ = lean_array_push(v___x_2166_, v___x_2156_);
v___x_2168_ = lean_array_push(v___x_2167_, v___x_2158_);
v___x_2169_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v___x_2169_);
v___x_2171_ = v___x_2133_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_fst_2131_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2173_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v_a_2123_);
lean_ctor_set(v___x_2129_, 0, v___x_2171_);
v___x_2173_ = v___x_2129_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_a_2123_);
v___x_2173_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
v_a_2122_ = v_tail_2127_;
v_a_2123_ = v___x_2173_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
if (lean_obj_tag(v_a_2181_) == 0)
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_array_to_list(v_a_2182_);
return v___x_2183_;
}
else
{
lean_object* v_head_2184_; lean_object* v_tail_2185_; lean_object* v___x_2186_; 
v_head_2184_ = lean_ctor_get(v_a_2181_, 0);
lean_inc(v_head_2184_);
v_tail_2185_ = lean_ctor_get(v_a_2181_, 1);
lean_inc(v_tail_2185_);
lean_dec_ref_known(v_a_2181_, 2);
v___x_2186_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2182_, v_head_2184_);
v_a_2181_ = v_tail_2185_;
v_a_2182_ = v___x_2186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(lean_object* v_init_2188_, lean_object* v_x_2189_){
_start:
{
if (lean_obj_tag(v_x_2189_) == 0)
{
lean_object* v_k_2190_; lean_object* v_v_2191_; lean_object* v_l_2192_; lean_object* v_r_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_k_2190_ = lean_ctor_get(v_x_2189_, 1);
v_v_2191_ = lean_ctor_get(v_x_2189_, 2);
v_l_2192_ = lean_ctor_get(v_x_2189_, 3);
v_r_2193_ = lean_ctor_get(v_x_2189_, 4);
v___x_2194_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2188_, v_r_2193_);
lean_inc(v_v_2191_);
lean_inc(v_k_2190_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_k_2190_);
lean_ctor_set(v___x_2195_, 1, v_v_2191_);
v___x_2196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2194_);
v_init_2188_ = v___x_2196_;
v_x_2189_ = v_l_2192_;
goto _start;
}
else
{
return v_init_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7___boxed(lean_object* v_init_2198_, lean_object* v_x_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2198_, v_x_2199_);
lean_dec(v_x_2199_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonIlean_toJson(lean_object* v_x_2203_){
_start:
{
lean_object* v_version_2204_; lean_object* v_module_2205_; lean_object* v_directImports_2206_; lean_object* v_references_2207_; lean_object* v_decls_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_version_2204_ = lean_ctor_get(v_x_2203_, 0);
lean_inc(v_version_2204_);
v_module_2205_ = lean_ctor_get(v_x_2203_, 1);
lean_inc(v_module_2205_);
v_directImports_2206_ = lean_ctor_get(v_x_2203_, 2);
lean_inc_ref(v_directImports_2206_);
v_references_2207_ = lean_ctor_get(v_x_2203_, 3);
lean_inc(v_references_2207_);
v_decls_2208_ = lean_ctor_get(v_x_2203_, 4);
lean_inc(v_decls_2208_);
lean_dec_ref(v_x_2203_);
v___x_2209_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
v___x_2210_ = l_Lean_JsonNumber_fromNat(v_version_2204_);
v___x_2211_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2209_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
v___x_2216_ = 1;
v___x_2217_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_2205_, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2215_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v___x_2213_);
v___x_2221_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
v___x_2222_ = l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(v_directImports_2206_);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v___x_2213_);
v___x_2225_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
v___x_2226_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v___x_2213_, v_references_2207_);
lean_dec(v_references_2207_);
v___x_2227_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(v___x_2226_, v___x_2213_);
v___x_2228_ = l_Lean_Json_mkObj(v___x_2227_);
lean_dec(v___x_2227_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2225_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___x_2213_);
v___x_2231_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_2232_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v___x_2213_, v_decls_2208_);
lean_dec(v_decls_2208_);
v___x_2233_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(v___x_2232_, v___x_2213_);
v___x_2234_ = l_Lean_Json_mkObj(v___x_2233_);
lean_dec(v___x_2233_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2231_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v___x_2213_);
v___x_2237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
lean_ctor_set(v___x_2237_, 1, v___x_2213_);
v___x_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2230_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2224_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2220_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2214_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = ((lean_object*)(l_Lean_Server_instToJsonIlean_toJson___closed__0));
v___x_2243_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(v___x_2241_, v___x_2242_);
v___x_2244_ = l_Lean_Json_mkObj(v___x_2243_);
lean_dec(v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1(lean_object* v_compactedIleanPath_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___closed__0));
v___x_2254_ = lean_compacted_region_read(v_compactedIleanPath_2251_, v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___boxed(lean_object* v_compactedIleanPath_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1(v_compactedIleanPath_2255_);
lean_dec_ref(v_compactedIleanPath_2255_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_loadCompacted_x3f(lean_object* v_ileanPath_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2265_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v_ileanPath_2263_);
v___x_2266_ = l_System_FilePath_extension(v_ileanPath_2263_);
v___x_2267_ = ((lean_object*)(l_Lean_Server_Ilean_loadCompacted_x3f___closed__1));
v___x_2268_ = l_Option_instDecidableEq___redArg(v___x_2265_, v___x_2266_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2269_ = ((lean_object*)(l_Lean_Server_Ilean_loadCompacted_x3f___closed__2));
v___x_2270_ = lean_string_append(v___x_2269_, v_ileanPath_2263_);
lean_dec_ref(v_ileanPath_2263_);
v___x_2271_ = ((lean_object*)(l_Lean_Server_Ilean_loadCompacted_x3f___closed__3));
v___x_2272_ = lean_string_append(v___x_2270_, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; lean_object* v_compactedIleanPath_2276_; lean_object* v___x_2277_; 
v___x_2275_ = ((lean_object*)(l_Lean_Server_Ilean_compactedExt___closed__0));
lean_inc_ref(v_ileanPath_2263_);
v_compactedIleanPath_2276_ = l_System_FilePath_withExtension(v_ileanPath_2263_, v___x_2275_);
v___x_2277_ = lean_io_metadata(v_compactedIleanPath_2276_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v_modified_2279_; lean_object* v___x_2280_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
v_modified_2279_ = lean_ctor_get(v_a_2278_, 1);
lean_inc_ref(v_modified_2279_);
lean_dec(v_a_2278_);
v___x_2280_ = lean_io_metadata(v_ileanPath_2263_);
lean_dec_ref(v_ileanPath_2263_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2311_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2311_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2311_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v_modified_2285_; uint8_t v___x_2286_; 
v_modified_2285_ = lean_ctor_get(v_a_2281_, 1);
lean_inc_ref(v_modified_2285_);
lean_dec(v_a_2281_);
v___x_2286_ = l_IO_FS_instOrdSystemTime_ord(v_modified_2279_, v_modified_2285_);
lean_dec_ref(v_modified_2285_);
lean_dec_ref(v_modified_2279_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
lean_dec_ref(v_compactedIleanPath_2276_);
v___x_2287_ = lean_box(0);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2287_);
v___x_2289_ = v___x_2283_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_del_object(v___x_2283_);
v___x_2291_ = ((lean_object*)(l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___closed__0));
v___x_2292_ = lean_compacted_region_read(v_compactedIleanPath_2276_, v___x_2291_);
lean_dec_ref(v_compactedIleanPath_2276_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2302_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2302_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2302_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_fst_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
v_fst_2297_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_fst_2297_);
lean_dec(v_a_2293_);
v___x_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2298_, 0, v_fst_2297_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2298_);
v___x_2300_ = v___x_2295_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
v_a_2303_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2292_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2292_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v_modified_2279_);
lean_dec_ref(v_compactedIleanPath_2276_);
v_a_2312_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2280_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2280_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref(v_compactedIleanPath_2276_);
lean_dec_ref(v_ileanPath_2263_);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v___x_2277_, 0);
lean_dec(v_unused_2328_);
v___x_2321_ = v___x_2277_;
v_isShared_2322_ = v_isSharedCheck_2327_;
goto v_resetjp_2320_;
}
else
{
lean_dec(v___x_2277_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2327_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = lean_box(0);
if (v_isShared_2322_ == 0)
{
lean_ctor_set_tag(v___x_2321_, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2323_);
v___x_2325_ = v___x_2321_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_loadCompacted_x3f___boxed(lean_object* v_ileanPath_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_Server_Ilean_loadCompacted_x3f(v_ileanPath_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load(lean_object* v_path_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_IO_FS_readFile(v_path_2333_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2357_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2357_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2357_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_a_2341_; lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_Json_parse(v_a_2336_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; 
lean_del_object(v___x_2338_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v_a_2341_ = v_a_2349_;
goto v___jp_2340_;
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2351_ = l_Lean_Server_instFromJsonIlean_fromJson(v_a_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; 
lean_del_object(v___x_2338_);
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v_a_2341_ = v_a_2352_;
goto v___jp_2340_;
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; 
v_a_2353_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2351_, 1);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v_a_2353_);
v___x_2355_ = v___x_2338_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
v___jp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2342_ = ((lean_object*)(l_Lean_Server_Ilean_load___closed__0));
v___x_2343_ = lean_string_append(v___x_2342_, v_path_2333_);
v___x_2344_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_2345_ = lean_string_append(v___x_2343_, v___x_2344_);
v___x_2346_ = lean_string_append(v___x_2345_, v_a_2341_);
lean_dec_ref(v_a_2341_);
v___x_2347_ = l_Lean_IO_throwServerError___redArg(v___x_2346_);
return v___x_2347_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2335_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2335_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load___boxed(lean_object* v_path_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Server_Ilean_load(v_path_2366_);
lean_dec_ref(v_path_2366_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f(lean_object* v_env_2369_, lean_object* v_declName_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2369_, v_declName_2370_);
if (lean_obj_tag(v___x_2371_) == 1)
{
lean_object* v_val_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2384_; 
v_val_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2384_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_val_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2384_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2376_ = l_Lean_Environment_allImportedModuleNames(v_env_2369_);
v___x_2377_ = lean_array_get_size(v___x_2376_);
v___x_2378_ = lean_nat_dec_lt(v_val_2372_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
lean_dec_ref(v___x_2376_);
lean_del_object(v___x_2374_);
lean_dec(v_val_2372_);
v___x_2379_ = lean_box(0);
return v___x_2379_;
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2380_ = lean_array_fget(v___x_2376_, v_val_2372_);
lean_dec(v_val_2372_);
lean_dec_ref(v___x_2376_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2380_);
v___x_2382_ = v___x_2374_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v___x_2385_; lean_object* v_mainModule_2386_; lean_object* v___x_2387_; 
lean_dec(v___x_2371_);
v___x_2385_ = l_Lean_Environment_header(v_env_2369_);
v_mainModule_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_mainModule_2386_);
lean_dec_ref(v___x_2385_);
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_mainModule_2386_);
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f___boxed(lean_object* v_env_2388_, lean_object* v_declName_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2388_, v_declName_2389_);
lean_dec(v_declName_2389_);
lean_dec_ref(v_env_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf(lean_object* v_ci_2391_, lean_object* v_i_2392_){
_start:
{
switch(lean_obj_tag(v_i_2392_))
{
case 1:
{
lean_object* v_i_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2434_; 
v_i_2393_ = lean_ctor_get(v_i_2392_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_i_2392_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2395_ = v_i_2392_;
v_isShared_2396_ = v_isSharedCheck_2434_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_i_2393_);
lean_dec(v_i_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2434_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_expr_2397_; 
v_expr_2397_ = lean_ctor_get(v_i_2393_, 3);
lean_inc_ref(v_expr_2397_);
switch(lean_obj_tag(v_expr_2397_))
{
case 4:
{
lean_object* v_toCommandContextInfo_2398_; uint8_t v_isBinder_2399_; lean_object* v_declName_2400_; lean_object* v_env_2401_; lean_object* v___x_2402_; 
lean_del_object(v___x_2395_);
v_toCommandContextInfo_2398_ = lean_ctor_get(v_ci_2391_, 0);
v_isBinder_2399_ = lean_ctor_get_uint8(v_i_2393_, sizeof(void*)*4);
lean_dec_ref(v_i_2393_);
v_declName_2400_ = lean_ctor_get(v_expr_2397_, 0);
lean_inc(v_declName_2400_);
lean_dec_ref_known(v_expr_2397_, 2);
v_env_2401_ = lean_ctor_get(v_toCommandContextInfo_2398_, 0);
v___x_2402_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2401_, v_declName_2400_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v___x_2403_; 
lean_dec(v_declName_2400_);
v___x_2403_ = lean_box(0);
return v___x_2403_;
}
else
{
lean_object* v_val_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2417_; 
v_val_2404_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2406_ = v___x_2402_;
v_isShared_2407_ = v_isSharedCheck_2417_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_val_2404_);
lean_dec(v___x_2402_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2417_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2408_ = 1;
v___x_2409_ = l_Lean_Name_toString(v_val_2404_, v___x_2408_);
v___x_2410_ = l_Lean_Name_toString(v_declName_2400_, v___x_2408_);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_box(v_isBinder_2399_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2413_);
v___x_2415_ = v___x_2406_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
case 1:
{
lean_object* v_toCommandContextInfo_2418_; uint8_t v_isBinder_2419_; lean_object* v_fvarId_2420_; lean_object* v_env_2421_; lean_object* v___x_2422_; lean_object* v_mainModule_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v_toCommandContextInfo_2418_ = lean_ctor_get(v_ci_2391_, 0);
v_isBinder_2419_ = lean_ctor_get_uint8(v_i_2393_, sizeof(void*)*4);
lean_dec_ref(v_i_2393_);
v_fvarId_2420_ = lean_ctor_get(v_expr_2397_, 0);
lean_inc(v_fvarId_2420_);
lean_dec_ref_known(v_expr_2397_, 1);
v_env_2421_ = lean_ctor_get(v_toCommandContextInfo_2418_, 0);
v___x_2422_ = l_Lean_Environment_header(v_env_2421_);
v_mainModule_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_mainModule_2423_);
lean_dec_ref(v___x_2422_);
v___x_2424_ = 1;
v___x_2425_ = l_Lean_Name_toString(v_mainModule_2423_, v___x_2424_);
v___x_2426_ = l_Lean_Name_toString(v_fvarId_2420_, v___x_2424_);
v___x_2427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_box(v_isBinder_2419_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2429_);
v___x_2431_ = v___x_2395_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
default: 
{
lean_object* v___x_2433_; 
lean_dec_ref(v_expr_2397_);
lean_del_object(v___x_2395_);
lean_dec_ref(v_i_2393_);
v___x_2433_ = lean_box(0);
return v___x_2433_;
}
}
}
}
case 7:
{
lean_object* v_toCommandContextInfo_2435_; lean_object* v_i_2436_; lean_object* v_env_2437_; lean_object* v_projName_2438_; lean_object* v___x_2439_; 
v_toCommandContextInfo_2435_ = lean_ctor_get(v_ci_2391_, 0);
v_i_2436_ = lean_ctor_get(v_i_2392_, 0);
lean_inc_ref(v_i_2436_);
lean_dec_ref_known(v_i_2392_, 1);
v_env_2437_ = lean_ctor_get(v_toCommandContextInfo_2435_, 0);
v_projName_2438_ = lean_ctor_get(v_i_2436_, 0);
lean_inc(v_projName_2438_);
lean_dec_ref(v_i_2436_);
v___x_2439_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2437_, v_projName_2438_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v___x_2440_; 
lean_dec(v_projName_2438_);
v___x_2440_ = lean_box(0);
return v___x_2440_;
}
else
{
lean_object* v_val_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2455_; 
v_val_2441_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2443_ = v___x_2439_;
v_isShared_2444_ = v_isSharedCheck_2455_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_val_2441_);
lean_dec(v___x_2439_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2455_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2445_ = 1;
v___x_2446_ = l_Lean_Name_toString(v_val_2441_, v___x_2445_);
v___x_2447_ = l_Lean_Name_toString(v_projName_2438_, v___x_2445_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = 0;
v___x_2450_ = lean_box(v___x_2449_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2448_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2451_);
v___x_2453_ = v___x_2443_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
case 5:
{
lean_object* v_toCommandContextInfo_2456_; lean_object* v_i_2457_; lean_object* v_env_2458_; lean_object* v_declName_2459_; lean_object* v___x_2460_; 
v_toCommandContextInfo_2456_ = lean_ctor_get(v_ci_2391_, 0);
v_i_2457_ = lean_ctor_get(v_i_2392_, 0);
lean_inc_ref(v_i_2457_);
lean_dec_ref_known(v_i_2392_, 1);
v_env_2458_ = lean_ctor_get(v_toCommandContextInfo_2456_, 0);
v_declName_2459_ = lean_ctor_get(v_i_2457_, 2);
lean_inc(v_declName_2459_);
lean_dec_ref(v_i_2457_);
v___x_2460_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2458_, v_declName_2459_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v___x_2461_; 
lean_dec(v_declName_2459_);
v___x_2461_ = lean_box(0);
return v___x_2461_;
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2476_; 
v_val_2462_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2464_ = v___x_2460_;
v_isShared_2465_ = v_isSharedCheck_2476_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_val_2462_);
lean_dec(v___x_2460_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2476_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
uint8_t v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2466_ = 1;
v___x_2467_ = l_Lean_Name_toString(v_val_2462_, v___x_2466_);
v___x_2468_ = l_Lean_Name_toString(v_declName_2459_, v___x_2466_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = 0;
v___x_2471_ = lean_box(v___x_2470_);
v___x_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2469_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2472_);
v___x_2474_ = v___x_2464_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
case 17:
{
lean_object* v_toCommandContextInfo_2477_; lean_object* v_i_2478_; lean_object* v_env_2479_; lean_object* v_name_2480_; lean_object* v___x_2481_; 
v_toCommandContextInfo_2477_ = lean_ctor_get(v_ci_2391_, 0);
v_i_2478_ = lean_ctor_get(v_i_2392_, 0);
lean_inc_ref(v_i_2478_);
lean_dec_ref_known(v_i_2392_, 1);
v_env_2479_ = lean_ctor_get(v_toCommandContextInfo_2477_, 0);
v_name_2480_ = lean_ctor_get(v_i_2478_, 1);
lean_inc(v_name_2480_);
lean_dec_ref(v_i_2478_);
v___x_2481_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2479_, v_name_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; 
lean_dec(v_name_2480_);
v___x_2482_ = lean_box(0);
return v___x_2482_;
}
else
{
lean_object* v_val_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2497_; 
v_val_2483_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2485_ = v___x_2481_;
v_isShared_2486_ = v_isSharedCheck_2497_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_val_2483_);
lean_dec(v___x_2481_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2497_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2487_ = 1;
v___x_2488_ = l_Lean_Name_toString(v_val_2483_, v___x_2487_);
v___x_2489_ = l_Lean_Name_toString(v_name_2480_, v___x_2487_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = 0;
v___x_2492_ = lean_box(v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2490_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2493_);
v___x_2495_ = v___x_2485_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
default: 
{
lean_object* v___x_2498_; 
lean_dec_ref(v_i_2392_);
v___x_2498_ = lean_box(0);
return v___x_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf___boxed(lean_object* v_ci_2499_, lean_object* v_i_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_Server_identOf(v_ci_2499_, v_i_2500_);
lean_dec_ref(v_ci_2499_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(uint8_t v___x_2502_, lean_object* v_x_2503_, lean_object* v_x_2504_, lean_object* v_x_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_box(v___x_2502_);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
lean_ctor_set(v___x_2508_, 1, v___y_2506_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed(lean_object* v___x_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_){
_start:
{
uint8_t v___x_3525__boxed_2514_; lean_object* v_res_2515_; 
v___x_3525__boxed_2514_ = lean_unbox(v___x_2509_);
v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(v___x_3525__boxed_2514_, v_x_2510_, v_x_2511_, v_x_2512_, v___y_2513_);
lean_dec_ref(v_x_2512_);
lean_dec_ref(v_x_2511_);
lean_dec_ref(v_x_2510_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(lean_object* v_text_2516_, lean_object* v_ci_2517_, lean_object* v_info_2518_, lean_object* v_x_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2521_; 
lean_inc_ref(v_info_2518_);
v___x_2521_ = l_Lean_Server_identOf(v_ci_2517_, v_info_2518_);
if (lean_obj_tag(v___x_2521_) == 1)
{
lean_object* v_val_2522_; lean_object* v_fst_2523_; lean_object* v_snd_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2549_; 
v_val_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_val_2522_);
lean_dec_ref_known(v___x_2521_, 1);
v_fst_2523_ = lean_ctor_get(v_val_2522_, 0);
v_snd_2524_ = lean_ctor_get(v_val_2522_, 1);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_val_2522_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2526_ = v_val_2522_;
v_isShared_2527_ = v_isSharedCheck_2549_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_snd_2524_);
lean_inc(v_fst_2523_);
lean_dec(v_val_2522_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2549_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_Elab_Info_range_x3f(v_info_2518_);
if (lean_obj_tag(v___x_2528_) == 1)
{
lean_object* v_val_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v_val_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_val_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = l_Lean_Elab_Info_stx(v_info_2518_);
v___x_2531_ = l_Lean_Syntax_getHeadInfo(v___x_2530_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
lean_dec_ref_known(v___x_2531_, 4);
v___x_2532_ = lean_box(0);
v___x_2533_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_2534_ = l_Lean_Syntax_Range_toLspRange(v_text_2516_, v_val_2529_);
v___x_2535_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2535_, 0, v_fst_2523_);
lean_ctor_set(v___x_2535_, 1, v___x_2533_);
lean_ctor_set(v___x_2535_, 2, v___x_2534_);
lean_ctor_set(v___x_2535_, 3, v___x_2530_);
lean_ctor_set(v___x_2535_, 4, v_ci_2517_);
lean_ctor_set(v___x_2535_, 5, v_info_2518_);
v___x_2536_ = lean_unbox(v_snd_2524_);
lean_dec(v_snd_2524_);
lean_ctor_set_uint8(v___x_2535_, sizeof(void*)*6, v___x_2536_);
v___x_2537_ = lean_array_push(v___y_2520_, v___x_2535_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 1, v___x_2537_);
lean_ctor_set(v___x_2526_, 0, v___x_2532_);
v___x_2539_ = v___x_2526_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
lean_dec(v___x_2531_);
lean_dec(v___x_2530_);
lean_dec(v_val_2529_);
lean_dec(v_snd_2524_);
lean_dec(v_fst_2523_);
lean_dec_ref(v_info_2518_);
lean_dec_ref(v_ci_2517_);
lean_dec_ref(v_text_2516_);
v___x_2541_ = lean_box(0);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 1, v___y_2520_);
lean_ctor_set(v___x_2526_, 0, v___x_2541_);
v___x_2543_ = v___x_2526_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___y_2520_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
lean_dec(v___x_2528_);
lean_dec(v_snd_2524_);
lean_dec(v_fst_2523_);
lean_dec_ref(v_info_2518_);
lean_dec_ref(v_ci_2517_);
lean_dec_ref(v_text_2516_);
v___x_2545_ = lean_box(0);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 1, v___y_2520_);
lean_ctor_set(v___x_2526_, 0, v___x_2545_);
v___x_2547_ = v___x_2526_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v___y_2520_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v___x_2521_);
lean_dec_ref(v_info_2518_);
lean_dec_ref(v_ci_2517_);
lean_dec_ref(v_text_2516_);
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
lean_ctor_set(v___x_2551_, 1, v___y_2520_);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed(lean_object* v_text_2552_, lean_object* v_ci_2553_, lean_object* v_info_2554_, lean_object* v_x_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(v_text_2552_, v_ci_2553_, v_info_2554_, v_x_2555_, v___y_2556_);
lean_dec_ref(v_x_2555_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; lean_object* v___f_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_3116__overap_2589_; lean_object* v___x_2590_; 
v___f_2567_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_2568_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_2569_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_2570_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_2571_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_2572_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_2573_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___f_2567_);
lean_ctor_set(v___x_2574_, 1, v___f_2568_);
v___x_2575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___f_2569_);
lean_ctor_set(v___x_2575_, 2, v___f_2570_);
lean_ctor_set(v___x_2575_, 3, v___f_2571_);
lean_ctor_set(v___x_2575_, 4, v___f_2572_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v___f_2573_);
lean_inc_ref_n(v___x_2576_, 6);
v___f_2577_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2577_, 0, v___x_2576_);
v___f_2578_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2578_, 0, v___x_2576_);
v___f_2579_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2579_, 0, v___x_2576_);
v___f_2580_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2580_, 0, v___x_2576_);
v___x_2581_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2581_, 0, lean_box(0));
lean_closure_set(v___x_2581_, 1, lean_box(0));
lean_closure_set(v___x_2581_, 2, v___x_2576_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
lean_ctor_set(v___x_2582_, 1, v___f_2577_);
v___x_2583_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2583_, 0, lean_box(0));
lean_closure_set(v___x_2583_, 1, lean_box(0));
lean_closure_set(v___x_2583_, 2, v___x_2576_);
v___x_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
lean_ctor_set(v___x_2584_, 2, v___f_2578_);
lean_ctor_set(v___x_2584_, 3, v___f_2579_);
lean_ctor_set(v___x_2584_, 4, v___f_2580_);
v___x_2585_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2585_, 0, lean_box(0));
lean_closure_set(v___x_2585_, 1, lean_box(0));
lean_closure_set(v___x_2585_, 2, v___x_2576_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_box(0);
v___x_2588_ = l_instInhabitedOfMonad___redArg(v___x_2586_, v___x_2587_);
v___x_3116__overap_2589_ = lean_panic_fn_borrowed(v___x_2588_, v_msg_2565_);
lean_dec(v___x_2588_);
v___x_2590_ = lean_apply_1(v___x_3116__overap_2589_, v___y_2566_);
return v___x_2590_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2594_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2));
v___x_2595_ = lean_unsigned_to_nat(21u);
v___x_2596_ = lean_unsigned_to_nat(65u);
v___x_2597_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1));
v___x_2598_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0));
v___x_2599_ = l_mkPanicMessageWithDecl(v___x_2598_, v___x_2597_, v___x_2596_, v___x_2595_, v___x_2594_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object* v_preNode_2600_, lean_object* v_postNode_2601_, lean_object* v_x_2602_, lean_object* v_x_2603_, lean_object* v___y_2604_){
_start:
{
switch(lean_obj_tag(v_x_2603_))
{
case 0:
{
lean_object* v_i_2605_; lean_object* v_t_2606_; lean_object* v___x_2607_; 
v_i_2605_ = lean_ctor_get(v_x_2603_, 0);
lean_inc_ref(v_i_2605_);
v_t_2606_ = lean_ctor_get(v_x_2603_, 1);
lean_inc_ref(v_t_2606_);
lean_dec_ref_known(v_x_2603_, 2);
v___x_2607_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2605_, v_x_2602_);
v_x_2602_ = v___x_2607_;
v_x_2603_ = v_t_2606_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_2602_) == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec_ref_known(v_x_2603_, 2);
lean_dec_ref(v_postNode_2601_);
lean_dec_ref(v_preNode_2600_);
v___x_2609_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_2610_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v___x_2609_, v___y_2604_);
return v___x_2610_;
}
else
{
lean_object* v_i_2611_; lean_object* v_children_2612_; lean_object* v_val_2613_; lean_object* v___x_2614_; lean_object* v_fst_2615_; uint8_t v___x_2616_; 
v_i_2611_ = lean_ctor_get(v_x_2603_, 0);
lean_inc_ref_n(v_i_2611_, 2);
v_children_2612_ = lean_ctor_get(v_x_2603_, 1);
lean_inc_ref_n(v_children_2612_, 2);
lean_dec_ref_known(v_x_2603_, 2);
v_val_2613_ = lean_ctor_get(v_x_2602_, 0);
lean_inc_n(v_val_2613_, 2);
lean_inc_ref(v_preNode_2600_);
v___x_2614_ = lean_apply_4(v_preNode_2600_, v_val_2613_, v_i_2611_, v_children_2612_, v___y_2604_);
v_fst_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_fst_2615_);
v___x_2616_ = lean_unbox(v_fst_2615_);
lean_dec(v_fst_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref(v_preNode_2600_);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_x_2602_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v_x_2602_, 0);
lean_dec(v_unused_2636_);
v___x_2618_ = v_x_2602_;
v_isShared_2619_ = v_isSharedCheck_2635_;
goto v_resetjp_2617_;
}
else
{
lean_dec(v_x_2602_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2635_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v_snd_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v_fst_2623_; lean_object* v_snd_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2634_; 
v_snd_2620_ = lean_ctor_get(v___x_2614_, 1);
lean_inc(v_snd_2620_);
lean_dec_ref(v___x_2614_);
v___x_2621_ = lean_box(0);
v___x_2622_ = lean_apply_5(v_postNode_2601_, v_val_2613_, v_i_2611_, v_children_2612_, v___x_2621_, v_snd_2620_);
v_fst_2623_ = lean_ctor_get(v___x_2622_, 0);
v_snd_2624_ = lean_ctor_get(v___x_2622_, 1);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2626_ = v___x_2622_;
v_isShared_2627_ = v_isSharedCheck_2634_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_snd_2624_);
lean_inc(v_fst_2623_);
lean_dec(v___x_2622_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2634_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v_fst_2623_);
v___x_2629_ = v___x_2618_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_fst_2623_);
v___x_2629_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2631_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2629_);
v___x_2631_ = v___x_2626_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_snd_2624_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
else
{
lean_object* v_snd_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v_fst_2642_; lean_object* v_snd_2643_; lean_object* v___x_2644_; lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2654_; 
v_snd_2637_ = lean_ctor_get(v___x_2614_, 1);
lean_inc(v_snd_2637_);
lean_dec_ref(v___x_2614_);
v___x_2638_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2602_, v_i_2611_);
v___x_2639_ = l_Lean_PersistentArray_toList___redArg(v_children_2612_);
v___x_2640_ = lean_box(0);
lean_inc_ref(v_postNode_2601_);
v___x_2641_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2600_, v_postNode_2601_, v___x_2638_, v___x_2639_, v___x_2640_, v_snd_2637_);
v_fst_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_fst_2642_);
v_snd_2643_ = lean_ctor_get(v___x_2641_, 1);
lean_inc(v_snd_2643_);
lean_dec_ref(v___x_2641_);
v___x_2644_ = lean_apply_5(v_postNode_2601_, v_val_2613_, v_i_2611_, v_children_2612_, v_fst_2642_, v_snd_2643_);
v_fst_2645_ = lean_ctor_get(v___x_2644_, 0);
v_snd_2646_ = lean_ctor_get(v___x_2644_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2648_ = v___x_2644_;
v_isShared_2649_ = v_isSharedCheck_2654_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_snd_2646_);
lean_inc(v_fst_2645_);
lean_dec(v___x_2644_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2654_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_fst_2645_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2650_);
v___x_2652_ = v___x_2648_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_snd_2646_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
default: 
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_dec_ref_known(v_x_2603_, 1);
lean_dec(v_x_2602_);
lean_dec_ref(v_postNode_2601_);
lean_dec_ref(v_preNode_2600_);
v___x_2655_ = lean_box(0);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set(v___x_2656_, 1, v___y_2604_);
return v___x_2656_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_2657_, lean_object* v_postNode_2658_, lean_object* v___x_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v___y_2662_){
_start:
{
if (lean_obj_tag(v_x_2660_) == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_dec(v___x_2659_);
lean_dec_ref(v_postNode_2658_);
lean_dec_ref(v_preNode_2657_);
v___x_2663_ = l_List_reverse___redArg(v_x_2661_);
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
lean_ctor_set(v___x_2664_, 1, v___y_2662_);
return v___x_2664_;
}
else
{
lean_object* v_head_2665_; lean_object* v_tail_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2677_; 
v_head_2665_ = lean_ctor_get(v_x_2660_, 0);
v_tail_2666_ = lean_ctor_get(v_x_2660_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_x_2660_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2668_ = v_x_2660_;
v_isShared_2669_ = v_isSharedCheck_2677_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_tail_2666_);
lean_inc(v_head_2665_);
lean_dec(v_x_2660_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2677_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v_fst_2671_; lean_object* v_snd_2672_; lean_object* v___x_2674_; 
lean_inc(v___x_2659_);
lean_inc_ref(v_postNode_2658_);
lean_inc_ref(v_preNode_2657_);
v___x_2670_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2657_, v_postNode_2658_, v___x_2659_, v_head_2665_, v___y_2662_);
v_fst_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_fst_2671_);
v_snd_2672_ = lean_ctor_get(v___x_2670_, 1);
lean_inc(v_snd_2672_);
lean_dec_ref(v___x_2670_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v_x_2661_);
lean_ctor_set(v___x_2668_, 0, v_fst_2671_);
v___x_2674_ = v___x_2668_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_fst_2671_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_x_2661_);
v___x_2674_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
v_x_2660_ = v_tail_2666_;
v_x_2661_ = v___x_2674_;
v___y_2662_ = v_snd_2672_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object* v_postNode_2678_, lean_object* v_ci_2679_, lean_object* v_i_2680_, lean_object* v_cs_2681_, lean_object* v_x_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_apply_4(v_postNode_2678_, v_ci_2679_, v_i_2680_, v_cs_2681_, v___y_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object* v_postNode_2685_, lean_object* v_ci_2686_, lean_object* v_i_2687_, lean_object* v_cs_2688_, lean_object* v_x_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(v_postNode_2685_, v_ci_2686_, v_i_2687_, v_cs_2688_, v_x_2689_, v___y_2690_);
lean_dec(v_x_2689_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object* v_preNode_2692_, lean_object* v_postNode_2693_, lean_object* v_ctx_x3f_2694_, lean_object* v_t_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___f_2697_; lean_object* v___x_2698_; lean_object* v_snd_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2707_; 
v___f_2697_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2697_, 0, v_postNode_2693_);
v___x_2698_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2692_, v___f_2697_, v_ctx_x3f_2694_, v_t_2695_, v___y_2696_);
v_snd_2699_ = lean_ctor_get(v___x_2698_, 1);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v___x_2698_, 0);
lean_dec(v_unused_2708_);
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2707_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_snd_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2707_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2703_ = lean_box(0);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v___x_2703_);
v___x_2705_ = v___x_2701_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_snd_2699_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(lean_object* v_text_2709_, lean_object* v_as_2710_, size_t v_sz_2711_, size_t v_i_2712_, lean_object* v_b_2713_, lean_object* v___y_2714_){
_start:
{
uint8_t v___x_2715_; 
v___x_2715_ = lean_usize_dec_lt(v_i_2712_, v_sz_2711_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
lean_dec_ref(v_text_2709_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_b_2713_);
lean_ctor_set(v___x_2716_, 1, v___y_2714_);
return v___x_2716_;
}
else
{
lean_object* v___x_2717_; lean_object* v___f_2718_; lean_object* v___f_2719_; lean_object* v_a_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v_snd_2723_; lean_object* v___x_2724_; size_t v___x_2725_; size_t v___x_2726_; 
v___x_2717_ = lean_box(v___x_2715_);
v___f_2718_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2718_, 0, v___x_2717_);
lean_inc_ref(v_text_2709_);
v___f_2719_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2719_, 0, v_text_2709_);
v_a_2720_ = lean_array_uget_borrowed(v_as_2710_, v_i_2712_);
v___x_2721_ = lean_box(0);
lean_inc(v_a_2720_);
v___x_2722_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(v___f_2718_, v___f_2719_, v___x_2721_, v_a_2720_, v___y_2714_);
v_snd_2723_ = lean_ctor_get(v___x_2722_, 1);
lean_inc(v_snd_2723_);
lean_dec_ref(v___x_2722_);
v___x_2724_ = lean_box(0);
v___x_2725_ = ((size_t)1ULL);
v___x_2726_ = lean_usize_add(v_i_2712_, v___x_2725_);
v_i_2712_ = v___x_2726_;
v_b_2713_ = v___x_2724_;
v___y_2714_ = v_snd_2723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___boxed(lean_object* v_text_2728_, lean_object* v_as_2729_, lean_object* v_sz_2730_, lean_object* v_i_2731_, lean_object* v_b_2732_, lean_object* v___y_2733_){
_start:
{
size_t v_sz_boxed_2734_; size_t v_i_boxed_2735_; lean_object* v_res_2736_; 
v_sz_boxed_2734_ = lean_unbox_usize(v_sz_2730_);
lean_dec(v_sz_2730_);
v_i_boxed_2735_ = lean_unbox_usize(v_i_2731_);
lean_dec(v_i_2731_);
v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2728_, v_as_2729_, v_sz_boxed_2734_, v_i_boxed_2735_, v_b_2732_, v___y_2733_);
lean_dec_ref(v_as_2729_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences(lean_object* v_text_2737_, lean_object* v_trees_2738_){
_start:
{
lean_object* v___x_2739_; size_t v_sz_2740_; size_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v_snd_2744_; 
v___x_2739_ = lean_box(0);
v_sz_2740_ = lean_array_size(v_trees_2738_);
v___x_2741_ = ((size_t)0ULL);
v___x_2742_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_2743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2737_, v_trees_2738_, v_sz_2740_, v___x_2741_, v___x_2739_, v___x_2742_);
v_snd_2744_ = lean_ctor_get(v___x_2743_, 1);
lean_inc(v_snd_2744_);
lean_dec_ref(v___x_2743_);
return v_snd_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences___boxed(lean_object* v_text_2745_, lean_object* v_trees_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Server_findReferences(v_text_2745_, v_trees_2746_);
lean_dec_ref(v_trees_2746_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2748_, lean_object* v_msg_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v_msg_2749_, v___y_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object* v_00_u03b1_2752_, lean_object* v_preNode_2753_, lean_object* v_postNode_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2753_, v_postNode_2754_, v_x_2755_, v_x_2756_, v___y_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2759_, lean_object* v_preNode_2760_, lean_object* v_postNode_2761_, lean_object* v___x_2762_, lean_object* v_x_2763_, lean_object* v_x_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2760_, v_postNode_2761_, v___x_2762_, v_x_2763_, v_x_2764_, v___y_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(lean_object* v_a_2767_, lean_object* v_x_2768_){
_start:
{
lean_object* v_key_2769_; lean_object* v_value_2770_; lean_object* v_tail_2771_; uint8_t v___x_2772_; 
v_key_2769_ = lean_ctor_get(v_x_2768_, 0);
v_value_2770_ = lean_ctor_get(v_x_2768_, 1);
v_tail_2771_ = lean_ctor_get(v_x_2768_, 2);
v___x_2772_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2769_, v_a_2767_);
if (v___x_2772_ == 0)
{
v_x_2768_ = v_tail_2771_;
goto _start;
}
else
{
lean_inc(v_value_2770_);
return v_value_2770_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg___boxed(lean_object* v_a_2774_, lean_object* v_x_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2774_, v_x_2775_);
lean_dec(v_x_2775_);
lean_dec_ref(v_a_2774_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(lean_object* v_m_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_buckets_2779_; lean_object* v___x_2780_; uint64_t v___x_2781_; uint64_t v___x_2782_; uint64_t v___x_2783_; uint64_t v_fold_2784_; uint64_t v___x_2785_; uint64_t v___x_2786_; uint64_t v___x_2787_; size_t v___x_2788_; size_t v___x_2789_; size_t v___x_2790_; size_t v___x_2791_; size_t v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_buckets_2779_ = lean_ctor_get(v_m_2777_, 1);
v___x_2780_ = lean_array_get_size(v_buckets_2779_);
v___x_2781_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2778_);
v___x_2782_ = 32ULL;
v___x_2783_ = lean_uint64_shift_right(v___x_2781_, v___x_2782_);
v_fold_2784_ = lean_uint64_xor(v___x_2781_, v___x_2783_);
v___x_2785_ = 16ULL;
v___x_2786_ = lean_uint64_shift_right(v_fold_2784_, v___x_2785_);
v___x_2787_ = lean_uint64_xor(v_fold_2784_, v___x_2786_);
v___x_2788_ = lean_uint64_to_usize(v___x_2787_);
v___x_2789_ = lean_usize_of_nat(v___x_2780_);
v___x_2790_ = ((size_t)1ULL);
v___x_2791_ = lean_usize_sub(v___x_2789_, v___x_2790_);
v___x_2792_ = lean_usize_land(v___x_2788_, v___x_2791_);
v___x_2793_ = lean_array_uget_borrowed(v_buckets_2779_, v___x_2792_);
v___x_2794_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2778_, v___x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg___boxed(lean_object* v_m_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2795_, v_a_2796_);
lean_dec_ref(v_a_2796_);
lean_dec_ref(v_m_2795_);
return v_res_2797_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(lean_object* v_a_2798_, lean_object* v_x_2799_){
_start:
{
if (lean_obj_tag(v_x_2799_) == 0)
{
uint8_t v___x_2800_; 
v___x_2800_ = 0;
return v___x_2800_;
}
else
{
lean_object* v_key_2801_; lean_object* v_tail_2802_; uint8_t v___x_2803_; 
v_key_2801_ = lean_ctor_get(v_x_2799_, 0);
v_tail_2802_ = lean_ctor_get(v_x_2799_, 2);
v___x_2803_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2801_, v_a_2798_);
if (v___x_2803_ == 0)
{
v_x_2799_ = v_tail_2802_;
goto _start;
}
else
{
return v___x_2803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg___boxed(lean_object* v_a_2805_, lean_object* v_x_2806_){
_start:
{
uint8_t v_res_2807_; lean_object* v_r_2808_; 
v_res_2807_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2805_, v_x_2806_);
lean_dec(v_x_2806_);
lean_dec_ref(v_a_2805_);
v_r_2808_ = lean_box(v_res_2807_);
return v_r_2808_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(lean_object* v_m_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_buckets_2811_; lean_object* v___x_2812_; uint64_t v___x_2813_; uint64_t v___x_2814_; uint64_t v___x_2815_; uint64_t v_fold_2816_; uint64_t v___x_2817_; uint64_t v___x_2818_; uint64_t v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; size_t v___x_2822_; size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v_buckets_2811_ = lean_ctor_get(v_m_2809_, 1);
v___x_2812_ = lean_array_get_size(v_buckets_2811_);
v___x_2813_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2810_);
v___x_2814_ = 32ULL;
v___x_2815_ = lean_uint64_shift_right(v___x_2813_, v___x_2814_);
v_fold_2816_ = lean_uint64_xor(v___x_2813_, v___x_2815_);
v___x_2817_ = 16ULL;
v___x_2818_ = lean_uint64_shift_right(v_fold_2816_, v___x_2817_);
v___x_2819_ = lean_uint64_xor(v_fold_2816_, v___x_2818_);
v___x_2820_ = lean_uint64_to_usize(v___x_2819_);
v___x_2821_ = lean_usize_of_nat(v___x_2812_);
v___x_2822_ = ((size_t)1ULL);
v___x_2823_ = lean_usize_sub(v___x_2821_, v___x_2822_);
v___x_2824_ = lean_usize_land(v___x_2820_, v___x_2823_);
v___x_2825_ = lean_array_uget_borrowed(v_buckets_2811_, v___x_2824_);
v___x_2826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2810_, v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg___boxed(lean_object* v_m_2827_, lean_object* v_a_2828_){
_start:
{
uint8_t v_res_2829_; lean_object* v_r_2830_; 
v_res_2829_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2827_, v_a_2828_);
lean_dec_ref(v_a_2828_);
lean_dec_ref(v_m_2827_);
v_r_2830_ = lean_box(v_res_2829_);
return v_r_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(lean_object* v_idMap_2831_, lean_object* v_a_2832_){
_start:
{
uint8_t v___x_2833_; 
v___x_2833_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_idMap_2831_, v_a_2832_);
if (v___x_2833_ == 0)
{
return v_a_2832_;
}
else
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_idMap_2831_, v_a_2832_);
lean_dec_ref(v_a_2832_);
v_a_2832_ = v___x_2834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg___boxed(lean_object* v_idMap_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2836_, v_a_2837_);
lean_dec_ref(v_idMap_2836_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object* v_idMap_2839_, lean_object* v_id_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2839_, v_id_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object* v_idMap_2842_, lean_object* v_id_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(v_idMap_2842_, v_id_2843_);
lean_dec_ref(v_idMap_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object* v_00_u03b2_2845_, lean_object* v_m_2846_, lean_object* v_a_2847_){
_start:
{
uint8_t v___x_2848_; 
v___x_2848_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2846_, v_a_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object* v_00_u03b2_2849_, lean_object* v_m_2850_, lean_object* v_a_2851_){
_start:
{
uint8_t v_res_2852_; lean_object* v_r_2853_; 
v_res_2852_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(v_00_u03b2_2849_, v_m_2850_, v_a_2851_);
lean_dec_ref(v_a_2851_);
lean_dec_ref(v_m_2850_);
v_r_2853_ = lean_box(v_res_2852_);
return v_r_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object* v_00_u03b2_2854_, lean_object* v_m_2855_, lean_object* v_a_2856_, lean_object* v_hma_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2855_, v_a_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object* v_00_u03b2_2859_, lean_object* v_m_2860_, lean_object* v_a_2861_, lean_object* v_hma_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(v_00_u03b2_2859_, v_m_2860_, v_a_2861_, v_hma_2862_);
lean_dec_ref(v_a_2861_);
lean_dec_ref(v_m_2860_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object* v_idMap_2864_, lean_object* v_inst_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2864_, v_a_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object* v_idMap_2868_, lean_object* v_inst_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2868_, v_inst_2869_, v_a_2870_);
lean_dec_ref(v_idMap_2868_);
return v_res_2871_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(lean_object* v_00_u03b2_2872_, lean_object* v_a_2873_, lean_object* v_x_2874_){
_start:
{
uint8_t v___x_2875_; 
v___x_2875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2873_, v_x_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2876_, lean_object* v_a_2877_, lean_object* v_x_2878_){
_start:
{
uint8_t v_res_2879_; lean_object* v_r_2880_; 
v_res_2879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(v_00_u03b2_2876_, v_a_2877_, v_x_2878_);
lean_dec(v_x_2878_);
lean_dec_ref(v_a_2877_);
v_r_2880_ = lean_box(v_res_2879_);
return v_r_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(lean_object* v_00_u03b2_2881_, lean_object* v_a_2882_, lean_object* v_x_2883_, lean_object* v_x_2884_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2882_, v_x_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2886_, lean_object* v_a_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(v_00_u03b2_2886_, v_a_2887_, v_x_2888_, v_x_2889_);
lean_dec(v_x_2888_);
lean_dec_ref(v_a_2887_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
if (lean_obj_tag(v_a_2891_) == 0)
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_a_2892_);
return v___x_2893_;
}
else
{
if (lean_obj_tag(v_a_2892_) == 0)
{
lean_object* v_tail_2894_; 
v_tail_2894_ = lean_ctor_get(v_a_2891_, 2);
lean_inc(v_tail_2894_);
lean_dec_ref_known(v_a_2891_, 3);
v_a_2891_ = v_tail_2894_;
goto _start;
}
else
{
lean_object* v_key_2896_; 
v_key_2896_ = lean_ctor_get(v_a_2891_, 0);
if (lean_obj_tag(v_key_2896_) == 0)
{
lean_object* v_tail_2897_; 
lean_inc_ref(v_key_2896_);
lean_dec_ref_known(v_a_2892_, 2);
v_tail_2897_ = lean_ctor_get(v_a_2891_, 2);
lean_inc(v_tail_2897_);
lean_dec_ref_known(v_a_2891_, 3);
v_a_2891_ = v_tail_2897_;
v_a_2892_ = v_key_2896_;
goto _start;
}
else
{
lean_object* v_tail_2899_; 
v_tail_2899_ = lean_ctor_get(v_a_2891_, 2);
lean_inc(v_tail_2899_);
lean_dec_ref_known(v_a_2891_, 3);
v_a_2891_ = v_tail_2899_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(lean_object* v_as_2901_, size_t v_sz_2902_, size_t v_i_2903_, lean_object* v_b_2904_){
_start:
{
uint8_t v___x_2905_; 
v___x_2905_ = lean_usize_dec_lt(v_i_2903_, v_sz_2902_);
if (v___x_2905_ == 0)
{
return v_b_2904_;
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2906_ = lean_array_uget_borrowed(v_as_2901_, v_i_2903_);
lean_inc(v_a_2906_);
v___x_2907_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(v_a_2906_, v_b_2904_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
return v_a_2908_;
}
else
{
lean_object* v_a_2909_; size_t v___x_2910_; size_t v___x_2911_; 
v_a_2909_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2907_, 1);
v___x_2910_ = ((size_t)1ULL);
v___x_2911_ = lean_usize_add(v_i_2903_, v___x_2910_);
v_i_2903_ = v___x_2911_;
v_b_2904_ = v_a_2909_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5___boxed(lean_object* v_as_2913_, lean_object* v_sz_2914_, lean_object* v_i_2915_, lean_object* v_b_2916_){
_start:
{
size_t v_sz_boxed_2917_; size_t v_i_boxed_2918_; lean_object* v_res_2919_; 
v_sz_boxed_2917_ = lean_unbox_usize(v_sz_2914_);
lean_dec(v_sz_2914_);
v_i_boxed_2918_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_as_2913_, v_sz_boxed_2917_, v_i_boxed_2918_, v_b_2916_);
lean_dec_ref(v_as_2913_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(lean_object* v_a_2920_, lean_object* v_b_2921_, lean_object* v_x_2922_){
_start:
{
if (lean_obj_tag(v_x_2922_) == 0)
{
lean_dec(v_b_2921_);
lean_dec_ref(v_a_2920_);
return v_x_2922_;
}
else
{
lean_object* v_key_2923_; lean_object* v_value_2924_; lean_object* v_tail_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2937_; 
v_key_2923_ = lean_ctor_get(v_x_2922_, 0);
v_value_2924_ = lean_ctor_get(v_x_2922_, 1);
v_tail_2925_ = lean_ctor_get(v_x_2922_, 2);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2927_ = v_x_2922_;
v_isShared_2928_ = v_isSharedCheck_2937_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_tail_2925_);
lean_inc(v_value_2924_);
lean_inc(v_key_2923_);
lean_dec(v_x_2922_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2937_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
uint8_t v___x_2929_; 
v___x_2929_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2923_, v_a_2920_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2920_, v_b_2921_, v_tail_2925_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 2, v___x_2930_);
v___x_2932_ = v___x_2927_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_key_2923_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_value_2924_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v___x_2930_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
else
{
lean_object* v___x_2935_; 
lean_dec(v_value_2924_);
lean_dec(v_key_2923_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 1, v_b_2921_);
lean_ctor_set(v___x_2927_, 0, v_a_2920_);
v___x_2935_ = v___x_2927_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2920_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_b_2921_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_tail_2925_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(lean_object* v_x_2938_, lean_object* v_x_2939_){
_start:
{
if (lean_obj_tag(v_x_2939_) == 0)
{
return v_x_2938_;
}
else
{
lean_object* v_key_2940_; lean_object* v_value_2941_; lean_object* v_tail_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2965_; 
v_key_2940_ = lean_ctor_get(v_x_2939_, 0);
v_value_2941_ = lean_ctor_get(v_x_2939_, 1);
v_tail_2942_ = lean_ctor_get(v_x_2939_, 2);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_x_2939_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2944_ = v_x_2939_;
v_isShared_2945_ = v_isSharedCheck_2965_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_tail_2942_);
lean_inc(v_value_2941_);
lean_inc(v_key_2940_);
lean_dec(v_x_2939_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2965_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; uint64_t v___x_2947_; uint64_t v___x_2948_; uint64_t v___x_2949_; uint64_t v_fold_2950_; uint64_t v___x_2951_; uint64_t v___x_2952_; uint64_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; size_t v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2946_ = lean_array_get_size(v_x_2938_);
v___x_2947_ = l_Lean_Lsp_instHashableRefIdent_hash(v_key_2940_);
v___x_2948_ = 32ULL;
v___x_2949_ = lean_uint64_shift_right(v___x_2947_, v___x_2948_);
v_fold_2950_ = lean_uint64_xor(v___x_2947_, v___x_2949_);
v___x_2951_ = 16ULL;
v___x_2952_ = lean_uint64_shift_right(v_fold_2950_, v___x_2951_);
v___x_2953_ = lean_uint64_xor(v_fold_2950_, v___x_2952_);
v___x_2954_ = lean_uint64_to_usize(v___x_2953_);
v___x_2955_ = lean_usize_of_nat(v___x_2946_);
v___x_2956_ = ((size_t)1ULL);
v___x_2957_ = lean_usize_sub(v___x_2955_, v___x_2956_);
v___x_2958_ = lean_usize_land(v___x_2954_, v___x_2957_);
v___x_2959_ = lean_array_uget_borrowed(v_x_2938_, v___x_2958_);
lean_inc(v___x_2959_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 2, v___x_2959_);
v___x_2961_ = v___x_2944_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_key_2940_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_value_2941_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_array_uset(v_x_2938_, v___x_2958_, v___x_2961_);
v_x_2938_ = v___x_2962_;
v_x_2939_ = v_tail_2942_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(lean_object* v_i_2966_, lean_object* v_source_2967_, lean_object* v_target_2968_){
_start:
{
lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = lean_array_get_size(v_source_2967_);
v___x_2970_ = lean_nat_dec_lt(v_i_2966_, v___x_2969_);
if (v___x_2970_ == 0)
{
lean_dec_ref(v_source_2967_);
lean_dec(v_i_2966_);
return v_target_2968_;
}
else
{
lean_object* v_es_2971_; lean_object* v___x_2972_; lean_object* v_source_2973_; lean_object* v_target_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_es_2971_ = lean_array_fget(v_source_2967_, v_i_2966_);
v___x_2972_ = lean_box(0);
v_source_2973_ = lean_array_fset(v_source_2967_, v_i_2966_, v___x_2972_);
v_target_2974_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_target_2968_, v_es_2971_);
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = lean_nat_add(v_i_2966_, v___x_2975_);
lean_dec(v_i_2966_);
v_i_2966_ = v___x_2976_;
v_source_2967_ = v_source_2973_;
v_target_2968_ = v_target_2974_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(lean_object* v_data_2978_){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_nbuckets_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2979_ = lean_array_get_size(v_data_2978_);
v___x_2980_ = lean_unsigned_to_nat(2u);
v_nbuckets_2981_ = lean_nat_mul(v___x_2979_, v___x_2980_);
v___x_2982_ = lean_unsigned_to_nat(0u);
v___x_2983_ = lean_box(0);
v___x_2984_ = lean_mk_array(v_nbuckets_2981_, v___x_2983_);
v___x_2985_ = lean_array_propagate_mark(v_data_2978_, v___x_2984_);
v___x_2986_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2982_, v_data_2978_, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object* v_m_2987_, lean_object* v_a_2988_, lean_object* v_b_2989_){
_start:
{
lean_object* v_size_2990_; lean_object* v_buckets_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3034_; 
v_size_2990_ = lean_ctor_get(v_m_2987_, 0);
v_buckets_2991_ = lean_ctor_get(v_m_2987_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_m_2987_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_2993_ = v_m_2987_;
v_isShared_2994_ = v_isSharedCheck_3034_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_buckets_2991_);
lean_inc(v_size_2990_);
lean_dec(v_m_2987_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3034_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; uint64_t v___x_2996_; uint64_t v___x_2997_; uint64_t v___x_2998_; uint64_t v_fold_2999_; uint64_t v___x_3000_; uint64_t v___x_3001_; uint64_t v___x_3002_; size_t v___x_3003_; size_t v___x_3004_; size_t v___x_3005_; size_t v___x_3006_; size_t v___x_3007_; lean_object* v_bkt_3008_; uint8_t v___x_3009_; 
v___x_2995_ = lean_array_get_size(v_buckets_2991_);
v___x_2996_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2988_);
v___x_2997_ = 32ULL;
v___x_2998_ = lean_uint64_shift_right(v___x_2996_, v___x_2997_);
v_fold_2999_ = lean_uint64_xor(v___x_2996_, v___x_2998_);
v___x_3000_ = 16ULL;
v___x_3001_ = lean_uint64_shift_right(v_fold_2999_, v___x_3000_);
v___x_3002_ = lean_uint64_xor(v_fold_2999_, v___x_3001_);
v___x_3003_ = lean_uint64_to_usize(v___x_3002_);
v___x_3004_ = lean_usize_of_nat(v___x_2995_);
v___x_3005_ = ((size_t)1ULL);
v___x_3006_ = lean_usize_sub(v___x_3004_, v___x_3005_);
v___x_3007_ = lean_usize_land(v___x_3003_, v___x_3006_);
v_bkt_3008_ = lean_array_uget_borrowed(v_buckets_2991_, v___x_3007_);
v___x_3009_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2988_, v_bkt_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v_size_x27_3011_; lean_object* v___x_3012_; lean_object* v_buckets_x27_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3010_ = lean_unsigned_to_nat(1u);
v_size_x27_3011_ = lean_nat_add(v_size_2990_, v___x_3010_);
lean_dec(v_size_2990_);
lean_inc(v_bkt_3008_);
v___x_3012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3012_, 0, v_a_2988_);
lean_ctor_set(v___x_3012_, 1, v_b_2989_);
lean_ctor_set(v___x_3012_, 2, v_bkt_3008_);
v_buckets_x27_3013_ = lean_array_uset(v_buckets_2991_, v___x_3007_, v___x_3012_);
v___x_3014_ = lean_unsigned_to_nat(4u);
v___x_3015_ = lean_nat_mul(v_size_x27_3011_, v___x_3014_);
v___x_3016_ = lean_unsigned_to_nat(3u);
v___x_3017_ = lean_nat_div(v___x_3015_, v___x_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_array_get_size(v_buckets_x27_3013_);
v___x_3019_ = lean_nat_dec_le(v___x_3017_, v___x_3018_);
lean_dec(v___x_3017_);
if (v___x_3019_ == 0)
{
lean_object* v_val_3020_; lean_object* v___x_3022_; 
v_val_3020_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3013_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v_val_3020_);
lean_ctor_set(v___x_2993_, 0, v_size_x27_3011_);
v___x_3022_ = v___x_2993_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_size_x27_3011_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_val_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
else
{
lean_object* v___x_3025_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v_buckets_x27_3013_);
lean_ctor_set(v___x_2993_, 0, v_size_x27_3011_);
v___x_3025_ = v___x_2993_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_size_x27_3011_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_buckets_x27_3013_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
else
{
lean_object* v___x_3027_; lean_object* v_buckets_x27_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
lean_inc(v_bkt_3008_);
v___x_3027_ = lean_box(0);
v_buckets_x27_3028_ = lean_array_uset(v_buckets_2991_, v___x_3007_, v___x_3027_);
v___x_3029_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2988_, v_b_2989_, v_bkt_3008_);
v___x_3030_ = lean_array_uset(v_buckets_x27_3028_, v___x_3007_, v___x_3029_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v___x_3030_);
v___x_3032_ = v___x_2993_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_size_2990_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object* v___x_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
if (lean_obj_tag(v_a_3036_) == 0)
{
lean_object* v___x_3038_; 
lean_dec_ref(v___x_3035_);
v___x_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_a_3037_);
return v___x_3038_;
}
else
{
lean_object* v_key_3039_; lean_object* v_tail_3040_; uint8_t v___x_3041_; 
v_key_3039_ = lean_ctor_get(v_a_3036_, 0);
lean_inc(v_key_3039_);
v_tail_3040_ = lean_ctor_get(v_a_3036_, 2);
lean_inc(v_tail_3040_);
lean_dec_ref_known(v_a_3036_, 3);
v___x_3041_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3039_, v___x_3035_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; 
lean_inc_ref(v___x_3035_);
v___x_3042_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3037_, v_key_3039_, v___x_3035_);
v_a_3036_ = v_tail_3040_;
v_a_3037_ = v___x_3042_;
goto _start;
}
else
{
lean_dec(v_key_3039_);
v_a_3036_ = v_tail_3040_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object* v___x_3045_, lean_object* v_as_3046_, size_t v_sz_3047_, size_t v_i_3048_, lean_object* v_b_3049_){
_start:
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_usize_dec_lt(v_i_3048_, v_sz_3047_);
if (v___x_3050_ == 0)
{
lean_dec_ref(v___x_3045_);
return v_b_3049_;
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3052_; 
v_a_3051_ = lean_array_uget_borrowed(v_as_3046_, v_i_3048_);
lean_inc(v_a_3051_);
lean_inc_ref(v___x_3045_);
v___x_3052_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(v___x_3045_, v_a_3051_, v_b_3049_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; 
lean_dec_ref(v___x_3045_);
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
return v_a_3053_;
}
else
{
lean_object* v_a_3054_; size_t v___x_3055_; size_t v___x_3056_; 
v_a_3054_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3055_ = ((size_t)1ULL);
v___x_3056_ = lean_usize_add(v_i_3048_, v___x_3055_);
v_i_3048_ = v___x_3056_;
v_b_3049_ = v_a_3054_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object* v___x_3058_, lean_object* v_as_3059_, lean_object* v_sz_3060_, lean_object* v_i_3061_, lean_object* v_b_3062_){
_start:
{
size_t v_sz_boxed_3063_; size_t v_i_boxed_3064_; lean_object* v_res_3065_; 
v_sz_boxed_3063_ = lean_unbox_usize(v_sz_3060_);
lean_dec(v_sz_3060_);
v_i_boxed_3064_ = lean_unbox_usize(v_i_3061_);
lean_dec(v_i_3061_);
v_res_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3058_, v_as_3059_, v_sz_boxed_3063_, v_i_boxed_3064_, v_b_3062_);
lean_dec_ref(v_as_3059_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
if (lean_obj_tag(v_a_3066_) == 0)
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3068_, 0, v_a_3067_);
return v___x_3068_;
}
else
{
lean_object* v_value_3069_; lean_object* v_key_3070_; lean_object* v_tail_3071_; lean_object* v_buckets_3072_; size_t v_sz_3073_; size_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v_value_3069_ = lean_ctor_get(v_a_3066_, 1);
lean_inc(v_value_3069_);
v_key_3070_ = lean_ctor_get(v_a_3066_, 0);
lean_inc(v_key_3070_);
v_tail_3071_ = lean_ctor_get(v_a_3066_, 2);
lean_inc(v_tail_3071_);
lean_dec_ref_known(v_a_3066_, 3);
v_buckets_3072_ = lean_ctor_get(v_value_3069_, 1);
lean_inc_ref(v_buckets_3072_);
lean_dec(v_value_3069_);
v_sz_3073_ = lean_array_size(v_buckets_3072_);
v___x_3074_ = ((size_t)0ULL);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_buckets_3072_, v_sz_3073_, v___x_3074_, v_key_3070_);
v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3075_, v_buckets_3072_, v_sz_3073_, v___x_3074_, v_a_3067_);
lean_dec_ref(v_buckets_3072_);
v_a_3066_ = v_tail_3071_;
v_a_3067_ = v___x_3076_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object* v_as_3078_, size_t v_sz_3079_, size_t v_i_3080_, lean_object* v_b_3081_){
_start:
{
uint8_t v___x_3082_; 
v___x_3082_ = lean_usize_dec_lt(v_i_3080_, v_sz_3079_);
if (v___x_3082_ == 0)
{
return v_b_3081_;
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3084_; 
v_a_3083_ = lean_array_uget_borrowed(v_as_3078_, v_i_3080_);
lean_inc(v_a_3083_);
v___x_3084_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(v_a_3083_, v_b_3081_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
lean_dec_ref_known(v___x_3084_, 1);
return v_a_3085_;
}
else
{
lean_object* v_a_3086_; size_t v___x_3087_; size_t v___x_3088_; 
v_a_3086_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3084_, 1);
v___x_3087_ = ((size_t)1ULL);
v___x_3088_ = lean_usize_add(v_i_3080_, v___x_3087_);
v_i_3080_ = v___x_3088_;
v_b_3081_ = v_a_3086_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object* v_as_3090_, lean_object* v_sz_3091_, lean_object* v_i_3092_, lean_object* v_b_3093_){
_start:
{
size_t v_sz_boxed_3094_; size_t v_i_boxed_3095_; lean_object* v_res_3096_; 
v_sz_boxed_3094_ = lean_unbox_usize(v_sz_3091_);
lean_dec(v_sz_3091_);
v_i_boxed_3095_ = lean_unbox_usize(v_i_3092_);
lean_dec(v_i_3092_);
v_res_3096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_as_3090_, v_sz_boxed_3094_, v_i_boxed_3095_, v_b_3093_);
lean_dec_ref(v_as_3090_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object* v_a_3097_, lean_object* v_x_3098_){
_start:
{
if (lean_obj_tag(v_x_3098_) == 0)
{
return v_x_3098_;
}
else
{
lean_object* v_key_3099_; lean_object* v_value_3100_; lean_object* v_tail_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3110_; 
v_key_3099_ = lean_ctor_get(v_x_3098_, 0);
v_value_3100_ = lean_ctor_get(v_x_3098_, 1);
v_tail_3101_ = lean_ctor_get(v_x_3098_, 2);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_x_3098_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3103_ = v_x_3098_;
v_isShared_3104_ = v_isSharedCheck_3110_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_tail_3101_);
lean_inc(v_value_3100_);
lean_inc(v_key_3099_);
lean_dec(v_x_3098_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3110_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
uint8_t v___x_3105_; 
v___x_3105_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3099_, v_a_3097_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3097_, v_tail_3101_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 2, v___x_3106_);
v___x_3108_ = v___x_3103_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_key_3099_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_value_3100_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
else
{
lean_del_object(v___x_3103_);
lean_dec(v_value_3100_);
lean_dec(v_key_3099_);
return v_tail_3101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object* v_a_3111_, lean_object* v_x_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3111_, v_x_3112_);
lean_dec_ref(v_a_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object* v_m_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_size_3116_; lean_object* v_buckets_3117_; lean_object* v___x_3118_; uint64_t v___x_3119_; uint64_t v___x_3120_; uint64_t v___x_3121_; uint64_t v_fold_3122_; uint64_t v___x_3123_; uint64_t v___x_3124_; uint64_t v___x_3125_; size_t v___x_3126_; size_t v___x_3127_; size_t v___x_3128_; size_t v___x_3129_; size_t v___x_3130_; lean_object* v_bkt_3131_; uint8_t v___x_3132_; 
v_size_3116_ = lean_ctor_get(v_m_3114_, 0);
v_buckets_3117_ = lean_ctor_get(v_m_3114_, 1);
v___x_3118_ = lean_array_get_size(v_buckets_3117_);
v___x_3119_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3115_);
v___x_3120_ = 32ULL;
v___x_3121_ = lean_uint64_shift_right(v___x_3119_, v___x_3120_);
v_fold_3122_ = lean_uint64_xor(v___x_3119_, v___x_3121_);
v___x_3123_ = 16ULL;
v___x_3124_ = lean_uint64_shift_right(v_fold_3122_, v___x_3123_);
v___x_3125_ = lean_uint64_xor(v_fold_3122_, v___x_3124_);
v___x_3126_ = lean_uint64_to_usize(v___x_3125_);
v___x_3127_ = lean_usize_of_nat(v___x_3118_);
v___x_3128_ = ((size_t)1ULL);
v___x_3129_ = lean_usize_sub(v___x_3127_, v___x_3128_);
v___x_3130_ = lean_usize_land(v___x_3126_, v___x_3129_);
v_bkt_3131_ = lean_array_uget_borrowed(v_buckets_3117_, v___x_3130_);
v___x_3132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3115_, v_bkt_3131_);
if (v___x_3132_ == 0)
{
return v_m_3114_;
}
else
{
lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3145_; 
lean_inc(v_bkt_3131_);
lean_inc_ref(v_buckets_3117_);
lean_inc(v_size_3116_);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_m_3114_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; lean_object* v_unused_3147_; 
v_unused_3146_ = lean_ctor_get(v_m_3114_, 1);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_m_3114_, 0);
lean_dec(v_unused_3147_);
v___x_3134_ = v_m_3114_;
v_isShared_3135_ = v_isSharedCheck_3145_;
goto v_resetjp_3133_;
}
else
{
lean_dec(v_m_3114_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3145_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v_buckets_x27_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3136_ = lean_box(0);
v_buckets_x27_3137_ = lean_array_uset(v_buckets_3117_, v___x_3130_, v___x_3136_);
v___x_3138_ = lean_unsigned_to_nat(1u);
v___x_3139_ = lean_nat_sub(v_size_3116_, v___x_3138_);
lean_dec(v_size_3116_);
v___x_3140_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3115_, v_bkt_3131_);
v___x_3141_ = lean_array_uset(v_buckets_x27_3137_, v___x_3130_, v___x_3140_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 1, v___x_3141_);
lean_ctor_set(v___x_3134_, 0, v___x_3139_);
v___x_3143_ = v___x_3134_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object* v_m_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3148_, v_a_3149_);
lean_dec_ref(v_a_3149_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object* v_m_3151_, lean_object* v_a_3152_, lean_object* v_b_3153_){
_start:
{
lean_object* v_size_3154_; lean_object* v_buckets_3155_; lean_object* v___x_3156_; uint64_t v___x_3157_; uint64_t v___x_3158_; uint64_t v___x_3159_; uint64_t v_fold_3160_; uint64_t v___x_3161_; uint64_t v___x_3162_; uint64_t v___x_3163_; size_t v___x_3164_; size_t v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; size_t v___x_3168_; lean_object* v_bkt_3169_; uint8_t v___x_3170_; 
v_size_3154_ = lean_ctor_get(v_m_3151_, 0);
v_buckets_3155_ = lean_ctor_get(v_m_3151_, 1);
v___x_3156_ = lean_array_get_size(v_buckets_3155_);
v___x_3157_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3152_);
v___x_3158_ = 32ULL;
v___x_3159_ = lean_uint64_shift_right(v___x_3157_, v___x_3158_);
v_fold_3160_ = lean_uint64_xor(v___x_3157_, v___x_3159_);
v___x_3161_ = 16ULL;
v___x_3162_ = lean_uint64_shift_right(v_fold_3160_, v___x_3161_);
v___x_3163_ = lean_uint64_xor(v_fold_3160_, v___x_3162_);
v___x_3164_ = lean_uint64_to_usize(v___x_3163_);
v___x_3165_ = lean_usize_of_nat(v___x_3156_);
v___x_3166_ = ((size_t)1ULL);
v___x_3167_ = lean_usize_sub(v___x_3165_, v___x_3166_);
v___x_3168_ = lean_usize_land(v___x_3164_, v___x_3167_);
v_bkt_3169_ = lean_array_uget_borrowed(v_buckets_3155_, v___x_3168_);
v___x_3170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3152_, v_bkt_3169_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3191_; 
lean_inc_ref(v_buckets_3155_);
lean_inc(v_size_3154_);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_m_3151_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; lean_object* v_unused_3193_; 
v_unused_3192_ = lean_ctor_get(v_m_3151_, 1);
lean_dec(v_unused_3192_);
v_unused_3193_ = lean_ctor_get(v_m_3151_, 0);
lean_dec(v_unused_3193_);
v___x_3172_ = v_m_3151_;
v_isShared_3173_ = v_isSharedCheck_3191_;
goto v_resetjp_3171_;
}
else
{
lean_dec(v_m_3151_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3191_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v_size_x27_3175_; lean_object* v___x_3176_; lean_object* v_buckets_x27_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3174_ = lean_unsigned_to_nat(1u);
v_size_x27_3175_ = lean_nat_add(v_size_3154_, v___x_3174_);
lean_dec(v_size_3154_);
lean_inc(v_bkt_3169_);
v___x_3176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3176_, 0, v_a_3152_);
lean_ctor_set(v___x_3176_, 1, v_b_3153_);
lean_ctor_set(v___x_3176_, 2, v_bkt_3169_);
v_buckets_x27_3177_ = lean_array_uset(v_buckets_3155_, v___x_3168_, v___x_3176_);
v___x_3178_ = lean_unsigned_to_nat(4u);
v___x_3179_ = lean_nat_mul(v_size_x27_3175_, v___x_3178_);
v___x_3180_ = lean_unsigned_to_nat(3u);
v___x_3181_ = lean_nat_div(v___x_3179_, v___x_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_array_get_size(v_buckets_x27_3177_);
v___x_3183_ = lean_nat_dec_le(v___x_3181_, v___x_3182_);
lean_dec(v___x_3181_);
if (v___x_3183_ == 0)
{
lean_object* v_val_3184_; lean_object* v___x_3186_; 
v_val_3184_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3177_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 1, v_val_3184_);
lean_ctor_set(v___x_3172_, 0, v_size_x27_3175_);
v___x_3186_ = v___x_3172_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_size_x27_3175_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_val_3184_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
else
{
lean_object* v___x_3189_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 1, v_buckets_x27_3177_);
lean_ctor_set(v___x_3172_, 0, v_size_x27_3175_);
v___x_3189_ = v___x_3172_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_size_x27_3175_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_buckets_x27_3177_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
else
{
lean_dec(v_b_3153_);
lean_dec_ref(v_a_3152_);
return v_m_3151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object* v_a_3194_, lean_object* v_fallback_3195_, lean_object* v_x_3196_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 0)
{
lean_inc(v_fallback_3195_);
return v_fallback_3195_;
}
else
{
lean_object* v_key_3197_; lean_object* v_value_3198_; lean_object* v_tail_3199_; uint8_t v___x_3200_; 
v_key_3197_ = lean_ctor_get(v_x_3196_, 0);
v_value_3198_ = lean_ctor_get(v_x_3196_, 1);
v_tail_3199_ = lean_ctor_get(v_x_3196_, 2);
v___x_3200_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3197_, v_a_3194_);
if (v___x_3200_ == 0)
{
v_x_3196_ = v_tail_3199_;
goto _start;
}
else
{
lean_inc(v_value_3198_);
return v_value_3198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object* v_a_3202_, lean_object* v_fallback_3203_, lean_object* v_x_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3202_, v_fallback_3203_, v_x_3204_);
lean_dec(v_x_3204_);
lean_dec(v_fallback_3203_);
lean_dec_ref(v_a_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object* v_m_3206_, lean_object* v_a_3207_, lean_object* v_fallback_3208_){
_start:
{
lean_object* v_buckets_3209_; lean_object* v___x_3210_; uint64_t v___x_3211_; uint64_t v___x_3212_; uint64_t v___x_3213_; uint64_t v_fold_3214_; uint64_t v___x_3215_; uint64_t v___x_3216_; uint64_t v___x_3217_; size_t v___x_3218_; size_t v___x_3219_; size_t v___x_3220_; size_t v___x_3221_; size_t v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_buckets_3209_ = lean_ctor_get(v_m_3206_, 1);
v___x_3210_ = lean_array_get_size(v_buckets_3209_);
v___x_3211_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3207_);
v___x_3212_ = 32ULL;
v___x_3213_ = lean_uint64_shift_right(v___x_3211_, v___x_3212_);
v_fold_3214_ = lean_uint64_xor(v___x_3211_, v___x_3213_);
v___x_3215_ = 16ULL;
v___x_3216_ = lean_uint64_shift_right(v_fold_3214_, v___x_3215_);
v___x_3217_ = lean_uint64_xor(v_fold_3214_, v___x_3216_);
v___x_3218_ = lean_uint64_to_usize(v___x_3217_);
v___x_3219_ = lean_usize_of_nat(v___x_3210_);
v___x_3220_ = ((size_t)1ULL);
v___x_3221_ = lean_usize_sub(v___x_3219_, v___x_3220_);
v___x_3222_ = lean_usize_land(v___x_3218_, v___x_3221_);
v___x_3223_ = lean_array_uget_borrowed(v_buckets_3209_, v___x_3222_);
v___x_3224_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3207_, v_fallback_3208_, v___x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object* v_m_3225_, lean_object* v_a_3226_, lean_object* v_fallback_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3225_, v_a_3226_, v_fallback_3227_);
lean_dec(v_fallback_3227_);
lean_dec_ref(v_a_3226_);
lean_dec_ref(v_m_3225_);
return v_res_3228_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_unsigned_to_nat(16u);
v___x_3231_ = lean_mk_array(v___x_3230_, v___x_3229_);
return v___x_3231_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0);
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
lean_ctor_set(v___x_3234_, 1, v___x_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object* v_idMap_3235_, lean_object* v_classesById_3236_, lean_object* v_id_3237_){
_start:
{
lean_object* v_representative_3238_; lean_object* v___x_3239_; lean_object* v_class_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v_class_3243_; lean_object* v___x_3244_; 
lean_inc_ref(v_id_3237_);
v_representative_3238_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_3235_, v_id_3237_);
v___x_3239_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_class_3240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_classesById_3236_, v_representative_3238_, v___x_3239_);
v___x_3241_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_classesById_3236_, v_representative_3238_);
v___x_3242_ = lean_box(0);
v_class_3243_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_class_3240_, v_id_3237_, v___x_3242_);
v___x_3244_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v___x_3241_, v_representative_3238_, v_class_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object* v_idMap_3245_, lean_object* v_classesById_3246_, lean_object* v_id_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3245_, v_classesById_3246_, v_id_3247_);
lean_dec_ref(v_idMap_3245_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object* v_idMap_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_){
_start:
{
if (lean_obj_tag(v_a_3250_) == 0)
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3252_, 0, v_a_3251_);
return v___x_3252_;
}
else
{
lean_object* v_key_3253_; lean_object* v_value_3254_; lean_object* v_tail_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_key_3253_ = lean_ctor_get(v_a_3250_, 0);
lean_inc(v_key_3253_);
v_value_3254_ = lean_ctor_get(v_a_3250_, 1);
lean_inc(v_value_3254_);
v_tail_3255_ = lean_ctor_get(v_a_3250_, 2);
lean_inc(v_tail_3255_);
lean_dec_ref_known(v_a_3250_, 3);
v___x_3256_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3249_, v_a_3251_, v_key_3253_);
v___x_3257_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3249_, v___x_3256_, v_value_3254_);
v_a_3250_ = v_tail_3255_;
v_a_3251_ = v___x_3257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object* v_idMap_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3259_, v_a_3260_, v_a_3261_);
lean_dec_ref(v_idMap_3259_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object* v_idMap_3263_, lean_object* v_as_3264_, size_t v_sz_3265_, size_t v_i_3266_, lean_object* v_b_3267_){
_start:
{
uint8_t v___x_3268_; 
v___x_3268_ = lean_usize_dec_lt(v_i_3266_, v_sz_3265_);
if (v___x_3268_ == 0)
{
return v_b_3267_;
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3270_; 
v_a_3269_ = lean_array_uget_borrowed(v_as_3264_, v_i_3266_);
lean_inc(v_a_3269_);
v___x_3270_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3263_, v_a_3269_, v_b_3267_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
return v_a_3271_;
}
else
{
lean_object* v_a_3272_; size_t v___x_3273_; size_t v___x_3274_; 
v_a_3272_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3273_ = ((size_t)1ULL);
v___x_3274_ = lean_usize_add(v_i_3266_, v___x_3273_);
v_i_3266_ = v___x_3274_;
v_b_3267_ = v_a_3272_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object* v_idMap_3276_, lean_object* v_as_3277_, lean_object* v_sz_3278_, lean_object* v_i_3279_, lean_object* v_b_3280_){
_start:
{
size_t v_sz_boxed_3281_; size_t v_i_boxed_3282_; lean_object* v_res_3283_; 
v_sz_boxed_3281_ = lean_unbox_usize(v_sz_3278_);
lean_dec(v_sz_3278_);
v_i_boxed_3282_ = lean_unbox_usize(v_i_3279_);
lean_dec(v_i_3279_);
v_res_3283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3276_, v_as_3277_, v_sz_boxed_3281_, v_i_boxed_3282_, v_b_3280_);
lean_dec_ref(v_as_3277_);
lean_dec_ref(v_idMap_3276_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object* v_idMap_3284_){
_start:
{
lean_object* v_buckets_3285_; lean_object* v_classesById_3286_; size_t v_sz_3287_; size_t v___x_3288_; lean_object* v___x_3289_; lean_object* v_buckets_3290_; size_t v_sz_3291_; lean_object* v___x_3292_; 
v_buckets_3285_ = lean_ctor_get(v_idMap_3284_, 1);
v_classesById_3286_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_sz_3287_ = lean_array_size(v_buckets_3285_);
v___x_3288_ = ((size_t)0ULL);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3284_, v_buckets_3285_, v_sz_3287_, v___x_3288_, v_classesById_3286_);
v_buckets_3290_ = lean_ctor_get(v___x_3289_, 1);
lean_inc_ref(v_buckets_3290_);
lean_dec_ref(v___x_3289_);
v_sz_3291_ = lean_array_size(v_buckets_3290_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_buckets_3290_, v_sz_3291_, v___x_3288_, v_classesById_3286_);
lean_dec_ref(v_buckets_3290_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object* v_idMap_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v_idMap_3293_);
lean_dec_ref(v_idMap_3293_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object* v_00_u03b2_3295_, lean_object* v_m_3296_, lean_object* v_a_3297_, lean_object* v_fallback_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3296_, v_a_3297_, v_fallback_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object* v_00_u03b2_3300_, lean_object* v_m_3301_, lean_object* v_a_3302_, lean_object* v_fallback_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(v_00_u03b2_3300_, v_m_3301_, v_a_3302_, v_fallback_3303_);
lean_dec(v_fallback_3303_);
lean_dec_ref(v_a_3302_);
lean_dec_ref(v_m_3301_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object* v_00_u03b2_3305_, lean_object* v_m_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3306_, v_a_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object* v_00_u03b2_3309_, lean_object* v_m_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(v_00_u03b2_3309_, v_m_3310_, v_a_3311_);
lean_dec_ref(v_a_3311_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object* v_00_u03b2_3313_, lean_object* v_m_3314_, lean_object* v_a_3315_, lean_object* v_b_3316_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_m_3314_, v_a_3315_, v_b_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object* v_00_u03b2_3318_, lean_object* v_m_3319_, lean_object* v_a_3320_, lean_object* v_b_3321_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_m_3319_, v_a_3320_, v_b_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object* v_00_u03b2_3323_, lean_object* v_a_3324_, lean_object* v_fallback_3325_, lean_object* v_x_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3324_, v_fallback_3325_, v_x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3328_, lean_object* v_a_3329_, lean_object* v_fallback_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(v_00_u03b2_3328_, v_a_3329_, v_fallback_3330_, v_x_3331_);
lean_dec(v_x_3331_);
lean_dec(v_fallback_3330_);
lean_dec_ref(v_a_3329_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object* v_00_u03b2_3333_, lean_object* v_a_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3334_, v_x_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3337_, lean_object* v_a_3338_, lean_object* v_x_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(v_00_u03b2_3337_, v_a_3338_, v_x_3339_);
lean_dec_ref(v_a_3338_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object* v_00_u03b2_3341_, lean_object* v_data_3342_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_data_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object* v_00_u03b2_3344_, lean_object* v_a_3345_, lean_object* v_b_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_3345_, v_b_3346_, v_x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3349_, lean_object* v_i_3350_, lean_object* v_source_3351_, lean_object* v_target_3352_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v_i_3350_, v_source_3351_, v_target_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object* v_00_u03b2_3354_, lean_object* v_x_3355_, lean_object* v_x_3356_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_x_3355_, v_x_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object* v_id_3358_, lean_object* v_baseId_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v___x_3361_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3360_, v_id_3358_);
v___x_3362_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3360_, v_baseId_3359_);
v___x_3363_ = l_Lean_Lsp_instBEqRefIdent_beq(v___x_3362_, v___x_3361_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3364_ = lean_box(0);
v___x_3365_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3360_, v___x_3361_, v___x_3362_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3364_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
return v___x_3366_;
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec_ref(v___x_3362_);
lean_dec_ref(v___x_3361_);
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
lean_ctor_set(v___x_3368_, 1, v_a_3360_);
return v___x_3368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object* v_ci_3369_, lean_object* v_info_3370_, lean_object* v_x_3371_, lean_object* v___y_3372_){
_start:
{
if (lean_obj_tag(v_info_3370_) == 11)
{
lean_object* v_toCommandContextInfo_3373_; lean_object* v_i_3374_; lean_object* v_env_3375_; lean_object* v___x_3376_; lean_object* v_mainModule_3377_; lean_object* v_id_3378_; lean_object* v_baseId_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v_toCommandContextInfo_3373_ = lean_ctor_get(v_ci_3369_, 0);
v_i_3374_ = lean_ctor_get(v_info_3370_, 0);
lean_inc_ref(v_i_3374_);
lean_dec_ref_known(v_info_3370_, 1);
v_env_3375_ = lean_ctor_get(v_toCommandContextInfo_3373_, 0);
v___x_3376_ = l_Lean_Environment_header(v_env_3375_);
v_mainModule_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_mainModule_3377_);
lean_dec_ref(v___x_3376_);
v_id_3378_ = lean_ctor_get(v_i_3374_, 1);
lean_inc(v_id_3378_);
v_baseId_3379_ = lean_ctor_get(v_i_3374_, 2);
lean_inc(v_baseId_3379_);
lean_dec_ref(v_i_3374_);
v___x_3380_ = 1;
v___x_3381_ = l_Lean_Name_toString(v_mainModule_3377_, v___x_3380_);
v___x_3382_ = l_Lean_Name_toString(v_id_3378_, v___x_3380_);
lean_inc_ref(v___x_3381_);
v___x_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = l_Lean_Name_toString(v_baseId_3379_, v___x_3380_);
v___x_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3381_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v___x_3383_, v___x_3385_, v___y_3372_);
return v___x_3386_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_dec_ref(v_info_3370_);
v___x_3387_ = lean_box(0);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___y_3372_);
return v___x_3388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object* v_ci_3389_, lean_object* v_info_3390_, lean_object* v_x_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(v_ci_3389_, v_info_3390_, v_x_3391_, v___y_3392_);
lean_dec_ref(v_x_3391_);
lean_dec_ref(v_ci_3389_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object* v_x_3394_, lean_object* v_x_3395_, lean_object* v_x_3396_, lean_object* v___y_3397_){
_start:
{
uint8_t v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = 1;
v___x_3399_ = lean_box(v___x_3398_);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
lean_ctor_set(v___x_3400_, 1, v___y_3397_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object* v_x_3401_, lean_object* v_x_3402_, lean_object* v_x_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(v_x_3401_, v_x_3402_, v_x_3403_, v___y_3404_);
lean_dec_ref(v_x_3403_);
lean_dec_ref(v_x_3402_);
lean_dec_ref(v_x_3401_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___f_3408_; lean_object* v___f_3409_; lean_object* v___f_3410_; lean_object* v___f_3411_; lean_object* v___f_3412_; lean_object* v___f_3413_; lean_object* v___f_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___f_3418_; lean_object* v___f_3419_; lean_object* v___f_3420_; lean_object* v___f_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3750__overap_3430_; lean_object* v___x_3431_; 
v___f_3408_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3409_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3410_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3411_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3412_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3413_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3414_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___f_3408_);
lean_ctor_set(v___x_3415_, 1, v___f_3409_);
v___x_3416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v___f_3410_);
lean_ctor_set(v___x_3416_, 2, v___f_3411_);
lean_ctor_set(v___x_3416_, 3, v___f_3412_);
lean_ctor_set(v___x_3416_, 4, v___f_3413_);
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
lean_ctor_set(v___x_3417_, 1, v___f_3414_);
lean_inc_ref_n(v___x_3417_, 6);
v___f_3418_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3418_, 0, v___x_3417_);
v___f_3419_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3419_, 0, v___x_3417_);
v___f_3420_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3420_, 0, v___x_3417_);
v___f_3421_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3421_, 0, v___x_3417_);
v___x_3422_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3422_, 0, lean_box(0));
lean_closure_set(v___x_3422_, 1, lean_box(0));
lean_closure_set(v___x_3422_, 2, v___x_3417_);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v___f_3418_);
v___x_3424_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3424_, 0, lean_box(0));
lean_closure_set(v___x_3424_, 1, lean_box(0));
lean_closure_set(v___x_3424_, 2, v___x_3417_);
v___x_3425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
lean_ctor_set(v___x_3425_, 2, v___f_3419_);
lean_ctor_set(v___x_3425_, 3, v___f_3420_);
lean_ctor_set(v___x_3425_, 4, v___f_3421_);
v___x_3426_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3426_, 0, lean_box(0));
lean_closure_set(v___x_3426_, 1, lean_box(0));
lean_closure_set(v___x_3426_, 2, v___x_3417_);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = lean_box(0);
v___x_3429_ = l_instInhabitedOfMonad___redArg(v___x_3427_, v___x_3428_);
v___x_3750__overap_3430_ = lean_panic_fn_borrowed(v___x_3429_, v_msg_3406_);
lean_dec(v___x_3429_);
v___x_3431_ = lean_apply_1(v___x_3750__overap_3430_, v___y_3407_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3432_, lean_object* v_postNode_3433_, lean_object* v_x_3434_, lean_object* v_x_3435_, lean_object* v___y_3436_){
_start:
{
switch(lean_obj_tag(v_x_3435_))
{
case 0:
{
lean_object* v_i_3437_; lean_object* v_t_3438_; lean_object* v___x_3439_; 
v_i_3437_ = lean_ctor_get(v_x_3435_, 0);
lean_inc_ref(v_i_3437_);
v_t_3438_ = lean_ctor_get(v_x_3435_, 1);
lean_inc_ref(v_t_3438_);
lean_dec_ref_known(v_x_3435_, 2);
v___x_3439_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3437_, v_x_3434_);
v_x_3434_ = v___x_3439_;
v_x_3435_ = v_t_3438_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3434_) == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
lean_dec_ref_known(v_x_3435_, 2);
lean_dec_ref(v_postNode_3433_);
lean_dec_ref(v_preNode_3432_);
v___x_3441_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3442_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3441_, v___y_3436_);
return v___x_3442_;
}
else
{
lean_object* v_i_3443_; lean_object* v_children_3444_; lean_object* v_val_3445_; lean_object* v___x_3446_; lean_object* v_fst_3447_; uint8_t v___x_3448_; 
v_i_3443_ = lean_ctor_get(v_x_3435_, 0);
lean_inc_ref_n(v_i_3443_, 2);
v_children_3444_ = lean_ctor_get(v_x_3435_, 1);
lean_inc_ref_n(v_children_3444_, 2);
lean_dec_ref_known(v_x_3435_, 2);
v_val_3445_ = lean_ctor_get(v_x_3434_, 0);
lean_inc_n(v_val_3445_, 2);
lean_inc_ref(v_preNode_3432_);
v___x_3446_ = lean_apply_4(v_preNode_3432_, v_val_3445_, v_i_3443_, v_children_3444_, v___y_3436_);
v_fst_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_fst_3447_);
v___x_3448_ = lean_unbox(v_fst_3447_);
lean_dec(v_fst_3447_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v_preNode_3432_);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_x_3434_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; 
v_unused_3468_ = lean_ctor_get(v_x_3434_, 0);
lean_dec(v_unused_3468_);
v___x_3450_ = v_x_3434_;
v_isShared_3451_ = v_isSharedCheck_3467_;
goto v_resetjp_3449_;
}
else
{
lean_dec(v_x_3434_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3467_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_snd_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v_fst_3455_; lean_object* v_snd_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3466_; 
v_snd_3452_ = lean_ctor_get(v___x_3446_, 1);
lean_inc(v_snd_3452_);
lean_dec_ref(v___x_3446_);
v___x_3453_ = lean_box(0);
v___x_3454_ = lean_apply_5(v_postNode_3433_, v_val_3445_, v_i_3443_, v_children_3444_, v___x_3453_, v_snd_3452_);
v_fst_3455_ = lean_ctor_get(v___x_3454_, 0);
v_snd_3456_ = lean_ctor_get(v___x_3454_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3458_ = v___x_3454_;
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_snd_3456_);
lean_inc(v_fst_3455_);
lean_dec(v___x_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3466_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v_fst_3455_);
v___x_3461_ = v___x_3450_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_fst_3455_);
v___x_3461_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3461_);
v___x_3463_ = v___x_3458_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_snd_3456_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
else
{
lean_object* v_snd_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v_fst_3474_; lean_object* v_snd_3475_; lean_object* v___x_3476_; lean_object* v_fst_3477_; lean_object* v_snd_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3486_; 
v_snd_3469_ = lean_ctor_get(v___x_3446_, 1);
lean_inc(v_snd_3469_);
lean_dec_ref(v___x_3446_);
v___x_3470_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3434_, v_i_3443_);
v___x_3471_ = l_Lean_PersistentArray_toList___redArg(v_children_3444_);
v___x_3472_ = lean_box(0);
lean_inc_ref(v_postNode_3433_);
v___x_3473_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3432_, v_postNode_3433_, v___x_3470_, v___x_3471_, v___x_3472_, v_snd_3469_);
v_fst_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_fst_3474_);
v_snd_3475_ = lean_ctor_get(v___x_3473_, 1);
lean_inc(v_snd_3475_);
lean_dec_ref(v___x_3473_);
v___x_3476_ = lean_apply_5(v_postNode_3433_, v_val_3445_, v_i_3443_, v_children_3444_, v_fst_3474_, v_snd_3475_);
v_fst_3477_ = lean_ctor_get(v___x_3476_, 0);
v_snd_3478_ = lean_ctor_get(v___x_3476_, 1);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3480_ = v___x_3476_;
v_isShared_3481_ = v_isSharedCheck_3486_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_snd_3478_);
lean_inc(v_fst_3477_);
lean_dec(v___x_3476_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3486_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; lean_object* v___x_3484_; 
v___x_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3482_, 0, v_fst_3477_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3482_);
v___x_3484_ = v___x_3480_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_snd_3478_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
default: 
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref_known(v_x_3435_, 1);
lean_dec(v_x_3434_);
lean_dec_ref(v_postNode_3433_);
lean_dec_ref(v_preNode_3432_);
v___x_3487_ = lean_box(0);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___y_3436_);
return v___x_3488_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3489_, lean_object* v_postNode_3490_, lean_object* v___x_3491_, lean_object* v_x_3492_, lean_object* v_x_3493_, lean_object* v___y_3494_){
_start:
{
if (lean_obj_tag(v_x_3492_) == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
lean_dec(v___x_3491_);
lean_dec_ref(v_postNode_3490_);
lean_dec_ref(v_preNode_3489_);
v___x_3495_ = l_List_reverse___redArg(v_x_3493_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v___y_3494_);
return v___x_3496_;
}
else
{
lean_object* v_head_3497_; lean_object* v_tail_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3509_; 
v_head_3497_ = lean_ctor_get(v_x_3492_, 0);
v_tail_3498_ = lean_ctor_get(v_x_3492_, 1);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_x_3492_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3500_ = v_x_3492_;
v_isShared_3501_ = v_isSharedCheck_3509_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_tail_3498_);
lean_inc(v_head_3497_);
lean_dec(v_x_3492_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3509_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v_fst_3503_; lean_object* v_snd_3504_; lean_object* v___x_3506_; 
lean_inc(v___x_3491_);
lean_inc_ref(v_postNode_3490_);
lean_inc_ref(v_preNode_3489_);
v___x_3502_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3489_, v_postNode_3490_, v___x_3491_, v_head_3497_, v___y_3494_);
v_fst_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_fst_3503_);
v_snd_3504_ = lean_ctor_get(v___x_3502_, 1);
lean_inc(v_snd_3504_);
lean_dec_ref(v___x_3502_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v_x_3493_);
lean_ctor_set(v___x_3500_, 0, v_fst_3503_);
v___x_3506_ = v___x_3500_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_fst_3503_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_x_3493_);
v___x_3506_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
v_x_3492_ = v_tail_3498_;
v_x_3493_ = v___x_3506_;
v___y_3494_ = v_snd_3504_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3510_, lean_object* v_ci_3511_, lean_object* v_i_3512_, lean_object* v_cs_3513_, lean_object* v_x_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_apply_4(v_postNode_3510_, v_ci_3511_, v_i_3512_, v_cs_3513_, v___y_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3517_, lean_object* v_ci_3518_, lean_object* v_i_3519_, lean_object* v_cs_3520_, lean_object* v_x_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3517_, v_ci_3518_, v_i_3519_, v_cs_3520_, v_x_3521_, v___y_3522_);
lean_dec(v_x_3521_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3524_, lean_object* v_postNode_3525_, lean_object* v_ctx_x3f_3526_, lean_object* v_t_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___f_3529_; lean_object* v___x_3530_; lean_object* v_snd_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3539_; 
v___f_3529_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3529_, 0, v_postNode_3525_);
v___x_3530_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3524_, v___f_3529_, v_ctx_x3f_3526_, v_t_3527_, v___y_3528_);
v_snd_3531_ = lean_ctor_get(v___x_3530_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v___x_3530_, 0);
lean_dec(v_unused_3540_);
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3539_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_snd_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3539_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3535_ = lean_box(0);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3535_);
v___x_3537_ = v___x_3533_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_snd_3531_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(lean_object* v_as_3543_, size_t v_i_3544_, size_t v_stop_3545_, lean_object* v_b_3546_, lean_object* v___y_3547_){
_start:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_usize_dec_eq(v_i_3544_, v_stop_3545_);
if (v___x_3548_ == 0)
{
lean_object* v___f_3549_; lean_object* v___f_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v_fst_3554_; lean_object* v_snd_3555_; size_t v___x_3556_; size_t v___x_3557_; 
v___f_3549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0));
v___f_3550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1));
v___x_3551_ = lean_array_uget_borrowed(v_as_3543_, v_i_3544_);
v___x_3552_ = lean_box(0);
lean_inc(v___x_3551_);
v___x_3553_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(v___f_3549_, v___f_3550_, v___x_3552_, v___x_3551_, v___y_3547_);
v_fst_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_fst_3554_);
v_snd_3555_ = lean_ctor_get(v___x_3553_, 1);
lean_inc(v_snd_3555_);
lean_dec_ref(v___x_3553_);
v___x_3556_ = ((size_t)1ULL);
v___x_3557_ = lean_usize_add(v_i_3544_, v___x_3556_);
v_i_3544_ = v___x_3557_;
v_b_3546_ = v_fst_3554_;
v___y_3547_ = v_snd_3555_;
goto _start;
}
else
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3559_, 0, v_b_3546_);
lean_ctor_set(v___x_3559_, 1, v___y_3547_);
return v___x_3559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___boxed(lean_object* v_as_3560_, lean_object* v_i_3561_, lean_object* v_stop_3562_, lean_object* v_b_3563_, lean_object* v___y_3564_){
_start:
{
size_t v_i_boxed_3565_; size_t v_stop_boxed_3566_; lean_object* v_res_3567_; 
v_i_boxed_3565_ = lean_unbox_usize(v_i_3561_);
lean_dec(v_i_3561_);
v_stop_boxed_3566_ = lean_unbox_usize(v_stop_3562_);
lean_dec(v_stop_3562_);
v_res_3567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_as_3560_, v_i_boxed_3565_, v_stop_boxed_3566_, v_b_3563_, v___y_3564_);
lean_dec_ref(v_as_3560_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(lean_object* v_a_3568_, lean_object* v_x_3569_){
_start:
{
if (lean_obj_tag(v_x_3569_) == 0)
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_box(0);
return v___x_3570_;
}
else
{
lean_object* v_key_3571_; lean_object* v_value_3572_; lean_object* v_tail_3573_; uint8_t v___x_3574_; 
v_key_3571_ = lean_ctor_get(v_x_3569_, 0);
v_value_3572_ = lean_ctor_get(v_x_3569_, 1);
v_tail_3573_ = lean_ctor_get(v_x_3569_, 2);
v___x_3574_ = l_Lean_Lsp_instBEqRange_beq(v_key_3571_, v_a_3568_);
if (v___x_3574_ == 0)
{
v_x_3569_ = v_tail_3573_;
goto _start;
}
else
{
lean_object* v___x_3576_; 
lean_inc(v_value_3572_);
v___x_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3576_, 0, v_value_3572_);
return v___x_3576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_3577_, lean_object* v_x_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3577_, v_x_3578_);
lean_dec(v_x_3578_);
lean_dec_ref(v_a_3577_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(lean_object* v_m_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_buckets_3582_; lean_object* v___x_3583_; uint64_t v___x_3584_; uint64_t v___x_3585_; uint64_t v___x_3586_; uint64_t v_fold_3587_; uint64_t v___x_3588_; uint64_t v___x_3589_; uint64_t v___x_3590_; size_t v___x_3591_; size_t v___x_3592_; size_t v___x_3593_; size_t v___x_3594_; size_t v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v_buckets_3582_ = lean_ctor_get(v_m_3580_, 1);
v___x_3583_ = lean_array_get_size(v_buckets_3582_);
v___x_3584_ = l_Lean_Lsp_instHashableRange_hash(v_a_3581_);
v___x_3585_ = 32ULL;
v___x_3586_ = lean_uint64_shift_right(v___x_3584_, v___x_3585_);
v_fold_3587_ = lean_uint64_xor(v___x_3584_, v___x_3586_);
v___x_3588_ = 16ULL;
v___x_3589_ = lean_uint64_shift_right(v_fold_3587_, v___x_3588_);
v___x_3590_ = lean_uint64_xor(v_fold_3587_, v___x_3589_);
v___x_3591_ = lean_uint64_to_usize(v___x_3590_);
v___x_3592_ = lean_usize_of_nat(v___x_3583_);
v___x_3593_ = ((size_t)1ULL);
v___x_3594_ = lean_usize_sub(v___x_3592_, v___x_3593_);
v___x_3595_ = lean_usize_land(v___x_3591_, v___x_3594_);
v___x_3596_ = lean_array_uget_borrowed(v_buckets_3582_, v___x_3595_);
v___x_3597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3581_, v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg___boxed(lean_object* v_m_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3598_, v_a_3599_);
lean_dec_ref(v_a_3599_);
lean_dec_ref(v_m_3598_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(lean_object* v_posMap_3601_, lean_object* v_as_3602_, size_t v_sz_3603_, size_t v_i_3604_, lean_object* v_b_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_a_3608_; lean_object* v_snd_3609_; uint8_t v___x_3613_; 
v___x_3613_ = lean_usize_dec_lt(v_i_3604_, v_sz_3603_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v_b_3605_);
lean_ctor_set(v___x_3614_, 1, v___y_3606_);
return v___x_3614_;
}
else
{
lean_object* v_a_3615_; lean_object* v_ident_3616_; lean_object* v_range_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v_a_3615_ = lean_array_uget_borrowed(v_as_3602_, v_i_3604_);
v_ident_3616_ = lean_ctor_get(v_a_3615_, 0);
v_range_3617_ = lean_ctor_get(v_a_3615_, 2);
v___x_3618_ = lean_box(0);
v___x_3619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_posMap_3601_, v_range_3617_);
if (lean_obj_tag(v___x_3619_) == 1)
{
lean_object* v_val_3620_; lean_object* v___x_3621_; lean_object* v_snd_3622_; 
v_val_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_val_3620_);
lean_dec_ref_known(v___x_3619_, 1);
lean_inc_ref(v_ident_3616_);
v___x_3621_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v_val_3620_, v_ident_3616_, v___y_3606_);
v_snd_3622_ = lean_ctor_get(v___x_3621_, 1);
lean_inc(v_snd_3622_);
lean_dec_ref(v___x_3621_);
v_a_3608_ = v___x_3618_;
v_snd_3609_ = v_snd_3622_;
goto v___jp_3607_;
}
else
{
lean_dec(v___x_3619_);
v_a_3608_ = v___x_3618_;
v_snd_3609_ = v___y_3606_;
goto v___jp_3607_;
}
}
v___jp_3607_:
{
size_t v___x_3610_; size_t v___x_3611_; 
v___x_3610_ = ((size_t)1ULL);
v___x_3611_ = lean_usize_add(v_i_3604_, v___x_3610_);
v_i_3604_ = v___x_3611_;
v_b_3605_ = v_a_3608_;
v___y_3606_ = v_snd_3609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2___boxed(lean_object* v_posMap_3623_, lean_object* v_as_3624_, lean_object* v_sz_3625_, lean_object* v_i_3626_, lean_object* v_b_3627_, lean_object* v___y_3628_){
_start:
{
size_t v_sz_boxed_3629_; size_t v_i_boxed_3630_; lean_object* v_res_3631_; 
v_sz_boxed_3629_ = lean_unbox_usize(v_sz_3625_);
lean_dec(v_sz_3625_);
v_i_boxed_3630_ = lean_unbox_usize(v_i_3626_);
lean_dec(v_i_3626_);
v_res_3631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3623_, v_as_3624_, v_sz_boxed_3629_, v_i_boxed_3630_, v_b_3627_, v___y_3628_);
lean_dec_ref(v_as_3624_);
lean_dec_ref(v_posMap_3623_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(lean_object* v_trees_3632_, lean_object* v_refs_3633_, lean_object* v_posMap_3634_){
_start:
{
lean_object* v___x_3635_; size_t v_sz_3636_; size_t v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v_snd_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; 
v___x_3635_ = lean_box(0);
v_sz_3636_ = lean_array_size(v_refs_3633_);
v___x_3637_ = ((size_t)0ULL);
v___x_3638_ = lean_unsigned_to_nat(0u);
v___x_3639_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3634_, v_refs_3633_, v_sz_3636_, v___x_3637_, v___x_3635_, v___x_3639_);
v_snd_3641_ = lean_ctor_get(v___x_3640_, 1);
lean_inc(v_snd_3641_);
lean_dec_ref(v___x_3640_);
v___x_3642_ = lean_array_get_size(v_trees_3632_);
v___x_3643_ = lean_nat_dec_lt(v___x_3638_, v___x_3642_);
if (v___x_3643_ == 0)
{
return v_snd_3641_;
}
else
{
size_t v___x_3644_; lean_object* v___x_3645_; lean_object* v_snd_3646_; 
v___x_3644_ = lean_usize_of_nat(v___x_3642_);
v___x_3645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3632_, v___x_3637_, v___x_3644_, v___x_3635_, v_snd_3641_);
v_snd_3646_ = lean_ctor_get(v___x_3645_, 1);
lean_inc(v_snd_3646_);
lean_dec_ref(v___x_3645_);
return v_snd_3646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap___boxed(lean_object* v_trees_3647_, lean_object* v_refs_3648_, lean_object* v_posMap_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3647_, v_refs_3648_, v_posMap_3649_);
lean_dec_ref(v_posMap_3649_);
lean_dec_ref(v_refs_3648_);
lean_dec_ref(v_trees_3647_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(lean_object* v_00_u03b2_3651_, lean_object* v_m_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3652_, v_a_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___boxed(lean_object* v_00_u03b2_3655_, lean_object* v_m_3656_, lean_object* v_a_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(v_00_u03b2_3655_, v_m_3656_, v_a_3657_);
lean_dec_ref(v_a_3657_);
lean_dec_ref(v_m_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3659_, lean_object* v_msg_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v_msg_3660_, v___y_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object* v_00_u03b1_3663_, lean_object* v_preNode_3664_, lean_object* v_postNode_3665_, lean_object* v_x_3666_, lean_object* v_x_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3664_, v_postNode_3665_, v_x_3666_, v_x_3667_, v___y_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object* v_00_u03b2_3670_, lean_object* v_a_3671_, lean_object* v_x_3672_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3671_, v_x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3674_, lean_object* v_a_3675_, lean_object* v_x_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(v_00_u03b2_3674_, v_a_3675_, v_x_3676_);
lean_dec(v_x_3676_);
lean_dec_ref(v_a_3675_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3678_, lean_object* v_preNode_3679_, lean_object* v_postNode_3680_, lean_object* v___x_3681_, lean_object* v_x_3682_, lean_object* v_x_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3679_, v_postNode_3680_, v___x_3681_, v_x_3682_, v_x_3683_, v___y_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(lean_object* v_a_3686_, lean_object* v_b_3687_, lean_object* v_x_3688_){
_start:
{
if (lean_obj_tag(v_x_3688_) == 0)
{
lean_dec(v_b_3687_);
lean_dec_ref(v_a_3686_);
return v_x_3688_;
}
else
{
lean_object* v_key_3689_; lean_object* v_value_3690_; lean_object* v_tail_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3703_; 
v_key_3689_ = lean_ctor_get(v_x_3688_, 0);
v_value_3690_ = lean_ctor_get(v_x_3688_, 1);
v_tail_3691_ = lean_ctor_get(v_x_3688_, 2);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_x_3688_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3693_ = v_x_3688_;
v_isShared_3694_ = v_isSharedCheck_3703_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_tail_3691_);
lean_inc(v_value_3690_);
lean_inc(v_key_3689_);
lean_dec(v_x_3688_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3703_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
uint8_t v___x_3695_; 
v___x_3695_ = l_Lean_Lsp_instBEqRange_beq(v_key_3689_, v_a_3686_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3696_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3686_, v_b_3687_, v_tail_3691_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 2, v___x_3696_);
v___x_3698_ = v___x_3693_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_key_3689_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_value_3690_);
lean_ctor_set(v_reuseFailAlloc_3699_, 2, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
else
{
lean_object* v___x_3701_; 
lean_dec(v_value_3690_);
lean_dec(v_key_3689_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 1, v_b_3687_);
lean_ctor_set(v___x_3693_, 0, v_a_3686_);
v___x_3701_ = v___x_3693_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3686_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_b_3687_);
lean_ctor_set(v_reuseFailAlloc_3702_, 2, v_tail_3691_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_3704_, lean_object* v_x_3705_){
_start:
{
if (lean_obj_tag(v_x_3705_) == 0)
{
return v_x_3704_;
}
else
{
lean_object* v_key_3706_; lean_object* v_value_3707_; lean_object* v_tail_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3731_; 
v_key_3706_ = lean_ctor_get(v_x_3705_, 0);
v_value_3707_ = lean_ctor_get(v_x_3705_, 1);
v_tail_3708_ = lean_ctor_get(v_x_3705_, 2);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_x_3705_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3710_ = v_x_3705_;
v_isShared_3711_ = v_isSharedCheck_3731_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_tail_3708_);
lean_inc(v_value_3707_);
lean_inc(v_key_3706_);
lean_dec(v_x_3705_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3731_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3712_; uint64_t v___x_3713_; uint64_t v___x_3714_; uint64_t v___x_3715_; uint64_t v_fold_3716_; uint64_t v___x_3717_; uint64_t v___x_3718_; uint64_t v___x_3719_; size_t v___x_3720_; size_t v___x_3721_; size_t v___x_3722_; size_t v___x_3723_; size_t v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3712_ = lean_array_get_size(v_x_3704_);
v___x_3713_ = l_Lean_Lsp_instHashableRange_hash(v_key_3706_);
v___x_3714_ = 32ULL;
v___x_3715_ = lean_uint64_shift_right(v___x_3713_, v___x_3714_);
v_fold_3716_ = lean_uint64_xor(v___x_3713_, v___x_3715_);
v___x_3717_ = 16ULL;
v___x_3718_ = lean_uint64_shift_right(v_fold_3716_, v___x_3717_);
v___x_3719_ = lean_uint64_xor(v_fold_3716_, v___x_3718_);
v___x_3720_ = lean_uint64_to_usize(v___x_3719_);
v___x_3721_ = lean_usize_of_nat(v___x_3712_);
v___x_3722_ = ((size_t)1ULL);
v___x_3723_ = lean_usize_sub(v___x_3721_, v___x_3722_);
v___x_3724_ = lean_usize_land(v___x_3720_, v___x_3723_);
v___x_3725_ = lean_array_uget_borrowed(v_x_3704_, v___x_3724_);
lean_inc(v___x_3725_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 2, v___x_3725_);
v___x_3727_ = v___x_3710_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_key_3706_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_value_3707_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_array_uset(v_x_3704_, v___x_3724_, v___x_3727_);
v_x_3704_ = v___x_3728_;
v_x_3705_ = v_tail_3708_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3732_, lean_object* v_source_3733_, lean_object* v_target_3734_){
_start:
{
lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3735_ = lean_array_get_size(v_source_3733_);
v___x_3736_ = lean_nat_dec_lt(v_i_3732_, v___x_3735_);
if (v___x_3736_ == 0)
{
lean_dec_ref(v_source_3733_);
lean_dec(v_i_3732_);
return v_target_3734_;
}
else
{
lean_object* v_es_3737_; lean_object* v___x_3738_; lean_object* v_source_3739_; lean_object* v_target_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_es_3737_ = lean_array_fget(v_source_3733_, v_i_3732_);
v___x_3738_ = lean_box(0);
v_source_3739_ = lean_array_fset(v_source_3733_, v_i_3732_, v___x_3738_);
v_target_3740_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3734_, v_es_3737_);
v___x_3741_ = lean_unsigned_to_nat(1u);
v___x_3742_ = lean_nat_add(v_i_3732_, v___x_3741_);
lean_dec(v_i_3732_);
v_i_3732_ = v___x_3742_;
v_source_3733_ = v_source_3739_;
v_target_3734_ = v_target_3740_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(lean_object* v_data_3744_){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v_nbuckets_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3745_ = lean_array_get_size(v_data_3744_);
v___x_3746_ = lean_unsigned_to_nat(2u);
v_nbuckets_3747_ = lean_nat_mul(v___x_3745_, v___x_3746_);
v___x_3748_ = lean_unsigned_to_nat(0u);
v___x_3749_ = lean_box(0);
v___x_3750_ = lean_mk_array(v_nbuckets_3747_, v___x_3749_);
v___x_3751_ = lean_array_propagate_mark(v_data_3744_, v___x_3750_);
v___x_3752_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v___x_3748_, v_data_3744_, v___x_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object* v_a_3753_, lean_object* v_x_3754_){
_start:
{
if (lean_obj_tag(v_x_3754_) == 0)
{
uint8_t v___x_3755_; 
v___x_3755_ = 0;
return v___x_3755_;
}
else
{
lean_object* v_key_3756_; lean_object* v_tail_3757_; uint8_t v___x_3758_; 
v_key_3756_ = lean_ctor_get(v_x_3754_, 0);
v_tail_3757_ = lean_ctor_get(v_x_3754_, 2);
v___x_3758_ = l_Lean_Lsp_instBEqRange_beq(v_key_3756_, v_a_3753_);
if (v___x_3758_ == 0)
{
v_x_3754_ = v_tail_3757_;
goto _start;
}
else
{
return v___x_3758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object* v_a_3760_, lean_object* v_x_3761_){
_start:
{
uint8_t v_res_3762_; lean_object* v_r_3763_; 
v_res_3762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3760_, v_x_3761_);
lean_dec(v_x_3761_);
lean_dec_ref(v_a_3760_);
v_r_3763_ = lean_box(v_res_3762_);
return v_r_3763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object* v_m_3764_, lean_object* v_a_3765_, lean_object* v_b_3766_){
_start:
{
lean_object* v_size_3767_; lean_object* v_buckets_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3811_; 
v_size_3767_ = lean_ctor_get(v_m_3764_, 0);
v_buckets_3768_ = lean_ctor_get(v_m_3764_, 1);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_m_3764_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3770_ = v_m_3764_;
v_isShared_3771_ = v_isSharedCheck_3811_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_buckets_3768_);
lean_inc(v_size_3767_);
lean_dec(v_m_3764_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3811_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3772_; uint64_t v___x_3773_; uint64_t v___x_3774_; uint64_t v___x_3775_; uint64_t v_fold_3776_; uint64_t v___x_3777_; uint64_t v___x_3778_; uint64_t v___x_3779_; size_t v___x_3780_; size_t v___x_3781_; size_t v___x_3782_; size_t v___x_3783_; size_t v___x_3784_; lean_object* v_bkt_3785_; uint8_t v___x_3786_; 
v___x_3772_ = lean_array_get_size(v_buckets_3768_);
v___x_3773_ = l_Lean_Lsp_instHashableRange_hash(v_a_3765_);
v___x_3774_ = 32ULL;
v___x_3775_ = lean_uint64_shift_right(v___x_3773_, v___x_3774_);
v_fold_3776_ = lean_uint64_xor(v___x_3773_, v___x_3775_);
v___x_3777_ = 16ULL;
v___x_3778_ = lean_uint64_shift_right(v_fold_3776_, v___x_3777_);
v___x_3779_ = lean_uint64_xor(v_fold_3776_, v___x_3778_);
v___x_3780_ = lean_uint64_to_usize(v___x_3779_);
v___x_3781_ = lean_usize_of_nat(v___x_3772_);
v___x_3782_ = ((size_t)1ULL);
v___x_3783_ = lean_usize_sub(v___x_3781_, v___x_3782_);
v___x_3784_ = lean_usize_land(v___x_3780_, v___x_3783_);
v_bkt_3785_ = lean_array_uget_borrowed(v_buckets_3768_, v___x_3784_);
v___x_3786_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3765_, v_bkt_3785_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; lean_object* v_size_x27_3788_; lean_object* v___x_3789_; lean_object* v_buckets_x27_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; 
v___x_3787_ = lean_unsigned_to_nat(1u);
v_size_x27_3788_ = lean_nat_add(v_size_3767_, v___x_3787_);
lean_dec(v_size_3767_);
lean_inc(v_bkt_3785_);
v___x_3789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3789_, 0, v_a_3765_);
lean_ctor_set(v___x_3789_, 1, v_b_3766_);
lean_ctor_set(v___x_3789_, 2, v_bkt_3785_);
v_buckets_x27_3790_ = lean_array_uset(v_buckets_3768_, v___x_3784_, v___x_3789_);
v___x_3791_ = lean_unsigned_to_nat(4u);
v___x_3792_ = lean_nat_mul(v_size_x27_3788_, v___x_3791_);
v___x_3793_ = lean_unsigned_to_nat(3u);
v___x_3794_ = lean_nat_div(v___x_3792_, v___x_3793_);
lean_dec(v___x_3792_);
v___x_3795_ = lean_array_get_size(v_buckets_x27_3790_);
v___x_3796_ = lean_nat_dec_le(v___x_3794_, v___x_3795_);
lean_dec(v___x_3794_);
if (v___x_3796_ == 0)
{
lean_object* v_val_3797_; lean_object* v___x_3799_; 
v_val_3797_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_buckets_x27_3790_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 1, v_val_3797_);
lean_ctor_set(v___x_3770_, 0, v_size_x27_3788_);
v___x_3799_ = v___x_3770_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_size_x27_3788_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_val_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
else
{
lean_object* v___x_3802_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 1, v_buckets_x27_3790_);
lean_ctor_set(v___x_3770_, 0, v_size_x27_3788_);
v___x_3802_ = v___x_3770_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_size_x27_3788_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_buckets_x27_3790_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
else
{
lean_object* v___x_3804_; lean_object* v_buckets_x27_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
lean_inc(v_bkt_3785_);
v___x_3804_ = lean_box(0);
v_buckets_x27_3805_ = lean_array_uset(v_buckets_3768_, v___x_3784_, v___x_3804_);
v___x_3806_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3765_, v_b_3766_, v_bkt_3785_);
v___x_3807_ = lean_array_uset(v_buckets_x27_3805_, v___x_3784_, v___x_3806_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 1, v___x_3807_);
v___x_3809_ = v___x_3770_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_size_3767_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object* v_as_3812_, size_t v_sz_3813_, size_t v_i_3814_, lean_object* v_b_3815_){
_start:
{
lean_object* v_a_3817_; uint8_t v___x_3821_; 
v___x_3821_ = lean_usize_dec_lt(v_i_3814_, v_sz_3813_);
if (v___x_3821_ == 0)
{
return v_b_3815_;
}
else
{
lean_object* v_a_3822_; uint8_t v_isBinder_3823_; 
v_a_3822_ = lean_array_uget_borrowed(v_as_3812_, v_i_3814_);
v_isBinder_3823_ = lean_ctor_get_uint8(v_a_3822_, sizeof(void*)*6);
if (v_isBinder_3823_ == 1)
{
lean_object* v_ident_3824_; lean_object* v_range_3825_; lean_object* v___x_3826_; 
v_ident_3824_ = lean_ctor_get(v_a_3822_, 0);
v_range_3825_ = lean_ctor_get(v_a_3822_, 2);
lean_inc_ref(v_ident_3824_);
lean_inc_ref(v_range_3825_);
v___x_3826_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_b_3815_, v_range_3825_, v_ident_3824_);
v_a_3817_ = v___x_3826_;
goto v___jp_3816_;
}
else
{
v_a_3817_ = v_b_3815_;
goto v___jp_3816_;
}
}
v___jp_3816_:
{
size_t v___x_3818_; size_t v___x_3819_; 
v___x_3818_ = ((size_t)1ULL);
v___x_3819_ = lean_usize_add(v_i_3814_, v___x_3818_);
v_i_3814_ = v___x_3819_;
v_b_3815_ = v_a_3817_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object* v_as_3827_, lean_object* v_sz_3828_, lean_object* v_i_3829_, lean_object* v_b_3830_){
_start:
{
size_t v_sz_boxed_3831_; size_t v_i_boxed_3832_; lean_object* v_res_3833_; 
v_sz_boxed_3831_ = lean_unbox_usize(v_sz_3828_);
lean_dec(v_sz_3828_);
v_i_boxed_3832_ = lean_unbox_usize(v_i_3829_);
lean_dec(v_i_3829_);
v_res_3833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_as_3827_, v_sz_boxed_3831_, v_i_boxed_3832_, v_b_3830_);
lean_dec_ref(v_as_3827_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object* v___x_3834_, lean_object* v_as_3835_, size_t v_sz_3836_, size_t v_i_3837_, lean_object* v_b_3838_){
_start:
{
lean_object* v_a_3840_; uint8_t v___x_3844_; 
v___x_3844_ = lean_usize_dec_lt(v_i_3837_, v_sz_3836_);
if (v___x_3844_ == 0)
{
return v_b_3838_;
}
else
{
lean_object* v_a_3845_; lean_object* v_ident_3846_; lean_object* v_range_3847_; lean_object* v_stx_3848_; lean_object* v_ci_3849_; lean_object* v_info_3850_; uint8_t v_isBinder_3851_; uint8_t v___x_3852_; 
v_a_3845_ = lean_array_uget(v_as_3835_, v_i_3837_);
v_ident_3846_ = lean_ctor_get(v_a_3845_, 0);
v_range_3847_ = lean_ctor_get(v_a_3845_, 2);
v_stx_3848_ = lean_ctor_get(v_a_3845_, 3);
v_ci_3849_ = lean_ctor_get(v_a_3845_, 4);
v_info_3850_ = lean_ctor_get(v_a_3845_, 5);
v_isBinder_3851_ = lean_ctor_get_uint8(v_a_3845_, sizeof(void*)*6);
v___x_3852_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v___x_3834_, v_ident_3846_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_array_push(v_b_3838_, v_a_3845_);
v_a_3840_ = v___x_3853_;
goto v___jp_3839_;
}
else
{
lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3865_; 
lean_inc_ref(v_info_3850_);
lean_inc_ref(v_ci_3849_);
lean_inc(v_stx_3848_);
lean_inc_ref(v_range_3847_);
lean_inc_ref(v_ident_3846_);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_a_3845_);
if (v_isSharedCheck_3865_ == 0)
{
lean_object* v_unused_3866_; lean_object* v_unused_3867_; lean_object* v_unused_3868_; lean_object* v_unused_3869_; lean_object* v_unused_3870_; lean_object* v_unused_3871_; 
v_unused_3866_ = lean_ctor_get(v_a_3845_, 5);
lean_dec(v_unused_3866_);
v_unused_3867_ = lean_ctor_get(v_a_3845_, 4);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v_a_3845_, 3);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v_a_3845_, 2);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v_a_3845_, 1);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_a_3845_, 0);
lean_dec(v_unused_3871_);
v___x_3855_ = v_a_3845_;
v_isShared_3856_ = v_isSharedCheck_3865_;
goto v_resetjp_3854_;
}
else
{
lean_dec(v_a_3845_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3865_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3862_; 
lean_inc_ref(v_ident_3846_);
v___x_3857_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v___x_3834_, v_ident_3846_);
v___x_3858_ = lean_unsigned_to_nat(1u);
v___x_3859_ = lean_mk_empty_array_with_capacity(v___x_3858_);
v___x_3860_ = lean_array_push(v___x_3859_, v_ident_3846_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 1, v___x_3860_);
lean_ctor_set(v___x_3855_, 0, v___x_3857_);
v___x_3862_ = v___x_3855_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_range_3847_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v_stx_3848_);
lean_ctor_set(v_reuseFailAlloc_3864_, 4, v_ci_3849_);
lean_ctor_set(v_reuseFailAlloc_3864_, 5, v_info_3850_);
lean_ctor_set_uint8(v_reuseFailAlloc_3864_, sizeof(void*)*6, v_isBinder_3851_);
v___x_3862_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_array_push(v_b_3838_, v___x_3862_);
v_a_3840_ = v___x_3863_;
goto v___jp_3839_;
}
}
}
}
v___jp_3839_:
{
size_t v___x_3841_; size_t v___x_3842_; 
v___x_3841_ = ((size_t)1ULL);
v___x_3842_ = lean_usize_add(v_i_3837_, v___x_3841_);
v_i_3837_ = v___x_3842_;
v_b_3838_ = v_a_3840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object* v___x_3872_, lean_object* v_as_3873_, lean_object* v_sz_3874_, lean_object* v_i_3875_, lean_object* v_b_3876_){
_start:
{
size_t v_sz_boxed_3877_; size_t v_i_boxed_3878_; lean_object* v_res_3879_; 
v_sz_boxed_3877_ = lean_unbox_usize(v_sz_3874_);
lean_dec(v_sz_3874_);
v_i_boxed_3878_ = lean_unbox_usize(v_i_3875_);
lean_dec(v_i_3875_);
v_res_3879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3872_, v_as_3873_, v_sz_boxed_3877_, v_i_boxed_3878_, v_b_3876_);
lean_dec_ref(v_as_3873_);
lean_dec_ref(v___x_3872_);
return v_res_3879_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__0(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_box(0);
v___x_3881_ = lean_unsigned_to_nat(16u);
v___x_3882_ = lean_mk_array(v___x_3881_, v___x_3880_);
return v___x_3882_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__1(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v_posMap_3885_; 
v___x_3883_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__0, &l_Lean_Server_combineIdents___closed__0_once, _init_l_Lean_Server_combineIdents___closed__0);
v___x_3884_ = lean_unsigned_to_nat(0u);
v_posMap_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_posMap_3885_, 0, v___x_3884_);
lean_ctor_set(v_posMap_3885_, 1, v___x_3883_);
return v_posMap_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object* v_trees_3886_, lean_object* v_refs_3887_){
_start:
{
lean_object* v_posMap_3888_; size_t v_sz_3889_; size_t v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_posMap_3888_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__1, &l_Lean_Server_combineIdents___closed__1_once, _init_l_Lean_Server_combineIdents___closed__1);
v_sz_3889_ = lean_array_size(v_refs_3887_);
v___x_3890_ = ((size_t)0ULL);
v___x_3891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_refs_3887_, v_sz_3889_, v___x_3890_, v_posMap_3888_);
v___x_3892_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3886_, v_refs_3887_, v___x_3891_);
lean_dec_ref(v___x_3891_);
v___x_3893_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v___x_3892_);
lean_dec_ref(v___x_3892_);
v___x_3894_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_3895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3893_, v_refs_3887_, v_sz_3889_, v___x_3890_, v___x_3894_);
lean_dec_ref(v___x_3893_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object* v_trees_3896_, lean_object* v_refs_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_Server_combineIdents(v_trees_3896_, v_refs_3897_);
lean_dec_ref(v_refs_3897_);
lean_dec_ref(v_trees_3896_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object* v_00_u03b2_3899_, lean_object* v_m_3900_, lean_object* v_a_3901_, lean_object* v_b_3902_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_m_3900_, v_a_3901_, v_b_3902_);
return v___x_3903_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object* v_00_u03b2_3904_, lean_object* v_a_3905_, lean_object* v_x_3906_){
_start:
{
uint8_t v___x_3907_; 
v___x_3907_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3905_, v_x_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3908_, lean_object* v_a_3909_, lean_object* v_x_3910_){
_start:
{
uint8_t v_res_3911_; lean_object* v_r_3912_; 
v_res_3911_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(v_00_u03b2_3908_, v_a_3909_, v_x_3910_);
lean_dec(v_x_3910_);
lean_dec_ref(v_a_3909_);
v_r_3912_ = lean_box(v_res_3911_);
return v_r_3912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object* v_00_u03b2_3913_, lean_object* v_data_3914_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_data_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object* v_00_u03b2_3916_, lean_object* v_a_3917_, lean_object* v_b_3918_, lean_object* v_x_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3917_, v_b_3918_, v_x_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3921_, lean_object* v_i_3922_, lean_object* v_source_3923_, lean_object* v_target_3924_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v_i_3922_, v_source_3923_, v_target_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3926_, lean_object* v_x_3927_, lean_object* v_x_3928_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3927_, v_x_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object* v_hi_3930_, lean_object* v_pivot_3931_, lean_object* v_as_3932_, lean_object* v_i_3933_, lean_object* v_k_3934_){
_start:
{
uint8_t v___x_3935_; 
v___x_3935_ = lean_nat_dec_lt(v_k_3934_, v_hi_3930_);
if (v___x_3935_ == 0)
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec(v_k_3934_);
v___x_3936_ = lean_array_fswap(v_as_3932_, v_i_3933_, v_hi_3930_);
v___x_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3937_, 0, v_i_3933_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
return v___x_3937_;
}
else
{
lean_object* v___x_3938_; lean_object* v_range_3939_; lean_object* v_range_3940_; uint8_t v___x_3941_; 
v___x_3938_ = lean_array_fget_borrowed(v_as_3932_, v_k_3934_);
v_range_3939_ = lean_ctor_get(v___x_3938_, 2);
v_range_3940_ = lean_ctor_get(v_pivot_3931_, 2);
v___x_3941_ = l_Lean_Lsp_instOrdRange_ord(v_range_3939_, v_range_3940_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3942_ = lean_array_fswap(v_as_3932_, v_i_3933_, v_k_3934_);
v___x_3943_ = lean_unsigned_to_nat(1u);
v___x_3944_ = lean_nat_add(v_i_3933_, v___x_3943_);
lean_dec(v_i_3933_);
v___x_3945_ = lean_nat_add(v_k_3934_, v___x_3943_);
lean_dec(v_k_3934_);
v_as_3932_ = v___x_3942_;
v_i_3933_ = v___x_3944_;
v_k_3934_ = v___x_3945_;
goto _start;
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = lean_nat_add(v_k_3934_, v___x_3947_);
lean_dec(v_k_3934_);
v_k_3934_ = v___x_3948_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object* v_hi_3950_, lean_object* v_pivot_3951_, lean_object* v_as_3952_, lean_object* v_i_3953_, lean_object* v_k_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3950_, v_pivot_3951_, v_as_3952_, v_i_3953_, v_k_3954_);
lean_dec_ref(v_pivot_3951_);
lean_dec(v_hi_3950_);
return v_res_3955_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3956_, lean_object* v_x1_3957_, lean_object* v_x2_3958_){
_start:
{
lean_object* v_range_3959_; lean_object* v_range_3960_; uint8_t v___x_3961_; 
v_range_3959_ = lean_ctor_get(v_x1_3957_, 2);
v_range_3960_ = lean_ctor_get(v_x2_3958_, 2);
v___x_3961_ = l_Lean_Lsp_instOrdRange_ord(v_range_3959_, v_range_3960_);
if (v___x_3961_ == 0)
{
return v___x_3956_;
}
else
{
uint8_t v___x_3962_; 
v___x_3962_ = 0;
return v___x_3962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3963_, lean_object* v_x1_3964_, lean_object* v_x2_3965_){
_start:
{
uint8_t v___x_2138__boxed_3966_; uint8_t v_res_3967_; lean_object* v_r_3968_; 
v___x_2138__boxed_3966_ = lean_unbox(v___x_3963_);
v_res_3967_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_2138__boxed_3966_, v_x1_3964_, v_x2_3965_);
lean_dec_ref(v_x2_3965_);
lean_dec_ref(v_x1_3964_);
v_r_3968_ = lean_box(v_res_3967_);
return v_r_3968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_n_3969_, lean_object* v_as_3970_, lean_object* v_lo_3971_, lean_object* v_hi_3972_){
_start:
{
lean_object* v___y_3974_; uint8_t v___x_3984_; 
v___x_3984_ = lean_nat_dec_lt(v_lo_3971_, v_hi_3972_);
if (v___x_3984_ == 0)
{
lean_dec(v_lo_3971_);
return v_as_3970_;
}
else
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v_mid_3987_; lean_object* v___y_3989_; lean_object* v___y_3995_; lean_object* v___x_4000_; lean_object* v___x_4001_; uint8_t v___x_4002_; 
v___x_3985_ = lean_nat_add(v_lo_3971_, v_hi_3972_);
v___x_3986_ = lean_unsigned_to_nat(1u);
v_mid_3987_ = lean_nat_shiftr(v___x_3985_, v___x_3986_);
lean_dec(v___x_3985_);
v___x_4000_ = lean_array_fget_borrowed(v_as_3970_, v_mid_3987_);
v___x_4001_ = lean_array_fget_borrowed(v_as_3970_, v_lo_3971_);
v___x_4002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3984_, v___x_4000_, v___x_4001_);
if (v___x_4002_ == 0)
{
v___y_3995_ = v_as_3970_;
goto v___jp_3994_;
}
else
{
lean_object* v___x_4003_; 
v___x_4003_ = lean_array_fswap(v_as_3970_, v_lo_3971_, v_mid_3987_);
v___y_3995_ = v___x_4003_;
goto v___jp_3994_;
}
v___jp_3988_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3990_ = lean_array_fget_borrowed(v___y_3989_, v_mid_3987_);
v___x_3991_ = lean_array_fget_borrowed(v___y_3989_, v_hi_3972_);
v___x_3992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3984_, v___x_3990_, v___x_3991_);
if (v___x_3992_ == 0)
{
lean_dec(v_mid_3987_);
v___y_3974_ = v___y_3989_;
goto v___jp_3973_;
}
else
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_array_fswap(v___y_3989_, v_mid_3987_, v_hi_3972_);
lean_dec(v_mid_3987_);
v___y_3974_ = v___x_3993_;
goto v___jp_3973_;
}
}
v___jp_3994_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; 
v___x_3996_ = lean_array_fget_borrowed(v___y_3995_, v_hi_3972_);
v___x_3997_ = lean_array_fget_borrowed(v___y_3995_, v_lo_3971_);
v___x_3998_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3984_, v___x_3996_, v___x_3997_);
if (v___x_3998_ == 0)
{
v___y_3989_ = v___y_3995_;
goto v___jp_3988_;
}
else
{
lean_object* v___x_3999_; 
v___x_3999_ = lean_array_fswap(v___y_3995_, v_lo_3971_, v_hi_3972_);
v___y_3989_ = v___x_3999_;
goto v___jp_3988_;
}
}
}
v___jp_3973_:
{
lean_object* v_pivot_3975_; lean_object* v___x_3976_; lean_object* v_fst_3977_; lean_object* v_snd_3978_; uint8_t v___x_3979_; 
v_pivot_3975_ = lean_array_fget(v___y_3974_, v_hi_3972_);
lean_inc_n(v_lo_3971_, 2);
v___x_3976_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3972_, v_pivot_3975_, v___y_3974_, v_lo_3971_, v_lo_3971_);
lean_dec(v_pivot_3975_);
v_fst_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_fst_3977_);
v_snd_3978_ = lean_ctor_get(v___x_3976_, 1);
lean_inc(v_snd_3978_);
lean_dec_ref(v___x_3976_);
v___x_3979_ = lean_nat_dec_le(v_hi_3972_, v_fst_3977_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3980_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3969_, v_snd_3978_, v_lo_3971_, v_fst_3977_);
v___x_3981_ = lean_unsigned_to_nat(1u);
v___x_3982_ = lean_nat_add(v_fst_3977_, v___x_3981_);
lean_dec(v_fst_3977_);
v_as_3970_ = v___x_3980_;
v_lo_3971_ = v___x_3982_;
goto _start;
}
else
{
lean_dec(v_fst_3977_);
lean_dec(v_lo_3971_);
return v_snd_3978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_n_4004_, lean_object* v_as_4005_, lean_object* v_lo_4006_, lean_object* v_hi_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4004_, v_as_4005_, v_lo_4006_, v_hi_4007_);
lean_dec(v_hi_4007_);
lean_dec(v_n_4004_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object* v_x_4009_, lean_object* v_x_4010_){
_start:
{
if (lean_obj_tag(v_x_4010_) == 0)
{
return v_x_4009_;
}
else
{
lean_object* v_key_4011_; lean_object* v_snd_4012_; lean_object* v_value_4013_; lean_object* v_tail_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4054_; 
v_key_4011_ = lean_ctor_get(v_x_4010_, 0);
lean_inc(v_key_4011_);
v_snd_4012_ = lean_ctor_get(v_key_4011_, 1);
v_value_4013_ = lean_ctor_get(v_x_4010_, 1);
v_tail_4014_ = lean_ctor_get(v_x_4010_, 2);
v_isSharedCheck_4054_ = !lean_is_exclusive(v_x_4010_);
if (v_isSharedCheck_4054_ == 0)
{
lean_object* v_unused_4055_; 
v_unused_4055_ = lean_ctor_get(v_x_4010_, 0);
lean_dec(v_unused_4055_);
v___x_4016_ = v_x_4010_;
v_isShared_4017_ = v_isSharedCheck_4054_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_tail_4014_);
lean_inc(v_value_4013_);
lean_dec(v_x_4010_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4054_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v_fst_4018_; lean_object* v_fst_4019_; lean_object* v_snd_4020_; lean_object* v___x_4021_; uint64_t v___x_4022_; uint64_t v___y_4024_; uint64_t v___y_4046_; 
v_fst_4018_ = lean_ctor_get(v_key_4011_, 0);
v_fst_4019_ = lean_ctor_get(v_snd_4012_, 0);
v_snd_4020_ = lean_ctor_get(v_snd_4012_, 1);
v___x_4021_ = lean_array_get_size(v_x_4009_);
v___x_4022_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4018_);
if (lean_obj_tag(v_fst_4019_) == 0)
{
uint64_t v___x_4049_; 
v___x_4049_ = 11ULL;
v___y_4024_ = v___x_4049_;
goto v___jp_4023_;
}
else
{
lean_object* v_val_4050_; uint8_t v___x_4051_; 
v_val_4050_ = lean_ctor_get(v_fst_4019_, 0);
v___x_4051_ = lean_unbox(v_val_4050_);
if (v___x_4051_ == 0)
{
uint64_t v___x_4052_; 
v___x_4052_ = 13ULL;
v___y_4046_ = v___x_4052_;
goto v___jp_4045_;
}
else
{
uint64_t v___x_4053_; 
v___x_4053_ = 11ULL;
v___y_4046_ = v___x_4053_;
goto v___jp_4045_;
}
}
v___jp_4023_:
{
uint64_t v___x_4025_; uint64_t v___x_4026_; uint64_t v___x_4027_; uint64_t v___x_4028_; uint64_t v___x_4029_; uint64_t v_fold_4030_; uint64_t v___x_4031_; uint64_t v___x_4032_; uint64_t v___x_4033_; size_t v___x_4034_; size_t v___x_4035_; size_t v___x_4036_; size_t v___x_4037_; size_t v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4041_; 
v___x_4025_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4020_);
v___x_4026_ = lean_uint64_mix_hash(v___y_4024_, v___x_4025_);
v___x_4027_ = lean_uint64_mix_hash(v___x_4022_, v___x_4026_);
v___x_4028_ = 32ULL;
v___x_4029_ = lean_uint64_shift_right(v___x_4027_, v___x_4028_);
v_fold_4030_ = lean_uint64_xor(v___x_4027_, v___x_4029_);
v___x_4031_ = 16ULL;
v___x_4032_ = lean_uint64_shift_right(v_fold_4030_, v___x_4031_);
v___x_4033_ = lean_uint64_xor(v_fold_4030_, v___x_4032_);
v___x_4034_ = lean_uint64_to_usize(v___x_4033_);
v___x_4035_ = lean_usize_of_nat(v___x_4021_);
v___x_4036_ = ((size_t)1ULL);
v___x_4037_ = lean_usize_sub(v___x_4035_, v___x_4036_);
v___x_4038_ = lean_usize_land(v___x_4034_, v___x_4037_);
v___x_4039_ = lean_array_uget_borrowed(v_x_4009_, v___x_4038_);
lean_inc(v___x_4039_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 2, v___x_4039_);
v___x_4041_ = v___x_4016_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_key_4011_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_value_4013_);
lean_ctor_set(v_reuseFailAlloc_4044_, 2, v___x_4039_);
v___x_4041_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4042_; 
v___x_4042_ = lean_array_uset(v_x_4009_, v___x_4038_, v___x_4041_);
v_x_4009_ = v___x_4042_;
v_x_4010_ = v_tail_4014_;
goto _start;
}
}
v___jp_4045_:
{
uint64_t v___x_4047_; uint64_t v___x_4048_; 
v___x_4047_ = 13ULL;
v___x_4048_ = lean_uint64_mix_hash(v___y_4046_, v___x_4047_);
v___y_4024_ = v___x_4048_;
goto v___jp_4023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object* v_i_4056_, lean_object* v_source_4057_, lean_object* v_target_4058_){
_start:
{
lean_object* v___x_4059_; uint8_t v___x_4060_; 
v___x_4059_ = lean_array_get_size(v_source_4057_);
v___x_4060_ = lean_nat_dec_lt(v_i_4056_, v___x_4059_);
if (v___x_4060_ == 0)
{
lean_dec_ref(v_source_4057_);
lean_dec(v_i_4056_);
return v_target_4058_;
}
else
{
lean_object* v_es_4061_; lean_object* v___x_4062_; lean_object* v_source_4063_; lean_object* v_target_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_es_4061_ = lean_array_fget(v_source_4057_, v_i_4056_);
v___x_4062_ = lean_box(0);
v_source_4063_ = lean_array_fset(v_source_4057_, v_i_4056_, v___x_4062_);
v_target_4064_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_target_4058_, v_es_4061_);
v___x_4065_ = lean_unsigned_to_nat(1u);
v___x_4066_ = lean_nat_add(v_i_4056_, v___x_4065_);
lean_dec(v_i_4056_);
v_i_4056_ = v___x_4066_;
v_source_4057_ = v_source_4063_;
v_target_4058_ = v_target_4064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object* v_data_4068_){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v_nbuckets_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4069_ = lean_array_get_size(v_data_4068_);
v___x_4070_ = lean_unsigned_to_nat(2u);
v_nbuckets_4071_ = lean_nat_mul(v___x_4069_, v___x_4070_);
v___x_4072_ = lean_unsigned_to_nat(0u);
v___x_4073_ = lean_box(0);
v___x_4074_ = lean_mk_array(v_nbuckets_4071_, v___x_4073_);
v___x_4075_ = lean_array_propagate_mark(v_data_4068_, v___x_4074_);
v___x_4076_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v___x_4072_, v_data_4068_, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object* v_x_4077_, lean_object* v_x_4078_){
_start:
{
if (lean_obj_tag(v_x_4077_) == 0)
{
if (lean_obj_tag(v_x_4078_) == 0)
{
uint8_t v___x_4079_; 
v___x_4079_ = 1;
return v___x_4079_;
}
else
{
uint8_t v___x_4080_; 
v___x_4080_ = 0;
return v___x_4080_;
}
}
else
{
if (lean_obj_tag(v_x_4078_) == 0)
{
uint8_t v___x_4081_; 
v___x_4081_ = 0;
return v___x_4081_;
}
else
{
lean_object* v_val_4082_; uint8_t v___x_4083_; 
v_val_4082_ = lean_ctor_get(v_x_4078_, 0);
v___x_4083_ = lean_unbox(v_val_4082_);
if (v___x_4083_ == 0)
{
lean_object* v_val_4084_; uint8_t v___x_4085_; 
v_val_4084_ = lean_ctor_get(v_x_4077_, 0);
v___x_4085_ = lean_unbox(v_val_4084_);
if (v___x_4085_ == 0)
{
uint8_t v___x_4086_; 
v___x_4086_ = 1;
return v___x_4086_;
}
else
{
uint8_t v___x_4087_; 
v___x_4087_ = lean_unbox(v_val_4082_);
return v___x_4087_;
}
}
else
{
lean_object* v_val_4088_; uint8_t v___x_4089_; 
v_val_4088_ = lean_ctor_get(v_x_4077_, 0);
v___x_4089_ = lean_unbox(v_val_4088_);
return v___x_4089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object* v_x_4090_, lean_object* v_x_4091_){
_start:
{
uint8_t v_res_4092_; lean_object* v_r_4093_; 
v_res_4092_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_x_4090_, v_x_4091_);
lean_dec(v_x_4091_);
lean_dec(v_x_4090_);
v_r_4093_ = lean_box(v_res_4092_);
return v_r_4093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object* v_a_4094_, lean_object* v_x_4095_){
_start:
{
if (lean_obj_tag(v_x_4095_) == 0)
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4096_, 0, v_a_4094_);
return v___x_4096_;
}
else
{
lean_object* v_val_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4125_; 
v_val_4097_ = lean_ctor_get(v_x_4095_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_x_4095_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4099_ = v_x_4095_;
v_isShared_4100_ = v_isSharedCheck_4125_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_val_4097_);
lean_dec(v_x_4095_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4125_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v_ident_4101_; lean_object* v_aliases_4102_; lean_object* v_range_4103_; lean_object* v_stx_4104_; lean_object* v_ci_4105_; lean_object* v_info_4106_; uint8_t v_isBinder_4107_; lean_object* v_aliases_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4119_; 
v_ident_4101_ = lean_ctor_get(v_val_4097_, 0);
lean_inc_ref(v_ident_4101_);
v_aliases_4102_ = lean_ctor_get(v_val_4097_, 1);
lean_inc_ref(v_aliases_4102_);
v_range_4103_ = lean_ctor_get(v_val_4097_, 2);
lean_inc_ref(v_range_4103_);
v_stx_4104_ = lean_ctor_get(v_val_4097_, 3);
lean_inc(v_stx_4104_);
v_ci_4105_ = lean_ctor_get(v_val_4097_, 4);
lean_inc_ref(v_ci_4105_);
v_info_4106_ = lean_ctor_get(v_val_4097_, 5);
lean_inc_ref(v_info_4106_);
v_isBinder_4107_ = lean_ctor_get_uint8(v_val_4097_, sizeof(void*)*6);
lean_dec(v_val_4097_);
v_aliases_4108_ = lean_ctor_get(v_a_4094_, 1);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_a_4094_);
if (v_isSharedCheck_4119_ == 0)
{
lean_object* v_unused_4120_; lean_object* v_unused_4121_; lean_object* v_unused_4122_; lean_object* v_unused_4123_; lean_object* v_unused_4124_; 
v_unused_4120_ = lean_ctor_get(v_a_4094_, 5);
lean_dec(v_unused_4120_);
v_unused_4121_ = lean_ctor_get(v_a_4094_, 4);
lean_dec(v_unused_4121_);
v_unused_4122_ = lean_ctor_get(v_a_4094_, 3);
lean_dec(v_unused_4122_);
v_unused_4123_ = lean_ctor_get(v_a_4094_, 2);
lean_dec(v_unused_4123_);
v_unused_4124_ = lean_ctor_get(v_a_4094_, 0);
lean_dec(v_unused_4124_);
v___x_4110_ = v_a_4094_;
v_isShared_4111_ = v_isSharedCheck_4119_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_aliases_4108_);
lean_dec(v_a_4094_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4119_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4112_ = l_Array_append___redArg(v_aliases_4102_, v_aliases_4108_);
lean_dec_ref(v_aliases_4108_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 5, v_info_4106_);
lean_ctor_set(v___x_4110_, 4, v_ci_4105_);
lean_ctor_set(v___x_4110_, 3, v_stx_4104_);
lean_ctor_set(v___x_4110_, 2, v_range_4103_);
lean_ctor_set(v___x_4110_, 1, v___x_4112_);
lean_ctor_set(v___x_4110_, 0, v_ident_4101_);
v___x_4114_ = v___x_4110_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_ident_4101_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4118_, 2, v_range_4103_);
lean_ctor_set(v_reuseFailAlloc_4118_, 3, v_stx_4104_);
lean_ctor_set(v_reuseFailAlloc_4118_, 4, v_ci_4105_);
lean_ctor_set(v_reuseFailAlloc_4118_, 5, v_info_4106_);
v___x_4114_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4116_; 
lean_ctor_set_uint8(v___x_4114_, sizeof(void*)*6, v_isBinder_4107_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___x_4114_);
v___x_4116_ = v___x_4099_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4114_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_x_4128_){
_start:
{
if (lean_obj_tag(v_x_4128_) == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v_val_4131_; lean_object* v___x_4132_; 
v___x_4129_ = lean_box(0);
v___x_4130_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4126_, v___x_4129_);
v_val_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_val_4131_);
lean_dec(v___x_4130_);
v___x_4132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4132_, 0, v_a_4127_);
lean_ctor_set(v___x_4132_, 1, v_val_4131_);
lean_ctor_set(v___x_4132_, 2, v_x_4128_);
return v___x_4132_;
}
else
{
lean_object* v_key_4133_; lean_object* v_value_4134_; lean_object* v_tail_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4159_; 
v_key_4133_ = lean_ctor_get(v_x_4128_, 0);
v_value_4134_ = lean_ctor_get(v_x_4128_, 1);
v_tail_4135_ = lean_ctor_get(v_x_4128_, 2);
v_isSharedCheck_4159_ = !lean_is_exclusive(v_x_4128_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4137_ = v_x_4128_;
v_isShared_4138_ = v_isSharedCheck_4159_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_tail_4135_);
lean_inc(v_value_4134_);
lean_inc(v_key_4133_);
lean_dec(v_x_4128_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4159_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v_fst_4144_; lean_object* v_snd_4145_; lean_object* v_fst_4146_; lean_object* v_snd_4147_; uint8_t v___x_4148_; 
v_fst_4144_ = lean_ctor_get(v_key_4133_, 0);
v_snd_4145_ = lean_ctor_get(v_key_4133_, 1);
v_fst_4146_ = lean_ctor_get(v_a_4127_, 0);
v_snd_4147_ = lean_ctor_get(v_a_4127_, 1);
v___x_4148_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4144_, v_fst_4146_);
if (v___x_4148_ == 0)
{
goto v___jp_4139_;
}
else
{
lean_object* v_fst_4149_; lean_object* v_snd_4150_; lean_object* v_fst_4151_; lean_object* v_snd_4152_; uint8_t v___x_4153_; 
v_fst_4149_ = lean_ctor_get(v_snd_4145_, 0);
v_snd_4150_ = lean_ctor_get(v_snd_4145_, 1);
v_fst_4151_ = lean_ctor_get(v_snd_4147_, 0);
v_snd_4152_ = lean_ctor_get(v_snd_4147_, 1);
v___x_4153_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4149_, v_fst_4151_);
if (v___x_4153_ == 0)
{
goto v___jp_4139_;
}
else
{
uint8_t v___x_4154_; 
v___x_4154_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4150_, v_snd_4152_);
if (v___x_4154_ == 0)
{
goto v___jp_4139_;
}
else
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v_val_4157_; lean_object* v___x_4158_; 
lean_del_object(v___x_4137_);
lean_dec(v_key_4133_);
v___x_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4155_, 0, v_value_4134_);
v___x_4156_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4126_, v___x_4155_);
v_val_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_val_4157_);
lean_dec(v___x_4156_);
v___x_4158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4158_, 0, v_a_4127_);
lean_ctor_set(v___x_4158_, 1, v_val_4157_);
lean_ctor_set(v___x_4158_, 2, v_tail_4135_);
return v___x_4158_;
}
}
}
v___jp_4139_:
{
lean_object* v_tail_4140_; lean_object* v___x_4142_; 
v_tail_4140_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4126_, v_a_4127_, v_tail_4135_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 2, v_tail_4140_);
v___x_4142_ = v___x_4137_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_key_4133_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v_value_4134_);
lean_ctor_set(v_reuseFailAlloc_4143_, 2, v_tail_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_a_4160_, lean_object* v_x_4161_){
_start:
{
if (lean_obj_tag(v_x_4161_) == 0)
{
uint8_t v___x_4162_; 
v___x_4162_ = 0;
return v___x_4162_;
}
else
{
lean_object* v_key_4163_; lean_object* v_tail_4164_; lean_object* v_fst_4165_; lean_object* v_snd_4166_; lean_object* v_fst_4167_; lean_object* v_snd_4168_; uint8_t v___x_4169_; 
v_key_4163_ = lean_ctor_get(v_x_4161_, 0);
v_tail_4164_ = lean_ctor_get(v_x_4161_, 2);
v_fst_4165_ = lean_ctor_get(v_key_4163_, 0);
v_snd_4166_ = lean_ctor_get(v_key_4163_, 1);
v_fst_4167_ = lean_ctor_get(v_a_4160_, 0);
v_snd_4168_ = lean_ctor_get(v_a_4160_, 1);
v___x_4169_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4165_, v_fst_4167_);
if (v___x_4169_ == 0)
{
v_x_4161_ = v_tail_4164_;
goto _start;
}
else
{
lean_object* v_fst_4171_; lean_object* v_snd_4172_; lean_object* v_fst_4173_; lean_object* v_snd_4174_; uint8_t v___x_4175_; 
v_fst_4171_ = lean_ctor_get(v_snd_4166_, 0);
v_snd_4172_ = lean_ctor_get(v_snd_4166_, 1);
v_fst_4173_ = lean_ctor_get(v_snd_4168_, 0);
v_snd_4174_ = lean_ctor_get(v_snd_4168_, 1);
v___x_4175_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4171_, v_fst_4173_);
if (v___x_4175_ == 0)
{
v_x_4161_ = v_tail_4164_;
goto _start;
}
else
{
uint8_t v___x_4177_; 
v___x_4177_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4172_, v_snd_4174_);
if (v___x_4177_ == 0)
{
v_x_4161_ = v_tail_4164_;
goto _start;
}
else
{
return v___x_4177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object* v_a_4179_, lean_object* v_x_4180_){
_start:
{
uint8_t v_res_4181_; lean_object* v_r_4182_; 
v_res_4181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4179_, v_x_4180_);
lean_dec(v_x_4180_);
lean_dec_ref(v_a_4179_);
v_r_4182_ = lean_box(v_res_4181_);
return v_r_4182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4183_, lean_object* v_m_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___y_4187_; lean_object* v___y_4188_; size_t v___y_4189_; lean_object* v___y_4190_; lean_object* v_snd_4193_; lean_object* v_size_4194_; lean_object* v_buckets_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4254_; 
v_snd_4193_ = lean_ctor_get(v_a_4185_, 1);
v_size_4194_ = lean_ctor_get(v_m_4184_, 0);
v_buckets_4195_ = lean_ctor_get(v_m_4184_, 1);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_m_4184_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4197_ = v_m_4184_;
v_isShared_4198_ = v_isSharedCheck_4254_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_buckets_4195_);
lean_inc(v_size_4194_);
lean_dec(v_m_4184_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4254_;
goto v_resetjp_4196_;
}
v___jp_4186_:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4191_ = lean_array_uset(v___y_4187_, v___y_4189_, v___y_4188_);
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___y_4190_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
return v___x_4192_;
}
v_resetjp_4196_:
{
lean_object* v_fst_4199_; lean_object* v_fst_4200_; lean_object* v_snd_4201_; lean_object* v___x_4202_; uint64_t v___x_4203_; uint64_t v___y_4205_; uint64_t v___y_4246_; 
v_fst_4199_ = lean_ctor_get(v_a_4185_, 0);
v_fst_4200_ = lean_ctor_get(v_snd_4193_, 0);
v_snd_4201_ = lean_ctor_get(v_snd_4193_, 1);
v___x_4202_ = lean_array_get_size(v_buckets_4195_);
v___x_4203_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4199_);
if (lean_obj_tag(v_fst_4200_) == 0)
{
uint64_t v___x_4249_; 
v___x_4249_ = 11ULL;
v___y_4205_ = v___x_4249_;
goto v___jp_4204_;
}
else
{
lean_object* v_val_4250_; uint8_t v___x_4251_; 
v_val_4250_ = lean_ctor_get(v_fst_4200_, 0);
v___x_4251_ = lean_unbox(v_val_4250_);
if (v___x_4251_ == 0)
{
uint64_t v___x_4252_; 
v___x_4252_ = 13ULL;
v___y_4246_ = v___x_4252_;
goto v___jp_4245_;
}
else
{
uint64_t v___x_4253_; 
v___x_4253_ = 11ULL;
v___y_4246_ = v___x_4253_;
goto v___jp_4245_;
}
}
v___jp_4204_:
{
uint64_t v___x_4206_; uint64_t v___x_4207_; uint64_t v___x_4208_; uint64_t v___x_4209_; uint64_t v___x_4210_; uint64_t v_fold_4211_; uint64_t v___x_4212_; uint64_t v___x_4213_; uint64_t v___x_4214_; size_t v___x_4215_; size_t v___x_4216_; size_t v___x_4217_; size_t v___x_4218_; size_t v___x_4219_; lean_object* v_bkt_4220_; uint8_t v___x_4221_; 
v___x_4206_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4201_);
v___x_4207_ = lean_uint64_mix_hash(v___y_4205_, v___x_4206_);
v___x_4208_ = lean_uint64_mix_hash(v___x_4203_, v___x_4207_);
v___x_4209_ = 32ULL;
v___x_4210_ = lean_uint64_shift_right(v___x_4208_, v___x_4209_);
v_fold_4211_ = lean_uint64_xor(v___x_4208_, v___x_4210_);
v___x_4212_ = 16ULL;
v___x_4213_ = lean_uint64_shift_right(v_fold_4211_, v___x_4212_);
v___x_4214_ = lean_uint64_xor(v_fold_4211_, v___x_4213_);
v___x_4215_ = lean_uint64_to_usize(v___x_4214_);
v___x_4216_ = lean_usize_of_nat(v___x_4202_);
v___x_4217_ = ((size_t)1ULL);
v___x_4218_ = lean_usize_sub(v___x_4216_, v___x_4217_);
v___x_4219_ = lean_usize_land(v___x_4215_, v___x_4218_);
v_bkt_4220_ = lean_array_uget_borrowed(v_buckets_4195_, v___x_4219_);
v___x_4221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4185_, v_bkt_4220_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; lean_object* v_size_x27_4223_; lean_object* v___x_4224_; lean_object* v_buckets_x27_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; uint8_t v___x_4231_; 
v___x_4222_ = lean_unsigned_to_nat(1u);
v_size_x27_4223_ = lean_nat_add(v_size_4194_, v___x_4222_);
lean_dec(v_size_4194_);
lean_inc(v_bkt_4220_);
v___x_4224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4224_, 0, v_a_4185_);
lean_ctor_set(v___x_4224_, 1, v_a_4183_);
lean_ctor_set(v___x_4224_, 2, v_bkt_4220_);
v_buckets_x27_4225_ = lean_array_uset(v_buckets_4195_, v___x_4219_, v___x_4224_);
v___x_4226_ = lean_unsigned_to_nat(4u);
v___x_4227_ = lean_nat_mul(v_size_x27_4223_, v___x_4226_);
v___x_4228_ = lean_unsigned_to_nat(3u);
v___x_4229_ = lean_nat_div(v___x_4227_, v___x_4228_);
lean_dec(v___x_4227_);
v___x_4230_ = lean_array_get_size(v_buckets_x27_4225_);
v___x_4231_ = lean_nat_dec_le(v___x_4229_, v___x_4230_);
lean_dec(v___x_4229_);
if (v___x_4231_ == 0)
{
lean_object* v_val_4232_; lean_object* v___x_4234_; 
v_val_4232_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_buckets_x27_4225_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 1, v_val_4232_);
lean_ctor_set(v___x_4197_, 0, v_size_x27_4223_);
v___x_4234_ = v___x_4197_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_size_x27_4223_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v_val_4232_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
else
{
lean_object* v___x_4237_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 1, v_buckets_x27_4225_);
lean_ctor_set(v___x_4197_, 0, v_size_x27_4223_);
v___x_4237_ = v___x_4197_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_size_x27_4223_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_buckets_x27_4225_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
else
{
lean_object* v___x_4239_; lean_object* v_buckets_x27_4240_; lean_object* v_bkt_x27_4241_; uint8_t v___x_4242_; 
lean_inc(v_bkt_4220_);
lean_del_object(v___x_4197_);
v___x_4239_ = lean_box(0);
v_buckets_x27_4240_ = lean_array_uset(v_buckets_4195_, v___x_4219_, v___x_4239_);
lean_inc_ref(v_a_4185_);
v_bkt_x27_4241_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4183_, v_a_4185_, v_bkt_4220_);
v___x_4242_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4185_, v_bkt_x27_4241_);
lean_dec_ref(v_a_4185_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = lean_unsigned_to_nat(1u);
v___x_4244_ = lean_nat_sub(v_size_4194_, v___x_4243_);
lean_dec(v_size_4194_);
v___y_4187_ = v_buckets_x27_4240_;
v___y_4188_ = v_bkt_x27_4241_;
v___y_4189_ = v___x_4219_;
v___y_4190_ = v___x_4244_;
goto v___jp_4186_;
}
else
{
v___y_4187_ = v_buckets_x27_4240_;
v___y_4188_ = v_bkt_x27_4241_;
v___y_4189_ = v___x_4219_;
v___y_4190_ = v_size_4194_;
goto v___jp_4186_;
}
}
}
v___jp_4245_:
{
uint64_t v___x_4247_; uint64_t v___x_4248_; 
v___x_4247_ = 13ULL;
v___x_4248_ = lean_uint64_mix_hash(v___y_4246_, v___x_4247_);
v___y_4205_ = v___x_4248_;
goto v___jp_4204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4255_, lean_object* v_as_4256_, size_t v_sz_4257_, size_t v_i_4258_, lean_object* v_b_4259_){
_start:
{
uint8_t v___x_4260_; 
v___x_4260_ = lean_usize_dec_lt(v_i_4258_, v_sz_4257_);
if (v___x_4260_ == 0)
{
return v_b_4259_;
}
else
{
lean_object* v_a_4261_; lean_object* v___y_4263_; 
v_a_4261_ = lean_array_uget_borrowed(v_as_4256_, v_i_4258_);
if (v_allowSimultaneousBinderUse_4255_ == 0)
{
lean_object* v___x_4272_; 
v___x_4272_ = lean_box(0);
v___y_4263_ = v___x_4272_;
goto v___jp_4262_;
}
else
{
uint8_t v_isBinder_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_isBinder_4273_ = lean_ctor_get_uint8(v_a_4261_, sizeof(void*)*6);
v___x_4274_ = lean_box(v_isBinder_4273_);
v___x_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
v___y_4263_ = v___x_4275_;
goto v___jp_4262_;
}
v___jp_4262_:
{
lean_object* v_ident_4264_; lean_object* v_range_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; size_t v___x_4269_; size_t v___x_4270_; 
v_ident_4264_ = lean_ctor_get(v_a_4261_, 0);
v_range_4265_ = lean_ctor_get(v_a_4261_, 2);
lean_inc_ref(v_range_4265_);
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___y_4263_);
lean_ctor_set(v___x_4266_, 1, v_range_4265_);
lean_inc_ref(v_ident_4264_);
v___x_4267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4267_, 0, v_ident_4264_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
lean_inc(v_a_4261_);
v___x_4268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4261_, v_b_4259_, v___x_4267_);
v___x_4269_ = ((size_t)1ULL);
v___x_4270_ = lean_usize_add(v_i_4258_, v___x_4269_);
v_i_4258_ = v___x_4270_;
v_b_4259_ = v___x_4268_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4276_, lean_object* v_as_4277_, lean_object* v_sz_4278_, lean_object* v_i_4279_, lean_object* v_b_4280_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4281_; size_t v_sz_boxed_4282_; size_t v_i_boxed_4283_; lean_object* v_res_4284_; 
v_allowSimultaneousBinderUse_boxed_4281_ = lean_unbox(v_allowSimultaneousBinderUse_4276_);
v_sz_boxed_4282_ = lean_unbox_usize(v_sz_4278_);
lean_dec(v_sz_4278_);
v_i_boxed_4283_ = lean_unbox_usize(v_i_4279_);
lean_dec(v_i_4279_);
v_res_4284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4281_, v_as_4277_, v_sz_boxed_4282_, v_i_boxed_4283_, v_b_4280_);
lean_dec_ref(v_as_4277_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4285_, lean_object* v_x_4286_){
_start:
{
if (lean_obj_tag(v_x_4286_) == 0)
{
return v_x_4285_;
}
else
{
lean_object* v_value_4287_; lean_object* v_tail_4288_; lean_object* v___x_4289_; 
v_value_4287_ = lean_ctor_get(v_x_4286_, 1);
lean_inc(v_value_4287_);
v_tail_4288_ = lean_ctor_get(v_x_4286_, 2);
lean_inc(v_tail_4288_);
lean_dec_ref_known(v_x_4286_, 3);
v___x_4289_ = lean_array_push(v_x_4285_, v_value_4287_);
v_x_4285_ = v___x_4289_;
v_x_4286_ = v_tail_4288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4291_, size_t v_i_4292_, size_t v_stop_4293_, lean_object* v_b_4294_){
_start:
{
uint8_t v___x_4295_; 
v___x_4295_ = lean_usize_dec_eq(v_i_4292_, v_stop_4293_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; lean_object* v___x_4297_; size_t v___x_4298_; size_t v___x_4299_; 
v___x_4296_ = lean_array_uget_borrowed(v_as_4291_, v_i_4292_);
lean_inc(v___x_4296_);
v___x_4297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4294_, v___x_4296_);
v___x_4298_ = ((size_t)1ULL);
v___x_4299_ = lean_usize_add(v_i_4292_, v___x_4298_);
v_i_4292_ = v___x_4299_;
v_b_4294_ = v___x_4297_;
goto _start;
}
else
{
return v_b_4294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4301_, lean_object* v_i_4302_, lean_object* v_stop_4303_, lean_object* v_b_4304_){
_start:
{
size_t v_i_boxed_4305_; size_t v_stop_boxed_4306_; lean_object* v_res_4307_; 
v_i_boxed_4305_ = lean_unbox_usize(v_i_4302_);
lean_dec(v_i_4302_);
v_stop_boxed_4306_ = lean_unbox_usize(v_stop_4303_);
lean_dec(v_stop_4303_);
v_res_4307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4301_, v_i_boxed_4305_, v_stop_boxed_4306_, v_b_4304_);
lean_dec_ref(v_as_4301_);
return v_res_4307_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4308_ = lean_box(0);
v___x_4309_ = lean_unsigned_to_nat(16u);
v___x_4310_ = lean_mk_array(v___x_4309_, v___x_4308_);
return v___x_4310_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v_refsByIdAndRange_4313_; 
v___x_4311_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4312_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4313_, 0, v___x_4312_);
lean_ctor_set(v_refsByIdAndRange_4313_, 1, v___x_4311_);
return v_refsByIdAndRange_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4314_, uint8_t v_allowSimultaneousBinderUse_4315_){
_start:
{
lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4325_; lean_object* v___x_4332_; lean_object* v_refsByIdAndRange_4333_; size_t v_sz_4334_; size_t v___x_4335_; lean_object* v___x_4336_; lean_object* v_buckets_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; uint8_t v___x_4340_; 
v___x_4332_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4333_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4334_ = lean_array_size(v_refs_4314_);
v___x_4335_ = ((size_t)0ULL);
v___x_4336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4315_, v_refs_4314_, v_sz_4334_, v___x_4335_, v_refsByIdAndRange_4333_);
v_buckets_4337_ = lean_ctor_get(v___x_4336_, 1);
lean_inc_ref(v_buckets_4337_);
lean_dec_ref(v___x_4336_);
v___x_4338_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4339_ = lean_array_get_size(v_buckets_4337_);
v___x_4340_ = lean_nat_dec_lt(v___x_4332_, v___x_4339_);
if (v___x_4340_ == 0)
{
lean_dec_ref(v_buckets_4337_);
v___y_4325_ = v___x_4338_;
goto v___jp_4324_;
}
else
{
size_t v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = lean_usize_of_nat(v___x_4339_);
v___x_4342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4337_, v___x_4335_, v___x_4341_, v___x_4338_);
lean_dec_ref(v_buckets_4337_);
v___y_4325_ = v___x_4342_;
goto v___jp_4324_;
}
v___jp_4316_:
{
uint8_t v___x_4321_; 
v___x_4321_ = lean_nat_dec_le(v___y_4320_, v___y_4317_);
if (v___x_4321_ == 0)
{
lean_object* v___x_4322_; 
lean_dec(v___y_4317_);
lean_inc(v___y_4320_);
v___x_4322_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4319_, v___y_4318_, v___y_4320_, v___y_4320_);
lean_dec(v___y_4320_);
lean_dec(v___y_4319_);
return v___x_4322_;
}
else
{
lean_object* v___x_4323_; 
v___x_4323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4319_, v___y_4318_, v___y_4320_, v___y_4317_);
lean_dec(v___y_4317_);
lean_dec(v___y_4319_);
return v___x_4323_;
}
}
v___jp_4324_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; uint8_t v___x_4328_; 
v___x_4326_ = lean_array_get_size(v___y_4325_);
v___x_4327_ = lean_unsigned_to_nat(0u);
v___x_4328_ = lean_nat_dec_eq(v___x_4326_, v___x_4327_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4329_ = lean_unsigned_to_nat(1u);
v___x_4330_ = lean_nat_sub(v___x_4326_, v___x_4329_);
v___x_4331_ = lean_nat_dec_le(v___x_4327_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_inc(v___x_4330_);
v___y_4317_ = v___x_4330_;
v___y_4318_ = v___y_4325_;
v___y_4319_ = v___x_4326_;
v___y_4320_ = v___x_4330_;
goto v___jp_4316_;
}
else
{
v___y_4317_ = v___x_4330_;
v___y_4318_ = v___y_4325_;
v___y_4319_ = v___x_4326_;
v___y_4320_ = v___x_4327_;
goto v___jp_4316_;
}
}
else
{
return v___y_4325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object* v_refs_4343_, lean_object* v_allowSimultaneousBinderUse_4344_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4345_; lean_object* v_res_4346_; 
v_allowSimultaneousBinderUse_boxed_4345_ = lean_unbox(v_allowSimultaneousBinderUse_4344_);
v_res_4346_ = l_Lean_Server_dedupReferences(v_refs_4343_, v_allowSimultaneousBinderUse_boxed_4345_);
lean_dec_ref(v_refs_4343_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object* v_n_4347_, lean_object* v_as_4348_, lean_object* v_lo_4349_, lean_object* v_hi_4350_, lean_object* v_w_4351_, lean_object* v_hlo_4352_, lean_object* v_hhi_4353_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4347_, v_as_4348_, v_lo_4349_, v_hi_4350_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object* v_n_4355_, lean_object* v_as_4356_, lean_object* v_lo_4357_, lean_object* v_hi_4358_, lean_object* v_w_4359_, lean_object* v_hlo_4360_, lean_object* v_hhi_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(v_n_4355_, v_as_4356_, v_lo_4357_, v_hi_4358_, v_w_4359_, v_hlo_4360_, v_hhi_4361_);
lean_dec(v_hi_4358_);
lean_dec(v_n_4355_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(lean_object* v_n_4363_, lean_object* v_lo_4364_, lean_object* v_hi_4365_, lean_object* v_hhi_4366_, lean_object* v_pivot_4367_, lean_object* v_as_4368_, lean_object* v_i_4369_, lean_object* v_k_4370_, lean_object* v_ilo_4371_, lean_object* v_ik_4372_, lean_object* v_w_4373_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_4365_, v_pivot_4367_, v_as_4368_, v_i_4369_, v_k_4370_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___boxed(lean_object* v_n_4375_, lean_object* v_lo_4376_, lean_object* v_hi_4377_, lean_object* v_hhi_4378_, lean_object* v_pivot_4379_, lean_object* v_as_4380_, lean_object* v_i_4381_, lean_object* v_k_4382_, lean_object* v_ilo_4383_, lean_object* v_ik_4384_, lean_object* v_w_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(v_n_4375_, v_lo_4376_, v_hi_4377_, v_hhi_4378_, v_pivot_4379_, v_as_4380_, v_i_4381_, v_k_4382_, v_ilo_4383_, v_ik_4384_, v_w_4385_);
lean_dec_ref(v_pivot_4379_);
lean_dec(v_hi_4377_);
lean_dec(v_lo_4376_);
lean_dec(v_n_4375_);
return v_res_4386_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object* v_00_u03b2_4387_, lean_object* v_a_4388_, lean_object* v_x_4389_){
_start:
{
uint8_t v___x_4390_; 
v___x_4390_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4388_, v_x_4389_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4391_, lean_object* v_a_4392_, lean_object* v_x_4393_){
_start:
{
uint8_t v_res_4394_; lean_object* v_r_4395_; 
v_res_4394_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(v_00_u03b2_4391_, v_a_4392_, v_x_4393_);
lean_dec(v_x_4393_);
lean_dec_ref(v_a_4392_);
v_r_4395_ = lean_box(v_res_4394_);
return v_r_4395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object* v_00_u03b2_4396_, lean_object* v_data_4397_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_data_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4399_, lean_object* v_i_4400_, lean_object* v_source_4401_, lean_object* v_target_4402_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v_i_4400_, v_source_4401_, v_target_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4404_, lean_object* v_x_4405_, lean_object* v_x_4406_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_x_4405_, v_x_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object* v_as_4408_, size_t v_i_4409_, size_t v_stop_4410_, lean_object* v_b_4411_){
_start:
{
uint8_t v___x_4412_; 
v___x_4412_ = lean_usize_dec_eq(v_i_4409_, v_stop_4410_);
if (v___x_4412_ == 0)
{
lean_object* v___x_4413_; lean_object* v___x_4414_; size_t v___x_4415_; size_t v___x_4416_; 
v___x_4413_ = lean_array_uget_borrowed(v_as_4408_, v_i_4409_);
lean_inc(v___x_4413_);
v___x_4414_ = l_Lean_Server_ModuleRefs_addRef(v_b_4411_, v___x_4413_);
v___x_4415_ = ((size_t)1ULL);
v___x_4416_ = lean_usize_add(v_i_4409_, v___x_4415_);
v_i_4409_ = v___x_4416_;
v_b_4411_ = v___x_4414_;
goto _start;
}
else
{
return v_b_4411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object* v_as_4418_, lean_object* v_i_4419_, lean_object* v_stop_4420_, lean_object* v_b_4421_){
_start:
{
size_t v_i_boxed_4422_; size_t v_stop_boxed_4423_; lean_object* v_res_4424_; 
v_i_boxed_4422_ = lean_unbox_usize(v_i_4419_);
lean_dec(v_i_4419_);
v_stop_boxed_4423_ = lean_unbox_usize(v_stop_4420_);
lean_dec(v_stop_4420_);
v_res_4424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_as_4418_, v_i_boxed_4422_, v_stop_boxed_4423_, v_b_4421_);
lean_dec_ref(v_as_4418_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object* v_as_4425_, size_t v_i_4426_, size_t v_stop_4427_, lean_object* v_b_4428_){
_start:
{
lean_object* v___y_4430_; uint8_t v___x_4434_; 
v___x_4434_ = lean_usize_dec_eq(v_i_4426_, v_stop_4427_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; lean_object* v_ident_4436_; 
v___x_4435_ = lean_array_uget_borrowed(v_as_4425_, v_i_4426_);
v_ident_4436_ = lean_ctor_get(v___x_4435_, 0);
if (lean_obj_tag(v_ident_4436_) == 1)
{
v___y_4430_ = v_b_4428_;
goto v___jp_4429_;
}
else
{
lean_object* v___x_4437_; 
lean_inc(v___x_4435_);
v___x_4437_ = lean_array_push(v_b_4428_, v___x_4435_);
v___y_4430_ = v___x_4437_;
goto v___jp_4429_;
}
}
else
{
return v_b_4428_;
}
v___jp_4429_:
{
size_t v___x_4431_; size_t v___x_4432_; 
v___x_4431_ = ((size_t)1ULL);
v___x_4432_ = lean_usize_add(v_i_4426_, v___x_4431_);
v_i_4426_ = v___x_4432_;
v_b_4428_ = v___y_4430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object* v_as_4438_, lean_object* v_i_4439_, lean_object* v_stop_4440_, lean_object* v_b_4441_){
_start:
{
size_t v_i_boxed_4442_; size_t v_stop_boxed_4443_; lean_object* v_res_4444_; 
v_i_boxed_4442_ = lean_unbox_usize(v_i_4439_);
lean_dec(v_i_4439_);
v_stop_boxed_4443_ = lean_unbox_usize(v_stop_4440_);
lean_dec(v_stop_4440_);
v_res_4444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_as_4438_, v_i_boxed_4442_, v_stop_boxed_4443_, v_b_4441_);
lean_dec_ref(v_as_4438_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object* v_text_4445_, lean_object* v_trees_4446_, uint8_t v_localVars_4447_, uint8_t v_allowSimultaneousBinderUse_4448_){
_start:
{
lean_object* v_refs_4450_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v_refs_4460_; 
v___x_4458_ = l_Lean_Server_findReferences(v_text_4445_, v_trees_4446_);
v___x_4459_ = l_Lean_Server_combineIdents(v_trees_4446_, v___x_4458_);
lean_dec_ref(v___x_4458_);
v_refs_4460_ = l_Lean_Server_dedupReferences(v___x_4459_, v_allowSimultaneousBinderUse_4448_);
lean_dec_ref(v___x_4459_);
if (v_localVars_4447_ == 0)
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; uint8_t v___x_4464_; 
v___x_4461_ = lean_unsigned_to_nat(0u);
v___x_4462_ = lean_array_get_size(v_refs_4460_);
v___x_4463_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4464_ = lean_nat_dec_lt(v___x_4461_, v___x_4462_);
if (v___x_4464_ == 0)
{
lean_dec_ref(v_refs_4460_);
v_refs_4450_ = v___x_4463_;
goto v___jp_4449_;
}
else
{
size_t v___x_4465_; size_t v___x_4466_; lean_object* v___x_4467_; 
v___x_4465_ = ((size_t)0ULL);
v___x_4466_ = lean_usize_of_nat(v___x_4462_);
v___x_4467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4460_, v___x_4465_, v___x_4466_, v___x_4463_);
lean_dec_ref(v_refs_4460_);
v_refs_4450_ = v___x_4467_;
goto v___jp_4449_;
}
}
else
{
v_refs_4450_ = v_refs_4460_;
goto v___jp_4449_;
}
v___jp_4449_:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; uint8_t v___x_4454_; 
v___x_4451_ = lean_box(1);
v___x_4452_ = lean_unsigned_to_nat(0u);
v___x_4453_ = lean_array_get_size(v_refs_4450_);
v___x_4454_ = lean_nat_dec_lt(v___x_4452_, v___x_4453_);
if (v___x_4454_ == 0)
{
lean_dec_ref(v_refs_4450_);
return v___x_4451_;
}
else
{
size_t v___x_4455_; size_t v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = ((size_t)0ULL);
v___x_4456_ = lean_usize_of_nat(v___x_4453_);
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4450_, v___x_4455_, v___x_4456_, v___x_4451_);
lean_dec_ref(v_refs_4450_);
return v___x_4457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object* v_text_4468_, lean_object* v_trees_4469_, lean_object* v_localVars_4470_, lean_object* v_allowSimultaneousBinderUse_4471_){
_start:
{
uint8_t v_localVars_boxed_4472_; uint8_t v_allowSimultaneousBinderUse_boxed_4473_; lean_object* v_res_4474_; 
v_localVars_boxed_4472_ = lean_unbox(v_localVars_4470_);
v_allowSimultaneousBinderUse_boxed_4473_ = lean_unbox(v_allowSimultaneousBinderUse_4471_);
v_res_4474_ = l_Lean_Server_findModuleRefs(v_text_4468_, v_trees_4469_, v_localVars_boxed_4472_, v_allowSimultaneousBinderUse_boxed_4473_);
lean_dec_ref(v_trees_4469_);
return v_res_4474_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t v_a_4482_, uint8_t v_a_4483_){
_start:
{
switch(v_a_4482_)
{
case 0:
{
if (v_a_4483_ == 1)
{
uint8_t v___x_4484_; 
v___x_4484_ = 2;
return v___x_4484_;
}
else
{
return v_a_4483_;
}
}
case 1:
{
if (v_a_4483_ == 0)
{
uint8_t v___x_4485_; 
v___x_4485_ = 2;
return v___x_4485_;
}
else
{
return v_a_4483_;
}
}
default: 
{
return v_a_4482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
uint8_t v_a_46__boxed_4488_; uint8_t v_a_47__boxed_4489_; uint8_t v_res_4490_; lean_object* v_r_4491_; 
v_a_46__boxed_4488_ = lean_unbox(v_a_4486_);
v_a_47__boxed_4489_ = lean_unbox(v_a_4487_);
v_res_4490_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_a_46__boxed_4488_, v_a_47__boxed_4489_);
v_r_4491_ = lean_box(v_res_4490_);
return v_r_4491_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object* v_upperBound_4492_, lean_object* v_identicalImports_4493_, lean_object* v_a_4494_, lean_object* v_b_4495_){
_start:
{
uint8_t v___x_4496_; 
v___x_4496_ = lean_nat_dec_lt(v_a_4494_, v_upperBound_4492_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4497_; 
lean_dec(v_a_4494_);
v___x_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4497_, 0, v_b_4495_);
return v___x_4497_;
}
else
{
lean_object* v_module_4498_; lean_object* v_uri_4499_; uint8_t v_isAll_4500_; uint8_t v_isPrivate_4501_; uint8_t v_metaKind_4502_; lean_object* v___x_4503_; lean_object* v_module_4504_; lean_object* v_uri_4505_; uint8_t v_isAll_4506_; uint8_t v_isPrivate_4507_; uint8_t v_metaKind_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4528_; 
v_module_4498_ = lean_ctor_get(v_b_4495_, 0);
lean_inc(v_module_4498_);
v_uri_4499_ = lean_ctor_get(v_b_4495_, 1);
lean_inc_ref(v_uri_4499_);
v_isAll_4500_ = lean_ctor_get_uint8(v_b_4495_, sizeof(void*)*2);
v_isPrivate_4501_ = lean_ctor_get_uint8(v_b_4495_, sizeof(void*)*2 + 1);
v_metaKind_4502_ = lean_ctor_get_uint8(v_b_4495_, sizeof(void*)*2 + 2);
lean_dec_ref(v_b_4495_);
v___x_4503_ = lean_array_fget(v_identicalImports_4493_, v_a_4494_);
v_module_4504_ = lean_ctor_get(v___x_4503_, 0);
v_uri_4505_ = lean_ctor_get(v___x_4503_, 1);
v_isAll_4506_ = lean_ctor_get_uint8(v___x_4503_, sizeof(void*)*2);
v_isPrivate_4507_ = lean_ctor_get_uint8(v___x_4503_, sizeof(void*)*2 + 1);
v_metaKind_4508_ = lean_ctor_get_uint8(v___x_4503_, sizeof(void*)*2 + 2);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4510_ = v___x_4503_;
v_isShared_4511_ = v_isSharedCheck_4528_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_uri_4505_);
lean_inc(v_module_4504_);
lean_dec(v___x_4503_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4528_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
uint8_t v___y_4513_; uint8_t v___y_4514_; uint8_t v___y_4523_; uint8_t v___x_4524_; 
v___x_4524_ = lean_name_eq(v_module_4498_, v_module_4504_);
lean_dec(v_module_4504_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4525_; 
lean_del_object(v___x_4510_);
lean_dec_ref(v_uri_4505_);
lean_dec_ref(v_uri_4499_);
lean_dec(v_module_4498_);
lean_dec(v_a_4494_);
v___x_4525_ = lean_box(0);
return v___x_4525_;
}
else
{
uint8_t v___x_4526_; 
v___x_4526_ = lean_string_dec_eq(v_uri_4499_, v_uri_4505_);
lean_dec_ref(v_uri_4505_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
lean_del_object(v___x_4510_);
lean_dec_ref(v_uri_4499_);
lean_dec(v_module_4498_);
lean_dec(v_a_4494_);
v___x_4527_ = lean_box(0);
return v___x_4527_;
}
else
{
if (v_isAll_4500_ == 0)
{
v___y_4523_ = v_isAll_4506_;
goto v___jp_4522_;
}
else
{
v___y_4523_ = v___x_4496_;
goto v___jp_4522_;
}
}
}
v___jp_4512_:
{
uint8_t v___x_4515_; lean_object* v___x_4517_; 
v___x_4515_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_metaKind_4502_, v_metaKind_4508_);
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 1, v_uri_4499_);
lean_ctor_set(v___x_4510_, 0, v_module_4498_);
v___x_4517_ = v___x_4510_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_module_4498_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v_uri_4499_);
v___x_4517_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*2, v___y_4513_);
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*2 + 1, v___y_4514_);
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*2 + 2, v___x_4515_);
v___x_4518_ = lean_unsigned_to_nat(1u);
v___x_4519_ = lean_nat_add(v_a_4494_, v___x_4518_);
lean_dec(v_a_4494_);
v_a_4494_ = v___x_4519_;
v_b_4495_ = v___x_4517_;
goto _start;
}
}
v___jp_4522_:
{
if (v_isPrivate_4501_ == 0)
{
v___y_4513_ = v___y_4523_;
v___y_4514_ = v_isPrivate_4501_;
goto v___jp_4512_;
}
else
{
v___y_4513_ = v___y_4523_;
v___y_4514_ = v_isPrivate_4507_;
goto v___jp_4512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_4529_, lean_object* v_identicalImports_4530_, lean_object* v_a_4531_, lean_object* v_b_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4529_, v_identicalImports_4530_, v_a_4531_, v_b_4532_);
lean_dec_ref(v_identicalImports_4530_);
lean_dec(v_upperBound_4529_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object* v_identicalImports_4534_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; uint8_t v___x_4537_; 
v___x_4535_ = lean_unsigned_to_nat(0u);
v___x_4536_ = lean_array_get_size(v_identicalImports_4534_);
v___x_4537_ = lean_nat_dec_lt(v___x_4535_, v___x_4536_);
if (v___x_4537_ == 0)
{
lean_object* v___x_4538_; 
v___x_4538_ = lean_box(0);
return v___x_4538_;
}
else
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4539_ = lean_unsigned_to_nat(1u);
v___x_4540_ = lean_array_fget_borrowed(v_identicalImports_4534_, v___x_4535_);
lean_inc(v___x_4540_);
v___x_4541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v___x_4536_, v_identicalImports_4534_, v___x_4539_, v___x_4540_);
return v___x_4541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object* v_identicalImports_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_identicalImports_4542_);
lean_dec_ref(v_identicalImports_4542_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object* v_upperBound_4544_, lean_object* v_identicalImports_4545_, lean_object* v_inst_4546_, lean_object* v_R_4547_, lean_object* v_a_4548_, lean_object* v_b_4549_, lean_object* v_c_4550_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4544_, v_identicalImports_4545_, v_a_4548_, v_b_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object* v_upperBound_4552_, lean_object* v_identicalImports_4553_, lean_object* v_inst_4554_, lean_object* v_R_4555_, lean_object* v_a_4556_, lean_object* v_b_4557_, lean_object* v_c_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(v_upperBound_4552_, v_identicalImports_4553_, v_inst_4554_, v_R_4555_, v_a_4556_, v_b_4557_, v_c_4558_);
lean_dec_ref(v_identicalImports_4553_);
lean_dec(v_upperBound_4552_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object* v_x_4566_){
_start:
{
lean_object* v_module_4567_; 
v_module_4567_ = lean_ctor_get(v_x_4566_, 0);
lean_inc(v_module_4567_);
return v_module_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object* v_x_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_Server_DirectImports_convertImportInfos___lam__0(v_x_4568_);
lean_dec_ref(v_x_4568_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object* v_x_4570_, lean_object* v_x_4571_){
_start:
{
if (lean_obj_tag(v_x_4571_) == 0)
{
return v_x_4570_;
}
else
{
lean_object* v_key_4572_; lean_object* v_value_4573_; lean_object* v_tail_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v_key_4572_ = lean_ctor_get(v_x_4571_, 0);
v_value_4573_ = lean_ctor_get(v_x_4571_, 1);
v_tail_4574_ = lean_ctor_get(v_x_4571_, 2);
lean_inc(v_value_4573_);
lean_inc(v_key_4572_);
v___x_4575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4575_, 0, v_key_4572_);
lean_ctor_set(v___x_4575_, 1, v_value_4573_);
v___x_4576_ = lean_array_push(v_x_4570_, v___x_4575_);
v_x_4570_ = v___x_4576_;
v_x_4571_ = v_tail_4574_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object* v_x_4578_, lean_object* v_x_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_x_4578_, v_x_4579_);
lean_dec(v_x_4579_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object* v_as_4581_, size_t v_i_4582_, size_t v_stop_4583_, lean_object* v_b_4584_){
_start:
{
uint8_t v___x_4585_; 
v___x_4585_ = lean_usize_dec_eq(v_i_4582_, v_stop_4583_);
if (v___x_4585_ == 0)
{
lean_object* v___x_4586_; lean_object* v___x_4587_; size_t v___x_4588_; size_t v___x_4589_; 
v___x_4586_ = lean_array_uget_borrowed(v_as_4581_, v_i_4582_);
v___x_4587_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_b_4584_, v___x_4586_);
v___x_4588_ = ((size_t)1ULL);
v___x_4589_ = lean_usize_add(v_i_4582_, v___x_4588_);
v_i_4582_ = v___x_4589_;
v_b_4584_ = v___x_4587_;
goto _start;
}
else
{
return v_b_4584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object* v_as_4591_, lean_object* v_i_4592_, lean_object* v_stop_4593_, lean_object* v_b_4594_){
_start:
{
size_t v_i_boxed_4595_; size_t v_stop_boxed_4596_; lean_object* v_res_4597_; 
v_i_boxed_4595_ = lean_unbox_usize(v_i_4592_);
lean_dec(v_i_4592_);
v_stop_boxed_4596_ = lean_unbox_usize(v_stop_4593_);
lean_dec(v_stop_4593_);
v_res_4597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_as_4591_, v_i_boxed_4595_, v_stop_boxed_4596_, v_b_4594_);
lean_dec_ref(v_as_4591_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object* v_as_4598_, size_t v_i_4599_, size_t v_stop_4600_, lean_object* v_b_4601_){
_start:
{
lean_object* v_a_4604_; uint8_t v___x_4608_; 
v___x_4608_ = lean_usize_dec_eq(v_i_4599_, v_stop_4600_);
if (v___x_4608_ == 0)
{
lean_object* v___x_4609_; lean_object* v_module_4610_; uint8_t v_isPrivate_4611_; uint8_t v_isAll_4612_; uint8_t v_isMeta_4613_; lean_object* v_module_4614_; lean_object* v___x_4615_; 
v___x_4609_ = lean_array_uget_borrowed(v_as_4598_, v_i_4599_);
v_module_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isPrivate_4611_ = lean_ctor_get_uint8(v___x_4609_, sizeof(void*)*1);
v_isAll_4612_ = lean_ctor_get_uint8(v___x_4609_, sizeof(void*)*1 + 1);
v_isMeta_4613_ = lean_ctor_get_uint8(v___x_4609_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4610_);
v_module_4614_ = l_String_toName(v_module_4610_);
lean_inc(v_module_4614_);
v___x_4615_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4614_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc(v_a_4616_);
lean_dec_ref_known(v___x_4615_, 1);
if (lean_obj_tag(v_a_4616_) == 1)
{
lean_object* v_val_4617_; uint8_t v___y_4619_; 
v_val_4617_ = lean_ctor_get(v_a_4616_, 0);
lean_inc(v_val_4617_);
lean_dec_ref_known(v_a_4616_, 1);
if (v_isMeta_4613_ == 0)
{
uint8_t v___x_4622_; 
v___x_4622_ = 0;
v___y_4619_ = v___x_4622_;
goto v___jp_4618_;
}
else
{
uint8_t v___x_4623_; 
v___x_4623_ = 1;
v___y_4619_ = v___x_4623_;
goto v___jp_4618_;
}
v___jp_4618_:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4620_, 0, v_module_4614_);
lean_ctor_set(v___x_4620_, 1, v_val_4617_);
lean_ctor_set_uint8(v___x_4620_, sizeof(void*)*2, v_isAll_4612_);
lean_ctor_set_uint8(v___x_4620_, sizeof(void*)*2 + 1, v_isPrivate_4611_);
lean_ctor_set_uint8(v___x_4620_, sizeof(void*)*2 + 2, v___y_4619_);
v___x_4621_ = lean_array_push(v_b_4601_, v___x_4620_);
v_a_4604_ = v___x_4621_;
goto v___jp_4603_;
}
}
else
{
lean_dec(v_a_4616_);
lean_dec(v_module_4614_);
v_a_4604_ = v_b_4601_;
goto v___jp_4603_;
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_dec(v_module_4614_);
lean_dec_ref(v_b_4601_);
v_a_4624_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4615_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4615_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
else
{
lean_object* v___x_4632_; 
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v_b_4601_);
return v___x_4632_;
}
v___jp_4603_:
{
size_t v___x_4605_; size_t v___x_4606_; 
v___x_4605_ = ((size_t)1ULL);
v___x_4606_ = lean_usize_add(v_i_4599_, v___x_4605_);
v_i_4599_ = v___x_4606_;
v_b_4601_ = v_a_4604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object* v_as_4633_, lean_object* v_i_4634_, lean_object* v_stop_4635_, lean_object* v_b_4636_, lean_object* v___y_4637_){
_start:
{
size_t v_i_boxed_4638_; size_t v_stop_boxed_4639_; lean_object* v_res_4640_; 
v_i_boxed_4638_ = lean_unbox_usize(v_i_4634_);
lean_dec(v_i_4634_);
v_stop_boxed_4639_ = lean_unbox_usize(v_stop_4635_);
lean_dec(v_stop_4635_);
v_res_4640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4633_, v_i_boxed_4638_, v_stop_boxed_4639_, v_b_4636_);
lean_dec_ref(v_as_4633_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object* v_as_4641_, lean_object* v_start_4642_, lean_object* v_stop_4643_){
_start:
{
lean_object* v___x_4645_; uint8_t v___x_4646_; 
v___x_4645_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_4646_ = lean_nat_dec_lt(v_start_4642_, v_stop_4643_);
if (v___x_4646_ == 0)
{
lean_object* v___x_4647_; 
v___x_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4645_);
return v___x_4647_;
}
else
{
lean_object* v___x_4648_; uint8_t v___x_4649_; 
v___x_4648_ = lean_array_get_size(v_as_4641_);
v___x_4649_ = lean_nat_dec_le(v_stop_4643_, v___x_4648_);
if (v___x_4649_ == 0)
{
uint8_t v___x_4650_; 
v___x_4650_ = lean_nat_dec_lt(v_start_4642_, v___x_4648_);
if (v___x_4650_ == 0)
{
lean_object* v___x_4651_; 
v___x_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4645_);
return v___x_4651_;
}
else
{
size_t v___x_4652_; size_t v___x_4653_; lean_object* v___x_4654_; 
v___x_4652_ = lean_usize_of_nat(v_start_4642_);
v___x_4653_ = lean_usize_of_nat(v___x_4648_);
v___x_4654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4641_, v___x_4652_, v___x_4653_, v___x_4645_);
return v___x_4654_;
}
}
else
{
size_t v___x_4655_; size_t v___x_4656_; lean_object* v___x_4657_; 
v___x_4655_ = lean_usize_of_nat(v_start_4642_);
v___x_4656_ = lean_usize_of_nat(v_stop_4643_);
v___x_4657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4641_, v___x_4655_, v___x_4656_, v___x_4645_);
return v___x_4657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object* v_as_4658_, lean_object* v_start_4659_, lean_object* v_stop_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_as_4658_, v_start_4659_, v_stop_4660_);
lean_dec(v_stop_4660_);
lean_dec(v_start_4659_);
lean_dec_ref(v_as_4658_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object* v_k_4663_, lean_object* v_v_4664_, lean_object* v_t_4665_){
_start:
{
if (lean_obj_tag(v_t_4665_) == 0)
{
lean_object* v_size_4666_; lean_object* v_k_4667_; lean_object* v_v_4668_; lean_object* v_l_4669_; lean_object* v_r_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4950_; 
v_size_4666_ = lean_ctor_get(v_t_4665_, 0);
v_k_4667_ = lean_ctor_get(v_t_4665_, 1);
v_v_4668_ = lean_ctor_get(v_t_4665_, 2);
v_l_4669_ = lean_ctor_get(v_t_4665_, 3);
v_r_4670_ = lean_ctor_get(v_t_4665_, 4);
v_isSharedCheck_4950_ = !lean_is_exclusive(v_t_4665_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4672_ = v_t_4665_;
v_isShared_4673_ = v_isSharedCheck_4950_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_r_4670_);
lean_inc(v_l_4669_);
lean_inc(v_v_4668_);
lean_inc(v_k_4667_);
lean_inc(v_size_4666_);
lean_dec(v_t_4665_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4950_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
uint8_t v___x_4674_; 
v___x_4674_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4663_, v_k_4667_);
switch(v___x_4674_)
{
case 0:
{
lean_object* v_impl_4675_; lean_object* v___x_4676_; 
lean_dec(v_size_4666_);
v_impl_4675_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4663_, v_v_4664_, v_l_4669_);
v___x_4676_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4670_) == 0)
{
lean_object* v_size_4677_; lean_object* v_size_4678_; lean_object* v_k_4679_; lean_object* v_v_4680_; lean_object* v_l_4681_; lean_object* v_r_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; 
v_size_4677_ = lean_ctor_get(v_r_4670_, 0);
v_size_4678_ = lean_ctor_get(v_impl_4675_, 0);
v_k_4679_ = lean_ctor_get(v_impl_4675_, 1);
v_v_4680_ = lean_ctor_get(v_impl_4675_, 2);
v_l_4681_ = lean_ctor_get(v_impl_4675_, 3);
v_r_4682_ = lean_ctor_get(v_impl_4675_, 4);
lean_inc(v_r_4682_);
v___x_4683_ = lean_unsigned_to_nat(3u);
v___x_4684_ = lean_nat_mul(v___x_4683_, v_size_4677_);
v___x_4685_ = lean_nat_dec_lt(v___x_4684_, v_size_4678_);
lean_dec(v___x_4684_);
if (v___x_4685_ == 0)
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4689_; 
lean_dec(v_r_4682_);
v___x_4686_ = lean_nat_add(v___x_4676_, v_size_4678_);
v___x_4687_ = lean_nat_add(v___x_4686_, v_size_4677_);
lean_dec(v___x_4686_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 3, v_impl_4675_);
lean_ctor_set(v___x_4672_, 0, v___x_4687_);
v___x_4689_ = v___x_4672_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4687_);
lean_ctor_set(v_reuseFailAlloc_4690_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4690_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4690_, 3, v_impl_4675_);
lean_ctor_set(v_reuseFailAlloc_4690_, 4, v_r_4670_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
else
{
lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4756_; 
lean_inc(v_l_4681_);
lean_inc(v_v_4680_);
lean_inc(v_k_4679_);
lean_inc(v_size_4678_);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_impl_4675_);
if (v_isSharedCheck_4756_ == 0)
{
lean_object* v_unused_4757_; lean_object* v_unused_4758_; lean_object* v_unused_4759_; lean_object* v_unused_4760_; lean_object* v_unused_4761_; 
v_unused_4757_ = lean_ctor_get(v_impl_4675_, 4);
lean_dec(v_unused_4757_);
v_unused_4758_ = lean_ctor_get(v_impl_4675_, 3);
lean_dec(v_unused_4758_);
v_unused_4759_ = lean_ctor_get(v_impl_4675_, 2);
lean_dec(v_unused_4759_);
v_unused_4760_ = lean_ctor_get(v_impl_4675_, 1);
lean_dec(v_unused_4760_);
v_unused_4761_ = lean_ctor_get(v_impl_4675_, 0);
lean_dec(v_unused_4761_);
v___x_4692_ = v_impl_4675_;
v_isShared_4693_ = v_isSharedCheck_4756_;
goto v_resetjp_4691_;
}
else
{
lean_dec(v_impl_4675_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4756_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v_size_4694_; lean_object* v_size_4695_; lean_object* v_k_4696_; lean_object* v_v_4697_; lean_object* v_l_4698_; lean_object* v_r_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; 
v_size_4694_ = lean_ctor_get(v_l_4681_, 0);
v_size_4695_ = lean_ctor_get(v_r_4682_, 0);
v_k_4696_ = lean_ctor_get(v_r_4682_, 1);
v_v_4697_ = lean_ctor_get(v_r_4682_, 2);
v_l_4698_ = lean_ctor_get(v_r_4682_, 3);
v_r_4699_ = lean_ctor_get(v_r_4682_, 4);
v___x_4700_ = lean_unsigned_to_nat(2u);
v___x_4701_ = lean_nat_mul(v___x_4700_, v_size_4694_);
v___x_4702_ = lean_nat_dec_lt(v_size_4695_, v___x_4701_);
lean_dec(v___x_4701_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4731_; 
lean_inc(v_r_4699_);
lean_inc(v_l_4698_);
lean_inc(v_v_4697_);
lean_inc(v_k_4696_);
v_isSharedCheck_4731_ = !lean_is_exclusive(v_r_4682_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; lean_object* v_unused_4733_; lean_object* v_unused_4734_; lean_object* v_unused_4735_; lean_object* v_unused_4736_; 
v_unused_4732_ = lean_ctor_get(v_r_4682_, 4);
lean_dec(v_unused_4732_);
v_unused_4733_ = lean_ctor_get(v_r_4682_, 3);
lean_dec(v_unused_4733_);
v_unused_4734_ = lean_ctor_get(v_r_4682_, 2);
lean_dec(v_unused_4734_);
v_unused_4735_ = lean_ctor_get(v_r_4682_, 1);
lean_dec(v_unused_4735_);
v_unused_4736_ = lean_ctor_get(v_r_4682_, 0);
lean_dec(v_unused_4736_);
v___x_4704_ = v_r_4682_;
v_isShared_4705_ = v_isSharedCheck_4731_;
goto v_resetjp_4703_;
}
else
{
lean_dec(v_r_4682_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4731_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___x_4719_; lean_object* v___y_4721_; 
v___x_4706_ = lean_nat_add(v___x_4676_, v_size_4678_);
lean_dec(v_size_4678_);
v___x_4707_ = lean_nat_add(v___x_4706_, v_size_4677_);
lean_dec(v___x_4706_);
v___x_4719_ = lean_nat_add(v___x_4676_, v_size_4694_);
if (lean_obj_tag(v_l_4698_) == 0)
{
lean_object* v_size_4729_; 
v_size_4729_ = lean_ctor_get(v_l_4698_, 0);
lean_inc(v_size_4729_);
v___y_4721_ = v_size_4729_;
goto v___jp_4720_;
}
else
{
lean_object* v___x_4730_; 
v___x_4730_ = lean_unsigned_to_nat(0u);
v___y_4721_ = v___x_4730_;
goto v___jp_4720_;
}
v___jp_4708_:
{
lean_object* v___x_4712_; lean_object* v___x_4714_; 
v___x_4712_ = lean_nat_add(v___y_4710_, v___y_4711_);
lean_dec(v___y_4711_);
lean_dec(v___y_4710_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 4, v_r_4670_);
lean_ctor_set(v___x_4704_, 3, v_r_4699_);
lean_ctor_set(v___x_4704_, 2, v_v_4668_);
lean_ctor_set(v___x_4704_, 1, v_k_4667_);
lean_ctor_set(v___x_4704_, 0, v___x_4712_);
v___x_4714_ = v___x_4704_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v___x_4712_);
lean_ctor_set(v_reuseFailAlloc_4718_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4718_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4718_, 3, v_r_4699_);
lean_ctor_set(v_reuseFailAlloc_4718_, 4, v_r_4670_);
v___x_4714_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
lean_object* v___x_4716_; 
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 4, v___x_4714_);
lean_ctor_set(v___x_4692_, 3, v___y_4709_);
lean_ctor_set(v___x_4692_, 2, v_v_4697_);
lean_ctor_set(v___x_4692_, 1, v_k_4696_);
lean_ctor_set(v___x_4692_, 0, v___x_4707_);
v___x_4716_ = v___x_4692_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4707_);
lean_ctor_set(v_reuseFailAlloc_4717_, 1, v_k_4696_);
lean_ctor_set(v_reuseFailAlloc_4717_, 2, v_v_4697_);
lean_ctor_set(v_reuseFailAlloc_4717_, 3, v___y_4709_);
lean_ctor_set(v_reuseFailAlloc_4717_, 4, v___x_4714_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
v___jp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4724_; 
v___x_4722_ = lean_nat_add(v___x_4719_, v___y_4721_);
lean_dec(v___y_4721_);
lean_dec(v___x_4719_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v_l_4698_);
lean_ctor_set(v___x_4672_, 3, v_l_4681_);
lean_ctor_set(v___x_4672_, 2, v_v_4680_);
lean_ctor_set(v___x_4672_, 1, v_k_4679_);
lean_ctor_set(v___x_4672_, 0, v___x_4722_);
v___x_4724_ = v___x_4672_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v_k_4679_);
lean_ctor_set(v_reuseFailAlloc_4728_, 2, v_v_4680_);
lean_ctor_set(v_reuseFailAlloc_4728_, 3, v_l_4681_);
lean_ctor_set(v_reuseFailAlloc_4728_, 4, v_l_4698_);
v___x_4724_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; 
v___x_4725_ = lean_nat_add(v___x_4676_, v_size_4677_);
if (lean_obj_tag(v_r_4699_) == 0)
{
lean_object* v_size_4726_; 
v_size_4726_ = lean_ctor_get(v_r_4699_, 0);
lean_inc(v_size_4726_);
v___y_4709_ = v___x_4724_;
v___y_4710_ = v___x_4725_;
v___y_4711_ = v_size_4726_;
goto v___jp_4708_;
}
else
{
lean_object* v___x_4727_; 
v___x_4727_ = lean_unsigned_to_nat(0u);
v___y_4709_ = v___x_4724_;
v___y_4710_ = v___x_4725_;
v___y_4711_ = v___x_4727_;
goto v___jp_4708_;
}
}
}
}
}
else
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4742_; 
lean_del_object(v___x_4672_);
v___x_4737_ = lean_nat_add(v___x_4676_, v_size_4678_);
lean_dec(v_size_4678_);
v___x_4738_ = lean_nat_add(v___x_4737_, v_size_4677_);
lean_dec(v___x_4737_);
v___x_4739_ = lean_nat_add(v___x_4676_, v_size_4677_);
v___x_4740_ = lean_nat_add(v___x_4739_, v_size_4695_);
lean_dec(v___x_4739_);
lean_inc_ref(v_r_4670_);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 4, v_r_4670_);
lean_ctor_set(v___x_4692_, 3, v_r_4682_);
lean_ctor_set(v___x_4692_, 2, v_v_4668_);
lean_ctor_set(v___x_4692_, 1, v_k_4667_);
lean_ctor_set(v___x_4692_, 0, v___x_4740_);
v___x_4742_ = v___x_4692_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4740_);
lean_ctor_set(v_reuseFailAlloc_4755_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4755_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4755_, 3, v_r_4682_);
lean_ctor_set(v_reuseFailAlloc_4755_, 4, v_r_4670_);
v___x_4742_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
v_isSharedCheck_4749_ = !lean_is_exclusive(v_r_4670_);
if (v_isSharedCheck_4749_ == 0)
{
lean_object* v_unused_4750_; lean_object* v_unused_4751_; lean_object* v_unused_4752_; lean_object* v_unused_4753_; lean_object* v_unused_4754_; 
v_unused_4750_ = lean_ctor_get(v_r_4670_, 4);
lean_dec(v_unused_4750_);
v_unused_4751_ = lean_ctor_get(v_r_4670_, 3);
lean_dec(v_unused_4751_);
v_unused_4752_ = lean_ctor_get(v_r_4670_, 2);
lean_dec(v_unused_4752_);
v_unused_4753_ = lean_ctor_get(v_r_4670_, 1);
lean_dec(v_unused_4753_);
v_unused_4754_ = lean_ctor_get(v_r_4670_, 0);
lean_dec(v_unused_4754_);
v___x_4744_ = v_r_4670_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_dec(v_r_4670_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 4, v___x_4742_);
lean_ctor_set(v___x_4744_, 3, v_l_4681_);
lean_ctor_set(v___x_4744_, 2, v_v_4680_);
lean_ctor_set(v___x_4744_, 1, v_k_4679_);
lean_ctor_set(v___x_4744_, 0, v___x_4738_);
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v_k_4679_);
lean_ctor_set(v_reuseFailAlloc_4748_, 2, v_v_4680_);
lean_ctor_set(v_reuseFailAlloc_4748_, 3, v_l_4681_);
lean_ctor_set(v_reuseFailAlloc_4748_, 4, v___x_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4762_; 
v_l_4762_ = lean_ctor_get(v_impl_4675_, 3);
if (lean_obj_tag(v_l_4762_) == 0)
{
lean_object* v_r_4763_; lean_object* v_k_4764_; lean_object* v_v_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4776_; 
lean_inc_ref(v_l_4762_);
v_r_4763_ = lean_ctor_get(v_impl_4675_, 4);
v_k_4764_ = lean_ctor_get(v_impl_4675_, 1);
v_v_4765_ = lean_ctor_get(v_impl_4675_, 2);
v_isSharedCheck_4776_ = !lean_is_exclusive(v_impl_4675_);
if (v_isSharedCheck_4776_ == 0)
{
lean_object* v_unused_4777_; lean_object* v_unused_4778_; 
v_unused_4777_ = lean_ctor_get(v_impl_4675_, 3);
lean_dec(v_unused_4777_);
v_unused_4778_ = lean_ctor_get(v_impl_4675_, 0);
lean_dec(v_unused_4778_);
v___x_4767_ = v_impl_4675_;
v_isShared_4768_ = v_isSharedCheck_4776_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_r_4763_);
lean_inc(v_v_4765_);
lean_inc(v_k_4764_);
lean_dec(v_impl_4675_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4776_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4769_; lean_object* v___x_4771_; 
v___x_4769_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4763_);
if (v_isShared_4768_ == 0)
{
lean_ctor_set(v___x_4767_, 3, v_r_4763_);
lean_ctor_set(v___x_4767_, 2, v_v_4668_);
lean_ctor_set(v___x_4767_, 1, v_k_4667_);
lean_ctor_set(v___x_4767_, 0, v___x_4676_);
v___x_4771_ = v___x_4767_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4676_);
lean_ctor_set(v_reuseFailAlloc_4775_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4775_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4775_, 3, v_r_4763_);
lean_ctor_set(v_reuseFailAlloc_4775_, 4, v_r_4763_);
v___x_4771_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4773_; 
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v___x_4771_);
lean_ctor_set(v___x_4672_, 3, v_l_4762_);
lean_ctor_set(v___x_4672_, 2, v_v_4765_);
lean_ctor_set(v___x_4672_, 1, v_k_4764_);
lean_ctor_set(v___x_4672_, 0, v___x_4769_);
v___x_4773_ = v___x_4672_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4769_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v_k_4764_);
lean_ctor_set(v_reuseFailAlloc_4774_, 2, v_v_4765_);
lean_ctor_set(v_reuseFailAlloc_4774_, 3, v_l_4762_);
lean_ctor_set(v_reuseFailAlloc_4774_, 4, v___x_4771_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
else
{
lean_object* v_r_4779_; 
v_r_4779_ = lean_ctor_get(v_impl_4675_, 4);
lean_inc(v_r_4779_);
if (lean_obj_tag(v_r_4779_) == 0)
{
lean_object* v_k_4780_; lean_object* v_v_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4804_; 
lean_inc(v_l_4762_);
v_k_4780_ = lean_ctor_get(v_impl_4675_, 1);
v_v_4781_ = lean_ctor_get(v_impl_4675_, 2);
v_isSharedCheck_4804_ = !lean_is_exclusive(v_impl_4675_);
if (v_isSharedCheck_4804_ == 0)
{
lean_object* v_unused_4805_; lean_object* v_unused_4806_; lean_object* v_unused_4807_; 
v_unused_4805_ = lean_ctor_get(v_impl_4675_, 4);
lean_dec(v_unused_4805_);
v_unused_4806_ = lean_ctor_get(v_impl_4675_, 3);
lean_dec(v_unused_4806_);
v_unused_4807_ = lean_ctor_get(v_impl_4675_, 0);
lean_dec(v_unused_4807_);
v___x_4783_ = v_impl_4675_;
v_isShared_4784_ = v_isSharedCheck_4804_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_v_4781_);
lean_inc(v_k_4780_);
lean_dec(v_impl_4675_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4804_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v_k_4785_; lean_object* v_v_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4800_; 
v_k_4785_ = lean_ctor_get(v_r_4779_, 1);
v_v_4786_ = lean_ctor_get(v_r_4779_, 2);
v_isSharedCheck_4800_ = !lean_is_exclusive(v_r_4779_);
if (v_isSharedCheck_4800_ == 0)
{
lean_object* v_unused_4801_; lean_object* v_unused_4802_; lean_object* v_unused_4803_; 
v_unused_4801_ = lean_ctor_get(v_r_4779_, 4);
lean_dec(v_unused_4801_);
v_unused_4802_ = lean_ctor_get(v_r_4779_, 3);
lean_dec(v_unused_4802_);
v_unused_4803_ = lean_ctor_get(v_r_4779_, 0);
lean_dec(v_unused_4803_);
v___x_4788_ = v_r_4779_;
v_isShared_4789_ = v_isSharedCheck_4800_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_v_4786_);
lean_inc(v_k_4785_);
lean_dec(v_r_4779_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4800_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4790_; lean_object* v___x_4792_; 
v___x_4790_ = lean_unsigned_to_nat(3u);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 4, v_l_4762_);
lean_ctor_set(v___x_4788_, 3, v_l_4762_);
lean_ctor_set(v___x_4788_, 2, v_v_4781_);
lean_ctor_set(v___x_4788_, 1, v_k_4780_);
lean_ctor_set(v___x_4788_, 0, v___x_4676_);
v___x_4792_ = v___x_4788_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4676_);
lean_ctor_set(v_reuseFailAlloc_4799_, 1, v_k_4780_);
lean_ctor_set(v_reuseFailAlloc_4799_, 2, v_v_4781_);
lean_ctor_set(v_reuseFailAlloc_4799_, 3, v_l_4762_);
lean_ctor_set(v_reuseFailAlloc_4799_, 4, v_l_4762_);
v___x_4792_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
lean_object* v___x_4794_; 
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 4, v_l_4762_);
lean_ctor_set(v___x_4783_, 2, v_v_4668_);
lean_ctor_set(v___x_4783_, 1, v_k_4667_);
lean_ctor_set(v___x_4783_, 0, v___x_4676_);
v___x_4794_ = v___x_4783_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4676_);
lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4798_, 3, v_l_4762_);
lean_ctor_set(v_reuseFailAlloc_4798_, 4, v_l_4762_);
v___x_4794_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
lean_object* v___x_4796_; 
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v___x_4794_);
lean_ctor_set(v___x_4672_, 3, v___x_4792_);
lean_ctor_set(v___x_4672_, 2, v_v_4786_);
lean_ctor_set(v___x_4672_, 1, v_k_4785_);
lean_ctor_set(v___x_4672_, 0, v___x_4790_);
v___x_4796_ = v___x_4672_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4790_);
lean_ctor_set(v_reuseFailAlloc_4797_, 1, v_k_4785_);
lean_ctor_set(v_reuseFailAlloc_4797_, 2, v_v_4786_);
lean_ctor_set(v_reuseFailAlloc_4797_, 3, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4797_, 4, v___x_4794_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
}
}
else
{
lean_object* v___x_4808_; lean_object* v___x_4810_; 
v___x_4808_ = lean_unsigned_to_nat(2u);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v_r_4779_);
lean_ctor_set(v___x_4672_, 3, v_impl_4675_);
lean_ctor_set(v___x_4672_, 0, v___x_4808_);
v___x_4810_ = v___x_4672_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v___x_4808_);
lean_ctor_set(v_reuseFailAlloc_4811_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4811_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4811_, 3, v_impl_4675_);
lean_ctor_set(v_reuseFailAlloc_4811_, 4, v_r_4779_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4813_; 
lean_dec(v_v_4668_);
lean_dec(v_k_4667_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 2, v_v_4664_);
lean_ctor_set(v___x_4672_, 1, v_k_4663_);
v___x_4813_ = v___x_4672_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_size_4666_);
lean_ctor_set(v_reuseFailAlloc_4814_, 1, v_k_4663_);
lean_ctor_set(v_reuseFailAlloc_4814_, 2, v_v_4664_);
lean_ctor_set(v_reuseFailAlloc_4814_, 3, v_l_4669_);
lean_ctor_set(v_reuseFailAlloc_4814_, 4, v_r_4670_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
default: 
{
lean_object* v_impl_4815_; lean_object* v___x_4816_; 
lean_dec(v_size_4666_);
v_impl_4815_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4663_, v_v_4664_, v_r_4670_);
v___x_4816_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4669_) == 0)
{
lean_object* v_size_4817_; lean_object* v_size_4818_; lean_object* v_k_4819_; lean_object* v_v_4820_; lean_object* v_l_4821_; lean_object* v_r_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; uint8_t v___x_4825_; 
v_size_4817_ = lean_ctor_get(v_l_4669_, 0);
v_size_4818_ = lean_ctor_get(v_impl_4815_, 0);
v_k_4819_ = lean_ctor_get(v_impl_4815_, 1);
v_v_4820_ = lean_ctor_get(v_impl_4815_, 2);
v_l_4821_ = lean_ctor_get(v_impl_4815_, 3);
lean_inc(v_l_4821_);
v_r_4822_ = lean_ctor_get(v_impl_4815_, 4);
v___x_4823_ = lean_unsigned_to_nat(3u);
v___x_4824_ = lean_nat_mul(v___x_4823_, v_size_4817_);
v___x_4825_ = lean_nat_dec_lt(v___x_4824_, v_size_4818_);
lean_dec(v___x_4824_);
if (v___x_4825_ == 0)
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4829_; 
lean_dec(v_l_4821_);
v___x_4826_ = lean_nat_add(v___x_4816_, v_size_4817_);
v___x_4827_ = lean_nat_add(v___x_4826_, v_size_4818_);
lean_dec(v___x_4826_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v_impl_4815_);
lean_ctor_set(v___x_4672_, 0, v___x_4827_);
v___x_4829_ = v___x_4672_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4830_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4830_, 3, v_l_4669_);
lean_ctor_set(v_reuseFailAlloc_4830_, 4, v_impl_4815_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
else
{
lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4894_; 
lean_inc(v_r_4822_);
lean_inc(v_v_4820_);
lean_inc(v_k_4819_);
lean_inc(v_size_4818_);
v_isSharedCheck_4894_ = !lean_is_exclusive(v_impl_4815_);
if (v_isSharedCheck_4894_ == 0)
{
lean_object* v_unused_4895_; lean_object* v_unused_4896_; lean_object* v_unused_4897_; lean_object* v_unused_4898_; lean_object* v_unused_4899_; 
v_unused_4895_ = lean_ctor_get(v_impl_4815_, 4);
lean_dec(v_unused_4895_);
v_unused_4896_ = lean_ctor_get(v_impl_4815_, 3);
lean_dec(v_unused_4896_);
v_unused_4897_ = lean_ctor_get(v_impl_4815_, 2);
lean_dec(v_unused_4897_);
v_unused_4898_ = lean_ctor_get(v_impl_4815_, 1);
lean_dec(v_unused_4898_);
v_unused_4899_ = lean_ctor_get(v_impl_4815_, 0);
lean_dec(v_unused_4899_);
v___x_4832_ = v_impl_4815_;
v_isShared_4833_ = v_isSharedCheck_4894_;
goto v_resetjp_4831_;
}
else
{
lean_dec(v_impl_4815_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4894_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v_size_4834_; lean_object* v_k_4835_; lean_object* v_v_4836_; lean_object* v_l_4837_; lean_object* v_r_4838_; lean_object* v_size_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; uint8_t v___x_4842_; 
v_size_4834_ = lean_ctor_get(v_l_4821_, 0);
v_k_4835_ = lean_ctor_get(v_l_4821_, 1);
v_v_4836_ = lean_ctor_get(v_l_4821_, 2);
v_l_4837_ = lean_ctor_get(v_l_4821_, 3);
v_r_4838_ = lean_ctor_get(v_l_4821_, 4);
v_size_4839_ = lean_ctor_get(v_r_4822_, 0);
v___x_4840_ = lean_unsigned_to_nat(2u);
v___x_4841_ = lean_nat_mul(v___x_4840_, v_size_4839_);
v___x_4842_ = lean_nat_dec_lt(v_size_4834_, v___x_4841_);
lean_dec(v___x_4841_);
if (v___x_4842_ == 0)
{
lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4870_; 
lean_inc(v_r_4838_);
lean_inc(v_l_4837_);
lean_inc(v_v_4836_);
lean_inc(v_k_4835_);
v_isSharedCheck_4870_ = !lean_is_exclusive(v_l_4821_);
if (v_isSharedCheck_4870_ == 0)
{
lean_object* v_unused_4871_; lean_object* v_unused_4872_; lean_object* v_unused_4873_; lean_object* v_unused_4874_; lean_object* v_unused_4875_; 
v_unused_4871_ = lean_ctor_get(v_l_4821_, 4);
lean_dec(v_unused_4871_);
v_unused_4872_ = lean_ctor_get(v_l_4821_, 3);
lean_dec(v_unused_4872_);
v_unused_4873_ = lean_ctor_get(v_l_4821_, 2);
lean_dec(v_unused_4873_);
v_unused_4874_ = lean_ctor_get(v_l_4821_, 1);
lean_dec(v_unused_4874_);
v_unused_4875_ = lean_ctor_get(v_l_4821_, 0);
lean_dec(v_unused_4875_);
v___x_4844_ = v_l_4821_;
v_isShared_4845_ = v_isSharedCheck_4870_;
goto v_resetjp_4843_;
}
else
{
lean_dec(v_l_4821_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4870_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___y_4849_; lean_object* v___y_4850_; lean_object* v___y_4851_; lean_object* v___y_4860_; 
v___x_4846_ = lean_nat_add(v___x_4816_, v_size_4817_);
v___x_4847_ = lean_nat_add(v___x_4846_, v_size_4818_);
lean_dec(v_size_4818_);
if (lean_obj_tag(v_l_4837_) == 0)
{
lean_object* v_size_4868_; 
v_size_4868_ = lean_ctor_get(v_l_4837_, 0);
lean_inc(v_size_4868_);
v___y_4860_ = v_size_4868_;
goto v___jp_4859_;
}
else
{
lean_object* v___x_4869_; 
v___x_4869_ = lean_unsigned_to_nat(0u);
v___y_4860_ = v___x_4869_;
goto v___jp_4859_;
}
v___jp_4848_:
{
lean_object* v___x_4852_; lean_object* v___x_4854_; 
v___x_4852_ = lean_nat_add(v___y_4850_, v___y_4851_);
lean_dec(v___y_4851_);
lean_dec(v___y_4850_);
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 4, v_r_4822_);
lean_ctor_set(v___x_4844_, 3, v_r_4838_);
lean_ctor_set(v___x_4844_, 2, v_v_4820_);
lean_ctor_set(v___x_4844_, 1, v_k_4819_);
lean_ctor_set(v___x_4844_, 0, v___x_4852_);
v___x_4854_ = v___x_4844_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4852_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_k_4819_);
lean_ctor_set(v_reuseFailAlloc_4858_, 2, v_v_4820_);
lean_ctor_set(v_reuseFailAlloc_4858_, 3, v_r_4838_);
lean_ctor_set(v_reuseFailAlloc_4858_, 4, v_r_4822_);
v___x_4854_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
lean_object* v___x_4856_; 
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 4, v___x_4854_);
lean_ctor_set(v___x_4832_, 3, v___y_4849_);
lean_ctor_set(v___x_4832_, 2, v_v_4836_);
lean_ctor_set(v___x_4832_, 1, v_k_4835_);
lean_ctor_set(v___x_4832_, 0, v___x_4847_);
v___x_4856_ = v___x_4832_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4847_);
lean_ctor_set(v_reuseFailAlloc_4857_, 1, v_k_4835_);
lean_ctor_set(v_reuseFailAlloc_4857_, 2, v_v_4836_);
lean_ctor_set(v_reuseFailAlloc_4857_, 3, v___y_4849_);
lean_ctor_set(v_reuseFailAlloc_4857_, 4, v___x_4854_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
v___jp_4859_:
{
lean_object* v___x_4861_; lean_object* v___x_4863_; 
v___x_4861_ = lean_nat_add(v___x_4846_, v___y_4860_);
lean_dec(v___y_4860_);
lean_dec(v___x_4846_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v_l_4837_);
lean_ctor_set(v___x_4672_, 0, v___x_4861_);
v___x_4863_ = v___x_4672_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4861_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4867_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4867_, 3, v_l_4669_);
lean_ctor_set(v_reuseFailAlloc_4867_, 4, v_l_4837_);
v___x_4863_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
lean_object* v___x_4864_; 
v___x_4864_ = lean_nat_add(v___x_4816_, v_size_4839_);
if (lean_obj_tag(v_r_4838_) == 0)
{
lean_object* v_size_4865_; 
v_size_4865_ = lean_ctor_get(v_r_4838_, 0);
lean_inc(v_size_4865_);
v___y_4849_ = v___x_4863_;
v___y_4850_ = v___x_4864_;
v___y_4851_ = v_size_4865_;
goto v___jp_4848_;
}
else
{
lean_object* v___x_4866_; 
v___x_4866_ = lean_unsigned_to_nat(0u);
v___y_4849_ = v___x_4863_;
v___y_4850_ = v___x_4864_;
v___y_4851_ = v___x_4866_;
goto v___jp_4848_;
}
}
}
}
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4880_; 
lean_del_object(v___x_4672_);
v___x_4876_ = lean_nat_add(v___x_4816_, v_size_4817_);
v___x_4877_ = lean_nat_add(v___x_4876_, v_size_4818_);
lean_dec(v_size_4818_);
v___x_4878_ = lean_nat_add(v___x_4876_, v_size_4834_);
lean_dec(v___x_4876_);
lean_inc_ref(v_l_4669_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 4, v_l_4821_);
lean_ctor_set(v___x_4832_, 3, v_l_4669_);
lean_ctor_set(v___x_4832_, 2, v_v_4668_);
lean_ctor_set(v___x_4832_, 1, v_k_4667_);
lean_ctor_set(v___x_4832_, 0, v___x_4878_);
v___x_4880_ = v___x_4832_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4878_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4893_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4893_, 3, v_l_4669_);
lean_ctor_set(v_reuseFailAlloc_4893_, 4, v_l_4821_);
v___x_4880_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
v_isSharedCheck_4887_ = !lean_is_exclusive(v_l_4669_);
if (v_isSharedCheck_4887_ == 0)
{
lean_object* v_unused_4888_; lean_object* v_unused_4889_; lean_object* v_unused_4890_; lean_object* v_unused_4891_; lean_object* v_unused_4892_; 
v_unused_4888_ = lean_ctor_get(v_l_4669_, 4);
lean_dec(v_unused_4888_);
v_unused_4889_ = lean_ctor_get(v_l_4669_, 3);
lean_dec(v_unused_4889_);
v_unused_4890_ = lean_ctor_get(v_l_4669_, 2);
lean_dec(v_unused_4890_);
v_unused_4891_ = lean_ctor_get(v_l_4669_, 1);
lean_dec(v_unused_4891_);
v_unused_4892_ = lean_ctor_get(v_l_4669_, 0);
lean_dec(v_unused_4892_);
v___x_4882_ = v_l_4669_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_dec(v_l_4669_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 4, v_r_4822_);
lean_ctor_set(v___x_4882_, 3, v___x_4880_);
lean_ctor_set(v___x_4882_, 2, v_v_4820_);
lean_ctor_set(v___x_4882_, 1, v_k_4819_);
lean_ctor_set(v___x_4882_, 0, v___x_4877_);
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4877_);
lean_ctor_set(v_reuseFailAlloc_4886_, 1, v_k_4819_);
lean_ctor_set(v_reuseFailAlloc_4886_, 2, v_v_4820_);
lean_ctor_set(v_reuseFailAlloc_4886_, 3, v___x_4880_);
lean_ctor_set(v_reuseFailAlloc_4886_, 4, v_r_4822_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4900_; 
v_l_4900_ = lean_ctor_get(v_impl_4815_, 3);
lean_inc(v_l_4900_);
if (lean_obj_tag(v_l_4900_) == 0)
{
lean_object* v_r_4901_; lean_object* v_k_4902_; lean_object* v_v_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4926_; 
v_r_4901_ = lean_ctor_get(v_impl_4815_, 4);
v_k_4902_ = lean_ctor_get(v_impl_4815_, 1);
v_v_4903_ = lean_ctor_get(v_impl_4815_, 2);
v_isSharedCheck_4926_ = !lean_is_exclusive(v_impl_4815_);
if (v_isSharedCheck_4926_ == 0)
{
lean_object* v_unused_4927_; lean_object* v_unused_4928_; 
v_unused_4927_ = lean_ctor_get(v_impl_4815_, 3);
lean_dec(v_unused_4927_);
v_unused_4928_ = lean_ctor_get(v_impl_4815_, 0);
lean_dec(v_unused_4928_);
v___x_4905_ = v_impl_4815_;
v_isShared_4906_ = v_isSharedCheck_4926_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_r_4901_);
lean_inc(v_v_4903_);
lean_inc(v_k_4902_);
lean_dec(v_impl_4815_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4926_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v_k_4907_; lean_object* v_v_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4922_; 
v_k_4907_ = lean_ctor_get(v_l_4900_, 1);
v_v_4908_ = lean_ctor_get(v_l_4900_, 2);
v_isSharedCheck_4922_ = !lean_is_exclusive(v_l_4900_);
if (v_isSharedCheck_4922_ == 0)
{
lean_object* v_unused_4923_; lean_object* v_unused_4924_; lean_object* v_unused_4925_; 
v_unused_4923_ = lean_ctor_get(v_l_4900_, 4);
lean_dec(v_unused_4923_);
v_unused_4924_ = lean_ctor_get(v_l_4900_, 3);
lean_dec(v_unused_4924_);
v_unused_4925_ = lean_ctor_get(v_l_4900_, 0);
lean_dec(v_unused_4925_);
v___x_4910_ = v_l_4900_;
v_isShared_4911_ = v_isSharedCheck_4922_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_v_4908_);
lean_inc(v_k_4907_);
lean_dec(v_l_4900_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4922_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4912_; lean_object* v___x_4914_; 
v___x_4912_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4901_, 2);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 4, v_r_4901_);
lean_ctor_set(v___x_4910_, 3, v_r_4901_);
lean_ctor_set(v___x_4910_, 2, v_v_4668_);
lean_ctor_set(v___x_4910_, 1, v_k_4667_);
lean_ctor_set(v___x_4910_, 0, v___x_4816_);
v___x_4914_ = v___x_4910_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4921_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4921_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4921_, 3, v_r_4901_);
lean_ctor_set(v_reuseFailAlloc_4921_, 4, v_r_4901_);
v___x_4914_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
lean_object* v___x_4916_; 
lean_inc(v_r_4901_);
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 3, v_r_4901_);
lean_ctor_set(v___x_4905_, 0, v___x_4816_);
v___x_4916_ = v___x_4905_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_k_4902_);
lean_ctor_set(v_reuseFailAlloc_4920_, 2, v_v_4903_);
lean_ctor_set(v_reuseFailAlloc_4920_, 3, v_r_4901_);
lean_ctor_set(v_reuseFailAlloc_4920_, 4, v_r_4901_);
v___x_4916_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
lean_object* v___x_4918_; 
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v___x_4916_);
lean_ctor_set(v___x_4672_, 3, v___x_4914_);
lean_ctor_set(v___x_4672_, 2, v_v_4908_);
lean_ctor_set(v___x_4672_, 1, v_k_4907_);
lean_ctor_set(v___x_4672_, 0, v___x_4912_);
v___x_4918_ = v___x_4672_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4912_);
lean_ctor_set(v_reuseFailAlloc_4919_, 1, v_k_4907_);
lean_ctor_set(v_reuseFailAlloc_4919_, 2, v_v_4908_);
lean_ctor_set(v_reuseFailAlloc_4919_, 3, v___x_4914_);
lean_ctor_set(v_reuseFailAlloc_4919_, 4, v___x_4916_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
}
}
else
{
lean_object* v_r_4929_; 
v_r_4929_ = lean_ctor_get(v_impl_4815_, 4);
lean_inc(v_r_4929_);
if (lean_obj_tag(v_r_4929_) == 0)
{
lean_object* v_k_4930_; lean_object* v_v_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4942_; 
v_k_4930_ = lean_ctor_get(v_impl_4815_, 1);
v_v_4931_ = lean_ctor_get(v_impl_4815_, 2);
v_isSharedCheck_4942_ = !lean_is_exclusive(v_impl_4815_);
if (v_isSharedCheck_4942_ == 0)
{
lean_object* v_unused_4943_; lean_object* v_unused_4944_; lean_object* v_unused_4945_; 
v_unused_4943_ = lean_ctor_get(v_impl_4815_, 4);
lean_dec(v_unused_4943_);
v_unused_4944_ = lean_ctor_get(v_impl_4815_, 3);
lean_dec(v_unused_4944_);
v_unused_4945_ = lean_ctor_get(v_impl_4815_, 0);
lean_dec(v_unused_4945_);
v___x_4933_ = v_impl_4815_;
v_isShared_4934_ = v_isSharedCheck_4942_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_v_4931_);
lean_inc(v_k_4930_);
lean_dec(v_impl_4815_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4942_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4935_; lean_object* v___x_4937_; 
v___x_4935_ = lean_unsigned_to_nat(3u);
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 4, v_l_4900_);
lean_ctor_set(v___x_4933_, 2, v_v_4668_);
lean_ctor_set(v___x_4933_, 1, v_k_4667_);
lean_ctor_set(v___x_4933_, 0, v___x_4816_);
v___x_4937_ = v___x_4933_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4941_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4941_, 3, v_l_4900_);
lean_ctor_set(v_reuseFailAlloc_4941_, 4, v_l_4900_);
v___x_4937_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
lean_object* v___x_4939_; 
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v_r_4929_);
lean_ctor_set(v___x_4672_, 3, v___x_4937_);
lean_ctor_set(v___x_4672_, 2, v_v_4931_);
lean_ctor_set(v___x_4672_, 1, v_k_4930_);
lean_ctor_set(v___x_4672_, 0, v___x_4935_);
v___x_4939_ = v___x_4672_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4935_);
lean_ctor_set(v_reuseFailAlloc_4940_, 1, v_k_4930_);
lean_ctor_set(v_reuseFailAlloc_4940_, 2, v_v_4931_);
lean_ctor_set(v_reuseFailAlloc_4940_, 3, v___x_4937_);
lean_ctor_set(v_reuseFailAlloc_4940_, 4, v_r_4929_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
}
else
{
lean_object* v___x_4946_; lean_object* v___x_4948_; 
v___x_4946_ = lean_unsigned_to_nat(2u);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v_impl_4815_);
lean_ctor_set(v___x_4672_, 3, v_r_4929_);
lean_ctor_set(v___x_4672_, 0, v___x_4946_);
v___x_4948_ = v___x_4672_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_k_4667_);
lean_ctor_set(v_reuseFailAlloc_4949_, 2, v_v_4668_);
lean_ctor_set(v_reuseFailAlloc_4949_, 3, v_r_4929_);
lean_ctor_set(v_reuseFailAlloc_4949_, 4, v_impl_4815_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
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
lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4951_ = lean_unsigned_to_nat(1u);
v___x_4952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4951_);
lean_ctor_set(v___x_4952_, 1, v_k_4663_);
lean_ctor_set(v___x_4952_, 2, v_v_4664_);
lean_ctor_set(v___x_4952_, 3, v_t_4665_);
lean_ctor_set(v___x_4952_, 4, v_t_4665_);
return v___x_4952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object* v_as_4953_, size_t v_sz_4954_, size_t v_i_4955_, lean_object* v_b_4956_){
_start:
{
uint8_t v___x_4957_; 
v___x_4957_ = lean_usize_dec_lt(v_i_4955_, v_sz_4954_);
if (v___x_4957_ == 0)
{
return v_b_4956_;
}
else
{
lean_object* v_a_4958_; lean_object* v_fst_4959_; lean_object* v_snd_4960_; lean_object* v_r_4961_; size_t v___x_4962_; size_t v___x_4963_; 
v_a_4958_ = lean_array_uget_borrowed(v_as_4953_, v_i_4955_);
v_fst_4959_ = lean_ctor_get(v_a_4958_, 0);
v_snd_4960_ = lean_ctor_get(v_a_4958_, 1);
lean_inc(v_snd_4960_);
lean_inc(v_fst_4959_);
v_r_4961_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_fst_4959_, v_snd_4960_, v_b_4956_);
v___x_4962_ = ((size_t)1ULL);
v___x_4963_ = lean_usize_add(v_i_4955_, v___x_4962_);
v_i_4955_ = v___x_4963_;
v_b_4956_ = v_r_4961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object* v_as_4965_, lean_object* v_sz_4966_, lean_object* v_i_4967_, lean_object* v_b_4968_){
_start:
{
size_t v_sz_boxed_4969_; size_t v_i_boxed_4970_; lean_object* v_res_4971_; 
v_sz_boxed_4969_ = lean_unbox_usize(v_sz_4966_);
lean_dec(v_sz_4966_);
v_i_boxed_4970_ = lean_unbox_usize(v_i_4967_);
lean_dec(v_i_4967_);
v_res_4971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v_as_4965_, v_sz_boxed_4969_, v_i_boxed_4970_, v_b_4968_);
lean_dec_ref(v_as_4965_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object* v_a_4974_, lean_object* v_x_4975_){
_start:
{
lean_object* v___y_4977_; 
if (lean_obj_tag(v_x_4975_) == 0)
{
lean_object* v___x_4980_; 
v___x_4980_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___y_4977_ = v___x_4980_;
goto v___jp_4976_;
}
else
{
lean_object* v_val_4981_; 
v_val_4981_ = lean_ctor_get(v_x_4975_, 0);
lean_inc(v_val_4981_);
lean_dec_ref_known(v_x_4975_, 1);
v___y_4977_ = v_val_4981_;
goto v___jp_4976_;
}
v___jp_4976_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = lean_array_push(v___y_4977_, v_a_4974_);
v___x_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
return v___x_4979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_x_4984_){
_start:
{
if (lean_obj_tag(v_x_4984_) == 0)
{
lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v_val_4987_; lean_object* v___x_4988_; 
v___x_4985_ = lean_box(0);
v___x_4986_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4982_, v___x_4985_);
v_val_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_val_4987_);
lean_dec(v___x_4986_);
v___x_4988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4988_, 0, v_a_4983_);
lean_ctor_set(v___x_4988_, 1, v_val_4987_);
lean_ctor_set(v___x_4988_, 2, v_x_4984_);
return v___x_4988_;
}
else
{
lean_object* v_key_4989_; lean_object* v_value_4990_; lean_object* v_tail_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_5006_; 
v_key_4989_ = lean_ctor_get(v_x_4984_, 0);
v_value_4990_ = lean_ctor_get(v_x_4984_, 1);
v_tail_4991_ = lean_ctor_get(v_x_4984_, 2);
v_isSharedCheck_5006_ = !lean_is_exclusive(v_x_4984_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4993_ = v_x_4984_;
v_isShared_4994_ = v_isSharedCheck_5006_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_tail_4991_);
lean_inc(v_value_4990_);
lean_inc(v_key_4989_);
lean_dec(v_x_4984_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_5006_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
uint8_t v___x_4995_; 
v___x_4995_ = lean_name_eq(v_key_4989_, v_a_4983_);
if (v___x_4995_ == 0)
{
lean_object* v_tail_4996_; lean_object* v___x_4998_; 
v_tail_4996_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4982_, v_a_4983_, v_tail_4991_);
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 2, v_tail_4996_);
v___x_4998_ = v___x_4993_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_key_4989_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v_value_4990_);
lean_ctor_set(v_reuseFailAlloc_4999_, 2, v_tail_4996_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
else
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v_val_5002_; lean_object* v___x_5004_; 
lean_dec(v_key_4989_);
v___x_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5000_, 0, v_value_4990_);
v___x_5001_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4982_, v___x_5000_);
v_val_5002_ = lean_ctor_get(v___x_5001_, 0);
lean_inc(v_val_5002_);
lean_dec(v___x_5001_);
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v_val_5002_);
lean_ctor_set(v___x_4993_, 0, v_a_4983_);
v___x_5004_ = v___x_4993_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4983_);
lean_ctor_set(v_reuseFailAlloc_5005_, 1, v_val_5002_);
lean_ctor_set(v_reuseFailAlloc_5005_, 2, v_tail_4991_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_5007_, lean_object* v_x_5008_){
_start:
{
if (lean_obj_tag(v_x_5008_) == 0)
{
return v_x_5007_;
}
else
{
lean_object* v_key_5009_; lean_object* v_value_5010_; lean_object* v_tail_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5037_; 
v_key_5009_ = lean_ctor_get(v_x_5008_, 0);
v_value_5010_ = lean_ctor_get(v_x_5008_, 1);
v_tail_5011_ = lean_ctor_get(v_x_5008_, 2);
v_isSharedCheck_5037_ = !lean_is_exclusive(v_x_5008_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5013_ = v_x_5008_;
v_isShared_5014_ = v_isSharedCheck_5037_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_tail_5011_);
lean_inc(v_value_5010_);
lean_inc(v_key_5009_);
lean_dec(v_x_5008_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5037_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
lean_object* v___x_5015_; uint64_t v___y_5017_; 
v___x_5015_ = lean_array_get_size(v_x_5007_);
if (lean_obj_tag(v_key_5009_) == 0)
{
uint64_t v___x_5035_; 
v___x_5035_ = 1723ULL;
v___y_5017_ = v___x_5035_;
goto v___jp_5016_;
}
else
{
uint64_t v_hash_5036_; 
v_hash_5036_ = lean_ctor_get_uint64(v_key_5009_, sizeof(void*)*2);
v___y_5017_ = v_hash_5036_;
goto v___jp_5016_;
}
v___jp_5016_:
{
uint64_t v___x_5018_; uint64_t v___x_5019_; uint64_t v_fold_5020_; uint64_t v___x_5021_; uint64_t v___x_5022_; uint64_t v___x_5023_; size_t v___x_5024_; size_t v___x_5025_; size_t v___x_5026_; size_t v___x_5027_; size_t v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5031_; 
v___x_5018_ = 32ULL;
v___x_5019_ = lean_uint64_shift_right(v___y_5017_, v___x_5018_);
v_fold_5020_ = lean_uint64_xor(v___y_5017_, v___x_5019_);
v___x_5021_ = 16ULL;
v___x_5022_ = lean_uint64_shift_right(v_fold_5020_, v___x_5021_);
v___x_5023_ = lean_uint64_xor(v_fold_5020_, v___x_5022_);
v___x_5024_ = lean_uint64_to_usize(v___x_5023_);
v___x_5025_ = lean_usize_of_nat(v___x_5015_);
v___x_5026_ = ((size_t)1ULL);
v___x_5027_ = lean_usize_sub(v___x_5025_, v___x_5026_);
v___x_5028_ = lean_usize_land(v___x_5024_, v___x_5027_);
v___x_5029_ = lean_array_uget_borrowed(v_x_5007_, v___x_5028_);
lean_inc(v___x_5029_);
if (v_isShared_5014_ == 0)
{
lean_ctor_set(v___x_5013_, 2, v___x_5029_);
v___x_5031_ = v___x_5013_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_key_5009_);
lean_ctor_set(v_reuseFailAlloc_5034_, 1, v_value_5010_);
lean_ctor_set(v_reuseFailAlloc_5034_, 2, v___x_5029_);
v___x_5031_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
lean_object* v___x_5032_; 
v___x_5032_ = lean_array_uset(v_x_5007_, v___x_5028_, v___x_5031_);
v_x_5007_ = v___x_5032_;
v_x_5008_ = v_tail_5011_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object* v_i_5038_, lean_object* v_source_5039_, lean_object* v_target_5040_){
_start:
{
lean_object* v___x_5041_; uint8_t v___x_5042_; 
v___x_5041_ = lean_array_get_size(v_source_5039_);
v___x_5042_ = lean_nat_dec_lt(v_i_5038_, v___x_5041_);
if (v___x_5042_ == 0)
{
lean_dec_ref(v_source_5039_);
lean_dec(v_i_5038_);
return v_target_5040_;
}
else
{
lean_object* v_es_5043_; lean_object* v___x_5044_; lean_object* v_source_5045_; lean_object* v_target_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v_es_5043_ = lean_array_fget(v_source_5039_, v_i_5038_);
v___x_5044_ = lean_box(0);
v_source_5045_ = lean_array_fset(v_source_5039_, v_i_5038_, v___x_5044_);
v_target_5046_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_target_5040_, v_es_5043_);
v___x_5047_ = lean_unsigned_to_nat(1u);
v___x_5048_ = lean_nat_add(v_i_5038_, v___x_5047_);
lean_dec(v_i_5038_);
v_i_5038_ = v___x_5048_;
v_source_5039_ = v_source_5045_;
v_target_5040_ = v_target_5046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object* v_data_5050_){
_start:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v_nbuckets_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5051_ = lean_array_get_size(v_data_5050_);
v___x_5052_ = lean_unsigned_to_nat(2u);
v_nbuckets_5053_ = lean_nat_mul(v___x_5051_, v___x_5052_);
v___x_5054_ = lean_unsigned_to_nat(0u);
v___x_5055_ = lean_box(0);
v___x_5056_ = lean_mk_array(v_nbuckets_5053_, v___x_5055_);
v___x_5057_ = lean_array_propagate_mark(v_data_5050_, v___x_5056_);
v___x_5058_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_5054_, v_data_5050_, v___x_5057_);
return v___x_5058_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_5059_, lean_object* v_x_5060_){
_start:
{
if (lean_obj_tag(v_x_5060_) == 0)
{
uint8_t v___x_5061_; 
v___x_5061_ = 0;
return v___x_5061_;
}
else
{
lean_object* v_key_5062_; lean_object* v_tail_5063_; uint8_t v___x_5064_; 
v_key_5062_ = lean_ctor_get(v_x_5060_, 0);
v_tail_5063_ = lean_ctor_get(v_x_5060_, 2);
v___x_5064_ = lean_name_eq(v_key_5062_, v_a_5059_);
if (v___x_5064_ == 0)
{
v_x_5060_ = v_tail_5063_;
goto _start;
}
else
{
return v___x_5064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_5066_, lean_object* v_x_5067_){
_start:
{
uint8_t v_res_5068_; lean_object* v_r_5069_; 
v_res_5068_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5066_, v_x_5067_);
lean_dec(v_x_5067_);
lean_dec(v_a_5066_);
v_r_5069_ = lean_box(v_res_5068_);
return v_r_5069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_5070_, lean_object* v_m_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v___y_5074_; size_t v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v_size_5080_; lean_object* v_buckets_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5128_; 
v_size_5080_ = lean_ctor_get(v_m_5071_, 0);
v_buckets_5081_ = lean_ctor_get(v_m_5071_, 1);
v_isSharedCheck_5128_ = !lean_is_exclusive(v_m_5071_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5083_ = v_m_5071_;
v_isShared_5084_ = v_isSharedCheck_5128_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_buckets_5081_);
lean_inc(v_size_5080_);
lean_dec(v_m_5071_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5128_;
goto v_resetjp_5082_;
}
v___jp_5073_:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5078_ = lean_array_uset(v___y_5074_, v___y_5075_, v___y_5076_);
v___x_5079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5079_, 0, v___y_5077_);
lean_ctor_set(v___x_5079_, 1, v___x_5078_);
return v___x_5079_;
}
v_resetjp_5082_:
{
lean_object* v___x_5085_; uint64_t v___y_5087_; 
v___x_5085_ = lean_array_get_size(v_buckets_5081_);
if (lean_obj_tag(v_a_5072_) == 0)
{
uint64_t v___x_5126_; 
v___x_5126_ = 1723ULL;
v___y_5087_ = v___x_5126_;
goto v___jp_5086_;
}
else
{
uint64_t v_hash_5127_; 
v_hash_5127_ = lean_ctor_get_uint64(v_a_5072_, sizeof(void*)*2);
v___y_5087_ = v_hash_5127_;
goto v___jp_5086_;
}
v___jp_5086_:
{
uint64_t v___x_5088_; uint64_t v___x_5089_; uint64_t v_fold_5090_; uint64_t v___x_5091_; uint64_t v___x_5092_; uint64_t v___x_5093_; size_t v___x_5094_; size_t v___x_5095_; size_t v___x_5096_; size_t v___x_5097_; size_t v___x_5098_; lean_object* v_bkt_5099_; uint8_t v___x_5100_; 
v___x_5088_ = 32ULL;
v___x_5089_ = lean_uint64_shift_right(v___y_5087_, v___x_5088_);
v_fold_5090_ = lean_uint64_xor(v___y_5087_, v___x_5089_);
v___x_5091_ = 16ULL;
v___x_5092_ = lean_uint64_shift_right(v_fold_5090_, v___x_5091_);
v___x_5093_ = lean_uint64_xor(v_fold_5090_, v___x_5092_);
v___x_5094_ = lean_uint64_to_usize(v___x_5093_);
v___x_5095_ = lean_usize_of_nat(v___x_5085_);
v___x_5096_ = ((size_t)1ULL);
v___x_5097_ = lean_usize_sub(v___x_5095_, v___x_5096_);
v___x_5098_ = lean_usize_land(v___x_5094_, v___x_5097_);
v_bkt_5099_ = lean_array_uget_borrowed(v_buckets_5081_, v___x_5098_);
v___x_5100_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5072_, v_bkt_5099_);
if (v___x_5100_ == 0)
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v_size_x27_5104_; lean_object* v___x_5105_; lean_object* v_buckets_x27_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; uint8_t v___x_5112_; 
v___x_5101_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_5102_ = lean_array_push(v___x_5101_, v_a_5070_);
v___x_5103_ = lean_unsigned_to_nat(1u);
v_size_x27_5104_ = lean_nat_add(v_size_5080_, v___x_5103_);
lean_dec(v_size_5080_);
lean_inc(v_bkt_5099_);
v___x_5105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5105_, 0, v_a_5072_);
lean_ctor_set(v___x_5105_, 1, v___x_5102_);
lean_ctor_set(v___x_5105_, 2, v_bkt_5099_);
v_buckets_x27_5106_ = lean_array_uset(v_buckets_5081_, v___x_5098_, v___x_5105_);
v___x_5107_ = lean_unsigned_to_nat(4u);
v___x_5108_ = lean_nat_mul(v_size_x27_5104_, v___x_5107_);
v___x_5109_ = lean_unsigned_to_nat(3u);
v___x_5110_ = lean_nat_div(v___x_5108_, v___x_5109_);
lean_dec(v___x_5108_);
v___x_5111_ = lean_array_get_size(v_buckets_x27_5106_);
v___x_5112_ = lean_nat_dec_le(v___x_5110_, v___x_5111_);
lean_dec(v___x_5110_);
if (v___x_5112_ == 0)
{
lean_object* v_val_5113_; lean_object* v___x_5115_; 
v_val_5113_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5106_);
if (v_isShared_5084_ == 0)
{
lean_ctor_set(v___x_5083_, 1, v_val_5113_);
lean_ctor_set(v___x_5083_, 0, v_size_x27_5104_);
v___x_5115_ = v___x_5083_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_size_x27_5104_);
lean_ctor_set(v_reuseFailAlloc_5116_, 1, v_val_5113_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
else
{
lean_object* v___x_5118_; 
if (v_isShared_5084_ == 0)
{
lean_ctor_set(v___x_5083_, 1, v_buckets_x27_5106_);
lean_ctor_set(v___x_5083_, 0, v_size_x27_5104_);
v___x_5118_ = v___x_5083_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_size_x27_5104_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v_buckets_x27_5106_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
else
{
lean_object* v___x_5120_; lean_object* v_buckets_x27_5121_; lean_object* v_bkt_x27_5122_; uint8_t v___x_5123_; 
lean_inc(v_bkt_5099_);
lean_del_object(v___x_5083_);
v___x_5120_ = lean_box(0);
v_buckets_x27_5121_ = lean_array_uset(v_buckets_5081_, v___x_5098_, v___x_5120_);
lean_inc(v_a_5072_);
v_bkt_x27_5122_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5070_, v_a_5072_, v_bkt_5099_);
v___x_5123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5072_, v_bkt_x27_5122_);
lean_dec(v_a_5072_);
if (v___x_5123_ == 0)
{
lean_object* v___x_5124_; lean_object* v___x_5125_; 
v___x_5124_ = lean_unsigned_to_nat(1u);
v___x_5125_ = lean_nat_sub(v_size_5080_, v___x_5124_);
lean_dec(v_size_5080_);
v___y_5074_ = v_buckets_x27_5121_;
v___y_5075_ = v___x_5098_;
v___y_5076_ = v_bkt_x27_5122_;
v___y_5077_ = v___x_5125_;
goto v___jp_5073_;
}
else
{
v___y_5074_ = v_buckets_x27_5121_;
v___y_5075_ = v___x_5098_;
v___y_5076_ = v_bkt_x27_5122_;
v___y_5077_ = v_size_5080_;
goto v___jp_5073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5129_, lean_object* v_as_5130_, size_t v_sz_5131_, size_t v_i_5132_, lean_object* v_b_5133_){
_start:
{
uint8_t v___x_5134_; 
v___x_5134_ = lean_usize_dec_lt(v_i_5132_, v_sz_5131_);
if (v___x_5134_ == 0)
{
lean_dec_ref(v_key_5129_);
return v_b_5133_;
}
else
{
lean_object* v_a_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; size_t v___x_5138_; size_t v___x_5139_; 
v_a_5135_ = lean_array_uget_borrowed(v_as_5130_, v_i_5132_);
lean_inc_ref(v_key_5129_);
lean_inc_n(v_a_5135_, 2);
v___x_5136_ = lean_apply_1(v_key_5129_, v_a_5135_);
v___x_5137_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5135_, v_b_5133_, v___x_5136_);
v___x_5138_ = ((size_t)1ULL);
v___x_5139_ = lean_usize_add(v_i_5132_, v___x_5138_);
v_i_5132_ = v___x_5139_;
v_b_5133_ = v___x_5137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5141_, lean_object* v_as_5142_, lean_object* v_sz_5143_, lean_object* v_i_5144_, lean_object* v_b_5145_){
_start:
{
size_t v_sz_boxed_5146_; size_t v_i_boxed_5147_; lean_object* v_res_5148_; 
v_sz_boxed_5146_ = lean_unbox_usize(v_sz_5143_);
lean_dec(v_sz_5143_);
v_i_boxed_5147_ = lean_unbox_usize(v_i_5144_);
lean_dec(v_i_5144_);
v_res_5148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5141_, v_as_5142_, v_sz_boxed_5146_, v_i_boxed_5147_, v_b_5145_);
lean_dec_ref(v_as_5142_);
return v_res_5148_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5149_ = lean_box(0);
v___x_5150_ = lean_unsigned_to_nat(16u);
v___x_5151_ = lean_mk_array(v___x_5150_, v___x_5149_);
return v___x_5151_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v_groups_5154_; 
v___x_5152_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5153_ = lean_unsigned_to_nat(0u);
v_groups_5154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5154_, 0, v___x_5153_);
lean_ctor_set(v_groups_5154_, 1, v___x_5152_);
return v_groups_5154_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5155_, lean_object* v_xs_5156_){
_start:
{
lean_object* v_groups_5157_; size_t v_sz_5158_; size_t v___x_5159_; lean_object* v___x_5160_; 
v_groups_5157_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5158_ = lean_array_size(v_xs_5156_);
v___x_5159_ = ((size_t)0ULL);
v___x_5160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5155_, v_xs_5156_, v_sz_5158_, v___x_5159_, v_groups_5157_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5161_, lean_object* v_xs_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5161_, v_xs_5162_);
lean_dec_ref(v_xs_5162_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5165_){
_start:
{
lean_object* v___f_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v___f_5167_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5168_ = lean_unsigned_to_nat(0u);
v___x_5169_ = lean_array_get_size(v_infos_5165_);
v___x_5170_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5165_, v___x_5168_, v___x_5169_);
if (lean_obj_tag(v___x_5170_) == 0)
{
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5194_; 
v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5173_ = v___x_5170_;
v_isShared_5174_ = v_isSharedCheck_5194_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5170_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5194_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___y_5176_; lean_object* v___x_5185_; lean_object* v_size_5186_; lean_object* v_buckets_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; uint8_t v___x_5190_; 
v___x_5185_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5167_, v_a_5171_);
v_size_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_size_5186_);
v_buckets_5187_ = lean_ctor_get(v___x_5185_, 1);
lean_inc_ref(v_buckets_5187_);
lean_dec_ref(v___x_5185_);
v___x_5188_ = lean_mk_empty_array_with_capacity(v_size_5186_);
lean_dec(v_size_5186_);
v___x_5189_ = lean_array_get_size(v_buckets_5187_);
v___x_5190_ = lean_nat_dec_lt(v___x_5168_, v___x_5189_);
if (v___x_5190_ == 0)
{
lean_dec_ref(v_buckets_5187_);
v___y_5176_ = v___x_5188_;
goto v___jp_5175_;
}
else
{
size_t v___x_5191_; size_t v___x_5192_; lean_object* v___x_5193_; 
v___x_5191_ = ((size_t)0ULL);
v___x_5192_ = lean_usize_of_nat(v___x_5189_);
v___x_5193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5187_, v___x_5191_, v___x_5192_, v___x_5188_);
lean_dec_ref(v_buckets_5187_);
v___y_5176_ = v___x_5193_;
goto v___jp_5175_;
}
v___jp_5175_:
{
lean_object* v_r_5177_; size_t v_sz_5178_; size_t v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5183_; 
v_r_5177_ = lean_box(1);
v_sz_5178_ = lean_array_size(v___y_5176_);
v___x_5179_ = ((size_t)0ULL);
v___x_5180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5176_, v_sz_5178_, v___x_5179_, v_r_5177_);
lean_dec_ref(v___y_5176_);
v___x_5181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5181_, 0, v_a_5171_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
if (v_isShared_5174_ == 0)
{
lean_ctor_set(v___x_5173_, 0, v___x_5181_);
v___x_5183_ = v___x_5173_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
v_a_5195_ = lean_ctor_get(v___x_5170_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5170_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5170_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v___x_5200_; 
if (v_isShared_5198_ == 0)
{
v___x_5200_ = v___x_5197_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5203_, lean_object* v_a_5204_){
_start:
{
lean_object* v_res_5205_; 
v_res_5205_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5203_);
lean_dec_ref(v_infos_5203_);
return v_res_5205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5206_, lean_object* v_k_5207_, lean_object* v_v_5208_, lean_object* v_t_5209_, lean_object* v_hl_5210_){
_start:
{
lean_object* v___x_5211_; 
v___x_5211_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5207_, v_v_5208_, v_t_5209_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5212_, lean_object* v_key_5213_, lean_object* v_xs_5214_){
_start:
{
lean_object* v___x_5215_; 
v___x_5215_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5213_, v_xs_5214_);
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5216_, lean_object* v_key_5217_, lean_object* v_xs_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5216_, v_key_5217_, v_xs_5218_);
lean_dec_ref(v_xs_5218_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5220_, lean_object* v_a_5221_, lean_object* v_m_5222_, lean_object* v_a_5223_){
_start:
{
lean_object* v___x_5224_; 
v___x_5224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5221_, v_m_5222_, v_a_5223_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5225_, lean_object* v_key_5226_, lean_object* v_as_5227_, size_t v_sz_5228_, size_t v_i_5229_, lean_object* v_b_5230_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5226_, v_as_5227_, v_sz_5228_, v_i_5229_, v_b_5230_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5232_, lean_object* v_key_5233_, lean_object* v_as_5234_, lean_object* v_sz_5235_, lean_object* v_i_5236_, lean_object* v_b_5237_){
_start:
{
size_t v_sz_boxed_5238_; size_t v_i_boxed_5239_; lean_object* v_res_5240_; 
v_sz_boxed_5238_ = lean_unbox_usize(v_sz_5235_);
lean_dec(v_sz_5235_);
v_i_boxed_5239_ = lean_unbox_usize(v_i_5236_);
lean_dec(v_i_5236_);
v_res_5240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5232_, v_key_5233_, v_as_5234_, v_sz_boxed_5238_, v_i_boxed_5239_, v_b_5237_);
lean_dec_ref(v_as_5234_);
return v_res_5240_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5241_, lean_object* v_a_5242_, lean_object* v_x_5243_){
_start:
{
uint8_t v___x_5244_; 
v___x_5244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5242_, v_x_5243_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5245_, lean_object* v_a_5246_, lean_object* v_x_5247_){
_start:
{
uint8_t v_res_5248_; lean_object* v_r_5249_; 
v_res_5248_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5245_, v_a_5246_, v_x_5247_);
lean_dec(v_x_5247_);
lean_dec(v_a_5246_);
v_r_5249_ = lean_box(v_res_5248_);
return v_r_5249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5250_, lean_object* v_data_5251_){
_start:
{
lean_object* v___x_5252_; 
v___x_5252_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5251_);
return v___x_5252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_x_5256_){
_start:
{
lean_object* v___x_5257_; 
v___x_5257_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5254_, v_a_5255_, v_x_5256_);
return v___x_5257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5258_, lean_object* v_i_5259_, lean_object* v_source_5260_, lean_object* v_target_5261_){
_start:
{
lean_object* v___x_5262_; 
v___x_5262_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5259_, v_source_5260_, v_target_5261_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5263_, lean_object* v_x_5264_, lean_object* v_x_5265_){
_start:
{
lean_object* v___x_5266_; 
v___x_5266_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5264_, v_x_5265_);
return v___x_5266_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5267_){
_start:
{
lean_object* v_isSetupFailure_x3f_5268_; 
v_isSetupFailure_x3f_5268_ = lean_ctor_get(v_i_5267_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5268_) == 0)
{
uint8_t v___x_5269_; 
v___x_5269_ = 0;
return v___x_5269_;
}
else
{
lean_object* v_val_5270_; uint8_t v___x_5271_; 
v_val_5270_ = lean_ctor_get(v_isSetupFailure_x3f_5268_, 0);
v___x_5271_ = lean_unbox(v_val_5270_);
if (v___x_5271_ == 0)
{
uint8_t v___x_5272_; 
v___x_5272_ = 1;
return v___x_5272_;
}
else
{
uint8_t v___x_5273_; 
v___x_5273_ = 0;
return v___x_5273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5274_){
_start:
{
uint8_t v_res_5275_; lean_object* v_r_5276_; 
v_res_5275_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5274_);
lean_dec_ref(v_i_5274_);
v_r_5276_ = lean_box(v_res_5275_);
return v_r_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5282_, lean_object* v_path_5283_, lean_object* v_ilean_5284_){
_start:
{
lean_object* v_module_5286_; lean_object* v_directImports_5287_; lean_object* v_references_5288_; lean_object* v_decls_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5341_; 
v_module_5286_ = lean_ctor_get(v_ilean_5284_, 1);
v_directImports_5287_ = lean_ctor_get(v_ilean_5284_, 2);
v_references_5288_ = lean_ctor_get(v_ilean_5284_, 3);
v_decls_5289_ = lean_ctor_get(v_ilean_5284_, 4);
v_isSharedCheck_5341_ = !lean_is_exclusive(v_ilean_5284_);
if (v_isSharedCheck_5341_ == 0)
{
lean_object* v_unused_5342_; 
v_unused_5342_ = lean_ctor_get(v_ilean_5284_, 0);
lean_dec(v_unused_5342_);
v___x_5291_ = v_ilean_5284_;
v_isShared_5292_ = v_isSharedCheck_5341_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_decls_5289_);
lean_inc(v_references_5288_);
lean_inc(v_directImports_5287_);
lean_inc(v_module_5286_);
lean_dec(v_ilean_5284_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5341_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5293_; 
lean_inc(v_module_5286_);
v___x_5293_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5286_);
if (lean_obj_tag(v___x_5293_) == 0)
{
lean_object* v_a_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5332_; 
v_a_5294_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5296_ = v___x_5293_;
v_isShared_5297_ = v_isSharedCheck_5332_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_a_5294_);
lean_dec(v___x_5293_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5332_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
if (lean_obj_tag(v_a_5294_) == 1)
{
lean_object* v_val_5298_; lean_object* v___x_5299_; 
lean_del_object(v___x_5296_);
v_val_5298_ = lean_ctor_get(v_a_5294_, 0);
lean_inc(v_val_5298_);
lean_dec_ref_known(v_a_5294_, 1);
v___x_5299_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5287_);
lean_dec_ref(v_directImports_5287_);
if (lean_obj_tag(v___x_5299_) == 0)
{
lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5320_; 
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5320_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5320_ == 0)
{
v___x_5302_ = v___x_5299_;
v_isShared_5303_ = v_isSharedCheck_5320_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5299_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5320_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v_ileans_5304_; lean_object* v_workers_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5319_; 
v_ileans_5304_ = lean_ctor_get(v_self_5282_, 0);
v_workers_5305_ = lean_ctor_get(v_self_5282_, 1);
v_isSharedCheck_5319_ = !lean_is_exclusive(v_self_5282_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5307_ = v_self_5282_;
v_isShared_5308_ = v_isSharedCheck_5319_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_workers_5305_);
lean_inc(v_ileans_5304_);
lean_dec(v_self_5282_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5319_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 2, v_a_5300_);
lean_ctor_set(v___x_5291_, 1, v_path_5283_);
lean_ctor_set(v___x_5291_, 0, v_val_5298_);
v___x_5310_ = v___x_5291_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_val_5298_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_path_5283_);
lean_ctor_set(v_reuseFailAlloc_5318_, 2, v_a_5300_);
lean_ctor_set(v_reuseFailAlloc_5318_, 3, v_references_5288_);
lean_ctor_set(v_reuseFailAlloc_5318_, 4, v_decls_5289_);
v___x_5310_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
lean_object* v___x_5311_; lean_object* v___x_5313_; 
v___x_5311_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5286_, v___x_5310_, v_ileans_5304_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 0, v___x_5311_);
v___x_5313_ = v___x_5307_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v___x_5311_);
lean_ctor_set(v_reuseFailAlloc_5317_, 1, v_workers_5305_);
v___x_5313_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
lean_object* v___x_5315_; 
if (v_isShared_5303_ == 0)
{
lean_ctor_set(v___x_5302_, 0, v___x_5313_);
v___x_5315_ = v___x_5302_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5313_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
}
}
}
else
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
lean_dec(v_val_5298_);
lean_del_object(v___x_5291_);
lean_dec(v_decls_5289_);
lean_dec(v_references_5288_);
lean_dec(v_module_5286_);
lean_dec_ref(v_path_5283_);
lean_dec_ref(v_self_5282_);
v_a_5321_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5323_ = v___x_5299_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5299_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
else
{
lean_object* v___x_5330_; 
lean_dec(v_a_5294_);
lean_del_object(v___x_5291_);
lean_dec(v_decls_5289_);
lean_dec(v_references_5288_);
lean_dec_ref(v_directImports_5287_);
lean_dec(v_module_5286_);
lean_dec_ref(v_path_5283_);
if (v_isShared_5297_ == 0)
{
lean_ctor_set(v___x_5296_, 0, v_self_5282_);
v___x_5330_ = v___x_5296_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_self_5282_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
else
{
lean_object* v_a_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5340_; 
lean_del_object(v___x_5291_);
lean_dec(v_decls_5289_);
lean_dec(v_references_5288_);
lean_dec_ref(v_directImports_5287_);
lean_dec(v_module_5286_);
lean_dec_ref(v_path_5283_);
lean_dec_ref(v_self_5282_);
v_a_5333_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5340_ == 0)
{
v___x_5335_ = v___x_5293_;
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_a_5333_);
lean_dec(v___x_5293_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5338_; 
if (v_isShared_5336_ == 0)
{
v___x_5338_ = v___x_5335_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5333_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5343_, lean_object* v_path_5344_, lean_object* v_ilean_5345_, lean_object* v_a_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_Lean_Server_References_addIlean(v_self_5343_, v_path_5344_, v_ilean_5345_);
return v_res_5347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5348_, lean_object* v_t_5349_){
_start:
{
if (lean_obj_tag(v_t_5349_) == 0)
{
lean_object* v_v_5350_; lean_object* v_k_5351_; lean_object* v_l_5352_; lean_object* v_r_5353_; lean_object* v_ileanPath_5354_; uint8_t v___x_5355_; 
v_v_5350_ = lean_ctor_get(v_t_5349_, 2);
lean_inc(v_v_5350_);
v_k_5351_ = lean_ctor_get(v_t_5349_, 1);
lean_inc(v_k_5351_);
v_l_5352_ = lean_ctor_get(v_t_5349_, 3);
lean_inc(v_l_5352_);
v_r_5353_ = lean_ctor_get(v_t_5349_, 4);
lean_inc(v_r_5353_);
lean_dec_ref_known(v_t_5349_, 5);
v_ileanPath_5354_ = lean_ctor_get(v_v_5350_, 1);
v___x_5355_ = lean_string_dec_eq(v_ileanPath_5354_, v_path_5348_);
if (v___x_5355_ == 0)
{
lean_object* v_impl_5356_; lean_object* v_impl_5357_; lean_object* v___x_5358_; 
lean_dec(v_k_5351_);
lean_dec(v_v_5350_);
v_impl_5356_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5348_, v_l_5352_);
v_impl_5357_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5348_, v_r_5353_);
v___x_5358_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5356_, v_impl_5357_);
return v___x_5358_;
}
else
{
lean_object* v_impl_5359_; lean_object* v_impl_5360_; lean_object* v___x_5361_; 
v_impl_5359_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5348_, v_l_5352_);
v_impl_5360_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5348_, v_r_5353_);
v___x_5361_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5351_, v_v_5350_, v_impl_5359_, v_impl_5360_);
return v___x_5361_;
}
}
else
{
return v_t_5349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5362_, lean_object* v_t_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5362_, v_t_5363_);
lean_dec_ref(v_path_5362_);
return v_res_5364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5365_, lean_object* v_t_5366_){
_start:
{
if (lean_obj_tag(v_t_5366_) == 0)
{
lean_object* v_k_5367_; lean_object* v_v_5368_; lean_object* v_l_5369_; lean_object* v_r_5370_; lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_6024_; 
v_k_5367_ = lean_ctor_get(v_t_5366_, 1);
v_v_5368_ = lean_ctor_get(v_t_5366_, 2);
v_l_5369_ = lean_ctor_get(v_t_5366_, 3);
v_r_5370_ = lean_ctor_get(v_t_5366_, 4);
v_isSharedCheck_6024_ = !lean_is_exclusive(v_t_5366_);
if (v_isSharedCheck_6024_ == 0)
{
lean_object* v_unused_6025_; 
v_unused_6025_ = lean_ctor_get(v_t_5366_, 0);
lean_dec(v_unused_6025_);
v___x_5372_ = v_t_5366_;
v_isShared_5373_ = v_isSharedCheck_6024_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_r_5370_);
lean_inc(v_l_5369_);
lean_inc(v_v_5368_);
lean_inc(v_k_5367_);
lean_dec(v_t_5366_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_6024_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
uint8_t v___x_5374_; 
v___x_5374_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5365_, v_k_5367_);
switch(v___x_5374_)
{
case 0:
{
lean_object* v_impl_5375_; lean_object* v___x_5376_; 
v_impl_5375_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5365_, v_l_5369_);
v___x_5376_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5375_) == 0)
{
if (lean_obj_tag(v_r_5370_) == 0)
{
lean_object* v_size_5377_; lean_object* v_size_5378_; lean_object* v_k_5379_; lean_object* v_v_5380_; lean_object* v_l_5381_; lean_object* v_r_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; uint8_t v___x_5385_; 
v_size_5377_ = lean_ctor_get(v_impl_5375_, 0);
v_size_5378_ = lean_ctor_get(v_r_5370_, 0);
v_k_5379_ = lean_ctor_get(v_r_5370_, 1);
v_v_5380_ = lean_ctor_get(v_r_5370_, 2);
v_l_5381_ = lean_ctor_get(v_r_5370_, 3);
lean_inc(v_l_5381_);
v_r_5382_ = lean_ctor_get(v_r_5370_, 4);
v___x_5383_ = lean_unsigned_to_nat(3u);
v___x_5384_ = lean_nat_mul(v___x_5383_, v_size_5377_);
v___x_5385_ = lean_nat_dec_lt(v___x_5384_, v_size_5378_);
lean_dec(v___x_5384_);
if (v___x_5385_ == 0)
{
lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5389_; 
lean_dec(v_l_5381_);
v___x_5386_ = lean_nat_add(v___x_5376_, v_size_5377_);
v___x_5387_ = lean_nat_add(v___x_5386_, v_size_5378_);
lean_dec(v___x_5386_);
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 3, v_impl_5375_);
lean_ctor_set(v___x_5372_, 0, v___x_5387_);
v___x_5389_ = v___x_5372_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v___x_5387_);
lean_ctor_set(v_reuseFailAlloc_5390_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5390_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5390_, 3, v_impl_5375_);
lean_ctor_set(v_reuseFailAlloc_5390_, 4, v_r_5370_);
v___x_5389_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
return v___x_5389_;
}
}
else
{
lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5454_; 
lean_inc(v_r_5382_);
lean_inc(v_v_5380_);
lean_inc(v_k_5379_);
lean_inc(v_size_5378_);
v_isSharedCheck_5454_ = !lean_is_exclusive(v_r_5370_);
if (v_isSharedCheck_5454_ == 0)
{
lean_object* v_unused_5455_; lean_object* v_unused_5456_; lean_object* v_unused_5457_; lean_object* v_unused_5458_; lean_object* v_unused_5459_; 
v_unused_5455_ = lean_ctor_get(v_r_5370_, 4);
lean_dec(v_unused_5455_);
v_unused_5456_ = lean_ctor_get(v_r_5370_, 3);
lean_dec(v_unused_5456_);
v_unused_5457_ = lean_ctor_get(v_r_5370_, 2);
lean_dec(v_unused_5457_);
v_unused_5458_ = lean_ctor_get(v_r_5370_, 1);
lean_dec(v_unused_5458_);
v_unused_5459_ = lean_ctor_get(v_r_5370_, 0);
lean_dec(v_unused_5459_);
v___x_5392_ = v_r_5370_;
v_isShared_5393_ = v_isSharedCheck_5454_;
goto v_resetjp_5391_;
}
else
{
lean_dec(v_r_5370_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5454_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v_size_5394_; lean_object* v_k_5395_; lean_object* v_v_5396_; lean_object* v_l_5397_; lean_object* v_r_5398_; lean_object* v_size_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; uint8_t v___x_5402_; 
v_size_5394_ = lean_ctor_get(v_l_5381_, 0);
v_k_5395_ = lean_ctor_get(v_l_5381_, 1);
v_v_5396_ = lean_ctor_get(v_l_5381_, 2);
v_l_5397_ = lean_ctor_get(v_l_5381_, 3);
v_r_5398_ = lean_ctor_get(v_l_5381_, 4);
v_size_5399_ = lean_ctor_get(v_r_5382_, 0);
v___x_5400_ = lean_unsigned_to_nat(2u);
v___x_5401_ = lean_nat_mul(v___x_5400_, v_size_5399_);
v___x_5402_ = lean_nat_dec_lt(v_size_5394_, v___x_5401_);
lean_dec(v___x_5401_);
if (v___x_5402_ == 0)
{
lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5430_; 
lean_inc(v_r_5398_);
lean_inc(v_l_5397_);
lean_inc(v_v_5396_);
lean_inc(v_k_5395_);
v_isSharedCheck_5430_ = !lean_is_exclusive(v_l_5381_);
if (v_isSharedCheck_5430_ == 0)
{
lean_object* v_unused_5431_; lean_object* v_unused_5432_; lean_object* v_unused_5433_; lean_object* v_unused_5434_; lean_object* v_unused_5435_; 
v_unused_5431_ = lean_ctor_get(v_l_5381_, 4);
lean_dec(v_unused_5431_);
v_unused_5432_ = lean_ctor_get(v_l_5381_, 3);
lean_dec(v_unused_5432_);
v_unused_5433_ = lean_ctor_get(v_l_5381_, 2);
lean_dec(v_unused_5433_);
v_unused_5434_ = lean_ctor_get(v_l_5381_, 1);
lean_dec(v_unused_5434_);
v_unused_5435_ = lean_ctor_get(v_l_5381_, 0);
lean_dec(v_unused_5435_);
v___x_5404_ = v_l_5381_;
v_isShared_5405_ = v_isSharedCheck_5430_;
goto v_resetjp_5403_;
}
else
{
lean_dec(v_l_5381_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5430_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___y_5409_; lean_object* v___y_5410_; lean_object* v___y_5411_; lean_object* v___y_5420_; 
v___x_5406_ = lean_nat_add(v___x_5376_, v_size_5377_);
v___x_5407_ = lean_nat_add(v___x_5406_, v_size_5378_);
lean_dec(v_size_5378_);
if (lean_obj_tag(v_l_5397_) == 0)
{
lean_object* v_size_5428_; 
v_size_5428_ = lean_ctor_get(v_l_5397_, 0);
lean_inc(v_size_5428_);
v___y_5420_ = v_size_5428_;
goto v___jp_5419_;
}
else
{
lean_object* v___x_5429_; 
v___x_5429_ = lean_unsigned_to_nat(0u);
v___y_5420_ = v___x_5429_;
goto v___jp_5419_;
}
v___jp_5408_:
{
lean_object* v___x_5412_; lean_object* v___x_5414_; 
v___x_5412_ = lean_nat_add(v___y_5410_, v___y_5411_);
lean_dec(v___y_5411_);
lean_dec(v___y_5410_);
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 4, v_r_5382_);
lean_ctor_set(v___x_5404_, 3, v_r_5398_);
lean_ctor_set(v___x_5404_, 2, v_v_5380_);
lean_ctor_set(v___x_5404_, 1, v_k_5379_);
lean_ctor_set(v___x_5404_, 0, v___x_5412_);
v___x_5414_ = v___x_5404_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5412_);
lean_ctor_set(v_reuseFailAlloc_5418_, 1, v_k_5379_);
lean_ctor_set(v_reuseFailAlloc_5418_, 2, v_v_5380_);
lean_ctor_set(v_reuseFailAlloc_5418_, 3, v_r_5398_);
lean_ctor_set(v_reuseFailAlloc_5418_, 4, v_r_5382_);
v___x_5414_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
lean_object* v___x_5416_; 
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 4, v___x_5414_);
lean_ctor_set(v___x_5392_, 3, v___y_5409_);
lean_ctor_set(v___x_5392_, 2, v_v_5396_);
lean_ctor_set(v___x_5392_, 1, v_k_5395_);
lean_ctor_set(v___x_5392_, 0, v___x_5407_);
v___x_5416_ = v___x_5392_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v___x_5407_);
lean_ctor_set(v_reuseFailAlloc_5417_, 1, v_k_5395_);
lean_ctor_set(v_reuseFailAlloc_5417_, 2, v_v_5396_);
lean_ctor_set(v_reuseFailAlloc_5417_, 3, v___y_5409_);
lean_ctor_set(v_reuseFailAlloc_5417_, 4, v___x_5414_);
v___x_5416_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
return v___x_5416_;
}
}
}
v___jp_5419_:
{
lean_object* v___x_5421_; lean_object* v___x_5423_; 
v___x_5421_ = lean_nat_add(v___x_5406_, v___y_5420_);
lean_dec(v___y_5420_);
lean_dec(v___x_5406_);
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v_l_5397_);
lean_ctor_set(v___x_5372_, 3, v_impl_5375_);
lean_ctor_set(v___x_5372_, 0, v___x_5421_);
v___x_5423_ = v___x_5372_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v___x_5421_);
lean_ctor_set(v_reuseFailAlloc_5427_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5427_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5427_, 3, v_impl_5375_);
lean_ctor_set(v_reuseFailAlloc_5427_, 4, v_l_5397_);
v___x_5423_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
lean_object* v___x_5424_; 
v___x_5424_ = lean_nat_add(v___x_5376_, v_size_5399_);
if (lean_obj_tag(v_r_5398_) == 0)
{
lean_object* v_size_5425_; 
v_size_5425_ = lean_ctor_get(v_r_5398_, 0);
lean_inc(v_size_5425_);
v___y_5409_ = v___x_5423_;
v___y_5410_ = v___x_5424_;
v___y_5411_ = v_size_5425_;
goto v___jp_5408_;
}
else
{
lean_object* v___x_5426_; 
v___x_5426_ = lean_unsigned_to_nat(0u);
v___y_5409_ = v___x_5423_;
v___y_5410_ = v___x_5424_;
v___y_5411_ = v___x_5426_;
goto v___jp_5408_;
}
}
}
}
}
else
{
lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5440_; 
lean_del_object(v___x_5372_);
v___x_5436_ = lean_nat_add(v___x_5376_, v_size_5377_);
v___x_5437_ = lean_nat_add(v___x_5436_, v_size_5378_);
lean_dec(v_size_5378_);
v___x_5438_ = lean_nat_add(v___x_5436_, v_size_5394_);
lean_dec(v___x_5436_);
lean_inc_ref(v_impl_5375_);
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 4, v_l_5381_);
lean_ctor_set(v___x_5392_, 3, v_impl_5375_);
lean_ctor_set(v___x_5392_, 2, v_v_5368_);
lean_ctor_set(v___x_5392_, 1, v_k_5367_);
lean_ctor_set(v___x_5392_, 0, v___x_5438_);
v___x_5440_ = v___x_5392_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v___x_5438_);
lean_ctor_set(v_reuseFailAlloc_5453_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5453_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5453_, 3, v_impl_5375_);
lean_ctor_set(v_reuseFailAlloc_5453_, 4, v_l_5381_);
v___x_5440_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5447_; 
v_isSharedCheck_5447_ = !lean_is_exclusive(v_impl_5375_);
if (v_isSharedCheck_5447_ == 0)
{
lean_object* v_unused_5448_; lean_object* v_unused_5449_; lean_object* v_unused_5450_; lean_object* v_unused_5451_; lean_object* v_unused_5452_; 
v_unused_5448_ = lean_ctor_get(v_impl_5375_, 4);
lean_dec(v_unused_5448_);
v_unused_5449_ = lean_ctor_get(v_impl_5375_, 3);
lean_dec(v_unused_5449_);
v_unused_5450_ = lean_ctor_get(v_impl_5375_, 2);
lean_dec(v_unused_5450_);
v_unused_5451_ = lean_ctor_get(v_impl_5375_, 1);
lean_dec(v_unused_5451_);
v_unused_5452_ = lean_ctor_get(v_impl_5375_, 0);
lean_dec(v_unused_5452_);
v___x_5442_ = v_impl_5375_;
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
else
{
lean_dec(v_impl_5375_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v___x_5445_; 
if (v_isShared_5443_ == 0)
{
lean_ctor_set(v___x_5442_, 4, v_r_5382_);
lean_ctor_set(v___x_5442_, 3, v___x_5440_);
lean_ctor_set(v___x_5442_, 2, v_v_5380_);
lean_ctor_set(v___x_5442_, 1, v_k_5379_);
lean_ctor_set(v___x_5442_, 0, v___x_5437_);
v___x_5445_ = v___x_5442_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v___x_5437_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v_k_5379_);
lean_ctor_set(v_reuseFailAlloc_5446_, 2, v_v_5380_);
lean_ctor_set(v_reuseFailAlloc_5446_, 3, v___x_5440_);
lean_ctor_set(v_reuseFailAlloc_5446_, 4, v_r_5382_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5460_; lean_object* v___x_5461_; lean_object* v___x_5463_; 
v_size_5460_ = lean_ctor_get(v_impl_5375_, 0);
v___x_5461_ = lean_nat_add(v___x_5376_, v_size_5460_);
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 3, v_impl_5375_);
lean_ctor_set(v___x_5372_, 0, v___x_5461_);
v___x_5463_ = v___x_5372_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v___x_5461_);
lean_ctor_set(v_reuseFailAlloc_5464_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5464_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5464_, 3, v_impl_5375_);
lean_ctor_set(v_reuseFailAlloc_5464_, 4, v_r_5370_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
}
else
{
if (lean_obj_tag(v_r_5370_) == 0)
{
lean_object* v_l_5465_; 
v_l_5465_ = lean_ctor_get(v_r_5370_, 3);
lean_inc(v_l_5465_);
if (lean_obj_tag(v_l_5465_) == 0)
{
lean_object* v_r_5466_; 
v_r_5466_ = lean_ctor_get(v_r_5370_, 4);
lean_inc(v_r_5466_);
if (lean_obj_tag(v_r_5466_) == 0)
{
lean_object* v_size_5467_; lean_object* v_k_5468_; lean_object* v_v_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5482_; 
v_size_5467_ = lean_ctor_get(v_r_5370_, 0);
v_k_5468_ = lean_ctor_get(v_r_5370_, 1);
v_v_5469_ = lean_ctor_get(v_r_5370_, 2);
v_isSharedCheck_5482_ = !lean_is_exclusive(v_r_5370_);
if (v_isSharedCheck_5482_ == 0)
{
lean_object* v_unused_5483_; lean_object* v_unused_5484_; 
v_unused_5483_ = lean_ctor_get(v_r_5370_, 4);
lean_dec(v_unused_5483_);
v_unused_5484_ = lean_ctor_get(v_r_5370_, 3);
lean_dec(v_unused_5484_);
v___x_5471_ = v_r_5370_;
v_isShared_5472_ = v_isSharedCheck_5482_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_v_5469_);
lean_inc(v_k_5468_);
lean_inc(v_size_5467_);
lean_dec(v_r_5370_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5482_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v_size_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5477_; 
v_size_5473_ = lean_ctor_get(v_l_5465_, 0);
v___x_5474_ = lean_nat_add(v___x_5376_, v_size_5467_);
lean_dec(v_size_5467_);
v___x_5475_ = lean_nat_add(v___x_5376_, v_size_5473_);
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 4, v_l_5465_);
lean_ctor_set(v___x_5471_, 3, v_impl_5375_);
lean_ctor_set(v___x_5471_, 2, v_v_5368_);
lean_ctor_set(v___x_5471_, 1, v_k_5367_);
lean_ctor_set(v___x_5471_, 0, v___x_5475_);
v___x_5477_ = v___x_5471_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v___x_5475_);
lean_ctor_set(v_reuseFailAlloc_5481_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5481_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5481_, 3, v_impl_5375_);
lean_ctor_set(v_reuseFailAlloc_5481_, 4, v_l_5465_);
v___x_5477_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
lean_object* v___x_5479_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v_r_5466_);
lean_ctor_set(v___x_5372_, 3, v___x_5477_);
lean_ctor_set(v___x_5372_, 2, v_v_5469_);
lean_ctor_set(v___x_5372_, 1, v_k_5468_);
lean_ctor_set(v___x_5372_, 0, v___x_5474_);
v___x_5479_ = v___x_5372_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5474_);
lean_ctor_set(v_reuseFailAlloc_5480_, 1, v_k_5468_);
lean_ctor_set(v_reuseFailAlloc_5480_, 2, v_v_5469_);
lean_ctor_set(v_reuseFailAlloc_5480_, 3, v___x_5477_);
lean_ctor_set(v_reuseFailAlloc_5480_, 4, v_r_5466_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
else
{
lean_object* v_k_5485_; lean_object* v_v_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5509_; 
v_k_5485_ = lean_ctor_get(v_r_5370_, 1);
v_v_5486_ = lean_ctor_get(v_r_5370_, 2);
v_isSharedCheck_5509_ = !lean_is_exclusive(v_r_5370_);
if (v_isSharedCheck_5509_ == 0)
{
lean_object* v_unused_5510_; lean_object* v_unused_5511_; lean_object* v_unused_5512_; 
v_unused_5510_ = lean_ctor_get(v_r_5370_, 4);
lean_dec(v_unused_5510_);
v_unused_5511_ = lean_ctor_get(v_r_5370_, 3);
lean_dec(v_unused_5511_);
v_unused_5512_ = lean_ctor_get(v_r_5370_, 0);
lean_dec(v_unused_5512_);
v___x_5488_ = v_r_5370_;
v_isShared_5489_ = v_isSharedCheck_5509_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_v_5486_);
lean_inc(v_k_5485_);
lean_dec(v_r_5370_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5509_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v_k_5490_; lean_object* v_v_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5505_; 
v_k_5490_ = lean_ctor_get(v_l_5465_, 1);
v_v_5491_ = lean_ctor_get(v_l_5465_, 2);
v_isSharedCheck_5505_ = !lean_is_exclusive(v_l_5465_);
if (v_isSharedCheck_5505_ == 0)
{
lean_object* v_unused_5506_; lean_object* v_unused_5507_; lean_object* v_unused_5508_; 
v_unused_5506_ = lean_ctor_get(v_l_5465_, 4);
lean_dec(v_unused_5506_);
v_unused_5507_ = lean_ctor_get(v_l_5465_, 3);
lean_dec(v_unused_5507_);
v_unused_5508_ = lean_ctor_get(v_l_5465_, 0);
lean_dec(v_unused_5508_);
v___x_5493_ = v_l_5465_;
v_isShared_5494_ = v_isSharedCheck_5505_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_v_5491_);
lean_inc(v_k_5490_);
lean_dec(v_l_5465_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5505_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5495_; lean_object* v___x_5497_; 
v___x_5495_ = lean_unsigned_to_nat(3u);
if (v_isShared_5494_ == 0)
{
lean_ctor_set(v___x_5493_, 4, v_r_5466_);
lean_ctor_set(v___x_5493_, 3, v_r_5466_);
lean_ctor_set(v___x_5493_, 2, v_v_5368_);
lean_ctor_set(v___x_5493_, 1, v_k_5367_);
lean_ctor_set(v___x_5493_, 0, v___x_5376_);
v___x_5497_ = v___x_5493_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5376_);
lean_ctor_set(v_reuseFailAlloc_5504_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5504_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5504_, 3, v_r_5466_);
lean_ctor_set(v_reuseFailAlloc_5504_, 4, v_r_5466_);
v___x_5497_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
lean_object* v___x_5499_; 
if (v_isShared_5489_ == 0)
{
lean_ctor_set(v___x_5488_, 3, v_r_5466_);
lean_ctor_set(v___x_5488_, 0, v___x_5376_);
v___x_5499_ = v___x_5488_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5376_);
lean_ctor_set(v_reuseFailAlloc_5503_, 1, v_k_5485_);
lean_ctor_set(v_reuseFailAlloc_5503_, 2, v_v_5486_);
lean_ctor_set(v_reuseFailAlloc_5503_, 3, v_r_5466_);
lean_ctor_set(v_reuseFailAlloc_5503_, 4, v_r_5466_);
v___x_5499_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
lean_object* v___x_5501_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v___x_5499_);
lean_ctor_set(v___x_5372_, 3, v___x_5497_);
lean_ctor_set(v___x_5372_, 2, v_v_5491_);
lean_ctor_set(v___x_5372_, 1, v_k_5490_);
lean_ctor_set(v___x_5372_, 0, v___x_5495_);
v___x_5501_ = v___x_5372_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v___x_5495_);
lean_ctor_set(v_reuseFailAlloc_5502_, 1, v_k_5490_);
lean_ctor_set(v_reuseFailAlloc_5502_, 2, v_v_5491_);
lean_ctor_set(v_reuseFailAlloc_5502_, 3, v___x_5497_);
lean_ctor_set(v_reuseFailAlloc_5502_, 4, v___x_5499_);
v___x_5501_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
return v___x_5501_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_5513_; 
v_r_5513_ = lean_ctor_get(v_r_5370_, 4);
lean_inc(v_r_5513_);
if (lean_obj_tag(v_r_5513_) == 0)
{
lean_object* v_k_5514_; lean_object* v_v_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5526_; 
v_k_5514_ = lean_ctor_get(v_r_5370_, 1);
v_v_5515_ = lean_ctor_get(v_r_5370_, 2);
v_isSharedCheck_5526_ = !lean_is_exclusive(v_r_5370_);
if (v_isSharedCheck_5526_ == 0)
{
lean_object* v_unused_5527_; lean_object* v_unused_5528_; lean_object* v_unused_5529_; 
v_unused_5527_ = lean_ctor_get(v_r_5370_, 4);
lean_dec(v_unused_5527_);
v_unused_5528_ = lean_ctor_get(v_r_5370_, 3);
lean_dec(v_unused_5528_);
v_unused_5529_ = lean_ctor_get(v_r_5370_, 0);
lean_dec(v_unused_5529_);
v___x_5517_ = v_r_5370_;
v_isShared_5518_ = v_isSharedCheck_5526_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_v_5515_);
lean_inc(v_k_5514_);
lean_dec(v_r_5370_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5526_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5519_; lean_object* v___x_5521_; 
v___x_5519_ = lean_unsigned_to_nat(3u);
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 4, v_l_5465_);
lean_ctor_set(v___x_5517_, 2, v_v_5368_);
lean_ctor_set(v___x_5517_, 1, v_k_5367_);
lean_ctor_set(v___x_5517_, 0, v___x_5376_);
v___x_5521_ = v___x_5517_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v___x_5376_);
lean_ctor_set(v_reuseFailAlloc_5525_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5525_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5525_, 3, v_l_5465_);
lean_ctor_set(v_reuseFailAlloc_5525_, 4, v_l_5465_);
v___x_5521_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
lean_object* v___x_5523_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v_r_5513_);
lean_ctor_set(v___x_5372_, 3, v___x_5521_);
lean_ctor_set(v___x_5372_, 2, v_v_5515_);
lean_ctor_set(v___x_5372_, 1, v_k_5514_);
lean_ctor_set(v___x_5372_, 0, v___x_5519_);
v___x_5523_ = v___x_5372_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5519_);
lean_ctor_set(v_reuseFailAlloc_5524_, 1, v_k_5514_);
lean_ctor_set(v_reuseFailAlloc_5524_, 2, v_v_5515_);
lean_ctor_set(v_reuseFailAlloc_5524_, 3, v___x_5521_);
lean_ctor_set(v_reuseFailAlloc_5524_, 4, v_r_5513_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
else
{
lean_object* v_size_5530_; lean_object* v_k_5531_; lean_object* v_v_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5543_; 
v_size_5530_ = lean_ctor_get(v_r_5370_, 0);
v_k_5531_ = lean_ctor_get(v_r_5370_, 1);
v_v_5532_ = lean_ctor_get(v_r_5370_, 2);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_r_5370_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; lean_object* v_unused_5545_; 
v_unused_5544_ = lean_ctor_get(v_r_5370_, 4);
lean_dec(v_unused_5544_);
v_unused_5545_ = lean_ctor_get(v_r_5370_, 3);
lean_dec(v_unused_5545_);
v___x_5534_ = v_r_5370_;
v_isShared_5535_ = v_isSharedCheck_5543_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_v_5532_);
lean_inc(v_k_5531_);
lean_inc(v_size_5530_);
lean_dec(v_r_5370_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5543_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
lean_ctor_set(v___x_5534_, 3, v_r_5513_);
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_size_5530_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v_k_5531_);
lean_ctor_set(v_reuseFailAlloc_5542_, 2, v_v_5532_);
lean_ctor_set(v_reuseFailAlloc_5542_, 3, v_r_5513_);
lean_ctor_set(v_reuseFailAlloc_5542_, 4, v_r_5513_);
v___x_5537_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
lean_object* v___x_5538_; lean_object* v___x_5540_; 
v___x_5538_ = lean_unsigned_to_nat(2u);
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v___x_5537_);
lean_ctor_set(v___x_5372_, 3, v_r_5513_);
lean_ctor_set(v___x_5372_, 0, v___x_5538_);
v___x_5540_ = v___x_5372_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v___x_5538_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5541_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5541_, 3, v_r_5513_);
lean_ctor_set(v_reuseFailAlloc_5541_, 4, v___x_5537_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
}
}
}
}
else
{
lean_object* v___x_5547_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 3, v_r_5370_);
lean_ctor_set(v___x_5372_, 0, v___x_5376_);
v___x_5547_ = v___x_5372_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5376_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5548_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5548_, 3, v_r_5370_);
lean_ctor_set(v_reuseFailAlloc_5548_, 4, v_r_5370_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
case 1:
{
lean_del_object(v___x_5372_);
lean_dec(v_v_5368_);
lean_dec(v_k_5367_);
if (lean_obj_tag(v_l_5369_) == 0)
{
if (lean_obj_tag(v_r_5370_) == 0)
{
lean_object* v_size_5549_; lean_object* v_k_5550_; lean_object* v_v_5551_; lean_object* v_l_5552_; lean_object* v_r_5553_; lean_object* v_size_5554_; lean_object* v_k_5555_; lean_object* v_v_5556_; lean_object* v_l_5557_; lean_object* v_r_5558_; lean_object* v___x_5559_; uint8_t v___x_5560_; 
v_size_5549_ = lean_ctor_get(v_l_5369_, 0);
v_k_5550_ = lean_ctor_get(v_l_5369_, 1);
v_v_5551_ = lean_ctor_get(v_l_5369_, 2);
v_l_5552_ = lean_ctor_get(v_l_5369_, 3);
v_r_5553_ = lean_ctor_get(v_l_5369_, 4);
lean_inc(v_r_5553_);
v_size_5554_ = lean_ctor_get(v_r_5370_, 0);
v_k_5555_ = lean_ctor_get(v_r_5370_, 1);
v_v_5556_ = lean_ctor_get(v_r_5370_, 2);
v_l_5557_ = lean_ctor_get(v_r_5370_, 3);
lean_inc(v_l_5557_);
v_r_5558_ = lean_ctor_get(v_r_5370_, 4);
v___x_5559_ = lean_unsigned_to_nat(1u);
v___x_5560_ = lean_nat_dec_lt(v_size_5549_, v_size_5554_);
if (v___x_5560_ == 0)
{
lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5696_; 
lean_inc(v_l_5552_);
lean_inc(v_v_5551_);
lean_inc(v_k_5550_);
v_isSharedCheck_5696_ = !lean_is_exclusive(v_l_5369_);
if (v_isSharedCheck_5696_ == 0)
{
lean_object* v_unused_5697_; lean_object* v_unused_5698_; lean_object* v_unused_5699_; lean_object* v_unused_5700_; lean_object* v_unused_5701_; 
v_unused_5697_ = lean_ctor_get(v_l_5369_, 4);
lean_dec(v_unused_5697_);
v_unused_5698_ = lean_ctor_get(v_l_5369_, 3);
lean_dec(v_unused_5698_);
v_unused_5699_ = lean_ctor_get(v_l_5369_, 2);
lean_dec(v_unused_5699_);
v_unused_5700_ = lean_ctor_get(v_l_5369_, 1);
lean_dec(v_unused_5700_);
v_unused_5701_ = lean_ctor_get(v_l_5369_, 0);
lean_dec(v_unused_5701_);
v___x_5562_ = v_l_5369_;
v_isShared_5563_ = v_isSharedCheck_5696_;
goto v_resetjp_5561_;
}
else
{
lean_dec(v_l_5369_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5696_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5564_; lean_object* v_tree_5565_; 
v___x_5564_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5550_, v_v_5551_, v_l_5552_, v_r_5553_);
v_tree_5565_ = lean_ctor_get(v___x_5564_, 2);
if (lean_obj_tag(v_tree_5565_) == 0)
{
lean_object* v_k_5566_; lean_object* v_v_5567_; lean_object* v_size_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; uint8_t v___x_5571_; 
lean_inc_ref(v_tree_5565_);
v_k_5566_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_k_5566_);
v_v_5567_ = lean_ctor_get(v___x_5564_, 1);
lean_inc(v_v_5567_);
lean_dec_ref(v___x_5564_);
v_size_5568_ = lean_ctor_get(v_tree_5565_, 0);
v___x_5569_ = lean_unsigned_to_nat(3u);
v___x_5570_ = lean_nat_mul(v___x_5569_, v_size_5568_);
v___x_5571_ = lean_nat_dec_lt(v___x_5570_, v_size_5554_);
lean_dec(v___x_5570_);
if (v___x_5571_ == 0)
{
lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5575_; 
lean_dec(v_l_5557_);
v___x_5572_ = lean_nat_add(v___x_5559_, v_size_5568_);
v___x_5573_ = lean_nat_add(v___x_5572_, v_size_5554_);
lean_dec(v___x_5572_);
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 4, v_r_5370_);
lean_ctor_set(v___x_5562_, 3, v_tree_5565_);
lean_ctor_set(v___x_5562_, 2, v_v_5567_);
lean_ctor_set(v___x_5562_, 1, v_k_5566_);
lean_ctor_set(v___x_5562_, 0, v___x_5573_);
v___x_5575_ = v___x_5562_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5576_, 1, v_k_5566_);
lean_ctor_set(v_reuseFailAlloc_5576_, 2, v_v_5567_);
lean_ctor_set(v_reuseFailAlloc_5576_, 3, v_tree_5565_);
lean_ctor_set(v_reuseFailAlloc_5576_, 4, v_r_5370_);
v___x_5575_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
return v___x_5575_;
}
}
else
{
lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5631_; 
lean_inc(v_r_5558_);
lean_inc(v_v_5556_);
lean_inc(v_k_5555_);
lean_inc(v_size_5554_);
v_isSharedCheck_5631_ = !lean_is_exclusive(v_r_5370_);
if (v_isSharedCheck_5631_ == 0)
{
lean_object* v_unused_5632_; lean_object* v_unused_5633_; lean_object* v_unused_5634_; lean_object* v_unused_5635_; lean_object* v_unused_5636_; 
v_unused_5632_ = lean_ctor_get(v_r_5370_, 4);
lean_dec(v_unused_5632_);
v_unused_5633_ = lean_ctor_get(v_r_5370_, 3);
lean_dec(v_unused_5633_);
v_unused_5634_ = lean_ctor_get(v_r_5370_, 2);
lean_dec(v_unused_5634_);
v_unused_5635_ = lean_ctor_get(v_r_5370_, 1);
lean_dec(v_unused_5635_);
v_unused_5636_ = lean_ctor_get(v_r_5370_, 0);
lean_dec(v_unused_5636_);
v___x_5578_ = v_r_5370_;
v_isShared_5579_ = v_isSharedCheck_5631_;
goto v_resetjp_5577_;
}
else
{
lean_dec(v_r_5370_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5631_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v_size_5580_; lean_object* v_k_5581_; lean_object* v_v_5582_; lean_object* v_l_5583_; lean_object* v_r_5584_; lean_object* v_size_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; uint8_t v___x_5588_; 
v_size_5580_ = lean_ctor_get(v_l_5557_, 0);
v_k_5581_ = lean_ctor_get(v_l_5557_, 1);
v_v_5582_ = lean_ctor_get(v_l_5557_, 2);
v_l_5583_ = lean_ctor_get(v_l_5557_, 3);
v_r_5584_ = lean_ctor_get(v_l_5557_, 4);
v_size_5585_ = lean_ctor_get(v_r_5558_, 0);
v___x_5586_ = lean_unsigned_to_nat(2u);
v___x_5587_ = lean_nat_mul(v___x_5586_, v_size_5585_);
v___x_5588_ = lean_nat_dec_lt(v_size_5580_, v___x_5587_);
lean_dec(v___x_5587_);
if (v___x_5588_ == 0)
{
lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5616_; 
lean_inc(v_r_5584_);
lean_inc(v_l_5583_);
lean_inc(v_v_5582_);
lean_inc(v_k_5581_);
v_isSharedCheck_5616_ = !lean_is_exclusive(v_l_5557_);
if (v_isSharedCheck_5616_ == 0)
{
lean_object* v_unused_5617_; lean_object* v_unused_5618_; lean_object* v_unused_5619_; lean_object* v_unused_5620_; lean_object* v_unused_5621_; 
v_unused_5617_ = lean_ctor_get(v_l_5557_, 4);
lean_dec(v_unused_5617_);
v_unused_5618_ = lean_ctor_get(v_l_5557_, 3);
lean_dec(v_unused_5618_);
v_unused_5619_ = lean_ctor_get(v_l_5557_, 2);
lean_dec(v_unused_5619_);
v_unused_5620_ = lean_ctor_get(v_l_5557_, 1);
lean_dec(v_unused_5620_);
v_unused_5621_ = lean_ctor_get(v_l_5557_, 0);
lean_dec(v_unused_5621_);
v___x_5590_ = v_l_5557_;
v_isShared_5591_ = v_isSharedCheck_5616_;
goto v_resetjp_5589_;
}
else
{
lean_dec(v_l_5557_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5616_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___y_5595_; lean_object* v___y_5596_; lean_object* v___y_5597_; lean_object* v___y_5606_; 
v___x_5592_ = lean_nat_add(v___x_5559_, v_size_5568_);
v___x_5593_ = lean_nat_add(v___x_5592_, v_size_5554_);
lean_dec(v_size_5554_);
if (lean_obj_tag(v_l_5583_) == 0)
{
lean_object* v_size_5614_; 
v_size_5614_ = lean_ctor_get(v_l_5583_, 0);
lean_inc(v_size_5614_);
v___y_5606_ = v_size_5614_;
goto v___jp_5605_;
}
else
{
lean_object* v___x_5615_; 
v___x_5615_ = lean_unsigned_to_nat(0u);
v___y_5606_ = v___x_5615_;
goto v___jp_5605_;
}
v___jp_5594_:
{
lean_object* v___x_5598_; lean_object* v___x_5600_; 
v___x_5598_ = lean_nat_add(v___y_5596_, v___y_5597_);
lean_dec(v___y_5597_);
lean_dec(v___y_5596_);
if (v_isShared_5591_ == 0)
{
lean_ctor_set(v___x_5590_, 4, v_r_5558_);
lean_ctor_set(v___x_5590_, 3, v_r_5584_);
lean_ctor_set(v___x_5590_, 2, v_v_5556_);
lean_ctor_set(v___x_5590_, 1, v_k_5555_);
lean_ctor_set(v___x_5590_, 0, v___x_5598_);
v___x_5600_ = v___x_5590_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v___x_5598_);
lean_ctor_set(v_reuseFailAlloc_5604_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5604_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5604_, 3, v_r_5584_);
lean_ctor_set(v_reuseFailAlloc_5604_, 4, v_r_5558_);
v___x_5600_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
lean_object* v___x_5602_; 
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 4, v___x_5600_);
lean_ctor_set(v___x_5578_, 3, v___y_5595_);
lean_ctor_set(v___x_5578_, 2, v_v_5582_);
lean_ctor_set(v___x_5578_, 1, v_k_5581_);
lean_ctor_set(v___x_5578_, 0, v___x_5593_);
v___x_5602_ = v___x_5578_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5593_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v_k_5581_);
lean_ctor_set(v_reuseFailAlloc_5603_, 2, v_v_5582_);
lean_ctor_set(v_reuseFailAlloc_5603_, 3, v___y_5595_);
lean_ctor_set(v_reuseFailAlloc_5603_, 4, v___x_5600_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
v___jp_5605_:
{
lean_object* v___x_5607_; lean_object* v___x_5609_; 
v___x_5607_ = lean_nat_add(v___x_5592_, v___y_5606_);
lean_dec(v___y_5606_);
lean_dec(v___x_5592_);
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 4, v_l_5583_);
lean_ctor_set(v___x_5562_, 3, v_tree_5565_);
lean_ctor_set(v___x_5562_, 2, v_v_5567_);
lean_ctor_set(v___x_5562_, 1, v_k_5566_);
lean_ctor_set(v___x_5562_, 0, v___x_5607_);
v___x_5609_ = v___x_5562_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5607_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v_k_5566_);
lean_ctor_set(v_reuseFailAlloc_5613_, 2, v_v_5567_);
lean_ctor_set(v_reuseFailAlloc_5613_, 3, v_tree_5565_);
lean_ctor_set(v_reuseFailAlloc_5613_, 4, v_l_5583_);
v___x_5609_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
lean_object* v___x_5610_; 
v___x_5610_ = lean_nat_add(v___x_5559_, v_size_5585_);
if (lean_obj_tag(v_r_5584_) == 0)
{
lean_object* v_size_5611_; 
v_size_5611_ = lean_ctor_get(v_r_5584_, 0);
lean_inc(v_size_5611_);
v___y_5595_ = v___x_5609_;
v___y_5596_ = v___x_5610_;
v___y_5597_ = v_size_5611_;
goto v___jp_5594_;
}
else
{
lean_object* v___x_5612_; 
v___x_5612_ = lean_unsigned_to_nat(0u);
v___y_5595_ = v___x_5609_;
v___y_5596_ = v___x_5610_;
v___y_5597_ = v___x_5612_;
goto v___jp_5594_;
}
}
}
}
}
else
{
lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5626_; 
v___x_5622_ = lean_nat_add(v___x_5559_, v_size_5568_);
v___x_5623_ = lean_nat_add(v___x_5622_, v_size_5554_);
lean_dec(v_size_5554_);
v___x_5624_ = lean_nat_add(v___x_5622_, v_size_5580_);
lean_dec(v___x_5622_);
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 4, v_l_5557_);
lean_ctor_set(v___x_5578_, 3, v_tree_5565_);
lean_ctor_set(v___x_5578_, 2, v_v_5567_);
lean_ctor_set(v___x_5578_, 1, v_k_5566_);
lean_ctor_set(v___x_5578_, 0, v___x_5624_);
v___x_5626_ = v___x_5578_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5624_);
lean_ctor_set(v_reuseFailAlloc_5630_, 1, v_k_5566_);
lean_ctor_set(v_reuseFailAlloc_5630_, 2, v_v_5567_);
lean_ctor_set(v_reuseFailAlloc_5630_, 3, v_tree_5565_);
lean_ctor_set(v_reuseFailAlloc_5630_, 4, v_l_5557_);
v___x_5626_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
lean_object* v___x_5628_; 
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 4, v_r_5558_);
lean_ctor_set(v___x_5562_, 3, v___x_5626_);
lean_ctor_set(v___x_5562_, 2, v_v_5556_);
lean_ctor_set(v___x_5562_, 1, v_k_5555_);
lean_ctor_set(v___x_5562_, 0, v___x_5623_);
v___x_5628_ = v___x_5562_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v___x_5623_);
lean_ctor_set(v_reuseFailAlloc_5629_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5629_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5629_, 3, v___x_5626_);
lean_ctor_set(v_reuseFailAlloc_5629_, 4, v_r_5558_);
v___x_5628_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
return v___x_5628_;
}
}
}
}
}
}
else
{
lean_object* v___x_5638_; uint8_t v_isShared_5639_; uint8_t v_isSharedCheck_5690_; 
lean_inc(v_r_5558_);
lean_inc(v_v_5556_);
lean_inc(v_k_5555_);
lean_inc(v_size_5554_);
v_isSharedCheck_5690_ = !lean_is_exclusive(v_r_5370_);
if (v_isSharedCheck_5690_ == 0)
{
lean_object* v_unused_5691_; lean_object* v_unused_5692_; lean_object* v_unused_5693_; lean_object* v_unused_5694_; lean_object* v_unused_5695_; 
v_unused_5691_ = lean_ctor_get(v_r_5370_, 4);
lean_dec(v_unused_5691_);
v_unused_5692_ = lean_ctor_get(v_r_5370_, 3);
lean_dec(v_unused_5692_);
v_unused_5693_ = lean_ctor_get(v_r_5370_, 2);
lean_dec(v_unused_5693_);
v_unused_5694_ = lean_ctor_get(v_r_5370_, 1);
lean_dec(v_unused_5694_);
v_unused_5695_ = lean_ctor_get(v_r_5370_, 0);
lean_dec(v_unused_5695_);
v___x_5638_ = v_r_5370_;
v_isShared_5639_ = v_isSharedCheck_5690_;
goto v_resetjp_5637_;
}
else
{
lean_dec(v_r_5370_);
v___x_5638_ = lean_box(0);
v_isShared_5639_ = v_isSharedCheck_5690_;
goto v_resetjp_5637_;
}
v_resetjp_5637_:
{
if (lean_obj_tag(v_l_5557_) == 0)
{
if (lean_obj_tag(v_r_5558_) == 0)
{
lean_object* v_k_5640_; lean_object* v_v_5641_; lean_object* v_size_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5646_; 
lean_inc(v_tree_5565_);
v_k_5640_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_k_5640_);
v_v_5641_ = lean_ctor_get(v___x_5564_, 1);
lean_inc(v_v_5641_);
lean_dec_ref(v___x_5564_);
v_size_5642_ = lean_ctor_get(v_l_5557_, 0);
v___x_5643_ = lean_nat_add(v___x_5559_, v_size_5554_);
lean_dec(v_size_5554_);
v___x_5644_ = lean_nat_add(v___x_5559_, v_size_5642_);
if (v_isShared_5639_ == 0)
{
lean_ctor_set(v___x_5638_, 4, v_l_5557_);
lean_ctor_set(v___x_5638_, 3, v_tree_5565_);
lean_ctor_set(v___x_5638_, 2, v_v_5641_);
lean_ctor_set(v___x_5638_, 1, v_k_5640_);
lean_ctor_set(v___x_5638_, 0, v___x_5644_);
v___x_5646_ = v___x_5638_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v___x_5644_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v_k_5640_);
lean_ctor_set(v_reuseFailAlloc_5650_, 2, v_v_5641_);
lean_ctor_set(v_reuseFailAlloc_5650_, 3, v_tree_5565_);
lean_ctor_set(v_reuseFailAlloc_5650_, 4, v_l_5557_);
v___x_5646_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
lean_object* v___x_5648_; 
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 4, v_r_5558_);
lean_ctor_set(v___x_5562_, 3, v___x_5646_);
lean_ctor_set(v___x_5562_, 2, v_v_5556_);
lean_ctor_set(v___x_5562_, 1, v_k_5555_);
lean_ctor_set(v___x_5562_, 0, v___x_5643_);
v___x_5648_ = v___x_5562_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5643_);
lean_ctor_set(v_reuseFailAlloc_5649_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5649_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5649_, 3, v___x_5646_);
lean_ctor_set(v_reuseFailAlloc_5649_, 4, v_r_5558_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
else
{
lean_object* v_k_5651_; lean_object* v_v_5652_; lean_object* v_k_5653_; lean_object* v_v_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5668_; 
lean_dec(v_size_5554_);
v_k_5651_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_k_5651_);
v_v_5652_ = lean_ctor_get(v___x_5564_, 1);
lean_inc(v_v_5652_);
lean_dec_ref(v___x_5564_);
v_k_5653_ = lean_ctor_get(v_l_5557_, 1);
v_v_5654_ = lean_ctor_get(v_l_5557_, 2);
v_isSharedCheck_5668_ = !lean_is_exclusive(v_l_5557_);
if (v_isSharedCheck_5668_ == 0)
{
lean_object* v_unused_5669_; lean_object* v_unused_5670_; lean_object* v_unused_5671_; 
v_unused_5669_ = lean_ctor_get(v_l_5557_, 4);
lean_dec(v_unused_5669_);
v_unused_5670_ = lean_ctor_get(v_l_5557_, 3);
lean_dec(v_unused_5670_);
v_unused_5671_ = lean_ctor_get(v_l_5557_, 0);
lean_dec(v_unused_5671_);
v___x_5656_ = v_l_5557_;
v_isShared_5657_ = v_isSharedCheck_5668_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_v_5654_);
lean_inc(v_k_5653_);
lean_dec(v_l_5557_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5668_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5658_; lean_object* v___x_5660_; 
v___x_5658_ = lean_unsigned_to_nat(3u);
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 4, v_r_5558_);
lean_ctor_set(v___x_5656_, 3, v_r_5558_);
lean_ctor_set(v___x_5656_, 2, v_v_5652_);
lean_ctor_set(v___x_5656_, 1, v_k_5651_);
lean_ctor_set(v___x_5656_, 0, v___x_5559_);
v___x_5660_ = v___x_5656_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5667_, 1, v_k_5651_);
lean_ctor_set(v_reuseFailAlloc_5667_, 2, v_v_5652_);
lean_ctor_set(v_reuseFailAlloc_5667_, 3, v_r_5558_);
lean_ctor_set(v_reuseFailAlloc_5667_, 4, v_r_5558_);
v___x_5660_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
lean_object* v___x_5662_; 
if (v_isShared_5639_ == 0)
{
lean_ctor_set(v___x_5638_, 3, v_r_5558_);
lean_ctor_set(v___x_5638_, 0, v___x_5559_);
v___x_5662_ = v___x_5638_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5666_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5666_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5666_, 3, v_r_5558_);
lean_ctor_set(v_reuseFailAlloc_5666_, 4, v_r_5558_);
v___x_5662_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
lean_object* v___x_5664_; 
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 4, v___x_5662_);
lean_ctor_set(v___x_5562_, 3, v___x_5660_);
lean_ctor_set(v___x_5562_, 2, v_v_5654_);
lean_ctor_set(v___x_5562_, 1, v_k_5653_);
lean_ctor_set(v___x_5562_, 0, v___x_5658_);
v___x_5664_ = v___x_5562_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v___x_5658_);
lean_ctor_set(v_reuseFailAlloc_5665_, 1, v_k_5653_);
lean_ctor_set(v_reuseFailAlloc_5665_, 2, v_v_5654_);
lean_ctor_set(v_reuseFailAlloc_5665_, 3, v___x_5660_);
lean_ctor_set(v_reuseFailAlloc_5665_, 4, v___x_5662_);
v___x_5664_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
return v___x_5664_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5558_) == 0)
{
lean_object* v_k_5672_; lean_object* v_v_5673_; lean_object* v___x_5674_; lean_object* v___x_5676_; 
lean_dec(v_size_5554_);
v_k_5672_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_k_5672_);
v_v_5673_ = lean_ctor_get(v___x_5564_, 1);
lean_inc(v_v_5673_);
lean_dec_ref(v___x_5564_);
v___x_5674_ = lean_unsigned_to_nat(3u);
if (v_isShared_5639_ == 0)
{
lean_ctor_set(v___x_5638_, 4, v_l_5557_);
lean_ctor_set(v___x_5638_, 2, v_v_5673_);
lean_ctor_set(v___x_5638_, 1, v_k_5672_);
lean_ctor_set(v___x_5638_, 0, v___x_5559_);
v___x_5676_ = v___x_5638_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5680_, 1, v_k_5672_);
lean_ctor_set(v_reuseFailAlloc_5680_, 2, v_v_5673_);
lean_ctor_set(v_reuseFailAlloc_5680_, 3, v_l_5557_);
lean_ctor_set(v_reuseFailAlloc_5680_, 4, v_l_5557_);
v___x_5676_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
lean_object* v___x_5678_; 
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 4, v_r_5558_);
lean_ctor_set(v___x_5562_, 3, v___x_5676_);
lean_ctor_set(v___x_5562_, 2, v_v_5556_);
lean_ctor_set(v___x_5562_, 1, v_k_5555_);
lean_ctor_set(v___x_5562_, 0, v___x_5674_);
v___x_5678_ = v___x_5562_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v___x_5674_);
lean_ctor_set(v_reuseFailAlloc_5679_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5679_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5679_, 3, v___x_5676_);
lean_ctor_set(v_reuseFailAlloc_5679_, 4, v_r_5558_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
return v___x_5678_;
}
}
}
else
{
lean_object* v_k_5681_; lean_object* v_v_5682_; lean_object* v___x_5684_; 
v_k_5681_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_k_5681_);
v_v_5682_ = lean_ctor_get(v___x_5564_, 1);
lean_inc(v_v_5682_);
lean_dec_ref(v___x_5564_);
if (v_isShared_5639_ == 0)
{
lean_ctor_set(v___x_5638_, 3, v_r_5558_);
v___x_5684_ = v___x_5638_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_size_5554_);
lean_ctor_set(v_reuseFailAlloc_5689_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5689_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5689_, 3, v_r_5558_);
lean_ctor_set(v_reuseFailAlloc_5689_, 4, v_r_5558_);
v___x_5684_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
lean_object* v___x_5685_; lean_object* v___x_5687_; 
v___x_5685_ = lean_unsigned_to_nat(2u);
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 4, v___x_5684_);
lean_ctor_set(v___x_5562_, 3, v_r_5558_);
lean_ctor_set(v___x_5562_, 2, v_v_5682_);
lean_ctor_set(v___x_5562_, 1, v_k_5681_);
lean_ctor_set(v___x_5562_, 0, v___x_5685_);
v___x_5687_ = v___x_5562_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v___x_5685_);
lean_ctor_set(v_reuseFailAlloc_5688_, 1, v_k_5681_);
lean_ctor_set(v_reuseFailAlloc_5688_, 2, v_v_5682_);
lean_ctor_set(v_reuseFailAlloc_5688_, 3, v_r_5558_);
lean_ctor_set(v_reuseFailAlloc_5688_, 4, v___x_5684_);
v___x_5687_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
return v___x_5687_;
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
lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5854_; 
lean_inc(v_r_5558_);
lean_inc(v_v_5556_);
lean_inc(v_k_5555_);
v_isSharedCheck_5854_ = !lean_is_exclusive(v_r_5370_);
if (v_isSharedCheck_5854_ == 0)
{
lean_object* v_unused_5855_; lean_object* v_unused_5856_; lean_object* v_unused_5857_; lean_object* v_unused_5858_; lean_object* v_unused_5859_; 
v_unused_5855_ = lean_ctor_get(v_r_5370_, 4);
lean_dec(v_unused_5855_);
v_unused_5856_ = lean_ctor_get(v_r_5370_, 3);
lean_dec(v_unused_5856_);
v_unused_5857_ = lean_ctor_get(v_r_5370_, 2);
lean_dec(v_unused_5857_);
v_unused_5858_ = lean_ctor_get(v_r_5370_, 1);
lean_dec(v_unused_5858_);
v_unused_5859_ = lean_ctor_get(v_r_5370_, 0);
lean_dec(v_unused_5859_);
v___x_5703_ = v_r_5370_;
v_isShared_5704_ = v_isSharedCheck_5854_;
goto v_resetjp_5702_;
}
else
{
lean_dec(v_r_5370_);
v___x_5703_ = lean_box(0);
v_isShared_5704_ = v_isSharedCheck_5854_;
goto v_resetjp_5702_;
}
v_resetjp_5702_:
{
lean_object* v___x_5705_; lean_object* v_tree_5706_; 
v___x_5705_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5555_, v_v_5556_, v_l_5557_, v_r_5558_);
v_tree_5706_ = lean_ctor_get(v___x_5705_, 2);
lean_inc(v_tree_5706_);
if (lean_obj_tag(v_tree_5706_) == 0)
{
lean_object* v_k_5707_; lean_object* v_v_5708_; lean_object* v_size_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; uint8_t v___x_5712_; 
v_k_5707_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_k_5707_);
v_v_5708_ = lean_ctor_get(v___x_5705_, 1);
lean_inc(v_v_5708_);
lean_dec_ref(v___x_5705_);
v_size_5709_ = lean_ctor_get(v_tree_5706_, 0);
v___x_5710_ = lean_unsigned_to_nat(3u);
v___x_5711_ = lean_nat_mul(v___x_5710_, v_size_5709_);
v___x_5712_ = lean_nat_dec_lt(v___x_5711_, v_size_5549_);
lean_dec(v___x_5711_);
if (v___x_5712_ == 0)
{
lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5716_; 
lean_dec(v_r_5553_);
v___x_5713_ = lean_nat_add(v___x_5559_, v_size_5549_);
v___x_5714_ = lean_nat_add(v___x_5713_, v_size_5709_);
lean_dec(v___x_5713_);
if (v_isShared_5704_ == 0)
{
lean_ctor_set(v___x_5703_, 4, v_tree_5706_);
lean_ctor_set(v___x_5703_, 3, v_l_5369_);
lean_ctor_set(v___x_5703_, 2, v_v_5708_);
lean_ctor_set(v___x_5703_, 1, v_k_5707_);
lean_ctor_set(v___x_5703_, 0, v___x_5714_);
v___x_5716_ = v___x_5703_;
goto v_reusejp_5715_;
}
else
{
lean_object* v_reuseFailAlloc_5717_; 
v_reuseFailAlloc_5717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5717_, 0, v___x_5714_);
lean_ctor_set(v_reuseFailAlloc_5717_, 1, v_k_5707_);
lean_ctor_set(v_reuseFailAlloc_5717_, 2, v_v_5708_);
lean_ctor_set(v_reuseFailAlloc_5717_, 3, v_l_5369_);
lean_ctor_set(v_reuseFailAlloc_5717_, 4, v_tree_5706_);
v___x_5716_ = v_reuseFailAlloc_5717_;
goto v_reusejp_5715_;
}
v_reusejp_5715_:
{
return v___x_5716_;
}
}
else
{
lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5783_; 
lean_inc(v_l_5552_);
lean_inc(v_v_5551_);
lean_inc(v_k_5550_);
lean_inc(v_size_5549_);
v_isSharedCheck_5783_ = !lean_is_exclusive(v_l_5369_);
if (v_isSharedCheck_5783_ == 0)
{
lean_object* v_unused_5784_; lean_object* v_unused_5785_; lean_object* v_unused_5786_; lean_object* v_unused_5787_; lean_object* v_unused_5788_; 
v_unused_5784_ = lean_ctor_get(v_l_5369_, 4);
lean_dec(v_unused_5784_);
v_unused_5785_ = lean_ctor_get(v_l_5369_, 3);
lean_dec(v_unused_5785_);
v_unused_5786_ = lean_ctor_get(v_l_5369_, 2);
lean_dec(v_unused_5786_);
v_unused_5787_ = lean_ctor_get(v_l_5369_, 1);
lean_dec(v_unused_5787_);
v_unused_5788_ = lean_ctor_get(v_l_5369_, 0);
lean_dec(v_unused_5788_);
v___x_5719_ = v_l_5369_;
v_isShared_5720_ = v_isSharedCheck_5783_;
goto v_resetjp_5718_;
}
else
{
lean_dec(v_l_5369_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5783_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v_size_5721_; lean_object* v_size_5722_; lean_object* v_k_5723_; lean_object* v_v_5724_; lean_object* v_l_5725_; lean_object* v_r_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; uint8_t v___x_5729_; 
v_size_5721_ = lean_ctor_get(v_l_5552_, 0);
v_size_5722_ = lean_ctor_get(v_r_5553_, 0);
v_k_5723_ = lean_ctor_get(v_r_5553_, 1);
v_v_5724_ = lean_ctor_get(v_r_5553_, 2);
v_l_5725_ = lean_ctor_get(v_r_5553_, 3);
v_r_5726_ = lean_ctor_get(v_r_5553_, 4);
v___x_5727_ = lean_unsigned_to_nat(2u);
v___x_5728_ = lean_nat_mul(v___x_5727_, v_size_5721_);
v___x_5729_ = lean_nat_dec_lt(v_size_5722_, v___x_5728_);
lean_dec(v___x_5728_);
if (v___x_5729_ == 0)
{
lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5767_; 
lean_inc(v_r_5726_);
lean_inc(v_l_5725_);
lean_inc(v_v_5724_);
lean_inc(v_k_5723_);
lean_del_object(v___x_5719_);
v_isSharedCheck_5767_ = !lean_is_exclusive(v_r_5553_);
if (v_isSharedCheck_5767_ == 0)
{
lean_object* v_unused_5768_; lean_object* v_unused_5769_; lean_object* v_unused_5770_; lean_object* v_unused_5771_; lean_object* v_unused_5772_; 
v_unused_5768_ = lean_ctor_get(v_r_5553_, 4);
lean_dec(v_unused_5768_);
v_unused_5769_ = lean_ctor_get(v_r_5553_, 3);
lean_dec(v_unused_5769_);
v_unused_5770_ = lean_ctor_get(v_r_5553_, 2);
lean_dec(v_unused_5770_);
v_unused_5771_ = lean_ctor_get(v_r_5553_, 1);
lean_dec(v_unused_5771_);
v_unused_5772_ = lean_ctor_get(v_r_5553_, 0);
lean_dec(v_unused_5772_);
v___x_5731_ = v_r_5553_;
v_isShared_5732_ = v_isSharedCheck_5767_;
goto v_resetjp_5730_;
}
else
{
lean_dec(v_r_5553_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5767_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___x_5755_; lean_object* v___y_5757_; 
v___x_5733_ = lean_nat_add(v___x_5559_, v_size_5549_);
lean_dec(v_size_5549_);
v___x_5734_ = lean_nat_add(v___x_5733_, v_size_5709_);
lean_dec(v___x_5733_);
v___x_5755_ = lean_nat_add(v___x_5559_, v_size_5721_);
if (lean_obj_tag(v_l_5725_) == 0)
{
lean_object* v_size_5765_; 
v_size_5765_ = lean_ctor_get(v_l_5725_, 0);
lean_inc(v_size_5765_);
v___y_5757_ = v_size_5765_;
goto v___jp_5756_;
}
else
{
lean_object* v___x_5766_; 
v___x_5766_ = lean_unsigned_to_nat(0u);
v___y_5757_ = v___x_5766_;
goto v___jp_5756_;
}
v___jp_5735_:
{
lean_object* v___x_5739_; lean_object* v___x_5741_; 
v___x_5739_ = lean_nat_add(v___y_5737_, v___y_5738_);
lean_dec(v___y_5738_);
lean_dec(v___y_5737_);
lean_inc_ref(v_tree_5706_);
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 4, v_tree_5706_);
lean_ctor_set(v___x_5731_, 3, v_r_5726_);
lean_ctor_set(v___x_5731_, 2, v_v_5708_);
lean_ctor_set(v___x_5731_, 1, v_k_5707_);
lean_ctor_set(v___x_5731_, 0, v___x_5739_);
v___x_5741_ = v___x_5731_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5739_);
lean_ctor_set(v_reuseFailAlloc_5754_, 1, v_k_5707_);
lean_ctor_set(v_reuseFailAlloc_5754_, 2, v_v_5708_);
lean_ctor_set(v_reuseFailAlloc_5754_, 3, v_r_5726_);
lean_ctor_set(v_reuseFailAlloc_5754_, 4, v_tree_5706_);
v___x_5741_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5748_; 
v_isSharedCheck_5748_ = !lean_is_exclusive(v_tree_5706_);
if (v_isSharedCheck_5748_ == 0)
{
lean_object* v_unused_5749_; lean_object* v_unused_5750_; lean_object* v_unused_5751_; lean_object* v_unused_5752_; lean_object* v_unused_5753_; 
v_unused_5749_ = lean_ctor_get(v_tree_5706_, 4);
lean_dec(v_unused_5749_);
v_unused_5750_ = lean_ctor_get(v_tree_5706_, 3);
lean_dec(v_unused_5750_);
v_unused_5751_ = lean_ctor_get(v_tree_5706_, 2);
lean_dec(v_unused_5751_);
v_unused_5752_ = lean_ctor_get(v_tree_5706_, 1);
lean_dec(v_unused_5752_);
v_unused_5753_ = lean_ctor_get(v_tree_5706_, 0);
lean_dec(v_unused_5753_);
v___x_5743_ = v_tree_5706_;
v_isShared_5744_ = v_isSharedCheck_5748_;
goto v_resetjp_5742_;
}
else
{
lean_dec(v_tree_5706_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5748_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v___x_5746_; 
if (v_isShared_5744_ == 0)
{
lean_ctor_set(v___x_5743_, 4, v___x_5741_);
lean_ctor_set(v___x_5743_, 3, v___y_5736_);
lean_ctor_set(v___x_5743_, 2, v_v_5724_);
lean_ctor_set(v___x_5743_, 1, v_k_5723_);
lean_ctor_set(v___x_5743_, 0, v___x_5734_);
v___x_5746_ = v___x_5743_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v___x_5734_);
lean_ctor_set(v_reuseFailAlloc_5747_, 1, v_k_5723_);
lean_ctor_set(v_reuseFailAlloc_5747_, 2, v_v_5724_);
lean_ctor_set(v_reuseFailAlloc_5747_, 3, v___y_5736_);
lean_ctor_set(v_reuseFailAlloc_5747_, 4, v___x_5741_);
v___x_5746_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
return v___x_5746_;
}
}
}
}
v___jp_5756_:
{
lean_object* v___x_5758_; lean_object* v___x_5760_; 
v___x_5758_ = lean_nat_add(v___x_5755_, v___y_5757_);
lean_dec(v___y_5757_);
lean_dec(v___x_5755_);
if (v_isShared_5704_ == 0)
{
lean_ctor_set(v___x_5703_, 4, v_l_5725_);
lean_ctor_set(v___x_5703_, 3, v_l_5552_);
lean_ctor_set(v___x_5703_, 2, v_v_5551_);
lean_ctor_set(v___x_5703_, 1, v_k_5550_);
lean_ctor_set(v___x_5703_, 0, v___x_5758_);
v___x_5760_ = v___x_5703_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5764_; 
v_reuseFailAlloc_5764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5764_, 0, v___x_5758_);
lean_ctor_set(v_reuseFailAlloc_5764_, 1, v_k_5550_);
lean_ctor_set(v_reuseFailAlloc_5764_, 2, v_v_5551_);
lean_ctor_set(v_reuseFailAlloc_5764_, 3, v_l_5552_);
lean_ctor_set(v_reuseFailAlloc_5764_, 4, v_l_5725_);
v___x_5760_ = v_reuseFailAlloc_5764_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
lean_object* v___x_5761_; 
v___x_5761_ = lean_nat_add(v___x_5559_, v_size_5709_);
if (lean_obj_tag(v_r_5726_) == 0)
{
lean_object* v_size_5762_; 
v_size_5762_ = lean_ctor_get(v_r_5726_, 0);
lean_inc(v_size_5762_);
v___y_5736_ = v___x_5760_;
v___y_5737_ = v___x_5761_;
v___y_5738_ = v_size_5762_;
goto v___jp_5735_;
}
else
{
lean_object* v___x_5763_; 
v___x_5763_ = lean_unsigned_to_nat(0u);
v___y_5736_ = v___x_5760_;
v___y_5737_ = v___x_5761_;
v___y_5738_ = v___x_5763_;
goto v___jp_5735_;
}
}
}
}
}
else
{
lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5778_; 
v___x_5773_ = lean_nat_add(v___x_5559_, v_size_5549_);
lean_dec(v_size_5549_);
v___x_5774_ = lean_nat_add(v___x_5773_, v_size_5709_);
lean_dec(v___x_5773_);
v___x_5775_ = lean_nat_add(v___x_5559_, v_size_5709_);
v___x_5776_ = lean_nat_add(v___x_5775_, v_size_5722_);
lean_dec(v___x_5775_);
if (v_isShared_5704_ == 0)
{
lean_ctor_set(v___x_5703_, 4, v_tree_5706_);
lean_ctor_set(v___x_5703_, 3, v_r_5553_);
lean_ctor_set(v___x_5703_, 2, v_v_5708_);
lean_ctor_set(v___x_5703_, 1, v_k_5707_);
lean_ctor_set(v___x_5703_, 0, v___x_5776_);
v___x_5778_ = v___x_5703_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5776_);
lean_ctor_set(v_reuseFailAlloc_5782_, 1, v_k_5707_);
lean_ctor_set(v_reuseFailAlloc_5782_, 2, v_v_5708_);
lean_ctor_set(v_reuseFailAlloc_5782_, 3, v_r_5553_);
lean_ctor_set(v_reuseFailAlloc_5782_, 4, v_tree_5706_);
v___x_5778_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
lean_object* v___x_5780_; 
if (v_isShared_5720_ == 0)
{
lean_ctor_set(v___x_5719_, 4, v___x_5778_);
lean_ctor_set(v___x_5719_, 0, v___x_5774_);
v___x_5780_ = v___x_5719_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v___x_5774_);
lean_ctor_set(v_reuseFailAlloc_5781_, 1, v_k_5550_);
lean_ctor_set(v_reuseFailAlloc_5781_, 2, v_v_5551_);
lean_ctor_set(v_reuseFailAlloc_5781_, 3, v_l_5552_);
lean_ctor_set(v_reuseFailAlloc_5781_, 4, v___x_5778_);
v___x_5780_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
return v___x_5780_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_5552_) == 0)
{
lean_object* v___x_5790_; uint8_t v_isShared_5791_; uint8_t v_isSharedCheck_5812_; 
lean_inc_ref(v_l_5552_);
lean_inc(v_v_5551_);
lean_inc(v_k_5550_);
lean_inc(v_size_5549_);
v_isSharedCheck_5812_ = !lean_is_exclusive(v_l_5369_);
if (v_isSharedCheck_5812_ == 0)
{
lean_object* v_unused_5813_; lean_object* v_unused_5814_; lean_object* v_unused_5815_; lean_object* v_unused_5816_; lean_object* v_unused_5817_; 
v_unused_5813_ = lean_ctor_get(v_l_5369_, 4);
lean_dec(v_unused_5813_);
v_unused_5814_ = lean_ctor_get(v_l_5369_, 3);
lean_dec(v_unused_5814_);
v_unused_5815_ = lean_ctor_get(v_l_5369_, 2);
lean_dec(v_unused_5815_);
v_unused_5816_ = lean_ctor_get(v_l_5369_, 1);
lean_dec(v_unused_5816_);
v_unused_5817_ = lean_ctor_get(v_l_5369_, 0);
lean_dec(v_unused_5817_);
v___x_5790_ = v_l_5369_;
v_isShared_5791_ = v_isSharedCheck_5812_;
goto v_resetjp_5789_;
}
else
{
lean_dec(v_l_5369_);
v___x_5790_ = lean_box(0);
v_isShared_5791_ = v_isSharedCheck_5812_;
goto v_resetjp_5789_;
}
v_resetjp_5789_:
{
if (lean_obj_tag(v_r_5553_) == 0)
{
lean_object* v_k_5792_; lean_object* v_v_5793_; lean_object* v_size_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5798_; 
v_k_5792_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_k_5792_);
v_v_5793_ = lean_ctor_get(v___x_5705_, 1);
lean_inc(v_v_5793_);
lean_dec_ref(v___x_5705_);
v_size_5794_ = lean_ctor_get(v_r_5553_, 0);
v___x_5795_ = lean_nat_add(v___x_5559_, v_size_5549_);
lean_dec(v_size_5549_);
v___x_5796_ = lean_nat_add(v___x_5559_, v_size_5794_);
if (v_isShared_5704_ == 0)
{
lean_ctor_set(v___x_5703_, 4, v_tree_5706_);
lean_ctor_set(v___x_5703_, 3, v_r_5553_);
lean_ctor_set(v___x_5703_, 2, v_v_5793_);
lean_ctor_set(v___x_5703_, 1, v_k_5792_);
lean_ctor_set(v___x_5703_, 0, v___x_5796_);
v___x_5798_ = v___x_5703_;
goto v_reusejp_5797_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v___x_5796_);
lean_ctor_set(v_reuseFailAlloc_5802_, 1, v_k_5792_);
lean_ctor_set(v_reuseFailAlloc_5802_, 2, v_v_5793_);
lean_ctor_set(v_reuseFailAlloc_5802_, 3, v_r_5553_);
lean_ctor_set(v_reuseFailAlloc_5802_, 4, v_tree_5706_);
v___x_5798_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5797_;
}
v_reusejp_5797_:
{
lean_object* v___x_5800_; 
if (v_isShared_5791_ == 0)
{
lean_ctor_set(v___x_5790_, 4, v___x_5798_);
lean_ctor_set(v___x_5790_, 0, v___x_5795_);
v___x_5800_ = v___x_5790_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v___x_5795_);
lean_ctor_set(v_reuseFailAlloc_5801_, 1, v_k_5550_);
lean_ctor_set(v_reuseFailAlloc_5801_, 2, v_v_5551_);
lean_ctor_set(v_reuseFailAlloc_5801_, 3, v_l_5552_);
lean_ctor_set(v_reuseFailAlloc_5801_, 4, v___x_5798_);
v___x_5800_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
return v___x_5800_;
}
}
}
else
{
lean_object* v_k_5803_; lean_object* v_v_5804_; lean_object* v___x_5805_; lean_object* v___x_5807_; 
lean_dec(v_size_5549_);
v_k_5803_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_k_5803_);
v_v_5804_ = lean_ctor_get(v___x_5705_, 1);
lean_inc(v_v_5804_);
lean_dec_ref(v___x_5705_);
v___x_5805_ = lean_unsigned_to_nat(3u);
if (v_isShared_5704_ == 0)
{
lean_ctor_set(v___x_5703_, 4, v_r_5553_);
lean_ctor_set(v___x_5703_, 3, v_r_5553_);
lean_ctor_set(v___x_5703_, 2, v_v_5804_);
lean_ctor_set(v___x_5703_, 1, v_k_5803_);
lean_ctor_set(v___x_5703_, 0, v___x_5559_);
v___x_5807_ = v___x_5703_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5811_, 1, v_k_5803_);
lean_ctor_set(v_reuseFailAlloc_5811_, 2, v_v_5804_);
lean_ctor_set(v_reuseFailAlloc_5811_, 3, v_r_5553_);
lean_ctor_set(v_reuseFailAlloc_5811_, 4, v_r_5553_);
v___x_5807_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
lean_object* v___x_5809_; 
if (v_isShared_5791_ == 0)
{
lean_ctor_set(v___x_5790_, 4, v___x_5807_);
lean_ctor_set(v___x_5790_, 0, v___x_5805_);
v___x_5809_ = v___x_5790_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5810_; 
v_reuseFailAlloc_5810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5810_, 0, v___x_5805_);
lean_ctor_set(v_reuseFailAlloc_5810_, 1, v_k_5550_);
lean_ctor_set(v_reuseFailAlloc_5810_, 2, v_v_5551_);
lean_ctor_set(v_reuseFailAlloc_5810_, 3, v_l_5552_);
lean_ctor_set(v_reuseFailAlloc_5810_, 4, v___x_5807_);
v___x_5809_ = v_reuseFailAlloc_5810_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
return v___x_5809_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5553_) == 0)
{
lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5842_; 
lean_inc(v_l_5552_);
lean_inc(v_v_5551_);
lean_inc(v_k_5550_);
v_isSharedCheck_5842_ = !lean_is_exclusive(v_l_5369_);
if (v_isSharedCheck_5842_ == 0)
{
lean_object* v_unused_5843_; lean_object* v_unused_5844_; lean_object* v_unused_5845_; lean_object* v_unused_5846_; lean_object* v_unused_5847_; 
v_unused_5843_ = lean_ctor_get(v_l_5369_, 4);
lean_dec(v_unused_5843_);
v_unused_5844_ = lean_ctor_get(v_l_5369_, 3);
lean_dec(v_unused_5844_);
v_unused_5845_ = lean_ctor_get(v_l_5369_, 2);
lean_dec(v_unused_5845_);
v_unused_5846_ = lean_ctor_get(v_l_5369_, 1);
lean_dec(v_unused_5846_);
v_unused_5847_ = lean_ctor_get(v_l_5369_, 0);
lean_dec(v_unused_5847_);
v___x_5819_ = v_l_5369_;
v_isShared_5820_ = v_isSharedCheck_5842_;
goto v_resetjp_5818_;
}
else
{
lean_dec(v_l_5369_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5842_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
lean_object* v_k_5821_; lean_object* v_v_5822_; lean_object* v_k_5823_; lean_object* v_v_5824_; lean_object* v___x_5826_; uint8_t v_isShared_5827_; uint8_t v_isSharedCheck_5838_; 
v_k_5821_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_k_5821_);
v_v_5822_ = lean_ctor_get(v___x_5705_, 1);
lean_inc(v_v_5822_);
lean_dec_ref(v___x_5705_);
v_k_5823_ = lean_ctor_get(v_r_5553_, 1);
v_v_5824_ = lean_ctor_get(v_r_5553_, 2);
v_isSharedCheck_5838_ = !lean_is_exclusive(v_r_5553_);
if (v_isSharedCheck_5838_ == 0)
{
lean_object* v_unused_5839_; lean_object* v_unused_5840_; lean_object* v_unused_5841_; 
v_unused_5839_ = lean_ctor_get(v_r_5553_, 4);
lean_dec(v_unused_5839_);
v_unused_5840_ = lean_ctor_get(v_r_5553_, 3);
lean_dec(v_unused_5840_);
v_unused_5841_ = lean_ctor_get(v_r_5553_, 0);
lean_dec(v_unused_5841_);
v___x_5826_ = v_r_5553_;
v_isShared_5827_ = v_isSharedCheck_5838_;
goto v_resetjp_5825_;
}
else
{
lean_inc(v_v_5824_);
lean_inc(v_k_5823_);
lean_dec(v_r_5553_);
v___x_5826_ = lean_box(0);
v_isShared_5827_ = v_isSharedCheck_5838_;
goto v_resetjp_5825_;
}
v_resetjp_5825_:
{
lean_object* v___x_5828_; lean_object* v___x_5830_; 
v___x_5828_ = lean_unsigned_to_nat(3u);
if (v_isShared_5827_ == 0)
{
lean_ctor_set(v___x_5826_, 4, v_l_5552_);
lean_ctor_set(v___x_5826_, 3, v_l_5552_);
lean_ctor_set(v___x_5826_, 2, v_v_5551_);
lean_ctor_set(v___x_5826_, 1, v_k_5550_);
lean_ctor_set(v___x_5826_, 0, v___x_5559_);
v___x_5830_ = v___x_5826_;
goto v_reusejp_5829_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5837_, 1, v_k_5550_);
lean_ctor_set(v_reuseFailAlloc_5837_, 2, v_v_5551_);
lean_ctor_set(v_reuseFailAlloc_5837_, 3, v_l_5552_);
lean_ctor_set(v_reuseFailAlloc_5837_, 4, v_l_5552_);
v___x_5830_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5829_;
}
v_reusejp_5829_:
{
lean_object* v___x_5832_; 
if (v_isShared_5704_ == 0)
{
lean_ctor_set(v___x_5703_, 4, v_l_5552_);
lean_ctor_set(v___x_5703_, 3, v_l_5552_);
lean_ctor_set(v___x_5703_, 2, v_v_5822_);
lean_ctor_set(v___x_5703_, 1, v_k_5821_);
lean_ctor_set(v___x_5703_, 0, v___x_5559_);
v___x_5832_ = v___x_5703_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5836_, 1, v_k_5821_);
lean_ctor_set(v_reuseFailAlloc_5836_, 2, v_v_5822_);
lean_ctor_set(v_reuseFailAlloc_5836_, 3, v_l_5552_);
lean_ctor_set(v_reuseFailAlloc_5836_, 4, v_l_5552_);
v___x_5832_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
lean_object* v___x_5834_; 
if (v_isShared_5820_ == 0)
{
lean_ctor_set(v___x_5819_, 4, v___x_5832_);
lean_ctor_set(v___x_5819_, 3, v___x_5830_);
lean_ctor_set(v___x_5819_, 2, v_v_5824_);
lean_ctor_set(v___x_5819_, 1, v_k_5823_);
lean_ctor_set(v___x_5819_, 0, v___x_5828_);
v___x_5834_ = v___x_5819_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v___x_5828_);
lean_ctor_set(v_reuseFailAlloc_5835_, 1, v_k_5823_);
lean_ctor_set(v_reuseFailAlloc_5835_, 2, v_v_5824_);
lean_ctor_set(v_reuseFailAlloc_5835_, 3, v___x_5830_);
lean_ctor_set(v_reuseFailAlloc_5835_, 4, v___x_5832_);
v___x_5834_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
return v___x_5834_;
}
}
}
}
}
}
else
{
lean_object* v_k_5848_; lean_object* v_v_5849_; lean_object* v___x_5850_; lean_object* v___x_5852_; 
v_k_5848_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_k_5848_);
v_v_5849_ = lean_ctor_get(v___x_5705_, 1);
lean_inc(v_v_5849_);
lean_dec_ref(v___x_5705_);
v___x_5850_ = lean_unsigned_to_nat(2u);
if (v_isShared_5704_ == 0)
{
lean_ctor_set(v___x_5703_, 4, v_r_5553_);
lean_ctor_set(v___x_5703_, 3, v_l_5369_);
lean_ctor_set(v___x_5703_, 2, v_v_5849_);
lean_ctor_set(v___x_5703_, 1, v_k_5848_);
lean_ctor_set(v___x_5703_, 0, v___x_5850_);
v___x_5852_ = v___x_5703_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5853_; 
v_reuseFailAlloc_5853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5853_, 0, v___x_5850_);
lean_ctor_set(v_reuseFailAlloc_5853_, 1, v_k_5848_);
lean_ctor_set(v_reuseFailAlloc_5853_, 2, v_v_5849_);
lean_ctor_set(v_reuseFailAlloc_5853_, 3, v_l_5369_);
lean_ctor_set(v_reuseFailAlloc_5853_, 4, v_r_5553_);
v___x_5852_ = v_reuseFailAlloc_5853_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
return v___x_5852_;
}
}
}
}
}
}
}
else
{
return v_l_5369_;
}
}
else
{
return v_r_5370_;
}
}
default: 
{
lean_object* v_impl_5860_; lean_object* v___x_5861_; 
v_impl_5860_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5365_, v_r_5370_);
v___x_5861_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5860_) == 0)
{
if (lean_obj_tag(v_l_5369_) == 0)
{
lean_object* v_size_5862_; lean_object* v_size_5863_; lean_object* v_k_5864_; lean_object* v_v_5865_; lean_object* v_l_5866_; lean_object* v_r_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; uint8_t v___x_5870_; 
v_size_5862_ = lean_ctor_get(v_impl_5860_, 0);
v_size_5863_ = lean_ctor_get(v_l_5369_, 0);
v_k_5864_ = lean_ctor_get(v_l_5369_, 1);
v_v_5865_ = lean_ctor_get(v_l_5369_, 2);
v_l_5866_ = lean_ctor_get(v_l_5369_, 3);
v_r_5867_ = lean_ctor_get(v_l_5369_, 4);
lean_inc(v_r_5867_);
v___x_5868_ = lean_unsigned_to_nat(3u);
v___x_5869_ = lean_nat_mul(v___x_5868_, v_size_5862_);
v___x_5870_ = lean_nat_dec_lt(v___x_5869_, v_size_5863_);
lean_dec(v___x_5869_);
if (v___x_5870_ == 0)
{
lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5874_; 
lean_dec(v_r_5867_);
v___x_5871_ = lean_nat_add(v___x_5861_, v_size_5863_);
v___x_5872_ = lean_nat_add(v___x_5871_, v_size_5862_);
lean_dec(v___x_5871_);
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v_impl_5860_);
lean_ctor_set(v___x_5372_, 0, v___x_5872_);
v___x_5874_ = v___x_5372_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v___x_5872_);
lean_ctor_set(v_reuseFailAlloc_5875_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5875_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5875_, 3, v_l_5369_);
lean_ctor_set(v_reuseFailAlloc_5875_, 4, v_impl_5860_);
v___x_5874_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
return v___x_5874_;
}
}
else
{
lean_object* v___x_5877_; uint8_t v_isShared_5878_; uint8_t v_isSharedCheck_5941_; 
lean_inc(v_l_5866_);
lean_inc(v_v_5865_);
lean_inc(v_k_5864_);
lean_inc(v_size_5863_);
v_isSharedCheck_5941_ = !lean_is_exclusive(v_l_5369_);
if (v_isSharedCheck_5941_ == 0)
{
lean_object* v_unused_5942_; lean_object* v_unused_5943_; lean_object* v_unused_5944_; lean_object* v_unused_5945_; lean_object* v_unused_5946_; 
v_unused_5942_ = lean_ctor_get(v_l_5369_, 4);
lean_dec(v_unused_5942_);
v_unused_5943_ = lean_ctor_get(v_l_5369_, 3);
lean_dec(v_unused_5943_);
v_unused_5944_ = lean_ctor_get(v_l_5369_, 2);
lean_dec(v_unused_5944_);
v_unused_5945_ = lean_ctor_get(v_l_5369_, 1);
lean_dec(v_unused_5945_);
v_unused_5946_ = lean_ctor_get(v_l_5369_, 0);
lean_dec(v_unused_5946_);
v___x_5877_ = v_l_5369_;
v_isShared_5878_ = v_isSharedCheck_5941_;
goto v_resetjp_5876_;
}
else
{
lean_dec(v_l_5369_);
v___x_5877_ = lean_box(0);
v_isShared_5878_ = v_isSharedCheck_5941_;
goto v_resetjp_5876_;
}
v_resetjp_5876_:
{
lean_object* v_size_5879_; lean_object* v_size_5880_; lean_object* v_k_5881_; lean_object* v_v_5882_; lean_object* v_l_5883_; lean_object* v_r_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; uint8_t v___x_5887_; 
v_size_5879_ = lean_ctor_get(v_l_5866_, 0);
v_size_5880_ = lean_ctor_get(v_r_5867_, 0);
v_k_5881_ = lean_ctor_get(v_r_5867_, 1);
v_v_5882_ = lean_ctor_get(v_r_5867_, 2);
v_l_5883_ = lean_ctor_get(v_r_5867_, 3);
v_r_5884_ = lean_ctor_get(v_r_5867_, 4);
v___x_5885_ = lean_unsigned_to_nat(2u);
v___x_5886_ = lean_nat_mul(v___x_5885_, v_size_5879_);
v___x_5887_ = lean_nat_dec_lt(v_size_5880_, v___x_5886_);
lean_dec(v___x_5886_);
if (v___x_5887_ == 0)
{
lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5916_; 
lean_inc(v_r_5884_);
lean_inc(v_l_5883_);
lean_inc(v_v_5882_);
lean_inc(v_k_5881_);
v_isSharedCheck_5916_ = !lean_is_exclusive(v_r_5867_);
if (v_isSharedCheck_5916_ == 0)
{
lean_object* v_unused_5917_; lean_object* v_unused_5918_; lean_object* v_unused_5919_; lean_object* v_unused_5920_; lean_object* v_unused_5921_; 
v_unused_5917_ = lean_ctor_get(v_r_5867_, 4);
lean_dec(v_unused_5917_);
v_unused_5918_ = lean_ctor_get(v_r_5867_, 3);
lean_dec(v_unused_5918_);
v_unused_5919_ = lean_ctor_get(v_r_5867_, 2);
lean_dec(v_unused_5919_);
v_unused_5920_ = lean_ctor_get(v_r_5867_, 1);
lean_dec(v_unused_5920_);
v_unused_5921_ = lean_ctor_get(v_r_5867_, 0);
lean_dec(v_unused_5921_);
v___x_5889_ = v_r_5867_;
v_isShared_5890_ = v_isSharedCheck_5916_;
goto v_resetjp_5888_;
}
else
{
lean_dec(v_r_5867_);
v___x_5889_ = lean_box(0);
v_isShared_5890_ = v_isSharedCheck_5916_;
goto v_resetjp_5888_;
}
v_resetjp_5888_:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___y_5894_; lean_object* v___y_5895_; lean_object* v___y_5896_; lean_object* v___x_5904_; lean_object* v___y_5906_; 
v___x_5891_ = lean_nat_add(v___x_5861_, v_size_5863_);
lean_dec(v_size_5863_);
v___x_5892_ = lean_nat_add(v___x_5891_, v_size_5862_);
lean_dec(v___x_5891_);
v___x_5904_ = lean_nat_add(v___x_5861_, v_size_5879_);
if (lean_obj_tag(v_l_5883_) == 0)
{
lean_object* v_size_5914_; 
v_size_5914_ = lean_ctor_get(v_l_5883_, 0);
lean_inc(v_size_5914_);
v___y_5906_ = v_size_5914_;
goto v___jp_5905_;
}
else
{
lean_object* v___x_5915_; 
v___x_5915_ = lean_unsigned_to_nat(0u);
v___y_5906_ = v___x_5915_;
goto v___jp_5905_;
}
v___jp_5893_:
{
lean_object* v___x_5897_; lean_object* v___x_5899_; 
v___x_5897_ = lean_nat_add(v___y_5894_, v___y_5896_);
lean_dec(v___y_5896_);
lean_dec(v___y_5894_);
if (v_isShared_5890_ == 0)
{
lean_ctor_set(v___x_5889_, 4, v_impl_5860_);
lean_ctor_set(v___x_5889_, 3, v_r_5884_);
lean_ctor_set(v___x_5889_, 2, v_v_5368_);
lean_ctor_set(v___x_5889_, 1, v_k_5367_);
lean_ctor_set(v___x_5889_, 0, v___x_5897_);
v___x_5899_ = v___x_5889_;
goto v_reusejp_5898_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v___x_5897_);
lean_ctor_set(v_reuseFailAlloc_5903_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5903_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5903_, 3, v_r_5884_);
lean_ctor_set(v_reuseFailAlloc_5903_, 4, v_impl_5860_);
v___x_5899_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5898_;
}
v_reusejp_5898_:
{
lean_object* v___x_5901_; 
if (v_isShared_5878_ == 0)
{
lean_ctor_set(v___x_5877_, 4, v___x_5899_);
lean_ctor_set(v___x_5877_, 3, v___y_5895_);
lean_ctor_set(v___x_5877_, 2, v_v_5882_);
lean_ctor_set(v___x_5877_, 1, v_k_5881_);
lean_ctor_set(v___x_5877_, 0, v___x_5892_);
v___x_5901_ = v___x_5877_;
goto v_reusejp_5900_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v___x_5892_);
lean_ctor_set(v_reuseFailAlloc_5902_, 1, v_k_5881_);
lean_ctor_set(v_reuseFailAlloc_5902_, 2, v_v_5882_);
lean_ctor_set(v_reuseFailAlloc_5902_, 3, v___y_5895_);
lean_ctor_set(v_reuseFailAlloc_5902_, 4, v___x_5899_);
v___x_5901_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5900_;
}
v_reusejp_5900_:
{
return v___x_5901_;
}
}
}
v___jp_5905_:
{
lean_object* v___x_5907_; lean_object* v___x_5909_; 
v___x_5907_ = lean_nat_add(v___x_5904_, v___y_5906_);
lean_dec(v___y_5906_);
lean_dec(v___x_5904_);
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v_l_5883_);
lean_ctor_set(v___x_5372_, 3, v_l_5866_);
lean_ctor_set(v___x_5372_, 2, v_v_5865_);
lean_ctor_set(v___x_5372_, 1, v_k_5864_);
lean_ctor_set(v___x_5372_, 0, v___x_5907_);
v___x_5909_ = v___x_5372_;
goto v_reusejp_5908_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v___x_5907_);
lean_ctor_set(v_reuseFailAlloc_5913_, 1, v_k_5864_);
lean_ctor_set(v_reuseFailAlloc_5913_, 2, v_v_5865_);
lean_ctor_set(v_reuseFailAlloc_5913_, 3, v_l_5866_);
lean_ctor_set(v_reuseFailAlloc_5913_, 4, v_l_5883_);
v___x_5909_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5908_;
}
v_reusejp_5908_:
{
lean_object* v___x_5910_; 
v___x_5910_ = lean_nat_add(v___x_5861_, v_size_5862_);
if (lean_obj_tag(v_r_5884_) == 0)
{
lean_object* v_size_5911_; 
v_size_5911_ = lean_ctor_get(v_r_5884_, 0);
lean_inc(v_size_5911_);
v___y_5894_ = v___x_5910_;
v___y_5895_ = v___x_5909_;
v___y_5896_ = v_size_5911_;
goto v___jp_5893_;
}
else
{
lean_object* v___x_5912_; 
v___x_5912_ = lean_unsigned_to_nat(0u);
v___y_5894_ = v___x_5910_;
v___y_5895_ = v___x_5909_;
v___y_5896_ = v___x_5912_;
goto v___jp_5893_;
}
}
}
}
}
else
{
lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5927_; 
lean_del_object(v___x_5372_);
v___x_5922_ = lean_nat_add(v___x_5861_, v_size_5863_);
lean_dec(v_size_5863_);
v___x_5923_ = lean_nat_add(v___x_5922_, v_size_5862_);
lean_dec(v___x_5922_);
v___x_5924_ = lean_nat_add(v___x_5861_, v_size_5862_);
v___x_5925_ = lean_nat_add(v___x_5924_, v_size_5880_);
lean_dec(v___x_5924_);
lean_inc_ref(v_impl_5860_);
if (v_isShared_5878_ == 0)
{
lean_ctor_set(v___x_5877_, 4, v_impl_5860_);
lean_ctor_set(v___x_5877_, 3, v_r_5867_);
lean_ctor_set(v___x_5877_, 2, v_v_5368_);
lean_ctor_set(v___x_5877_, 1, v_k_5367_);
lean_ctor_set(v___x_5877_, 0, v___x_5925_);
v___x_5927_ = v___x_5877_;
goto v_reusejp_5926_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5940_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5940_, 3, v_r_5867_);
lean_ctor_set(v_reuseFailAlloc_5940_, 4, v_impl_5860_);
v___x_5927_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5926_;
}
v_reusejp_5926_:
{
lean_object* v___x_5929_; uint8_t v_isShared_5930_; uint8_t v_isSharedCheck_5934_; 
v_isSharedCheck_5934_ = !lean_is_exclusive(v_impl_5860_);
if (v_isSharedCheck_5934_ == 0)
{
lean_object* v_unused_5935_; lean_object* v_unused_5936_; lean_object* v_unused_5937_; lean_object* v_unused_5938_; lean_object* v_unused_5939_; 
v_unused_5935_ = lean_ctor_get(v_impl_5860_, 4);
lean_dec(v_unused_5935_);
v_unused_5936_ = lean_ctor_get(v_impl_5860_, 3);
lean_dec(v_unused_5936_);
v_unused_5937_ = lean_ctor_get(v_impl_5860_, 2);
lean_dec(v_unused_5937_);
v_unused_5938_ = lean_ctor_get(v_impl_5860_, 1);
lean_dec(v_unused_5938_);
v_unused_5939_ = lean_ctor_get(v_impl_5860_, 0);
lean_dec(v_unused_5939_);
v___x_5929_ = v_impl_5860_;
v_isShared_5930_ = v_isSharedCheck_5934_;
goto v_resetjp_5928_;
}
else
{
lean_dec(v_impl_5860_);
v___x_5929_ = lean_box(0);
v_isShared_5930_ = v_isSharedCheck_5934_;
goto v_resetjp_5928_;
}
v_resetjp_5928_:
{
lean_object* v___x_5932_; 
if (v_isShared_5930_ == 0)
{
lean_ctor_set(v___x_5929_, 4, v___x_5927_);
lean_ctor_set(v___x_5929_, 3, v_l_5866_);
lean_ctor_set(v___x_5929_, 2, v_v_5865_);
lean_ctor_set(v___x_5929_, 1, v_k_5864_);
lean_ctor_set(v___x_5929_, 0, v___x_5923_);
v___x_5932_ = v___x_5929_;
goto v_reusejp_5931_;
}
else
{
lean_object* v_reuseFailAlloc_5933_; 
v_reuseFailAlloc_5933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5933_, 0, v___x_5923_);
lean_ctor_set(v_reuseFailAlloc_5933_, 1, v_k_5864_);
lean_ctor_set(v_reuseFailAlloc_5933_, 2, v_v_5865_);
lean_ctor_set(v_reuseFailAlloc_5933_, 3, v_l_5866_);
lean_ctor_set(v_reuseFailAlloc_5933_, 4, v___x_5927_);
v___x_5932_ = v_reuseFailAlloc_5933_;
goto v_reusejp_5931_;
}
v_reusejp_5931_:
{
return v___x_5932_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5947_; lean_object* v___x_5948_; lean_object* v___x_5950_; 
v_size_5947_ = lean_ctor_get(v_impl_5860_, 0);
v___x_5948_ = lean_nat_add(v___x_5861_, v_size_5947_);
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v_impl_5860_);
lean_ctor_set(v___x_5372_, 0, v___x_5948_);
v___x_5950_ = v___x_5372_;
goto v_reusejp_5949_;
}
else
{
lean_object* v_reuseFailAlloc_5951_; 
v_reuseFailAlloc_5951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5951_, 0, v___x_5948_);
lean_ctor_set(v_reuseFailAlloc_5951_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5951_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5951_, 3, v_l_5369_);
lean_ctor_set(v_reuseFailAlloc_5951_, 4, v_impl_5860_);
v___x_5950_ = v_reuseFailAlloc_5951_;
goto v_reusejp_5949_;
}
v_reusejp_5949_:
{
return v___x_5950_;
}
}
}
else
{
if (lean_obj_tag(v_l_5369_) == 0)
{
lean_object* v_l_5952_; 
v_l_5952_ = lean_ctor_get(v_l_5369_, 3);
if (lean_obj_tag(v_l_5952_) == 0)
{
lean_object* v_r_5953_; 
lean_inc_ref(v_l_5952_);
v_r_5953_ = lean_ctor_get(v_l_5369_, 4);
lean_inc(v_r_5953_);
if (lean_obj_tag(v_r_5953_) == 0)
{
lean_object* v_size_5954_; lean_object* v_k_5955_; lean_object* v_v_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5969_; 
v_size_5954_ = lean_ctor_get(v_l_5369_, 0);
v_k_5955_ = lean_ctor_get(v_l_5369_, 1);
v_v_5956_ = lean_ctor_get(v_l_5369_, 2);
v_isSharedCheck_5969_ = !lean_is_exclusive(v_l_5369_);
if (v_isSharedCheck_5969_ == 0)
{
lean_object* v_unused_5970_; lean_object* v_unused_5971_; 
v_unused_5970_ = lean_ctor_get(v_l_5369_, 4);
lean_dec(v_unused_5970_);
v_unused_5971_ = lean_ctor_get(v_l_5369_, 3);
lean_dec(v_unused_5971_);
v___x_5958_ = v_l_5369_;
v_isShared_5959_ = v_isSharedCheck_5969_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_v_5956_);
lean_inc(v_k_5955_);
lean_inc(v_size_5954_);
lean_dec(v_l_5369_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5969_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v_size_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5964_; 
v_size_5960_ = lean_ctor_get(v_r_5953_, 0);
v___x_5961_ = lean_nat_add(v___x_5861_, v_size_5954_);
lean_dec(v_size_5954_);
v___x_5962_ = lean_nat_add(v___x_5861_, v_size_5960_);
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 4, v_impl_5860_);
lean_ctor_set(v___x_5958_, 3, v_r_5953_);
lean_ctor_set(v___x_5958_, 2, v_v_5368_);
lean_ctor_set(v___x_5958_, 1, v_k_5367_);
lean_ctor_set(v___x_5958_, 0, v___x_5962_);
v___x_5964_ = v___x_5958_;
goto v_reusejp_5963_;
}
else
{
lean_object* v_reuseFailAlloc_5968_; 
v_reuseFailAlloc_5968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5968_, 0, v___x_5962_);
lean_ctor_set(v_reuseFailAlloc_5968_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5968_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5968_, 3, v_r_5953_);
lean_ctor_set(v_reuseFailAlloc_5968_, 4, v_impl_5860_);
v___x_5964_ = v_reuseFailAlloc_5968_;
goto v_reusejp_5963_;
}
v_reusejp_5963_:
{
lean_object* v___x_5966_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v___x_5964_);
lean_ctor_set(v___x_5372_, 3, v_l_5952_);
lean_ctor_set(v___x_5372_, 2, v_v_5956_);
lean_ctor_set(v___x_5372_, 1, v_k_5955_);
lean_ctor_set(v___x_5372_, 0, v___x_5961_);
v___x_5966_ = v___x_5372_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5967_; 
v_reuseFailAlloc_5967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5967_, 0, v___x_5961_);
lean_ctor_set(v_reuseFailAlloc_5967_, 1, v_k_5955_);
lean_ctor_set(v_reuseFailAlloc_5967_, 2, v_v_5956_);
lean_ctor_set(v_reuseFailAlloc_5967_, 3, v_l_5952_);
lean_ctor_set(v_reuseFailAlloc_5967_, 4, v___x_5964_);
v___x_5966_ = v_reuseFailAlloc_5967_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
return v___x_5966_;
}
}
}
}
else
{
lean_object* v_k_5972_; lean_object* v_v_5973_; lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_5984_; 
v_k_5972_ = lean_ctor_get(v_l_5369_, 1);
v_v_5973_ = lean_ctor_get(v_l_5369_, 2);
v_isSharedCheck_5984_ = !lean_is_exclusive(v_l_5369_);
if (v_isSharedCheck_5984_ == 0)
{
lean_object* v_unused_5985_; lean_object* v_unused_5986_; lean_object* v_unused_5987_; 
v_unused_5985_ = lean_ctor_get(v_l_5369_, 4);
lean_dec(v_unused_5985_);
v_unused_5986_ = lean_ctor_get(v_l_5369_, 3);
lean_dec(v_unused_5986_);
v_unused_5987_ = lean_ctor_get(v_l_5369_, 0);
lean_dec(v_unused_5987_);
v___x_5975_ = v_l_5369_;
v_isShared_5976_ = v_isSharedCheck_5984_;
goto v_resetjp_5974_;
}
else
{
lean_inc(v_v_5973_);
lean_inc(v_k_5972_);
lean_dec(v_l_5369_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_5984_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v___x_5977_; lean_object* v___x_5979_; 
v___x_5977_ = lean_unsigned_to_nat(3u);
if (v_isShared_5976_ == 0)
{
lean_ctor_set(v___x_5975_, 3, v_r_5953_);
lean_ctor_set(v___x_5975_, 2, v_v_5368_);
lean_ctor_set(v___x_5975_, 1, v_k_5367_);
lean_ctor_set(v___x_5975_, 0, v___x_5861_);
v___x_5979_ = v___x_5975_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v___x_5861_);
lean_ctor_set(v_reuseFailAlloc_5983_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_5983_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_5983_, 3, v_r_5953_);
lean_ctor_set(v_reuseFailAlloc_5983_, 4, v_r_5953_);
v___x_5979_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
lean_object* v___x_5981_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v___x_5979_);
lean_ctor_set(v___x_5372_, 3, v_l_5952_);
lean_ctor_set(v___x_5372_, 2, v_v_5973_);
lean_ctor_set(v___x_5372_, 1, v_k_5972_);
lean_ctor_set(v___x_5372_, 0, v___x_5977_);
v___x_5981_ = v___x_5372_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v___x_5977_);
lean_ctor_set(v_reuseFailAlloc_5982_, 1, v_k_5972_);
lean_ctor_set(v_reuseFailAlloc_5982_, 2, v_v_5973_);
lean_ctor_set(v_reuseFailAlloc_5982_, 3, v_l_5952_);
lean_ctor_set(v_reuseFailAlloc_5982_, 4, v___x_5979_);
v___x_5981_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
return v___x_5981_;
}
}
}
}
}
else
{
lean_object* v_r_5988_; 
v_r_5988_ = lean_ctor_get(v_l_5369_, 4);
lean_inc(v_r_5988_);
if (lean_obj_tag(v_r_5988_) == 0)
{
lean_object* v_k_5989_; lean_object* v_v_5990_; lean_object* v___x_5992_; uint8_t v_isShared_5993_; uint8_t v_isSharedCheck_6013_; 
lean_inc(v_l_5952_);
v_k_5989_ = lean_ctor_get(v_l_5369_, 1);
v_v_5990_ = lean_ctor_get(v_l_5369_, 2);
v_isSharedCheck_6013_ = !lean_is_exclusive(v_l_5369_);
if (v_isSharedCheck_6013_ == 0)
{
lean_object* v_unused_6014_; lean_object* v_unused_6015_; lean_object* v_unused_6016_; 
v_unused_6014_ = lean_ctor_get(v_l_5369_, 4);
lean_dec(v_unused_6014_);
v_unused_6015_ = lean_ctor_get(v_l_5369_, 3);
lean_dec(v_unused_6015_);
v_unused_6016_ = lean_ctor_get(v_l_5369_, 0);
lean_dec(v_unused_6016_);
v___x_5992_ = v_l_5369_;
v_isShared_5993_ = v_isSharedCheck_6013_;
goto v_resetjp_5991_;
}
else
{
lean_inc(v_v_5990_);
lean_inc(v_k_5989_);
lean_dec(v_l_5369_);
v___x_5992_ = lean_box(0);
v_isShared_5993_ = v_isSharedCheck_6013_;
goto v_resetjp_5991_;
}
v_resetjp_5991_:
{
lean_object* v_k_5994_; lean_object* v_v_5995_; lean_object* v___x_5997_; uint8_t v_isShared_5998_; uint8_t v_isSharedCheck_6009_; 
v_k_5994_ = lean_ctor_get(v_r_5988_, 1);
v_v_5995_ = lean_ctor_get(v_r_5988_, 2);
v_isSharedCheck_6009_ = !lean_is_exclusive(v_r_5988_);
if (v_isSharedCheck_6009_ == 0)
{
lean_object* v_unused_6010_; lean_object* v_unused_6011_; lean_object* v_unused_6012_; 
v_unused_6010_ = lean_ctor_get(v_r_5988_, 4);
lean_dec(v_unused_6010_);
v_unused_6011_ = lean_ctor_get(v_r_5988_, 3);
lean_dec(v_unused_6011_);
v_unused_6012_ = lean_ctor_get(v_r_5988_, 0);
lean_dec(v_unused_6012_);
v___x_5997_ = v_r_5988_;
v_isShared_5998_ = v_isSharedCheck_6009_;
goto v_resetjp_5996_;
}
else
{
lean_inc(v_v_5995_);
lean_inc(v_k_5994_);
lean_dec(v_r_5988_);
v___x_5997_ = lean_box(0);
v_isShared_5998_ = v_isSharedCheck_6009_;
goto v_resetjp_5996_;
}
v_resetjp_5996_:
{
lean_object* v___x_5999_; lean_object* v___x_6001_; 
v___x_5999_ = lean_unsigned_to_nat(3u);
if (v_isShared_5998_ == 0)
{
lean_ctor_set(v___x_5997_, 4, v_l_5952_);
lean_ctor_set(v___x_5997_, 3, v_l_5952_);
lean_ctor_set(v___x_5997_, 2, v_v_5990_);
lean_ctor_set(v___x_5997_, 1, v_k_5989_);
lean_ctor_set(v___x_5997_, 0, v___x_5861_);
v___x_6001_ = v___x_5997_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v___x_5861_);
lean_ctor_set(v_reuseFailAlloc_6008_, 1, v_k_5989_);
lean_ctor_set(v_reuseFailAlloc_6008_, 2, v_v_5990_);
lean_ctor_set(v_reuseFailAlloc_6008_, 3, v_l_5952_);
lean_ctor_set(v_reuseFailAlloc_6008_, 4, v_l_5952_);
v___x_6001_ = v_reuseFailAlloc_6008_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
lean_object* v___x_6003_; 
if (v_isShared_5993_ == 0)
{
lean_ctor_set(v___x_5992_, 4, v_l_5952_);
lean_ctor_set(v___x_5992_, 2, v_v_5368_);
lean_ctor_set(v___x_5992_, 1, v_k_5367_);
lean_ctor_set(v___x_5992_, 0, v___x_5861_);
v___x_6003_ = v___x_5992_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v___x_5861_);
lean_ctor_set(v_reuseFailAlloc_6007_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_6007_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_6007_, 3, v_l_5952_);
lean_ctor_set(v_reuseFailAlloc_6007_, 4, v_l_5952_);
v___x_6003_ = v_reuseFailAlloc_6007_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
lean_object* v___x_6005_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v___x_6003_);
lean_ctor_set(v___x_5372_, 3, v___x_6001_);
lean_ctor_set(v___x_5372_, 2, v_v_5995_);
lean_ctor_set(v___x_5372_, 1, v_k_5994_);
lean_ctor_set(v___x_5372_, 0, v___x_5999_);
v___x_6005_ = v___x_5372_;
goto v_reusejp_6004_;
}
else
{
lean_object* v_reuseFailAlloc_6006_; 
v_reuseFailAlloc_6006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6006_, 0, v___x_5999_);
lean_ctor_set(v_reuseFailAlloc_6006_, 1, v_k_5994_);
lean_ctor_set(v_reuseFailAlloc_6006_, 2, v_v_5995_);
lean_ctor_set(v_reuseFailAlloc_6006_, 3, v___x_6001_);
lean_ctor_set(v_reuseFailAlloc_6006_, 4, v___x_6003_);
v___x_6005_ = v_reuseFailAlloc_6006_;
goto v_reusejp_6004_;
}
v_reusejp_6004_:
{
return v___x_6005_;
}
}
}
}
}
}
else
{
lean_object* v___x_6017_; lean_object* v___x_6019_; 
v___x_6017_ = lean_unsigned_to_nat(2u);
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v_r_5988_);
lean_ctor_set(v___x_5372_, 0, v___x_6017_);
v___x_6019_ = v___x_5372_;
goto v_reusejp_6018_;
}
else
{
lean_object* v_reuseFailAlloc_6020_; 
v_reuseFailAlloc_6020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6020_, 0, v___x_6017_);
lean_ctor_set(v_reuseFailAlloc_6020_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_6020_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_6020_, 3, v_l_5369_);
lean_ctor_set(v_reuseFailAlloc_6020_, 4, v_r_5988_);
v___x_6019_ = v_reuseFailAlloc_6020_;
goto v_reusejp_6018_;
}
v_reusejp_6018_:
{
return v___x_6019_;
}
}
}
}
else
{
lean_object* v___x_6022_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 4, v_l_5369_);
lean_ctor_set(v___x_5372_, 0, v___x_5861_);
v___x_6022_ = v___x_5372_;
goto v_reusejp_6021_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v___x_5861_);
lean_ctor_set(v_reuseFailAlloc_6023_, 1, v_k_5367_);
lean_ctor_set(v_reuseFailAlloc_6023_, 2, v_v_5368_);
lean_ctor_set(v_reuseFailAlloc_6023_, 3, v_l_5369_);
lean_ctor_set(v_reuseFailAlloc_6023_, 4, v_l_5369_);
v___x_6022_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6021_;
}
v_reusejp_6021_:
{
return v___x_6022_;
}
}
}
}
}
}
}
else
{
return v_t_5366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_6026_, lean_object* v_t_6027_){
_start:
{
lean_object* v_res_6028_; 
v_res_6028_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6026_, v_t_6027_);
lean_dec(v_k_6026_);
return v_res_6028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_6029_, lean_object* v_x_6030_){
_start:
{
if (lean_obj_tag(v_x_6030_) == 0)
{
lean_object* v_k_6031_; lean_object* v_l_6032_; lean_object* v_r_6033_; lean_object* v___x_6034_; lean_object* v_ileans_6035_; lean_object* v_workers_6036_; lean_object* v___x_6038_; uint8_t v_isShared_6039_; uint8_t v_isSharedCheck_6045_; 
v_k_6031_ = lean_ctor_get(v_x_6030_, 1);
v_l_6032_ = lean_ctor_get(v_x_6030_, 3);
v_r_6033_ = lean_ctor_get(v_x_6030_, 4);
v___x_6034_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6029_, v_l_6032_);
v_ileans_6035_ = lean_ctor_get(v___x_6034_, 0);
v_workers_6036_ = lean_ctor_get(v___x_6034_, 1);
v_isSharedCheck_6045_ = !lean_is_exclusive(v___x_6034_);
if (v_isSharedCheck_6045_ == 0)
{
v___x_6038_ = v___x_6034_;
v_isShared_6039_ = v_isSharedCheck_6045_;
goto v_resetjp_6037_;
}
else
{
lean_inc(v_workers_6036_);
lean_inc(v_ileans_6035_);
lean_dec(v___x_6034_);
v___x_6038_ = lean_box(0);
v_isShared_6039_ = v_isSharedCheck_6045_;
goto v_resetjp_6037_;
}
v_resetjp_6037_:
{
lean_object* v___x_6040_; lean_object* v___x_6042_; 
v___x_6040_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6031_, v_ileans_6035_);
if (v_isShared_6039_ == 0)
{
lean_ctor_set(v___x_6038_, 0, v___x_6040_);
v___x_6042_ = v___x_6038_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v___x_6040_);
lean_ctor_set(v_reuseFailAlloc_6044_, 1, v_workers_6036_);
v___x_6042_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
v_init_6029_ = v___x_6042_;
v_x_6030_ = v_r_6033_;
goto _start;
}
}
}
else
{
return v_init_6029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_6046_, lean_object* v_x_6047_){
_start:
{
lean_object* v_res_6048_; 
v_res_6048_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6046_, v_x_6047_);
lean_dec(v_x_6047_);
return v_res_6048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_6049_, lean_object* v_path_6050_){
_start:
{
lean_object* v_ileans_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; 
v_ileans_6051_ = lean_ctor_get(v_self_6049_, 0);
lean_inc(v_ileans_6051_);
v___x_6052_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6050_, v_ileans_6051_);
v___x_6053_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_6049_, v___x_6052_);
lean_dec(v___x_6052_);
return v___x_6053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_6054_, lean_object* v_path_6055_){
_start:
{
lean_object* v_res_6056_; 
v_res_6056_ = l_Lean_Server_References_removeIlean(v_self_6054_, v_path_6055_);
lean_dec_ref(v_path_6055_);
return v_res_6056_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_6057_, lean_object* v_k_6058_, lean_object* v_t_6059_, lean_object* v_h_6060_){
_start:
{
lean_object* v___x_6061_; 
v___x_6061_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6058_, v_t_6059_);
return v___x_6061_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_6062_, lean_object* v_k_6063_, lean_object* v_t_6064_, lean_object* v_h_6065_){
_start:
{
lean_object* v_res_6066_; 
v_res_6066_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_6062_, v_k_6063_, v_t_6064_, v_h_6065_);
lean_dec(v_k_6063_);
return v_res_6066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_6067_, lean_object* v_t_6068_, lean_object* v_hl_6069_){
_start:
{
lean_object* v___x_6070_; 
v___x_6070_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6067_, v_t_6068_);
return v___x_6070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_6071_, lean_object* v_t_6072_, lean_object* v_hl_6073_){
_start:
{
lean_object* v_res_6074_; 
v_res_6074_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_6071_, v_t_6072_, v_hl_6073_);
lean_dec_ref(v_path_6071_);
return v_res_6074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_6075_, lean_object* v_t_6076_){
_start:
{
lean_object* v___x_6077_; 
v___x_6077_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6075_, v_t_6076_);
return v___x_6077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_6078_, lean_object* v_t_6079_){
_start:
{
lean_object* v_res_6080_; 
v_res_6080_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_6078_, v_t_6079_);
lean_dec(v_t_6079_);
return v_res_6080_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_6081_, lean_object* v_k_6082_){
_start:
{
if (lean_obj_tag(v_t_6081_) == 0)
{
lean_object* v_k_6083_; lean_object* v_v_6084_; lean_object* v_l_6085_; lean_object* v_r_6086_; uint8_t v___x_6087_; 
v_k_6083_ = lean_ctor_get(v_t_6081_, 1);
v_v_6084_ = lean_ctor_get(v_t_6081_, 2);
v_l_6085_ = lean_ctor_get(v_t_6081_, 3);
v_r_6086_ = lean_ctor_get(v_t_6081_, 4);
v___x_6087_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6082_, v_k_6083_);
switch(v___x_6087_)
{
case 0:
{
v_t_6081_ = v_l_6085_;
goto _start;
}
case 1:
{
lean_object* v___x_6089_; 
lean_inc(v_v_6084_);
v___x_6089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6089_, 0, v_v_6084_);
return v___x_6089_;
}
default: 
{
v_t_6081_ = v_r_6086_;
goto _start;
}
}
}
else
{
lean_object* v___x_6091_; 
v___x_6091_ = lean_box(0);
return v___x_6091_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_6092_, lean_object* v_k_6093_){
_start:
{
lean_object* v_res_6094_; 
v_res_6094_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6092_, v_k_6093_);
lean_dec(v_k_6093_);
lean_dec(v_t_6092_);
return v_res_6094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_6095_, lean_object* v_name_6096_, lean_object* v_moduleUri_6097_, lean_object* v_version_6098_, lean_object* v_directImports_6099_, uint8_t v_isSetupFailure_6100_){
_start:
{
lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6102_ = lean_box(1);
v___x_6103_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_6099_);
if (lean_obj_tag(v___x_6103_) == 0)
{
lean_object* v_a_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6169_; 
v_a_6104_ = lean_ctor_get(v___x_6103_, 0);
v_isSharedCheck_6169_ = !lean_is_exclusive(v___x_6103_);
if (v_isSharedCheck_6169_ == 0)
{
v___x_6106_ = v___x_6103_;
v_isShared_6107_ = v_isSharedCheck_6169_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_a_6104_);
lean_dec(v___x_6103_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6169_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v_ileans_6108_; lean_object* v_workers_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; 
v_ileans_6108_ = lean_ctor_get(v_self_6095_, 0);
v_workers_6109_ = lean_ctor_get(v_self_6095_, 1);
v___x_6110_ = lean_box(v_isSetupFailure_6100_);
v___x_6111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6110_);
v___x_6112_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6109_, v_name_6096_);
if (lean_obj_tag(v___x_6112_) == 1)
{
lean_object* v_val_6113_; lean_object* v_version_6114_; lean_object* v_refs_6115_; lean_object* v_decls_6116_; lean_object* v___x_6118_; uint8_t v_isShared_6119_; uint8_t v_isSharedCheck_6151_; 
v_val_6113_ = lean_ctor_get(v___x_6112_, 0);
lean_inc(v_val_6113_);
lean_dec_ref_known(v___x_6112_, 1);
v_version_6114_ = lean_ctor_get(v_val_6113_, 1);
v_refs_6115_ = lean_ctor_get(v_val_6113_, 4);
v_decls_6116_ = lean_ctor_get(v_val_6113_, 5);
v_isSharedCheck_6151_ = !lean_is_exclusive(v_val_6113_);
if (v_isSharedCheck_6151_ == 0)
{
lean_object* v_unused_6152_; lean_object* v_unused_6153_; lean_object* v_unused_6154_; 
v_unused_6152_ = lean_ctor_get(v_val_6113_, 3);
lean_dec(v_unused_6152_);
v_unused_6153_ = lean_ctor_get(v_val_6113_, 2);
lean_dec(v_unused_6153_);
v_unused_6154_ = lean_ctor_get(v_val_6113_, 0);
lean_dec(v_unused_6154_);
v___x_6118_ = v_val_6113_;
v_isShared_6119_ = v_isSharedCheck_6151_;
goto v_resetjp_6117_;
}
else
{
lean_inc(v_decls_6116_);
lean_inc(v_refs_6115_);
lean_inc(v_version_6114_);
lean_dec(v_val_6113_);
v___x_6118_ = lean_box(0);
v_isShared_6119_ = v_isSharedCheck_6151_;
goto v_resetjp_6117_;
}
v_resetjp_6117_:
{
uint8_t v___x_6120_; 
v___x_6120_ = lean_nat_dec_lt(v_version_6098_, v_version_6114_);
if (v___x_6120_ == 0)
{
lean_object* v___x_6122_; uint8_t v_isShared_6123_; uint8_t v_isSharedCheck_6145_; 
lean_inc(v_workers_6109_);
lean_inc(v_ileans_6108_);
v_isSharedCheck_6145_ = !lean_is_exclusive(v_self_6095_);
if (v_isSharedCheck_6145_ == 0)
{
lean_object* v_unused_6146_; lean_object* v_unused_6147_; 
v_unused_6146_ = lean_ctor_get(v_self_6095_, 1);
lean_dec(v_unused_6146_);
v_unused_6147_ = lean_ctor_get(v_self_6095_, 0);
lean_dec(v_unused_6147_);
v___x_6122_ = v_self_6095_;
v_isShared_6123_ = v_isSharedCheck_6145_;
goto v_resetjp_6121_;
}
else
{
lean_dec(v_self_6095_);
v___x_6122_ = lean_box(0);
v_isShared_6123_ = v_isSharedCheck_6145_;
goto v_resetjp_6121_;
}
v_resetjp_6121_:
{
uint8_t v___x_6124_; 
v___x_6124_ = lean_nat_dec_eq(v_version_6098_, v_version_6114_);
lean_dec(v_version_6114_);
if (v___x_6124_ == 0)
{
lean_object* v___x_6126_; 
lean_dec(v_decls_6116_);
lean_dec(v_refs_6115_);
if (v_isShared_6119_ == 0)
{
lean_ctor_set(v___x_6118_, 5, v___x_6102_);
lean_ctor_set(v___x_6118_, 4, v___x_6102_);
lean_ctor_set(v___x_6118_, 3, v___x_6111_);
lean_ctor_set(v___x_6118_, 2, v_a_6104_);
lean_ctor_set(v___x_6118_, 1, v_version_6098_);
lean_ctor_set(v___x_6118_, 0, v_moduleUri_6097_);
v___x_6126_ = v___x_6118_;
goto v_reusejp_6125_;
}
else
{
lean_object* v_reuseFailAlloc_6134_; 
v_reuseFailAlloc_6134_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6134_, 0, v_moduleUri_6097_);
lean_ctor_set(v_reuseFailAlloc_6134_, 1, v_version_6098_);
lean_ctor_set(v_reuseFailAlloc_6134_, 2, v_a_6104_);
lean_ctor_set(v_reuseFailAlloc_6134_, 3, v___x_6111_);
lean_ctor_set(v_reuseFailAlloc_6134_, 4, v___x_6102_);
lean_ctor_set(v_reuseFailAlloc_6134_, 5, v___x_6102_);
v___x_6126_ = v_reuseFailAlloc_6134_;
goto v_reusejp_6125_;
}
v_reusejp_6125_:
{
lean_object* v___x_6127_; lean_object* v___x_6129_; 
v___x_6127_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6096_, v___x_6126_, v_workers_6109_);
if (v_isShared_6123_ == 0)
{
lean_ctor_set(v___x_6122_, 1, v___x_6127_);
v___x_6129_ = v___x_6122_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6133_; 
v_reuseFailAlloc_6133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6133_, 0, v_ileans_6108_);
lean_ctor_set(v_reuseFailAlloc_6133_, 1, v___x_6127_);
v___x_6129_ = v_reuseFailAlloc_6133_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
lean_object* v___x_6131_; 
if (v_isShared_6107_ == 0)
{
lean_ctor_set(v___x_6106_, 0, v___x_6129_);
v___x_6131_ = v___x_6106_;
goto v_reusejp_6130_;
}
else
{
lean_object* v_reuseFailAlloc_6132_; 
v_reuseFailAlloc_6132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6132_, 0, v___x_6129_);
v___x_6131_ = v_reuseFailAlloc_6132_;
goto v_reusejp_6130_;
}
v_reusejp_6130_:
{
return v___x_6131_;
}
}
}
}
else
{
lean_object* v___x_6136_; 
if (v_isShared_6119_ == 0)
{
lean_ctor_set(v___x_6118_, 3, v___x_6111_);
lean_ctor_set(v___x_6118_, 2, v_a_6104_);
lean_ctor_set(v___x_6118_, 1, v_version_6098_);
lean_ctor_set(v___x_6118_, 0, v_moduleUri_6097_);
v___x_6136_ = v___x_6118_;
goto v_reusejp_6135_;
}
else
{
lean_object* v_reuseFailAlloc_6144_; 
v_reuseFailAlloc_6144_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6144_, 0, v_moduleUri_6097_);
lean_ctor_set(v_reuseFailAlloc_6144_, 1, v_version_6098_);
lean_ctor_set(v_reuseFailAlloc_6144_, 2, v_a_6104_);
lean_ctor_set(v_reuseFailAlloc_6144_, 3, v___x_6111_);
lean_ctor_set(v_reuseFailAlloc_6144_, 4, v_refs_6115_);
lean_ctor_set(v_reuseFailAlloc_6144_, 5, v_decls_6116_);
v___x_6136_ = v_reuseFailAlloc_6144_;
goto v_reusejp_6135_;
}
v_reusejp_6135_:
{
lean_object* v___x_6137_; lean_object* v___x_6139_; 
v___x_6137_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6096_, v___x_6136_, v_workers_6109_);
if (v_isShared_6123_ == 0)
{
lean_ctor_set(v___x_6122_, 1, v___x_6137_);
v___x_6139_ = v___x_6122_;
goto v_reusejp_6138_;
}
else
{
lean_object* v_reuseFailAlloc_6143_; 
v_reuseFailAlloc_6143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6143_, 0, v_ileans_6108_);
lean_ctor_set(v_reuseFailAlloc_6143_, 1, v___x_6137_);
v___x_6139_ = v_reuseFailAlloc_6143_;
goto v_reusejp_6138_;
}
v_reusejp_6138_:
{
lean_object* v___x_6141_; 
if (v_isShared_6107_ == 0)
{
lean_ctor_set(v___x_6106_, 0, v___x_6139_);
v___x_6141_ = v___x_6106_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6142_; 
v_reuseFailAlloc_6142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6142_, 0, v___x_6139_);
v___x_6141_ = v_reuseFailAlloc_6142_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
return v___x_6141_;
}
}
}
}
}
}
else
{
lean_object* v___x_6149_; 
lean_del_object(v___x_6118_);
lean_dec(v_decls_6116_);
lean_dec(v_refs_6115_);
lean_dec(v_version_6114_);
lean_dec_ref_known(v___x_6111_, 1);
lean_dec(v_a_6104_);
lean_dec(v_version_6098_);
lean_dec_ref(v_moduleUri_6097_);
lean_dec(v_name_6096_);
if (v_isShared_6107_ == 0)
{
lean_ctor_set(v___x_6106_, 0, v_self_6095_);
v___x_6149_ = v___x_6106_;
goto v_reusejp_6148_;
}
else
{
lean_object* v_reuseFailAlloc_6150_; 
v_reuseFailAlloc_6150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6150_, 0, v_self_6095_);
v___x_6149_ = v_reuseFailAlloc_6150_;
goto v_reusejp_6148_;
}
v_reusejp_6148_:
{
return v___x_6149_;
}
}
}
}
else
{
lean_object* v___x_6156_; uint8_t v_isShared_6157_; uint8_t v_isSharedCheck_6166_; 
lean_inc(v_workers_6109_);
lean_inc(v_ileans_6108_);
lean_dec(v___x_6112_);
v_isSharedCheck_6166_ = !lean_is_exclusive(v_self_6095_);
if (v_isSharedCheck_6166_ == 0)
{
lean_object* v_unused_6167_; lean_object* v_unused_6168_; 
v_unused_6167_ = lean_ctor_get(v_self_6095_, 1);
lean_dec(v_unused_6167_);
v_unused_6168_ = lean_ctor_get(v_self_6095_, 0);
lean_dec(v_unused_6168_);
v___x_6156_ = v_self_6095_;
v_isShared_6157_ = v_isSharedCheck_6166_;
goto v_resetjp_6155_;
}
else
{
lean_dec(v_self_6095_);
v___x_6156_ = lean_box(0);
v_isShared_6157_ = v_isSharedCheck_6166_;
goto v_resetjp_6155_;
}
v_resetjp_6155_:
{
lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6161_; 
v___x_6158_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6158_, 0, v_moduleUri_6097_);
lean_ctor_set(v___x_6158_, 1, v_version_6098_);
lean_ctor_set(v___x_6158_, 2, v_a_6104_);
lean_ctor_set(v___x_6158_, 3, v___x_6111_);
lean_ctor_set(v___x_6158_, 4, v___x_6102_);
lean_ctor_set(v___x_6158_, 5, v___x_6102_);
v___x_6159_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6096_, v___x_6158_, v_workers_6109_);
if (v_isShared_6157_ == 0)
{
lean_ctor_set(v___x_6156_, 1, v___x_6159_);
v___x_6161_ = v___x_6156_;
goto v_reusejp_6160_;
}
else
{
lean_object* v_reuseFailAlloc_6165_; 
v_reuseFailAlloc_6165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6165_, 0, v_ileans_6108_);
lean_ctor_set(v_reuseFailAlloc_6165_, 1, v___x_6159_);
v___x_6161_ = v_reuseFailAlloc_6165_;
goto v_reusejp_6160_;
}
v_reusejp_6160_:
{
lean_object* v___x_6163_; 
if (v_isShared_6107_ == 0)
{
lean_ctor_set(v___x_6106_, 0, v___x_6161_);
v___x_6163_ = v___x_6106_;
goto v_reusejp_6162_;
}
else
{
lean_object* v_reuseFailAlloc_6164_; 
v_reuseFailAlloc_6164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6164_, 0, v___x_6161_);
v___x_6163_ = v_reuseFailAlloc_6164_;
goto v_reusejp_6162_;
}
v_reusejp_6162_:
{
return v___x_6163_;
}
}
}
}
}
}
else
{
lean_object* v_a_6170_; lean_object* v___x_6172_; uint8_t v_isShared_6173_; uint8_t v_isSharedCheck_6177_; 
lean_dec(v_version_6098_);
lean_dec_ref(v_moduleUri_6097_);
lean_dec(v_name_6096_);
lean_dec_ref(v_self_6095_);
v_a_6170_ = lean_ctor_get(v___x_6103_, 0);
v_isSharedCheck_6177_ = !lean_is_exclusive(v___x_6103_);
if (v_isSharedCheck_6177_ == 0)
{
v___x_6172_ = v___x_6103_;
v_isShared_6173_ = v_isSharedCheck_6177_;
goto v_resetjp_6171_;
}
else
{
lean_inc(v_a_6170_);
lean_dec(v___x_6103_);
v___x_6172_ = lean_box(0);
v_isShared_6173_ = v_isSharedCheck_6177_;
goto v_resetjp_6171_;
}
v_resetjp_6171_:
{
lean_object* v___x_6175_; 
if (v_isShared_6173_ == 0)
{
v___x_6175_ = v___x_6172_;
goto v_reusejp_6174_;
}
else
{
lean_object* v_reuseFailAlloc_6176_; 
v_reuseFailAlloc_6176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6176_, 0, v_a_6170_);
v___x_6175_ = v_reuseFailAlloc_6176_;
goto v_reusejp_6174_;
}
v_reusejp_6174_:
{
return v___x_6175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6178_, lean_object* v_name_6179_, lean_object* v_moduleUri_6180_, lean_object* v_version_6181_, lean_object* v_directImports_6182_, lean_object* v_isSetupFailure_6183_, lean_object* v_a_6184_){
_start:
{
uint8_t v_isSetupFailure_boxed_6185_; lean_object* v_res_6186_; 
v_isSetupFailure_boxed_6185_ = lean_unbox(v_isSetupFailure_6183_);
v_res_6186_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6178_, v_name_6179_, v_moduleUri_6180_, v_version_6181_, v_directImports_6182_, v_isSetupFailure_boxed_6185_);
lean_dec_ref(v_directImports_6182_);
return v_res_6186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6187_, lean_object* v_t_6188_, lean_object* v_k_6189_){
_start:
{
lean_object* v___x_6190_; 
v___x_6190_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6188_, v_k_6189_);
return v___x_6190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6191_, lean_object* v_t_6192_, lean_object* v_k_6193_){
_start:
{
lean_object* v_res_6194_; 
v_res_6194_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6191_, v_t_6192_, v_k_6193_);
lean_dec(v_k_6193_);
lean_dec(v_t_6192_);
return v_res_6194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6195_, lean_object* v_____s_6196_){
_start:
{
lean_object* v_fst_6197_; lean_object* v_snd_6198_; lean_object* v_r_6199_; lean_object* v___x_6200_; 
v_fst_6197_ = lean_ctor_get(v_x_6195_, 0);
lean_inc(v_fst_6197_);
v_snd_6198_ = lean_ctor_get(v_x_6195_, 1);
lean_inc(v_snd_6198_);
lean_dec_ref(v_x_6195_);
v_r_6199_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6197_, v_snd_6198_, v_____s_6196_);
v___x_6200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6200_, 0, v_r_6199_);
return v___x_6200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6201_, lean_object* v_k_6202_, lean_object* v_fallback_6203_){
_start:
{
if (lean_obj_tag(v_t_6201_) == 0)
{
lean_object* v_k_6204_; lean_object* v_v_6205_; lean_object* v_l_6206_; lean_object* v_r_6207_; uint8_t v___x_6208_; 
v_k_6204_ = lean_ctor_get(v_t_6201_, 1);
v_v_6205_ = lean_ctor_get(v_t_6201_, 2);
v_l_6206_ = lean_ctor_get(v_t_6201_, 3);
v_r_6207_ = lean_ctor_get(v_t_6201_, 4);
v___x_6208_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6202_, v_k_6204_);
switch(v___x_6208_)
{
case 0:
{
v_t_6201_ = v_l_6206_;
goto _start;
}
case 1:
{
lean_inc(v_v_6205_);
return v_v_6205_;
}
default: 
{
v_t_6201_ = v_r_6207_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6203_);
return v_fallback_6203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6211_, lean_object* v_k_6212_, lean_object* v_fallback_6213_){
_start:
{
lean_object* v_res_6214_; 
v_res_6214_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6211_, v_k_6212_, v_fallback_6213_);
lean_dec(v_fallback_6213_);
lean_dec_ref(v_k_6212_);
lean_dec(v_t_6211_);
return v_res_6214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6215_, lean_object* v_x_6216_){
_start:
{
if (lean_obj_tag(v_x_6216_) == 0)
{
lean_object* v_k_6217_; lean_object* v_v_6218_; lean_object* v_l_6219_; lean_object* v_r_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; 
v_k_6217_ = lean_ctor_get(v_x_6216_, 1);
lean_inc(v_k_6217_);
v_v_6218_ = lean_ctor_get(v_x_6216_, 2);
lean_inc(v_v_6218_);
v_l_6219_ = lean_ctor_get(v_x_6216_, 3);
lean_inc(v_l_6219_);
v_r_6220_ = lean_ctor_get(v_x_6216_, 4);
lean_inc(v_r_6220_);
lean_dec_ref_known(v_x_6216_, 5);
v___x_6221_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6215_, v_l_6219_);
v___x_6222_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6223_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6221_, v_k_6217_, v___x_6222_);
v___x_6224_ = l_Lean_Lsp_RefInfo_merge(v___x_6223_, v_v_6218_);
v___x_6225_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6217_, v___x_6224_, v___x_6221_);
v_init_6215_ = v___x_6225_;
v_x_6216_ = v_r_6220_;
goto _start;
}
else
{
return v_init_6215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6228_, lean_object* v_name_6229_, lean_object* v_moduleUri_6230_, lean_object* v_version_6231_, lean_object* v_refs_6232_, lean_object* v_decls_6233_){
_start:
{
lean_object* v_ileans_6235_; lean_object* v_workers_6236_; lean_object* v___x_6237_; 
v_ileans_6235_ = lean_ctor_get(v_self_6228_, 0);
v_workers_6236_ = lean_ctor_get(v_self_6228_, 1);
v___x_6237_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6236_, v_name_6229_);
if (lean_obj_tag(v___x_6237_) == 1)
{
lean_object* v_val_6238_; lean_object* v___x_6240_; uint8_t v_isShared_6241_; uint8_t v_isSharedCheck_6286_; 
v_val_6238_ = lean_ctor_get(v___x_6237_, 0);
v_isSharedCheck_6286_ = !lean_is_exclusive(v___x_6237_);
if (v_isSharedCheck_6286_ == 0)
{
v___x_6240_ = v___x_6237_;
v_isShared_6241_ = v_isSharedCheck_6286_;
goto v_resetjp_6239_;
}
else
{
lean_inc(v_val_6238_);
lean_dec(v___x_6237_);
v___x_6240_ = lean_box(0);
v_isShared_6241_ = v_isSharedCheck_6286_;
goto v_resetjp_6239_;
}
v_resetjp_6239_:
{
lean_object* v_version_6242_; lean_object* v_directImports_6243_; lean_object* v_isSetupFailure_x3f_6244_; lean_object* v_refs_6245_; lean_object* v_decls_6246_; lean_object* v___x_6248_; uint8_t v_isShared_6249_; uint8_t v_isSharedCheck_6284_; 
v_version_6242_ = lean_ctor_get(v_val_6238_, 1);
v_directImports_6243_ = lean_ctor_get(v_val_6238_, 2);
v_isSetupFailure_x3f_6244_ = lean_ctor_get(v_val_6238_, 3);
v_refs_6245_ = lean_ctor_get(v_val_6238_, 4);
v_decls_6246_ = lean_ctor_get(v_val_6238_, 5);
v_isSharedCheck_6284_ = !lean_is_exclusive(v_val_6238_);
if (v_isSharedCheck_6284_ == 0)
{
lean_object* v_unused_6285_; 
v_unused_6285_ = lean_ctor_get(v_val_6238_, 0);
lean_dec(v_unused_6285_);
v___x_6248_ = v_val_6238_;
v_isShared_6249_ = v_isSharedCheck_6284_;
goto v_resetjp_6247_;
}
else
{
lean_inc(v_decls_6246_);
lean_inc(v_refs_6245_);
lean_inc(v_isSetupFailure_x3f_6244_);
lean_inc(v_directImports_6243_);
lean_inc(v_version_6242_);
lean_dec(v_val_6238_);
v___x_6248_ = lean_box(0);
v_isShared_6249_ = v_isSharedCheck_6284_;
goto v_resetjp_6247_;
}
v_resetjp_6247_:
{
uint8_t v___x_6250_; 
v___x_6250_ = lean_nat_dec_lt(v_version_6231_, v_version_6242_);
if (v___x_6250_ == 0)
{
lean_object* v___x_6252_; uint8_t v_isShared_6253_; uint8_t v_isSharedCheck_6278_; 
lean_inc(v_workers_6236_);
lean_inc(v_ileans_6235_);
v_isSharedCheck_6278_ = !lean_is_exclusive(v_self_6228_);
if (v_isSharedCheck_6278_ == 0)
{
lean_object* v_unused_6279_; lean_object* v_unused_6280_; 
v_unused_6279_ = lean_ctor_get(v_self_6228_, 1);
lean_dec(v_unused_6279_);
v_unused_6280_ = lean_ctor_get(v_self_6228_, 0);
lean_dec(v_unused_6280_);
v___x_6252_ = v_self_6228_;
v_isShared_6253_ = v_isSharedCheck_6278_;
goto v_resetjp_6251_;
}
else
{
lean_dec(v_self_6228_);
v___x_6252_ = lean_box(0);
v_isShared_6253_ = v_isSharedCheck_6278_;
goto v_resetjp_6251_;
}
v_resetjp_6251_:
{
uint8_t v___x_6254_; 
v___x_6254_ = lean_nat_dec_eq(v_version_6231_, v_version_6242_);
lean_dec(v_version_6242_);
if (v___x_6254_ == 0)
{
lean_object* v___x_6256_; 
lean_dec(v_decls_6246_);
lean_dec(v_refs_6245_);
if (v_isShared_6249_ == 0)
{
lean_ctor_set(v___x_6248_, 5, v_decls_6233_);
lean_ctor_set(v___x_6248_, 4, v_refs_6232_);
lean_ctor_set(v___x_6248_, 1, v_version_6231_);
lean_ctor_set(v___x_6248_, 0, v_moduleUri_6230_);
v___x_6256_ = v___x_6248_;
goto v_reusejp_6255_;
}
else
{
lean_object* v_reuseFailAlloc_6264_; 
v_reuseFailAlloc_6264_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6264_, 0, v_moduleUri_6230_);
lean_ctor_set(v_reuseFailAlloc_6264_, 1, v_version_6231_);
lean_ctor_set(v_reuseFailAlloc_6264_, 2, v_directImports_6243_);
lean_ctor_set(v_reuseFailAlloc_6264_, 3, v_isSetupFailure_x3f_6244_);
lean_ctor_set(v_reuseFailAlloc_6264_, 4, v_refs_6232_);
lean_ctor_set(v_reuseFailAlloc_6264_, 5, v_decls_6233_);
v___x_6256_ = v_reuseFailAlloc_6264_;
goto v_reusejp_6255_;
}
v_reusejp_6255_:
{
lean_object* v___x_6257_; lean_object* v___x_6259_; 
v___x_6257_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6229_, v___x_6256_, v_workers_6236_);
if (v_isShared_6253_ == 0)
{
lean_ctor_set(v___x_6252_, 1, v___x_6257_);
v___x_6259_ = v___x_6252_;
goto v_reusejp_6258_;
}
else
{
lean_object* v_reuseFailAlloc_6263_; 
v_reuseFailAlloc_6263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_ileans_6235_);
lean_ctor_set(v_reuseFailAlloc_6263_, 1, v___x_6257_);
v___x_6259_ = v_reuseFailAlloc_6263_;
goto v_reusejp_6258_;
}
v_reusejp_6258_:
{
lean_object* v___x_6261_; 
if (v_isShared_6241_ == 0)
{
lean_ctor_set_tag(v___x_6240_, 0);
lean_ctor_set(v___x_6240_, 0, v___x_6259_);
v___x_6261_ = v___x_6240_;
goto v_reusejp_6260_;
}
else
{
lean_object* v_reuseFailAlloc_6262_; 
v_reuseFailAlloc_6262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6262_, 0, v___x_6259_);
v___x_6261_ = v_reuseFailAlloc_6262_;
goto v_reusejp_6260_;
}
v_reusejp_6260_:
{
return v___x_6261_;
}
}
}
}
else
{
lean_object* v___f_6265_; lean_object* v_mergedRefs_6266_; lean_object* v_mergedDecls_6267_; lean_object* v___x_6269_; 
v___f_6265_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6266_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6245_, v_refs_6232_);
v_mergedDecls_6267_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6233_, v_decls_6246_, v___f_6265_);
lean_dec(v_decls_6233_);
if (v_isShared_6249_ == 0)
{
lean_ctor_set(v___x_6248_, 5, v_mergedDecls_6267_);
lean_ctor_set(v___x_6248_, 4, v_mergedRefs_6266_);
lean_ctor_set(v___x_6248_, 1, v_version_6231_);
lean_ctor_set(v___x_6248_, 0, v_moduleUri_6230_);
v___x_6269_ = v___x_6248_;
goto v_reusejp_6268_;
}
else
{
lean_object* v_reuseFailAlloc_6277_; 
v_reuseFailAlloc_6277_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6277_, 0, v_moduleUri_6230_);
lean_ctor_set(v_reuseFailAlloc_6277_, 1, v_version_6231_);
lean_ctor_set(v_reuseFailAlloc_6277_, 2, v_directImports_6243_);
lean_ctor_set(v_reuseFailAlloc_6277_, 3, v_isSetupFailure_x3f_6244_);
lean_ctor_set(v_reuseFailAlloc_6277_, 4, v_mergedRefs_6266_);
lean_ctor_set(v_reuseFailAlloc_6277_, 5, v_mergedDecls_6267_);
v___x_6269_ = v_reuseFailAlloc_6277_;
goto v_reusejp_6268_;
}
v_reusejp_6268_:
{
lean_object* v___x_6270_; lean_object* v___x_6272_; 
v___x_6270_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6229_, v___x_6269_, v_workers_6236_);
if (v_isShared_6253_ == 0)
{
lean_ctor_set(v___x_6252_, 1, v___x_6270_);
v___x_6272_ = v___x_6252_;
goto v_reusejp_6271_;
}
else
{
lean_object* v_reuseFailAlloc_6276_; 
v_reuseFailAlloc_6276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_ileans_6235_);
lean_ctor_set(v_reuseFailAlloc_6276_, 1, v___x_6270_);
v___x_6272_ = v_reuseFailAlloc_6276_;
goto v_reusejp_6271_;
}
v_reusejp_6271_:
{
lean_object* v___x_6274_; 
if (v_isShared_6241_ == 0)
{
lean_ctor_set_tag(v___x_6240_, 0);
lean_ctor_set(v___x_6240_, 0, v___x_6272_);
v___x_6274_ = v___x_6240_;
goto v_reusejp_6273_;
}
else
{
lean_object* v_reuseFailAlloc_6275_; 
v_reuseFailAlloc_6275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6275_, 0, v___x_6272_);
v___x_6274_ = v_reuseFailAlloc_6275_;
goto v_reusejp_6273_;
}
v_reusejp_6273_:
{
return v___x_6274_;
}
}
}
}
}
}
else
{
lean_object* v___x_6282_; 
lean_del_object(v___x_6248_);
lean_dec(v_decls_6246_);
lean_dec(v_refs_6245_);
lean_dec(v_isSetupFailure_x3f_6244_);
lean_dec_ref(v_directImports_6243_);
lean_dec(v_version_6242_);
lean_dec(v_decls_6233_);
lean_dec(v_refs_6232_);
lean_dec(v_version_6231_);
lean_dec_ref(v_moduleUri_6230_);
lean_dec(v_name_6229_);
if (v_isShared_6241_ == 0)
{
lean_ctor_set_tag(v___x_6240_, 0);
lean_ctor_set(v___x_6240_, 0, v_self_6228_);
v___x_6282_ = v___x_6240_;
goto v_reusejp_6281_;
}
else
{
lean_object* v_reuseFailAlloc_6283_; 
v_reuseFailAlloc_6283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6283_, 0, v_self_6228_);
v___x_6282_ = v_reuseFailAlloc_6283_;
goto v_reusejp_6281_;
}
v_reusejp_6281_:
{
return v___x_6282_;
}
}
}
}
}
else
{
lean_object* v___x_6288_; uint8_t v_isShared_6289_; uint8_t v_isSharedCheck_6298_; 
lean_inc(v_workers_6236_);
lean_inc(v_ileans_6235_);
lean_dec(v___x_6237_);
v_isSharedCheck_6298_ = !lean_is_exclusive(v_self_6228_);
if (v_isSharedCheck_6298_ == 0)
{
lean_object* v_unused_6299_; lean_object* v_unused_6300_; 
v_unused_6299_ = lean_ctor_get(v_self_6228_, 1);
lean_dec(v_unused_6299_);
v_unused_6300_ = lean_ctor_get(v_self_6228_, 0);
lean_dec(v_unused_6300_);
v___x_6288_ = v_self_6228_;
v_isShared_6289_ = v_isSharedCheck_6298_;
goto v_resetjp_6287_;
}
else
{
lean_dec(v_self_6228_);
v___x_6288_ = lean_box(0);
v_isShared_6289_ = v_isSharedCheck_6298_;
goto v_resetjp_6287_;
}
v_resetjp_6287_:
{
lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6295_; 
v___x_6290_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6291_ = lean_box(0);
v___x_6292_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6292_, 0, v_moduleUri_6230_);
lean_ctor_set(v___x_6292_, 1, v_version_6231_);
lean_ctor_set(v___x_6292_, 2, v___x_6290_);
lean_ctor_set(v___x_6292_, 3, v___x_6291_);
lean_ctor_set(v___x_6292_, 4, v_refs_6232_);
lean_ctor_set(v___x_6292_, 5, v_decls_6233_);
v___x_6293_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6229_, v___x_6292_, v_workers_6236_);
if (v_isShared_6289_ == 0)
{
lean_ctor_set(v___x_6288_, 1, v___x_6293_);
v___x_6295_ = v___x_6288_;
goto v_reusejp_6294_;
}
else
{
lean_object* v_reuseFailAlloc_6297_; 
v_reuseFailAlloc_6297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6297_, 0, v_ileans_6235_);
lean_ctor_set(v_reuseFailAlloc_6297_, 1, v___x_6293_);
v___x_6295_ = v_reuseFailAlloc_6297_;
goto v_reusejp_6294_;
}
v_reusejp_6294_:
{
lean_object* v___x_6296_; 
v___x_6296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6296_, 0, v___x_6295_);
return v___x_6296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6301_, lean_object* v_name_6302_, lean_object* v_moduleUri_6303_, lean_object* v_version_6304_, lean_object* v_refs_6305_, lean_object* v_decls_6306_, lean_object* v_a_6307_){
_start:
{
lean_object* v_res_6308_; 
v_res_6308_ = l_Lean_Server_References_updateWorkerRefs(v_self_6301_, v_name_6302_, v_moduleUri_6303_, v_version_6304_, v_refs_6305_, v_decls_6306_);
return v_res_6308_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6309_, lean_object* v_t_6310_, lean_object* v_k_6311_, lean_object* v_fallback_6312_){
_start:
{
lean_object* v___x_6313_; 
v___x_6313_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6310_, v_k_6311_, v_fallback_6312_);
return v___x_6313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6314_, lean_object* v_t_6315_, lean_object* v_k_6316_, lean_object* v_fallback_6317_){
_start:
{
lean_object* v_res_6318_; 
v_res_6318_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6314_, v_t_6315_, v_k_6316_, v_fallback_6317_);
lean_dec(v_fallback_6317_);
lean_dec_ref(v_k_6316_);
lean_dec(v_t_6315_);
return v_res_6318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6319_, lean_object* v_t_6320_){
_start:
{
lean_object* v___x_6321_; 
v___x_6321_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6319_, v_t_6320_);
return v___x_6321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6322_, lean_object* v_name_6323_, lean_object* v_moduleUri_6324_, lean_object* v_version_6325_, lean_object* v_refs_6326_, lean_object* v_decls_6327_){
_start:
{
lean_object* v_ileans_6329_; lean_object* v_workers_6330_; lean_object* v___x_6331_; 
v_ileans_6329_ = lean_ctor_get(v_self_6322_, 0);
v_workers_6330_ = lean_ctor_get(v_self_6322_, 1);
v___x_6331_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6330_, v_name_6323_);
if (lean_obj_tag(v___x_6331_) == 1)
{
lean_object* v_val_6332_; lean_object* v___x_6334_; uint8_t v_isShared_6335_; uint8_t v_isSharedCheck_6366_; 
v_val_6332_ = lean_ctor_get(v___x_6331_, 0);
v_isSharedCheck_6366_ = !lean_is_exclusive(v___x_6331_);
if (v_isSharedCheck_6366_ == 0)
{
v___x_6334_ = v___x_6331_;
v_isShared_6335_ = v_isSharedCheck_6366_;
goto v_resetjp_6333_;
}
else
{
lean_inc(v_val_6332_);
lean_dec(v___x_6331_);
v___x_6334_ = lean_box(0);
v_isShared_6335_ = v_isSharedCheck_6366_;
goto v_resetjp_6333_;
}
v_resetjp_6333_:
{
lean_object* v_version_6336_; lean_object* v_directImports_6337_; lean_object* v_isSetupFailure_x3f_6338_; lean_object* v___x_6340_; uint8_t v_isShared_6341_; uint8_t v_isSharedCheck_6362_; 
v_version_6336_ = lean_ctor_get(v_val_6332_, 1);
v_directImports_6337_ = lean_ctor_get(v_val_6332_, 2);
v_isSetupFailure_x3f_6338_ = lean_ctor_get(v_val_6332_, 3);
v_isSharedCheck_6362_ = !lean_is_exclusive(v_val_6332_);
if (v_isSharedCheck_6362_ == 0)
{
lean_object* v_unused_6363_; lean_object* v_unused_6364_; lean_object* v_unused_6365_; 
v_unused_6363_ = lean_ctor_get(v_val_6332_, 5);
lean_dec(v_unused_6363_);
v_unused_6364_ = lean_ctor_get(v_val_6332_, 4);
lean_dec(v_unused_6364_);
v_unused_6365_ = lean_ctor_get(v_val_6332_, 0);
lean_dec(v_unused_6365_);
v___x_6340_ = v_val_6332_;
v_isShared_6341_ = v_isSharedCheck_6362_;
goto v_resetjp_6339_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6338_);
lean_inc(v_directImports_6337_);
lean_inc(v_version_6336_);
lean_dec(v_val_6332_);
v___x_6340_ = lean_box(0);
v_isShared_6341_ = v_isSharedCheck_6362_;
goto v_resetjp_6339_;
}
v_resetjp_6339_:
{
uint8_t v___x_6342_; 
v___x_6342_ = lean_nat_dec_lt(v_version_6325_, v_version_6336_);
lean_dec(v_version_6336_);
if (v___x_6342_ == 0)
{
lean_object* v___x_6344_; uint8_t v_isShared_6345_; uint8_t v_isSharedCheck_6356_; 
lean_inc(v_workers_6330_);
lean_inc(v_ileans_6329_);
v_isSharedCheck_6356_ = !lean_is_exclusive(v_self_6322_);
if (v_isSharedCheck_6356_ == 0)
{
lean_object* v_unused_6357_; lean_object* v_unused_6358_; 
v_unused_6357_ = lean_ctor_get(v_self_6322_, 1);
lean_dec(v_unused_6357_);
v_unused_6358_ = lean_ctor_get(v_self_6322_, 0);
lean_dec(v_unused_6358_);
v___x_6344_ = v_self_6322_;
v_isShared_6345_ = v_isSharedCheck_6356_;
goto v_resetjp_6343_;
}
else
{
lean_dec(v_self_6322_);
v___x_6344_ = lean_box(0);
v_isShared_6345_ = v_isSharedCheck_6356_;
goto v_resetjp_6343_;
}
v_resetjp_6343_:
{
lean_object* v___x_6347_; 
if (v_isShared_6341_ == 0)
{
lean_ctor_set(v___x_6340_, 5, v_decls_6327_);
lean_ctor_set(v___x_6340_, 4, v_refs_6326_);
lean_ctor_set(v___x_6340_, 1, v_version_6325_);
lean_ctor_set(v___x_6340_, 0, v_moduleUri_6324_);
v___x_6347_ = v___x_6340_;
goto v_reusejp_6346_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_moduleUri_6324_);
lean_ctor_set(v_reuseFailAlloc_6355_, 1, v_version_6325_);
lean_ctor_set(v_reuseFailAlloc_6355_, 2, v_directImports_6337_);
lean_ctor_set(v_reuseFailAlloc_6355_, 3, v_isSetupFailure_x3f_6338_);
lean_ctor_set(v_reuseFailAlloc_6355_, 4, v_refs_6326_);
lean_ctor_set(v_reuseFailAlloc_6355_, 5, v_decls_6327_);
v___x_6347_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6346_;
}
v_reusejp_6346_:
{
lean_object* v___x_6348_; lean_object* v___x_6350_; 
v___x_6348_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6323_, v___x_6347_, v_workers_6330_);
if (v_isShared_6345_ == 0)
{
lean_ctor_set(v___x_6344_, 1, v___x_6348_);
v___x_6350_ = v___x_6344_;
goto v_reusejp_6349_;
}
else
{
lean_object* v_reuseFailAlloc_6354_; 
v_reuseFailAlloc_6354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6354_, 0, v_ileans_6329_);
lean_ctor_set(v_reuseFailAlloc_6354_, 1, v___x_6348_);
v___x_6350_ = v_reuseFailAlloc_6354_;
goto v_reusejp_6349_;
}
v_reusejp_6349_:
{
lean_object* v___x_6352_; 
if (v_isShared_6335_ == 0)
{
lean_ctor_set_tag(v___x_6334_, 0);
lean_ctor_set(v___x_6334_, 0, v___x_6350_);
v___x_6352_ = v___x_6334_;
goto v_reusejp_6351_;
}
else
{
lean_object* v_reuseFailAlloc_6353_; 
v_reuseFailAlloc_6353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6353_, 0, v___x_6350_);
v___x_6352_ = v_reuseFailAlloc_6353_;
goto v_reusejp_6351_;
}
v_reusejp_6351_:
{
return v___x_6352_;
}
}
}
}
}
else
{
lean_object* v___x_6360_; 
lean_del_object(v___x_6340_);
lean_dec(v_isSetupFailure_x3f_6338_);
lean_dec_ref(v_directImports_6337_);
lean_dec(v_decls_6327_);
lean_dec(v_refs_6326_);
lean_dec(v_version_6325_);
lean_dec_ref(v_moduleUri_6324_);
lean_dec(v_name_6323_);
if (v_isShared_6335_ == 0)
{
lean_ctor_set_tag(v___x_6334_, 0);
lean_ctor_set(v___x_6334_, 0, v_self_6322_);
v___x_6360_ = v___x_6334_;
goto v_reusejp_6359_;
}
else
{
lean_object* v_reuseFailAlloc_6361_; 
v_reuseFailAlloc_6361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_self_6322_);
v___x_6360_ = v_reuseFailAlloc_6361_;
goto v_reusejp_6359_;
}
v_reusejp_6359_:
{
return v___x_6360_;
}
}
}
}
}
else
{
lean_object* v___x_6368_; uint8_t v_isShared_6369_; uint8_t v_isSharedCheck_6378_; 
lean_inc(v_workers_6330_);
lean_inc(v_ileans_6329_);
lean_dec(v___x_6331_);
v_isSharedCheck_6378_ = !lean_is_exclusive(v_self_6322_);
if (v_isSharedCheck_6378_ == 0)
{
lean_object* v_unused_6379_; lean_object* v_unused_6380_; 
v_unused_6379_ = lean_ctor_get(v_self_6322_, 1);
lean_dec(v_unused_6379_);
v_unused_6380_ = lean_ctor_get(v_self_6322_, 0);
lean_dec(v_unused_6380_);
v___x_6368_ = v_self_6322_;
v_isShared_6369_ = v_isSharedCheck_6378_;
goto v_resetjp_6367_;
}
else
{
lean_dec(v_self_6322_);
v___x_6368_ = lean_box(0);
v_isShared_6369_ = v_isSharedCheck_6378_;
goto v_resetjp_6367_;
}
v_resetjp_6367_:
{
lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; lean_object* v___x_6375_; 
v___x_6370_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6371_ = lean_box(0);
v___x_6372_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6372_, 0, v_moduleUri_6324_);
lean_ctor_set(v___x_6372_, 1, v_version_6325_);
lean_ctor_set(v___x_6372_, 2, v___x_6370_);
lean_ctor_set(v___x_6372_, 3, v___x_6371_);
lean_ctor_set(v___x_6372_, 4, v_refs_6326_);
lean_ctor_set(v___x_6372_, 5, v_decls_6327_);
v___x_6373_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6323_, v___x_6372_, v_workers_6330_);
if (v_isShared_6369_ == 0)
{
lean_ctor_set(v___x_6368_, 1, v___x_6373_);
v___x_6375_ = v___x_6368_;
goto v_reusejp_6374_;
}
else
{
lean_object* v_reuseFailAlloc_6377_; 
v_reuseFailAlloc_6377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6377_, 0, v_ileans_6329_);
lean_ctor_set(v_reuseFailAlloc_6377_, 1, v___x_6373_);
v___x_6375_ = v_reuseFailAlloc_6377_;
goto v_reusejp_6374_;
}
v_reusejp_6374_:
{
lean_object* v___x_6376_; 
v___x_6376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6376_, 0, v___x_6375_);
return v___x_6376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6381_, lean_object* v_name_6382_, lean_object* v_moduleUri_6383_, lean_object* v_version_6384_, lean_object* v_refs_6385_, lean_object* v_decls_6386_, lean_object* v_a_6387_){
_start:
{
lean_object* v_res_6388_; 
v_res_6388_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6381_, v_name_6382_, v_moduleUri_6383_, v_version_6384_, v_refs_6385_, v_decls_6386_);
return v_res_6388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6389_, lean_object* v_name_6390_){
_start:
{
lean_object* v_ileans_6391_; lean_object* v_workers_6392_; lean_object* v___x_6394_; uint8_t v_isShared_6395_; uint8_t v_isSharedCheck_6400_; 
v_ileans_6391_ = lean_ctor_get(v_self_6389_, 0);
v_workers_6392_ = lean_ctor_get(v_self_6389_, 1);
v_isSharedCheck_6400_ = !lean_is_exclusive(v_self_6389_);
if (v_isSharedCheck_6400_ == 0)
{
v___x_6394_ = v_self_6389_;
v_isShared_6395_ = v_isSharedCheck_6400_;
goto v_resetjp_6393_;
}
else
{
lean_inc(v_workers_6392_);
lean_inc(v_ileans_6391_);
lean_dec(v_self_6389_);
v___x_6394_ = lean_box(0);
v_isShared_6395_ = v_isSharedCheck_6400_;
goto v_resetjp_6393_;
}
v_resetjp_6393_:
{
lean_object* v___x_6396_; lean_object* v___x_6398_; 
v___x_6396_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6390_, v_workers_6392_);
if (v_isShared_6395_ == 0)
{
lean_ctor_set(v___x_6394_, 1, v___x_6396_);
v___x_6398_ = v___x_6394_;
goto v_reusejp_6397_;
}
else
{
lean_object* v_reuseFailAlloc_6399_; 
v_reuseFailAlloc_6399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6399_, 0, v_ileans_6391_);
lean_ctor_set(v_reuseFailAlloc_6399_, 1, v___x_6396_);
v___x_6398_ = v_reuseFailAlloc_6399_;
goto v_reusejp_6397_;
}
v_reusejp_6397_:
{
return v___x_6398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6401_, lean_object* v_name_6402_){
_start:
{
lean_object* v_res_6403_; 
v_res_6403_ = l_Lean_Server_References_removeWorkerRefs(v_self_6401_, v_name_6402_);
lean_dec(v_name_6402_);
return v_res_6403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6404_, lean_object* v_x_6405_){
_start:
{
if (lean_obj_tag(v_x_6405_) == 0)
{
lean_object* v_v_6406_; lean_object* v_k_6407_; lean_object* v_l_6408_; lean_object* v_r_6409_; lean_object* v_moduleUri_6410_; lean_object* v_refs_6411_; lean_object* v_decls_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; 
v_v_6406_ = lean_ctor_get(v_x_6405_, 2);
lean_inc(v_v_6406_);
v_k_6407_ = lean_ctor_get(v_x_6405_, 1);
lean_inc(v_k_6407_);
v_l_6408_ = lean_ctor_get(v_x_6405_, 3);
lean_inc(v_l_6408_);
v_r_6409_ = lean_ctor_get(v_x_6405_, 4);
lean_inc(v_r_6409_);
lean_dec_ref_known(v_x_6405_, 5);
v_moduleUri_6410_ = lean_ctor_get(v_v_6406_, 0);
lean_inc_ref(v_moduleUri_6410_);
v_refs_6411_ = lean_ctor_get(v_v_6406_, 3);
lean_inc(v_refs_6411_);
v_decls_6412_ = lean_ctor_get(v_v_6406_, 4);
lean_inc(v_decls_6412_);
lean_dec(v_v_6406_);
v___x_6413_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6404_, v_l_6408_);
v___x_6414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6414_, 0, v_refs_6411_);
lean_ctor_set(v___x_6414_, 1, v_decls_6412_);
v___x_6415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6415_, 0, v_moduleUri_6410_);
lean_ctor_set(v___x_6415_, 1, v___x_6414_);
v___x_6416_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6407_, v___x_6415_, v___x_6413_);
v_init_6404_ = v___x_6416_;
v_x_6405_ = v_r_6409_;
goto _start;
}
else
{
return v_init_6404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6418_, lean_object* v_x_6419_){
_start:
{
if (lean_obj_tag(v_x_6419_) == 0)
{
lean_object* v_v_6420_; lean_object* v_k_6421_; lean_object* v_l_6422_; lean_object* v_r_6423_; lean_object* v_moduleUri_6424_; lean_object* v_refs_6425_; lean_object* v_decls_6426_; lean_object* v___x_6427_; uint8_t v___x_6428_; 
v_v_6420_ = lean_ctor_get(v_x_6419_, 2);
lean_inc(v_v_6420_);
v_k_6421_ = lean_ctor_get(v_x_6419_, 1);
lean_inc(v_k_6421_);
v_l_6422_ = lean_ctor_get(v_x_6419_, 3);
lean_inc(v_l_6422_);
v_r_6423_ = lean_ctor_get(v_x_6419_, 4);
lean_inc(v_r_6423_);
lean_dec_ref_known(v_x_6419_, 5);
v_moduleUri_6424_ = lean_ctor_get(v_v_6420_, 0);
lean_inc_ref(v_moduleUri_6424_);
v_refs_6425_ = lean_ctor_get(v_v_6420_, 4);
lean_inc(v_refs_6425_);
v_decls_6426_ = lean_ctor_get(v_v_6420_, 5);
lean_inc(v_decls_6426_);
v___x_6427_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6418_, v_l_6422_);
v___x_6428_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6420_);
lean_dec(v_v_6420_);
if (v___x_6428_ == 0)
{
lean_dec(v_decls_6426_);
lean_dec(v_refs_6425_);
lean_dec_ref(v_moduleUri_6424_);
lean_dec(v_k_6421_);
v_init_6418_ = v___x_6427_;
v_x_6419_ = v_r_6423_;
goto _start;
}
else
{
lean_object* v___x_6430_; lean_object* v___x_6431_; lean_object* v___x_6432_; 
v___x_6430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6430_, 0, v_refs_6425_);
lean_ctor_set(v___x_6430_, 1, v_decls_6426_);
v___x_6431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6431_, 0, v_moduleUri_6424_);
lean_ctor_set(v___x_6431_, 1, v___x_6430_);
v___x_6432_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6421_, v___x_6431_, v___x_6427_);
v_init_6418_ = v___x_6432_;
v_x_6419_ = v_r_6423_;
goto _start;
}
}
else
{
return v_init_6418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6434_){
_start:
{
lean_object* v_ileans_6435_; lean_object* v_workers_6436_; lean_object* v___x_6437_; lean_object* v_ileanRefs_6438_; lean_object* v___x_6439_; 
v_ileans_6435_ = lean_ctor_get(v_self_6434_, 0);
lean_inc(v_ileans_6435_);
v_workers_6436_ = lean_ctor_get(v_self_6434_, 1);
lean_inc(v_workers_6436_);
lean_dec_ref(v_self_6434_);
v___x_6437_ = lean_box(1);
v_ileanRefs_6438_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6437_, v_ileans_6435_);
v___x_6439_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6438_, v_workers_6436_);
return v___x_6439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6440_, lean_object* v_t_6441_){
_start:
{
lean_object* v___x_6442_; 
v___x_6442_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6440_, v_t_6441_);
return v___x_6442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6443_, lean_object* v_t_6444_){
_start:
{
lean_object* v___x_6445_; 
v___x_6445_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6443_, v_t_6444_);
return v___x_6445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6446_, lean_object* v_x_6447_){
_start:
{
if (lean_obj_tag(v_x_6447_) == 0)
{
lean_object* v_k_6448_; lean_object* v_v_6449_; lean_object* v_l_6450_; lean_object* v_r_6451_; lean_object* v___x_6452_; lean_object* v_a_6453_; uint8_t v___x_6454_; 
v_k_6448_ = lean_ctor_get(v_x_6447_, 1);
lean_inc(v_k_6448_);
v_v_6449_ = lean_ctor_get(v_x_6447_, 2);
lean_inc(v_v_6449_);
v_l_6450_ = lean_ctor_get(v_x_6447_, 3);
lean_inc(v_l_6450_);
v_r_6451_ = lean_ctor_get(v_x_6447_, 4);
lean_inc(v_r_6451_);
lean_dec_ref_known(v_x_6447_, 5);
v___x_6452_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6446_, v_l_6450_);
v_a_6453_ = lean_ctor_get(v___x_6452_, 0);
lean_inc(v_a_6453_);
lean_dec_ref(v___x_6452_);
v___x_6454_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6449_);
if (v___x_6454_ == 0)
{
lean_dec(v_v_6449_);
lean_dec(v_k_6448_);
v_init_6446_ = v_a_6453_;
v_x_6447_ = v_r_6451_;
goto _start;
}
else
{
lean_object* v_moduleUri_6456_; lean_object* v_directImports_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; 
v_moduleUri_6456_ = lean_ctor_get(v_v_6449_, 0);
lean_inc_ref(v_moduleUri_6456_);
v_directImports_6457_ = lean_ctor_get(v_v_6449_, 2);
lean_inc_ref(v_directImports_6457_);
lean_dec(v_v_6449_);
v___x_6458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6458_, 0, v_moduleUri_6456_);
lean_ctor_set(v___x_6458_, 1, v_directImports_6457_);
v___x_6459_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6448_, v___x_6458_, v_a_6453_);
v_init_6446_ = v___x_6459_;
v_x_6447_ = v_r_6451_;
goto _start;
}
}
else
{
lean_object* v___x_6461_; 
v___x_6461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6461_, 0, v_init_6446_);
return v___x_6461_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6462_, lean_object* v_x_6463_){
_start:
{
if (lean_obj_tag(v_x_6463_) == 0)
{
lean_object* v_k_6464_; lean_object* v_v_6465_; lean_object* v_l_6466_; lean_object* v_r_6467_; lean_object* v___x_6468_; lean_object* v_a_6469_; lean_object* v_moduleUri_6470_; lean_object* v_directImports_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; 
v_k_6464_ = lean_ctor_get(v_x_6463_, 1);
lean_inc(v_k_6464_);
v_v_6465_ = lean_ctor_get(v_x_6463_, 2);
lean_inc(v_v_6465_);
v_l_6466_ = lean_ctor_get(v_x_6463_, 3);
lean_inc(v_l_6466_);
v_r_6467_ = lean_ctor_get(v_x_6463_, 4);
lean_inc(v_r_6467_);
lean_dec_ref_known(v_x_6463_, 5);
v___x_6468_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6462_, v_l_6466_);
v_a_6469_ = lean_ctor_get(v___x_6468_, 0);
lean_inc(v_a_6469_);
lean_dec_ref(v___x_6468_);
v_moduleUri_6470_ = lean_ctor_get(v_v_6465_, 0);
lean_inc_ref(v_moduleUri_6470_);
v_directImports_6471_ = lean_ctor_get(v_v_6465_, 2);
lean_inc_ref(v_directImports_6471_);
lean_dec(v_v_6465_);
v___x_6472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6472_, 0, v_moduleUri_6470_);
lean_ctor_set(v___x_6472_, 1, v_directImports_6471_);
v___x_6473_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6464_, v___x_6472_, v_a_6469_);
v_init_6462_ = v___x_6473_;
v_x_6463_ = v_r_6467_;
goto _start;
}
else
{
lean_object* v___x_6475_; 
v___x_6475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6475_, 0, v_init_6462_);
return v___x_6475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6476_){
_start:
{
lean_object* v_ileans_6477_; lean_object* v_workers_6478_; lean_object* v___y_6480_; lean_object* v_allDirectImports_6483_; lean_object* v___x_6484_; lean_object* v_a_6485_; 
v_ileans_6477_ = lean_ctor_get(v_self_6476_, 0);
lean_inc(v_ileans_6477_);
v_workers_6478_ = lean_ctor_get(v_self_6476_, 1);
lean_inc(v_workers_6478_);
lean_dec_ref(v_self_6476_);
v_allDirectImports_6483_ = lean_box(1);
v___x_6484_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6483_, v_ileans_6477_);
v_a_6485_ = lean_ctor_get(v___x_6484_, 0);
lean_inc(v_a_6485_);
lean_dec_ref(v___x_6484_);
v___y_6480_ = v_a_6485_;
goto v___jp_6479_;
v___jp_6479_:
{
lean_object* v___x_6481_; lean_object* v_a_6482_; 
v___x_6481_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6480_, v_workers_6478_);
v_a_6482_ = lean_ctor_get(v___x_6481_, 0);
lean_inc(v_a_6482_);
lean_dec_ref(v___x_6481_);
return v_a_6482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6486_, lean_object* v_mod_6487_){
_start:
{
lean_object* v_ileans_6488_; lean_object* v_workers_6489_; lean_object* v___x_6491_; uint8_t v_isShared_6492_; uint8_t v_isSharedCheck_6526_; 
v_ileans_6488_ = lean_ctor_get(v_self_6486_, 0);
v_workers_6489_ = lean_ctor_get(v_self_6486_, 1);
v_isSharedCheck_6526_ = !lean_is_exclusive(v_self_6486_);
if (v_isSharedCheck_6526_ == 0)
{
v___x_6491_ = v_self_6486_;
v_isShared_6492_ = v_isSharedCheck_6526_;
goto v_resetjp_6490_;
}
else
{
lean_inc(v_workers_6489_);
lean_inc(v_ileans_6488_);
lean_dec(v_self_6486_);
v___x_6491_ = lean_box(0);
v_isShared_6492_ = v_isSharedCheck_6526_;
goto v_resetjp_6490_;
}
v_resetjp_6490_:
{
lean_object* v___x_6511_; 
v___x_6511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6489_, v_mod_6487_);
lean_dec(v_workers_6489_);
if (lean_obj_tag(v___x_6511_) == 1)
{
lean_object* v_val_6512_; lean_object* v___x_6514_; uint8_t v_isShared_6515_; uint8_t v_isSharedCheck_6525_; 
v_val_6512_ = lean_ctor_get(v___x_6511_, 0);
v_isSharedCheck_6525_ = !lean_is_exclusive(v___x_6511_);
if (v_isSharedCheck_6525_ == 0)
{
v___x_6514_ = v___x_6511_;
v_isShared_6515_ = v_isSharedCheck_6525_;
goto v_resetjp_6513_;
}
else
{
lean_inc(v_val_6512_);
lean_dec(v___x_6511_);
v___x_6514_ = lean_box(0);
v_isShared_6515_ = v_isSharedCheck_6525_;
goto v_resetjp_6513_;
}
v_resetjp_6513_:
{
uint8_t v___x_6516_; 
v___x_6516_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6512_);
if (v___x_6516_ == 0)
{
lean_del_object(v___x_6514_);
lean_dec(v_val_6512_);
goto v___jp_6493_;
}
else
{
lean_object* v_moduleUri_6517_; lean_object* v_refs_6518_; lean_object* v_decls_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6523_; 
lean_del_object(v___x_6491_);
lean_dec(v_ileans_6488_);
v_moduleUri_6517_ = lean_ctor_get(v_val_6512_, 0);
lean_inc_ref(v_moduleUri_6517_);
v_refs_6518_ = lean_ctor_get(v_val_6512_, 4);
lean_inc(v_refs_6518_);
v_decls_6519_ = lean_ctor_get(v_val_6512_, 5);
lean_inc(v_decls_6519_);
lean_dec(v_val_6512_);
v___x_6520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6520_, 0, v_refs_6518_);
lean_ctor_set(v___x_6520_, 1, v_decls_6519_);
v___x_6521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6521_, 0, v_moduleUri_6517_);
lean_ctor_set(v___x_6521_, 1, v___x_6520_);
if (v_isShared_6515_ == 0)
{
lean_ctor_set(v___x_6514_, 0, v___x_6521_);
v___x_6523_ = v___x_6514_;
goto v_reusejp_6522_;
}
else
{
lean_object* v_reuseFailAlloc_6524_; 
v_reuseFailAlloc_6524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6524_, 0, v___x_6521_);
v___x_6523_ = v_reuseFailAlloc_6524_;
goto v_reusejp_6522_;
}
v_reusejp_6522_:
{
return v___x_6523_;
}
}
}
}
else
{
lean_dec(v___x_6511_);
goto v___jp_6493_;
}
v___jp_6493_:
{
lean_object* v___x_6494_; 
v___x_6494_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6488_, v_mod_6487_);
lean_dec(v_ileans_6488_);
if (lean_obj_tag(v___x_6494_) == 1)
{
lean_object* v_val_6495_; lean_object* v___x_6497_; uint8_t v_isShared_6498_; uint8_t v_isSharedCheck_6509_; 
v_val_6495_ = lean_ctor_get(v___x_6494_, 0);
v_isSharedCheck_6509_ = !lean_is_exclusive(v___x_6494_);
if (v_isSharedCheck_6509_ == 0)
{
v___x_6497_ = v___x_6494_;
v_isShared_6498_ = v_isSharedCheck_6509_;
goto v_resetjp_6496_;
}
else
{
lean_inc(v_val_6495_);
lean_dec(v___x_6494_);
v___x_6497_ = lean_box(0);
v_isShared_6498_ = v_isSharedCheck_6509_;
goto v_resetjp_6496_;
}
v_resetjp_6496_:
{
lean_object* v_moduleUri_6499_; lean_object* v_refs_6500_; lean_object* v_decls_6501_; lean_object* v___x_6503_; 
v_moduleUri_6499_ = lean_ctor_get(v_val_6495_, 0);
lean_inc_ref(v_moduleUri_6499_);
v_refs_6500_ = lean_ctor_get(v_val_6495_, 3);
lean_inc(v_refs_6500_);
v_decls_6501_ = lean_ctor_get(v_val_6495_, 4);
lean_inc(v_decls_6501_);
lean_dec(v_val_6495_);
if (v_isShared_6492_ == 0)
{
lean_ctor_set(v___x_6491_, 1, v_decls_6501_);
lean_ctor_set(v___x_6491_, 0, v_refs_6500_);
v___x_6503_ = v___x_6491_;
goto v_reusejp_6502_;
}
else
{
lean_object* v_reuseFailAlloc_6508_; 
v_reuseFailAlloc_6508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6508_, 0, v_refs_6500_);
lean_ctor_set(v_reuseFailAlloc_6508_, 1, v_decls_6501_);
v___x_6503_ = v_reuseFailAlloc_6508_;
goto v_reusejp_6502_;
}
v_reusejp_6502_:
{
lean_object* v___x_6504_; lean_object* v___x_6506_; 
v___x_6504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6504_, 0, v_moduleUri_6499_);
lean_ctor_set(v___x_6504_, 1, v___x_6503_);
if (v_isShared_6498_ == 0)
{
lean_ctor_set(v___x_6497_, 0, v___x_6504_);
v___x_6506_ = v___x_6497_;
goto v_reusejp_6505_;
}
else
{
lean_object* v_reuseFailAlloc_6507_; 
v_reuseFailAlloc_6507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6507_, 0, v___x_6504_);
v___x_6506_ = v_reuseFailAlloc_6507_;
goto v_reusejp_6505_;
}
v_reusejp_6505_:
{
return v___x_6506_;
}
}
}
}
else
{
lean_object* v___x_6510_; 
lean_dec(v___x_6494_);
lean_del_object(v___x_6491_);
v___x_6510_ = lean_box(0);
return v___x_6510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6527_, lean_object* v_mod_6528_){
_start:
{
lean_object* v_res_6529_; 
v_res_6529_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6527_, v_mod_6528_);
lean_dec(v_mod_6528_);
return v_res_6529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6530_, lean_object* v_mod_6531_){
_start:
{
lean_object* v_ileans_6532_; lean_object* v_workers_6533_; lean_object* v___x_6546_; 
v_ileans_6532_ = lean_ctor_get(v_self_6530_, 0);
v_workers_6533_ = lean_ctor_get(v_self_6530_, 1);
v___x_6546_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6533_, v_mod_6531_);
if (lean_obj_tag(v___x_6546_) == 1)
{
lean_object* v_val_6547_; lean_object* v___x_6549_; uint8_t v_isShared_6550_; uint8_t v_isSharedCheck_6556_; 
v_val_6547_ = lean_ctor_get(v___x_6546_, 0);
v_isSharedCheck_6556_ = !lean_is_exclusive(v___x_6546_);
if (v_isSharedCheck_6556_ == 0)
{
v___x_6549_ = v___x_6546_;
v_isShared_6550_ = v_isSharedCheck_6556_;
goto v_resetjp_6548_;
}
else
{
lean_inc(v_val_6547_);
lean_dec(v___x_6546_);
v___x_6549_ = lean_box(0);
v_isShared_6550_ = v_isSharedCheck_6556_;
goto v_resetjp_6548_;
}
v_resetjp_6548_:
{
uint8_t v___x_6551_; 
v___x_6551_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6547_);
if (v___x_6551_ == 0)
{
lean_del_object(v___x_6549_);
lean_dec(v_val_6547_);
goto v___jp_6534_;
}
else
{
lean_object* v_directImports_6552_; lean_object* v___x_6554_; 
v_directImports_6552_ = lean_ctor_get(v_val_6547_, 2);
lean_inc_ref(v_directImports_6552_);
lean_dec(v_val_6547_);
if (v_isShared_6550_ == 0)
{
lean_ctor_set(v___x_6549_, 0, v_directImports_6552_);
v___x_6554_ = v___x_6549_;
goto v_reusejp_6553_;
}
else
{
lean_object* v_reuseFailAlloc_6555_; 
v_reuseFailAlloc_6555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6555_, 0, v_directImports_6552_);
v___x_6554_ = v_reuseFailAlloc_6555_;
goto v_reusejp_6553_;
}
v_reusejp_6553_:
{
return v___x_6554_;
}
}
}
}
else
{
lean_dec(v___x_6546_);
goto v___jp_6534_;
}
v___jp_6534_:
{
lean_object* v___x_6535_; 
v___x_6535_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6532_, v_mod_6531_);
if (lean_obj_tag(v___x_6535_) == 1)
{
lean_object* v_val_6536_; lean_object* v___x_6538_; uint8_t v_isShared_6539_; uint8_t v_isSharedCheck_6544_; 
v_val_6536_ = lean_ctor_get(v___x_6535_, 0);
v_isSharedCheck_6544_ = !lean_is_exclusive(v___x_6535_);
if (v_isSharedCheck_6544_ == 0)
{
v___x_6538_ = v___x_6535_;
v_isShared_6539_ = v_isSharedCheck_6544_;
goto v_resetjp_6537_;
}
else
{
lean_inc(v_val_6536_);
lean_dec(v___x_6535_);
v___x_6538_ = lean_box(0);
v_isShared_6539_ = v_isSharedCheck_6544_;
goto v_resetjp_6537_;
}
v_resetjp_6537_:
{
lean_object* v_directImports_6540_; lean_object* v___x_6542_; 
v_directImports_6540_ = lean_ctor_get(v_val_6536_, 2);
lean_inc_ref(v_directImports_6540_);
lean_dec(v_val_6536_);
if (v_isShared_6539_ == 0)
{
lean_ctor_set(v___x_6538_, 0, v_directImports_6540_);
v___x_6542_ = v___x_6538_;
goto v_reusejp_6541_;
}
else
{
lean_object* v_reuseFailAlloc_6543_; 
v_reuseFailAlloc_6543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_directImports_6540_);
v___x_6542_ = v_reuseFailAlloc_6543_;
goto v_reusejp_6541_;
}
v_reusejp_6541_:
{
return v___x_6542_;
}
}
}
else
{
lean_object* v___x_6545_; 
lean_dec(v___x_6535_);
v___x_6545_ = lean_box(0);
return v___x_6545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6557_, lean_object* v_mod_6558_){
_start:
{
lean_object* v_res_6559_; 
v_res_6559_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6557_, v_mod_6558_);
lean_dec(v_mod_6558_);
lean_dec_ref(v_self_6557_);
return v_res_6559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6560_, lean_object* v_mod_6561_){
_start:
{
lean_object* v_ileans_6562_; lean_object* v_workers_6563_; lean_object* v___x_6576_; 
v_ileans_6562_ = lean_ctor_get(v_self_6560_, 0);
v_workers_6563_ = lean_ctor_get(v_self_6560_, 1);
v___x_6576_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6563_, v_mod_6561_);
if (lean_obj_tag(v___x_6576_) == 1)
{
lean_object* v_val_6577_; lean_object* v___x_6579_; uint8_t v_isShared_6580_; uint8_t v_isSharedCheck_6586_; 
v_val_6577_ = lean_ctor_get(v___x_6576_, 0);
v_isSharedCheck_6586_ = !lean_is_exclusive(v___x_6576_);
if (v_isSharedCheck_6586_ == 0)
{
v___x_6579_ = v___x_6576_;
v_isShared_6580_ = v_isSharedCheck_6586_;
goto v_resetjp_6578_;
}
else
{
lean_inc(v_val_6577_);
lean_dec(v___x_6576_);
v___x_6579_ = lean_box(0);
v_isShared_6580_ = v_isSharedCheck_6586_;
goto v_resetjp_6578_;
}
v_resetjp_6578_:
{
uint8_t v___x_6581_; 
v___x_6581_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6577_);
if (v___x_6581_ == 0)
{
lean_del_object(v___x_6579_);
lean_dec(v_val_6577_);
goto v___jp_6564_;
}
else
{
lean_object* v_decls_6582_; lean_object* v___x_6584_; 
v_decls_6582_ = lean_ctor_get(v_val_6577_, 5);
lean_inc(v_decls_6582_);
lean_dec(v_val_6577_);
if (v_isShared_6580_ == 0)
{
lean_ctor_set(v___x_6579_, 0, v_decls_6582_);
v___x_6584_ = v___x_6579_;
goto v_reusejp_6583_;
}
else
{
lean_object* v_reuseFailAlloc_6585_; 
v_reuseFailAlloc_6585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6585_, 0, v_decls_6582_);
v___x_6584_ = v_reuseFailAlloc_6585_;
goto v_reusejp_6583_;
}
v_reusejp_6583_:
{
return v___x_6584_;
}
}
}
}
else
{
lean_dec(v___x_6576_);
goto v___jp_6564_;
}
v___jp_6564_:
{
lean_object* v___x_6565_; 
v___x_6565_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6562_, v_mod_6561_);
if (lean_obj_tag(v___x_6565_) == 1)
{
lean_object* v_val_6566_; lean_object* v___x_6568_; uint8_t v_isShared_6569_; uint8_t v_isSharedCheck_6574_; 
v_val_6566_ = lean_ctor_get(v___x_6565_, 0);
v_isSharedCheck_6574_ = !lean_is_exclusive(v___x_6565_);
if (v_isSharedCheck_6574_ == 0)
{
v___x_6568_ = v___x_6565_;
v_isShared_6569_ = v_isSharedCheck_6574_;
goto v_resetjp_6567_;
}
else
{
lean_inc(v_val_6566_);
lean_dec(v___x_6565_);
v___x_6568_ = lean_box(0);
v_isShared_6569_ = v_isSharedCheck_6574_;
goto v_resetjp_6567_;
}
v_resetjp_6567_:
{
lean_object* v_decls_6570_; lean_object* v___x_6572_; 
v_decls_6570_ = lean_ctor_get(v_val_6566_, 4);
lean_inc(v_decls_6570_);
lean_dec(v_val_6566_);
if (v_isShared_6569_ == 0)
{
lean_ctor_set(v___x_6568_, 0, v_decls_6570_);
v___x_6572_ = v___x_6568_;
goto v_reusejp_6571_;
}
else
{
lean_object* v_reuseFailAlloc_6573_; 
v_reuseFailAlloc_6573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6573_, 0, v_decls_6570_);
v___x_6572_ = v_reuseFailAlloc_6573_;
goto v_reusejp_6571_;
}
v_reusejp_6571_:
{
return v___x_6572_;
}
}
}
else
{
lean_object* v___x_6575_; 
lean_dec(v___x_6565_);
v___x_6575_ = lean_box(0);
return v___x_6575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6587_, lean_object* v_mod_6588_){
_start:
{
lean_object* v_res_6589_; 
v_res_6589_ = l_Lean_Server_References_getDecls_x3f(v_self_6587_, v_mod_6588_);
lean_dec(v_mod_6588_);
lean_dec_ref(v_self_6587_);
return v_res_6589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6590_, lean_object* v_x_6591_){
_start:
{
if (lean_obj_tag(v_x_6591_) == 0)
{
lean_object* v_k_6592_; lean_object* v_v_6593_; lean_object* v_l_6594_; lean_object* v_r_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; 
v_k_6592_ = lean_ctor_get(v_x_6591_, 1);
v_v_6593_ = lean_ctor_get(v_x_6591_, 2);
v_l_6594_ = lean_ctor_get(v_x_6591_, 3);
v_r_6595_ = lean_ctor_get(v_x_6591_, 4);
v___x_6596_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6590_, v_l_6594_);
lean_inc(v_v_6593_);
lean_inc(v_k_6592_);
v___x_6597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6597_, 0, v_k_6592_);
lean_ctor_set(v___x_6597_, 1, v_v_6593_);
v___x_6598_ = lean_array_push(v___x_6596_, v___x_6597_);
v_init_6590_ = v___x_6598_;
v_x_6591_ = v_r_6595_;
goto _start;
}
else
{
return v_init_6590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6600_, lean_object* v_x_6601_){
_start:
{
lean_object* v_res_6602_; 
v_res_6602_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6600_, v_x_6601_);
lean_dec(v_x_6601_);
return v_res_6602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6603_, lean_object* v_k_6604_){
_start:
{
if (lean_obj_tag(v_t_6603_) == 0)
{
lean_object* v_k_6605_; lean_object* v_v_6606_; lean_object* v_l_6607_; lean_object* v_r_6608_; uint8_t v___x_6609_; 
v_k_6605_ = lean_ctor_get(v_t_6603_, 1);
v_v_6606_ = lean_ctor_get(v_t_6603_, 2);
v_l_6607_ = lean_ctor_get(v_t_6603_, 3);
v_r_6608_ = lean_ctor_get(v_t_6603_, 4);
v___x_6609_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6604_, v_k_6605_);
switch(v___x_6609_)
{
case 0:
{
v_t_6603_ = v_l_6607_;
goto _start;
}
case 1:
{
lean_object* v___x_6611_; 
lean_inc(v_v_6606_);
v___x_6611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6611_, 0, v_v_6606_);
return v___x_6611_;
}
default: 
{
v_t_6603_ = v_r_6608_;
goto _start;
}
}
}
else
{
lean_object* v___x_6613_; 
v___x_6613_ = lean_box(0);
return v___x_6613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6614_, lean_object* v_k_6615_){
_start:
{
lean_object* v_res_6616_; 
v_res_6616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6614_, v_k_6615_);
lean_dec_ref(v_k_6615_);
lean_dec(v_t_6614_);
return v_res_6616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6617_, lean_object* v_as_6618_, size_t v_sz_6619_, size_t v_i_6620_, lean_object* v_b_6621_){
_start:
{
lean_object* v_a_6623_; uint8_t v___x_6627_; 
v___x_6627_ = lean_usize_dec_lt(v_i_6620_, v_sz_6619_);
if (v___x_6627_ == 0)
{
return v_b_6621_;
}
else
{
lean_object* v_a_6628_; lean_object* v_snd_6629_; lean_object* v_snd_6630_; lean_object* v_fst_6631_; lean_object* v___x_6633_; uint8_t v_isShared_6634_; uint8_t v_isSharedCheck_6659_; 
v_a_6628_ = lean_array_uget(v_as_6618_, v_i_6620_);
v_snd_6629_ = lean_ctor_get(v_a_6628_, 1);
lean_inc(v_snd_6629_);
v_snd_6630_ = lean_ctor_get(v_snd_6629_, 1);
lean_inc(v_snd_6630_);
v_fst_6631_ = lean_ctor_get(v_a_6628_, 0);
v_isSharedCheck_6659_ = !lean_is_exclusive(v_a_6628_);
if (v_isSharedCheck_6659_ == 0)
{
lean_object* v_unused_6660_; 
v_unused_6660_ = lean_ctor_get(v_a_6628_, 1);
lean_dec(v_unused_6660_);
v___x_6633_ = v_a_6628_;
v_isShared_6634_ = v_isSharedCheck_6659_;
goto v_resetjp_6632_;
}
else
{
lean_inc(v_fst_6631_);
lean_dec(v_a_6628_);
v___x_6633_ = lean_box(0);
v_isShared_6634_ = v_isSharedCheck_6659_;
goto v_resetjp_6632_;
}
v_resetjp_6632_:
{
lean_object* v_fst_6635_; lean_object* v___x_6637_; uint8_t v_isShared_6638_; uint8_t v_isSharedCheck_6657_; 
v_fst_6635_ = lean_ctor_get(v_snd_6629_, 0);
v_isSharedCheck_6657_ = !lean_is_exclusive(v_snd_6629_);
if (v_isSharedCheck_6657_ == 0)
{
lean_object* v_unused_6658_; 
v_unused_6658_ = lean_ctor_get(v_snd_6629_, 1);
lean_dec(v_unused_6658_);
v___x_6637_ = v_snd_6629_;
v_isShared_6638_ = v_isSharedCheck_6657_;
goto v_resetjp_6636_;
}
else
{
lean_inc(v_fst_6635_);
lean_dec(v_snd_6629_);
v___x_6637_ = lean_box(0);
v_isShared_6638_ = v_isSharedCheck_6657_;
goto v_resetjp_6636_;
}
v_resetjp_6636_:
{
lean_object* v_fst_6639_; lean_object* v_snd_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6656_; 
v_fst_6639_ = lean_ctor_get(v_snd_6630_, 0);
v_snd_6640_ = lean_ctor_get(v_snd_6630_, 1);
v_isSharedCheck_6656_ = !lean_is_exclusive(v_snd_6630_);
if (v_isSharedCheck_6656_ == 0)
{
v___x_6642_ = v_snd_6630_;
v_isShared_6643_ = v_isSharedCheck_6656_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_snd_6640_);
lean_inc(v_fst_6639_);
lean_dec(v_snd_6630_);
v___x_6642_ = lean_box(0);
v_isShared_6643_ = v_isSharedCheck_6656_;
goto v_resetjp_6641_;
}
v_resetjp_6641_:
{
lean_object* v___x_6644_; 
v___x_6644_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6639_, v_ident_6617_);
lean_dec(v_fst_6639_);
if (lean_obj_tag(v___x_6644_) == 1)
{
lean_object* v_val_6645_; lean_object* v___x_6647_; 
v_val_6645_ = lean_ctor_get(v___x_6644_, 0);
lean_inc(v_val_6645_);
lean_dec_ref_known(v___x_6644_, 1);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 0, v_val_6645_);
v___x_6647_ = v___x_6642_;
goto v_reusejp_6646_;
}
else
{
lean_object* v_reuseFailAlloc_6655_; 
v_reuseFailAlloc_6655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6655_, 0, v_val_6645_);
lean_ctor_set(v_reuseFailAlloc_6655_, 1, v_snd_6640_);
v___x_6647_ = v_reuseFailAlloc_6655_;
goto v_reusejp_6646_;
}
v_reusejp_6646_:
{
lean_object* v___x_6649_; 
if (v_isShared_6638_ == 0)
{
lean_ctor_set(v___x_6637_, 1, v___x_6647_);
lean_ctor_set(v___x_6637_, 0, v_fst_6631_);
v___x_6649_ = v___x_6637_;
goto v_reusejp_6648_;
}
else
{
lean_object* v_reuseFailAlloc_6654_; 
v_reuseFailAlloc_6654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_fst_6631_);
lean_ctor_set(v_reuseFailAlloc_6654_, 1, v___x_6647_);
v___x_6649_ = v_reuseFailAlloc_6654_;
goto v_reusejp_6648_;
}
v_reusejp_6648_:
{
lean_object* v___x_6651_; 
if (v_isShared_6634_ == 0)
{
lean_ctor_set(v___x_6633_, 1, v___x_6649_);
lean_ctor_set(v___x_6633_, 0, v_fst_6635_);
v___x_6651_ = v___x_6633_;
goto v_reusejp_6650_;
}
else
{
lean_object* v_reuseFailAlloc_6653_; 
v_reuseFailAlloc_6653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6653_, 0, v_fst_6635_);
lean_ctor_set(v_reuseFailAlloc_6653_, 1, v___x_6649_);
v___x_6651_ = v_reuseFailAlloc_6653_;
goto v_reusejp_6650_;
}
v_reusejp_6650_:
{
lean_object* v___x_6652_; 
v___x_6652_ = lean_array_push(v_b_6621_, v___x_6651_);
v_a_6623_ = v___x_6652_;
goto v___jp_6622_;
}
}
}
}
else
{
lean_dec(v___x_6644_);
lean_del_object(v___x_6642_);
lean_dec(v_snd_6640_);
lean_del_object(v___x_6637_);
lean_dec(v_fst_6635_);
lean_del_object(v___x_6633_);
lean_dec(v_fst_6631_);
v_a_6623_ = v_b_6621_;
goto v___jp_6622_;
}
}
}
}
}
v___jp_6622_:
{
size_t v___x_6624_; size_t v___x_6625_; 
v___x_6624_ = ((size_t)1ULL);
v___x_6625_ = lean_usize_add(v_i_6620_, v___x_6624_);
v_i_6620_ = v___x_6625_;
v_b_6621_ = v_a_6623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6661_, lean_object* v_as_6662_, lean_object* v_sz_6663_, lean_object* v_i_6664_, lean_object* v_b_6665_){
_start:
{
size_t v_sz_boxed_6666_; size_t v_i_boxed_6667_; lean_object* v_res_6668_; 
v_sz_boxed_6666_ = lean_unbox_usize(v_sz_6663_);
lean_dec(v_sz_6663_);
v_i_boxed_6667_ = lean_unbox_usize(v_i_6664_);
lean_dec(v_i_6664_);
v_res_6668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6661_, v_as_6662_, v_sz_boxed_6666_, v_i_boxed_6667_, v_b_6665_);
lean_dec_ref(v_as_6662_);
lean_dec_ref(v_ident_6661_);
return v_res_6668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6675_, lean_object* v_ident_6676_){
_start:
{
lean_object* v___y_6678_; 
if (lean_obj_tag(v_ident_6676_) == 0)
{
lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; 
v___x_6683_ = l_Lean_Server_References_allRefs(v_self_6675_);
v___x_6684_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6685_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6684_, v___x_6683_);
lean_dec(v___x_6683_);
v___y_6678_ = v___x_6685_;
goto v___jp_6677_;
}
else
{
lean_object* v_moduleName_6686_; lean_object* v_identModuleName_6687_; lean_object* v___x_6688_; 
v_moduleName_6686_ = lean_ctor_get(v_ident_6676_, 0);
lean_inc_ref(v_moduleName_6686_);
v_identModuleName_6687_ = l_String_toName(v_moduleName_6686_);
v___x_6688_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6675_, v_identModuleName_6687_);
if (lean_obj_tag(v___x_6688_) == 0)
{
lean_object* v___x_6689_; 
lean_dec(v_identModuleName_6687_);
v___x_6689_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6678_ = v___x_6689_;
goto v___jp_6677_;
}
else
{
lean_object* v_val_6690_; lean_object* v___x_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; 
v_val_6690_ = lean_ctor_get(v___x_6688_, 0);
lean_inc(v_val_6690_);
lean_dec_ref_known(v___x_6688_, 1);
v___x_6691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6691_, 0, v_identModuleName_6687_);
lean_ctor_set(v___x_6691_, 1, v_val_6690_);
v___x_6692_ = lean_unsigned_to_nat(1u);
v___x_6693_ = lean_mk_empty_array_with_capacity(v___x_6692_);
v___x_6694_ = lean_array_push(v___x_6693_, v___x_6691_);
v___y_6678_ = v___x_6694_;
goto v___jp_6677_;
}
}
v___jp_6677_:
{
lean_object* v_result_6679_; size_t v_sz_6680_; size_t v___x_6681_; lean_object* v___x_6682_; 
v_result_6679_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6680_ = lean_array_size(v___y_6678_);
v___x_6681_ = ((size_t)0ULL);
v___x_6682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6676_, v___y_6678_, v_sz_6680_, v___x_6681_, v_result_6679_);
lean_dec_ref(v___y_6678_);
lean_dec_ref(v_ident_6676_);
return v___x_6682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6695_, lean_object* v_t_6696_, lean_object* v_k_6697_){
_start:
{
lean_object* v___x_6698_; 
v___x_6698_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6696_, v_k_6697_);
return v___x_6698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6699_, lean_object* v_t_6700_, lean_object* v_k_6701_){
_start:
{
lean_object* v_res_6702_; 
v_res_6702_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6699_, v_t_6700_, v_k_6701_);
lean_dec_ref(v_k_6701_);
lean_dec(v_t_6700_);
return v_res_6702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6703_, lean_object* v_t_6704_){
_start:
{
lean_object* v___x_6705_; 
v___x_6705_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6703_, v_t_6704_);
return v___x_6705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6706_, lean_object* v_t_6707_){
_start:
{
lean_object* v_res_6708_; 
v_res_6708_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6706_, v_t_6707_);
lean_dec(v_t_6707_);
return v_res_6708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6709_, lean_object* v_module_6710_, lean_object* v_pos_6711_, uint8_t v_includeStop_6712_){
_start:
{
lean_object* v___x_6713_; 
v___x_6713_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6709_, v_module_6710_);
if (lean_obj_tag(v___x_6713_) == 1)
{
lean_object* v_val_6714_; lean_object* v_snd_6715_; lean_object* v_fst_6716_; lean_object* v___x_6717_; 
v_val_6714_ = lean_ctor_get(v___x_6713_, 0);
lean_inc(v_val_6714_);
lean_dec_ref_known(v___x_6713_, 1);
v_snd_6715_ = lean_ctor_get(v_val_6714_, 1);
lean_inc(v_snd_6715_);
lean_dec(v_val_6714_);
v_fst_6716_ = lean_ctor_get(v_snd_6715_, 0);
lean_inc(v_fst_6716_);
lean_dec(v_snd_6715_);
v___x_6717_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6716_, v_pos_6711_, v_includeStop_6712_);
return v___x_6717_;
}
else
{
lean_object* v___x_6718_; 
lean_dec(v___x_6713_);
v___x_6718_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6719_, lean_object* v_module_6720_, lean_object* v_pos_6721_, lean_object* v_includeStop_6722_){
_start:
{
uint8_t v_includeStop_boxed_6723_; lean_object* v_res_6724_; 
v_includeStop_boxed_6723_ = lean_unbox(v_includeStop_6722_);
v_res_6724_ = l_Lean_Server_References_findAt(v_self_6719_, v_module_6720_, v_pos_6721_, v_includeStop_boxed_6723_);
lean_dec_ref(v_pos_6721_);
lean_dec(v_module_6720_);
return v_res_6724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6725_, lean_object* v_module_6726_, lean_object* v_pos_6727_, uint8_t v_includeStop_6728_){
_start:
{
lean_object* v___x_6729_; 
v___x_6729_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6725_, v_module_6726_);
if (lean_obj_tag(v___x_6729_) == 0)
{
lean_object* v___x_6730_; 
v___x_6730_ = lean_box(0);
return v___x_6730_;
}
else
{
lean_object* v_val_6731_; lean_object* v_snd_6732_; lean_object* v_fst_6733_; lean_object* v___x_6734_; 
v_val_6731_ = lean_ctor_get(v___x_6729_, 0);
lean_inc(v_val_6731_);
lean_dec_ref_known(v___x_6729_, 1);
v_snd_6732_ = lean_ctor_get(v_val_6731_, 1);
lean_inc(v_snd_6732_);
lean_dec(v_val_6731_);
v_fst_6733_ = lean_ctor_get(v_snd_6732_, 0);
lean_inc(v_fst_6733_);
lean_dec(v_snd_6732_);
v___x_6734_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6733_, v_pos_6727_, v_includeStop_6728_);
lean_dec(v_fst_6733_);
return v___x_6734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6735_, lean_object* v_module_6736_, lean_object* v_pos_6737_, lean_object* v_includeStop_6738_){
_start:
{
uint8_t v_includeStop_boxed_6739_; lean_object* v_res_6740_; 
v_includeStop_boxed_6739_ = lean_unbox(v_includeStop_6738_);
v_res_6740_ = l_Lean_Server_References_findRange_x3f(v_self_6735_, v_module_6736_, v_pos_6737_, v_includeStop_boxed_6739_);
lean_dec_ref(v_pos_6737_);
lean_dec(v_module_6736_);
return v_res_6740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6741_, lean_object* v_k_6742_){
_start:
{
if (lean_obj_tag(v_t_6741_) == 0)
{
lean_object* v_k_6743_; lean_object* v_v_6744_; lean_object* v_l_6745_; lean_object* v_r_6746_; uint8_t v___x_6747_; 
v_k_6743_ = lean_ctor_get(v_t_6741_, 1);
v_v_6744_ = lean_ctor_get(v_t_6741_, 2);
v_l_6745_ = lean_ctor_get(v_t_6741_, 3);
v_r_6746_ = lean_ctor_get(v_t_6741_, 4);
v___x_6747_ = lean_string_compare(v_k_6742_, v_k_6743_);
switch(v___x_6747_)
{
case 0:
{
v_t_6741_ = v_l_6745_;
goto _start;
}
case 1:
{
lean_object* v___x_6749_; 
lean_inc(v_v_6744_);
v___x_6749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6749_, 0, v_v_6744_);
return v___x_6749_;
}
default: 
{
v_t_6741_ = v_r_6746_;
goto _start;
}
}
}
else
{
lean_object* v___x_6751_; 
v___x_6751_ = lean_box(0);
return v___x_6751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6752_, lean_object* v_k_6753_){
_start:
{
lean_object* v_res_6754_; 
v_res_6754_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6752_, v_k_6753_);
lean_dec_ref(v_k_6753_);
lean_dec(v_t_6752_);
return v_res_6754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6755_, lean_object* v_name_6756_){
_start:
{
lean_object* v___x_6757_; 
v___x_6757_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6755_, v_name_6756_);
if (lean_obj_tag(v___x_6757_) == 0)
{
lean_object* v___x_6758_; 
lean_dec_ref(v_name_6756_);
v___x_6758_ = lean_box(0);
return v___x_6758_;
}
else
{
lean_object* v_val_6759_; lean_object* v___x_6761_; uint8_t v_isShared_6762_; uint8_t v_isSharedCheck_6769_; 
v_val_6759_ = lean_ctor_get(v___x_6757_, 0);
v_isSharedCheck_6769_ = !lean_is_exclusive(v___x_6757_);
if (v_isSharedCheck_6769_ == 0)
{
v___x_6761_ = v___x_6757_;
v_isShared_6762_ = v_isSharedCheck_6769_;
goto v_resetjp_6760_;
}
else
{
lean_inc(v_val_6759_);
lean_dec(v___x_6757_);
v___x_6761_ = lean_box(0);
v_isShared_6762_ = v_isSharedCheck_6769_;
goto v_resetjp_6760_;
}
v_resetjp_6760_:
{
lean_object* v___x_6763_; lean_object* v___x_6764_; lean_object* v___x_6765_; lean_object* v___x_6767_; 
v___x_6763_ = l_Lean_Lsp_DeclInfo_range(v_val_6759_);
v___x_6764_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6759_);
lean_dec(v_val_6759_);
v___x_6765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6765_, 0, v_name_6756_);
lean_ctor_set(v___x_6765_, 1, v___x_6763_);
lean_ctor_set(v___x_6765_, 2, v___x_6764_);
if (v_isShared_6762_ == 0)
{
lean_ctor_set(v___x_6761_, 0, v___x_6765_);
v___x_6767_ = v___x_6761_;
goto v_reusejp_6766_;
}
else
{
lean_object* v_reuseFailAlloc_6768_; 
v_reuseFailAlloc_6768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6768_, 0, v___x_6765_);
v___x_6767_ = v_reuseFailAlloc_6768_;
goto v_reusejp_6766_;
}
v_reusejp_6766_:
{
return v___x_6767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6770_, lean_object* v_name_6771_){
_start:
{
lean_object* v_res_6772_; 
v_res_6772_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6770_, v_name_6771_);
lean_dec(v_ds_6770_);
return v_res_6772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6773_, lean_object* v_t_6774_, lean_object* v_k_6775_){
_start:
{
lean_object* v___x_6776_; 
v___x_6776_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6774_, v_k_6775_);
return v___x_6776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6777_, lean_object* v_t_6778_, lean_object* v_k_6779_){
_start:
{
lean_object* v_res_6780_; 
v_res_6780_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6777_, v_t_6778_, v_k_6779_);
lean_dec_ref(v_k_6779_);
lean_dec(v_t_6778_);
return v_res_6780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6781_, lean_object* v_fst_6782_, lean_object* v_snd_6783_, lean_object* v_as_6784_, size_t v_sz_6785_, size_t v_i_6786_, lean_object* v_b_6787_){
_start:
{
uint8_t v___x_6788_; 
v___x_6788_ = lean_usize_dec_lt(v_i_6786_, v_sz_6785_);
if (v___x_6788_ == 0)
{
lean_dec(v_fst_6782_);
lean_dec_ref(v_fst_6781_);
return v_b_6787_;
}
else
{
lean_object* v_a_6789_; lean_object* v___y_6791_; lean_object* v___x_6799_; 
v_a_6789_ = lean_array_uget_borrowed(v_as_6784_, v_i_6786_);
v___x_6799_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6789_);
if (lean_obj_tag(v___x_6799_) == 0)
{
lean_object* v___x_6800_; 
v___x_6800_ = lean_box(0);
v___y_6791_ = v___x_6800_;
goto v___jp_6790_;
}
else
{
lean_object* v_val_6801_; lean_object* v___x_6802_; 
v_val_6801_ = lean_ctor_get(v___x_6799_, 0);
lean_inc(v_val_6801_);
lean_dec_ref_known(v___x_6799_, 1);
v___x_6802_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6783_, v_val_6801_);
v___y_6791_ = v___x_6802_;
goto v___jp_6790_;
}
v___jp_6790_:
{
lean_object* v___x_6792_; lean_object* v___x_6793_; lean_object* v___x_6794_; lean_object* v___x_6795_; size_t v___x_6796_; size_t v___x_6797_; 
v___x_6792_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6789_);
lean_inc_ref(v_fst_6781_);
v___x_6793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6793_, 0, v_fst_6781_);
lean_ctor_set(v___x_6793_, 1, v___x_6792_);
lean_inc(v_fst_6782_);
v___x_6794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6794_, 0, v___x_6793_);
lean_ctor_set(v___x_6794_, 1, v_fst_6782_);
lean_ctor_set(v___x_6794_, 2, v___y_6791_);
v___x_6795_ = lean_array_push(v_b_6787_, v___x_6794_);
v___x_6796_ = ((size_t)1ULL);
v___x_6797_ = lean_usize_add(v_i_6786_, v___x_6796_);
v_i_6786_ = v___x_6797_;
v_b_6787_ = v___x_6795_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6803_, lean_object* v_fst_6804_, lean_object* v_snd_6805_, lean_object* v_as_6806_, lean_object* v_sz_6807_, lean_object* v_i_6808_, lean_object* v_b_6809_){
_start:
{
size_t v_sz_boxed_6810_; size_t v_i_boxed_6811_; lean_object* v_res_6812_; 
v_sz_boxed_6810_ = lean_unbox_usize(v_sz_6807_);
lean_dec(v_sz_6807_);
v_i_boxed_6811_ = lean_unbox_usize(v_i_6808_);
lean_dec(v_i_6808_);
v_res_6812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6803_, v_fst_6804_, v_snd_6805_, v_as_6806_, v_sz_boxed_6810_, v_i_boxed_6811_, v_b_6809_);
lean_dec_ref(v_as_6806_);
lean_dec(v_snd_6805_);
return v_res_6812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6813_, lean_object* v_as_6814_, size_t v_sz_6815_, size_t v_i_6816_, lean_object* v_b_6817_){
_start:
{
uint8_t v___x_6818_; 
v___x_6818_ = lean_usize_dec_lt(v_i_6816_, v_sz_6815_);
if (v___x_6818_ == 0)
{
return v_b_6817_;
}
else
{
lean_object* v_a_6819_; lean_object* v_snd_6820_; lean_object* v_snd_6821_; lean_object* v_fst_6822_; lean_object* v_fst_6823_; lean_object* v_fst_6824_; lean_object* v_snd_6825_; lean_object* v___x_6827_; uint8_t v_isShared_6828_; uint8_t v_isSharedCheck_6852_; 
v_a_6819_ = lean_array_uget_borrowed(v_as_6814_, v_i_6816_);
v_snd_6820_ = lean_ctor_get(v_a_6819_, 1);
v_snd_6821_ = lean_ctor_get(v_snd_6820_, 1);
lean_inc(v_snd_6821_);
v_fst_6822_ = lean_ctor_get(v_a_6819_, 0);
v_fst_6823_ = lean_ctor_get(v_snd_6820_, 0);
v_fst_6824_ = lean_ctor_get(v_snd_6821_, 0);
v_snd_6825_ = lean_ctor_get(v_snd_6821_, 1);
v_isSharedCheck_6852_ = !lean_is_exclusive(v_snd_6821_);
if (v_isSharedCheck_6852_ == 0)
{
v___x_6827_ = v_snd_6821_;
v_isShared_6828_ = v_isSharedCheck_6852_;
goto v_resetjp_6826_;
}
else
{
lean_inc(v_snd_6825_);
lean_inc(v_fst_6824_);
lean_dec(v_snd_6821_);
v___x_6827_ = lean_box(0);
v_isShared_6828_ = v_isSharedCheck_6852_;
goto v_resetjp_6826_;
}
v_resetjp_6826_:
{
lean_object* v_result_6830_; 
if (v_includeDefinition_6813_ == 0)
{
lean_del_object(v___x_6827_);
v_result_6830_ = v_b_6817_;
goto v___jp_6829_;
}
else
{
lean_object* v_definition_x3f_6838_; 
v_definition_x3f_6838_ = lean_ctor_get(v_fst_6824_, 0);
if (lean_obj_tag(v_definition_x3f_6838_) == 1)
{
lean_object* v_val_6839_; lean_object* v___y_6841_; lean_object* v___x_6848_; 
v_val_6839_ = lean_ctor_get(v_definition_x3f_6838_, 0);
v___x_6848_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6839_);
if (lean_obj_tag(v___x_6848_) == 0)
{
lean_object* v___x_6849_; 
v___x_6849_ = lean_box(0);
v___y_6841_ = v___x_6849_;
goto v___jp_6840_;
}
else
{
lean_object* v_val_6850_; lean_object* v___x_6851_; 
v_val_6850_ = lean_ctor_get(v___x_6848_, 0);
lean_inc(v_val_6850_);
lean_dec_ref_known(v___x_6848_, 1);
v___x_6851_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6825_, v_val_6850_);
v___y_6841_ = v___x_6851_;
goto v___jp_6840_;
}
v___jp_6840_:
{
lean_object* v___x_6842_; lean_object* v___x_6844_; 
v___x_6842_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6839_);
lean_inc(v_fst_6822_);
if (v_isShared_6828_ == 0)
{
lean_ctor_set(v___x_6827_, 1, v___x_6842_);
lean_ctor_set(v___x_6827_, 0, v_fst_6822_);
v___x_6844_ = v___x_6827_;
goto v_reusejp_6843_;
}
else
{
lean_object* v_reuseFailAlloc_6847_; 
v_reuseFailAlloc_6847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6847_, 0, v_fst_6822_);
lean_ctor_set(v_reuseFailAlloc_6847_, 1, v___x_6842_);
v___x_6844_ = v_reuseFailAlloc_6847_;
goto v_reusejp_6843_;
}
v_reusejp_6843_:
{
lean_object* v___x_6845_; lean_object* v___x_6846_; 
lean_inc(v_fst_6823_);
v___x_6845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6845_, 0, v___x_6844_);
lean_ctor_set(v___x_6845_, 1, v_fst_6823_);
lean_ctor_set(v___x_6845_, 2, v___y_6841_);
v___x_6846_ = lean_array_push(v_b_6817_, v___x_6845_);
v_result_6830_ = v___x_6846_;
goto v___jp_6829_;
}
}
}
else
{
lean_del_object(v___x_6827_);
v_result_6830_ = v_b_6817_;
goto v___jp_6829_;
}
}
v___jp_6829_:
{
lean_object* v_usages_6831_; size_t v_sz_6832_; size_t v___x_6833_; lean_object* v___x_6834_; size_t v___x_6835_; size_t v___x_6836_; 
v_usages_6831_ = lean_ctor_get(v_fst_6824_, 1);
lean_inc_ref(v_usages_6831_);
lean_dec(v_fst_6824_);
v_sz_6832_ = lean_array_size(v_usages_6831_);
v___x_6833_ = ((size_t)0ULL);
lean_inc(v_fst_6823_);
lean_inc(v_fst_6822_);
v___x_6834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6822_, v_fst_6823_, v_snd_6825_, v_usages_6831_, v_sz_6832_, v___x_6833_, v_result_6830_);
lean_dec_ref(v_usages_6831_);
lean_dec(v_snd_6825_);
v___x_6835_ = ((size_t)1ULL);
v___x_6836_ = lean_usize_add(v_i_6816_, v___x_6835_);
v_i_6816_ = v___x_6836_;
v_b_6817_ = v___x_6834_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6853_, lean_object* v_as_6854_, lean_object* v_sz_6855_, lean_object* v_i_6856_, lean_object* v_b_6857_){
_start:
{
uint8_t v_includeDefinition_boxed_6858_; size_t v_sz_boxed_6859_; size_t v_i_boxed_6860_; lean_object* v_res_6861_; 
v_includeDefinition_boxed_6858_ = lean_unbox(v_includeDefinition_6853_);
v_sz_boxed_6859_ = lean_unbox_usize(v_sz_6855_);
lean_dec(v_sz_6855_);
v_i_boxed_6860_ = lean_unbox_usize(v_i_6856_);
lean_dec(v_i_6856_);
v_res_6861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6858_, v_as_6854_, v_sz_boxed_6859_, v_i_boxed_6860_, v_b_6857_);
lean_dec_ref(v_as_6854_);
return v_res_6861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6864_, lean_object* v_ident_6865_, uint8_t v_includeDefinition_6866_){
_start:
{
lean_object* v_result_6867_; lean_object* v___x_6868_; size_t v_sz_6869_; size_t v___x_6870_; lean_object* v___x_6871_; 
v_result_6867_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6868_ = l_Lean_Server_References_allRefsFor(v_self_6864_, v_ident_6865_);
v_sz_6869_ = lean_array_size(v___x_6868_);
v___x_6870_ = ((size_t)0ULL);
v___x_6871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6866_, v___x_6868_, v_sz_6869_, v___x_6870_, v_result_6867_);
lean_dec_ref(v___x_6868_);
return v___x_6871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6872_, lean_object* v_ident_6873_, lean_object* v_includeDefinition_6874_){
_start:
{
uint8_t v_includeDefinition_boxed_6875_; lean_object* v_res_6876_; 
v_includeDefinition_boxed_6875_ = lean_unbox(v_includeDefinition_6874_);
v_res_6876_ = l_Lean_Server_References_referringTo(v_self_6872_, v_ident_6873_, v_includeDefinition_boxed_6875_);
return v_res_6876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6880_, size_t v_sz_6881_, size_t v_i_6882_, lean_object* v_b_6883_){
_start:
{
uint8_t v___x_6884_; 
v___x_6884_ = lean_usize_dec_lt(v_i_6882_, v_sz_6881_);
if (v___x_6884_ == 0)
{
lean_inc_ref(v_b_6883_);
return v_b_6883_;
}
else
{
lean_object* v_a_6885_; lean_object* v_snd_6886_; lean_object* v_snd_6887_; lean_object* v_fst_6888_; lean_object* v_fst_6889_; lean_object* v_fst_6890_; lean_object* v_snd_6891_; lean_object* v___x_6893_; uint8_t v_isShared_6894_; uint8_t v_isSharedCheck_6929_; 
v_a_6885_ = lean_array_uget_borrowed(v_as_6880_, v_i_6882_);
v_snd_6886_ = lean_ctor_get(v_a_6885_, 1);
v_snd_6887_ = lean_ctor_get(v_snd_6886_, 1);
lean_inc(v_snd_6887_);
v_fst_6888_ = lean_ctor_get(v_snd_6887_, 0);
lean_inc(v_fst_6888_);
v_fst_6889_ = lean_ctor_get(v_a_6885_, 0);
v_fst_6890_ = lean_ctor_get(v_snd_6886_, 0);
v_snd_6891_ = lean_ctor_get(v_snd_6887_, 1);
v_isSharedCheck_6929_ = !lean_is_exclusive(v_snd_6887_);
if (v_isSharedCheck_6929_ == 0)
{
lean_object* v_unused_6930_; 
v_unused_6930_ = lean_ctor_get(v_snd_6887_, 0);
lean_dec(v_unused_6930_);
v___x_6893_ = v_snd_6887_;
v_isShared_6894_ = v_isSharedCheck_6929_;
goto v_resetjp_6892_;
}
else
{
lean_inc(v_snd_6891_);
lean_dec(v_snd_6887_);
v___x_6893_ = lean_box(0);
v_isShared_6894_ = v_isSharedCheck_6929_;
goto v_resetjp_6892_;
}
v_resetjp_6892_:
{
lean_object* v_definition_x3f_6895_; lean_object* v___x_6897_; uint8_t v_isShared_6898_; uint8_t v_isSharedCheck_6927_; 
v_definition_x3f_6895_ = lean_ctor_get(v_fst_6888_, 0);
v_isSharedCheck_6927_ = !lean_is_exclusive(v_fst_6888_);
if (v_isSharedCheck_6927_ == 0)
{
lean_object* v_unused_6928_; 
v_unused_6928_ = lean_ctor_get(v_fst_6888_, 1);
lean_dec(v_unused_6928_);
v___x_6897_ = v_fst_6888_;
v_isShared_6898_ = v_isSharedCheck_6927_;
goto v_resetjp_6896_;
}
else
{
lean_inc(v_definition_x3f_6895_);
lean_dec(v_fst_6888_);
v___x_6897_ = lean_box(0);
v_isShared_6898_ = v_isSharedCheck_6927_;
goto v_resetjp_6896_;
}
v_resetjp_6896_:
{
lean_object* v___x_6899_; 
v___x_6899_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6895_) == 1)
{
lean_object* v_val_6900_; lean_object* v___x_6902_; uint8_t v_isShared_6903_; uint8_t v_isSharedCheck_6922_; 
v_val_6900_ = lean_ctor_get(v_definition_x3f_6895_, 0);
v_isSharedCheck_6922_ = !lean_is_exclusive(v_definition_x3f_6895_);
if (v_isSharedCheck_6922_ == 0)
{
v___x_6902_ = v_definition_x3f_6895_;
v_isShared_6903_ = v_isSharedCheck_6922_;
goto v_resetjp_6901_;
}
else
{
lean_inc(v_val_6900_);
lean_dec(v_definition_x3f_6895_);
v___x_6902_ = lean_box(0);
v_isShared_6903_ = v_isSharedCheck_6922_;
goto v_resetjp_6901_;
}
v_resetjp_6901_:
{
lean_object* v___y_6905_; lean_object* v___x_6918_; 
v___x_6918_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6900_);
if (lean_obj_tag(v___x_6918_) == 0)
{
lean_object* v___x_6919_; 
lean_dec(v_snd_6891_);
v___x_6919_ = lean_box(0);
v___y_6905_ = v___x_6919_;
goto v___jp_6904_;
}
else
{
lean_object* v_val_6920_; lean_object* v___x_6921_; 
v_val_6920_ = lean_ctor_get(v___x_6918_, 0);
lean_inc(v_val_6920_);
lean_dec_ref_known(v___x_6918_, 1);
v___x_6921_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6891_, v_val_6920_);
lean_dec(v_snd_6891_);
v___y_6905_ = v___x_6921_;
goto v___jp_6904_;
}
v___jp_6904_:
{
lean_object* v___x_6906_; lean_object* v___x_6908_; 
v___x_6906_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6900_);
lean_dec(v_val_6900_);
lean_inc(v_fst_6889_);
if (v_isShared_6898_ == 0)
{
lean_ctor_set(v___x_6897_, 1, v___x_6906_);
lean_ctor_set(v___x_6897_, 0, v_fst_6889_);
v___x_6908_ = v___x_6897_;
goto v_reusejp_6907_;
}
else
{
lean_object* v_reuseFailAlloc_6917_; 
v_reuseFailAlloc_6917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6917_, 0, v_fst_6889_);
lean_ctor_set(v_reuseFailAlloc_6917_, 1, v___x_6906_);
v___x_6908_ = v_reuseFailAlloc_6917_;
goto v_reusejp_6907_;
}
v_reusejp_6907_:
{
lean_object* v___x_6909_; lean_object* v___x_6911_; 
lean_inc(v_fst_6890_);
v___x_6909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6909_, 0, v___x_6908_);
lean_ctor_set(v___x_6909_, 1, v_fst_6890_);
lean_ctor_set(v___x_6909_, 2, v___y_6905_);
if (v_isShared_6903_ == 0)
{
lean_ctor_set(v___x_6902_, 0, v___x_6909_);
v___x_6911_ = v___x_6902_;
goto v_reusejp_6910_;
}
else
{
lean_object* v_reuseFailAlloc_6916_; 
v_reuseFailAlloc_6916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6916_, 0, v___x_6909_);
v___x_6911_ = v_reuseFailAlloc_6916_;
goto v_reusejp_6910_;
}
v_reusejp_6910_:
{
lean_object* v___x_6912_; lean_object* v___x_6914_; 
v___x_6912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6912_, 0, v___x_6911_);
if (v_isShared_6894_ == 0)
{
lean_ctor_set(v___x_6893_, 1, v___x_6899_);
lean_ctor_set(v___x_6893_, 0, v___x_6912_);
v___x_6914_ = v___x_6893_;
goto v_reusejp_6913_;
}
else
{
lean_object* v_reuseFailAlloc_6915_; 
v_reuseFailAlloc_6915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6915_, 0, v___x_6912_);
lean_ctor_set(v_reuseFailAlloc_6915_, 1, v___x_6899_);
v___x_6914_ = v_reuseFailAlloc_6915_;
goto v_reusejp_6913_;
}
v_reusejp_6913_:
{
return v___x_6914_;
}
}
}
}
}
}
else
{
lean_object* v___x_6923_; size_t v___x_6924_; size_t v___x_6925_; 
lean_del_object(v___x_6897_);
lean_dec(v_definition_x3f_6895_);
lean_del_object(v___x_6893_);
lean_dec(v_snd_6891_);
v___x_6923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6924_ = ((size_t)1ULL);
v___x_6925_ = lean_usize_add(v_i_6882_, v___x_6924_);
v_i_6882_ = v___x_6925_;
v_b_6883_ = v___x_6923_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6931_, lean_object* v_sz_6932_, lean_object* v_i_6933_, lean_object* v_b_6934_){
_start:
{
size_t v_sz_boxed_6935_; size_t v_i_boxed_6936_; lean_object* v_res_6937_; 
v_sz_boxed_6935_ = lean_unbox_usize(v_sz_6932_);
lean_dec(v_sz_6932_);
v_i_boxed_6936_ = lean_unbox_usize(v_i_6933_);
lean_dec(v_i_6933_);
v_res_6937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6931_, v_sz_boxed_6935_, v_i_boxed_6936_, v_b_6934_);
lean_dec_ref(v_b_6934_);
lean_dec_ref(v_as_6931_);
return v_res_6937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6938_, lean_object* v_ident_6939_){
_start:
{
lean_object* v___x_6940_; lean_object* v___x_6941_; lean_object* v___x_6942_; size_t v_sz_6943_; size_t v___x_6944_; lean_object* v___x_6945_; lean_object* v_fst_6946_; 
v___x_6940_ = l_Lean_Server_References_allRefsFor(v_self_6938_, v_ident_6939_);
v___x_6941_ = lean_box(0);
v___x_6942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6943_ = lean_array_size(v___x_6940_);
v___x_6944_ = ((size_t)0ULL);
v___x_6945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6940_, v_sz_6943_, v___x_6944_, v___x_6942_);
lean_dec_ref(v___x_6940_);
v_fst_6946_ = lean_ctor_get(v___x_6945_, 0);
lean_inc(v_fst_6946_);
lean_dec_ref(v___x_6945_);
if (lean_obj_tag(v_fst_6946_) == 0)
{
return v___x_6941_;
}
else
{
lean_object* v_val_6947_; 
v_val_6947_ = lean_ctor_get(v_fst_6946_, 0);
lean_inc(v_val_6947_);
lean_dec_ref_known(v_fst_6946_, 1);
return v_val_6947_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6948_, lean_object* v_a_6949_, lean_object* v_fst_6950_, lean_object* v_init_6951_, lean_object* v_x_6952_){
_start:
{
if (lean_obj_tag(v_x_6952_) == 0)
{
lean_object* v_k_6954_; lean_object* v_v_6955_; lean_object* v_l_6956_; lean_object* v_r_6957_; lean_object* v___x_6958_; 
v_k_6954_ = lean_ctor_get(v_x_6952_, 1);
lean_inc(v_k_6954_);
v_v_6955_ = lean_ctor_get(v_x_6952_, 2);
lean_inc(v_v_6955_);
v_l_6956_ = lean_ctor_get(v_x_6952_, 3);
lean_inc(v_l_6956_);
v_r_6957_ = lean_ctor_get(v_x_6952_, 4);
lean_inc(v_r_6957_);
lean_dec_ref_known(v_x_6952_, 5);
lean_inc_ref(v_fst_6950_);
lean_inc(v_a_6949_);
lean_inc_ref(v_filterMapIdent_6948_);
v___x_6958_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6948_, v_a_6949_, v_fst_6950_, v_init_6951_, v_l_6956_);
if (lean_obj_tag(v_k_6954_) == 0)
{
lean_object* v_definition_x3f_6959_; 
v_definition_x3f_6959_ = lean_ctor_get(v_v_6955_, 0);
lean_inc(v_definition_x3f_6959_);
lean_dec(v_v_6955_);
if (lean_obj_tag(v_definition_x3f_6959_) == 1)
{
lean_object* v_a_6960_; lean_object* v_identName_6961_; lean_object* v_val_6962_; lean_object* v___x_6963_; lean_object* v___x_6964_; 
v_a_6960_ = lean_ctor_get(v___x_6958_, 0);
lean_inc(v_a_6960_);
lean_dec_ref(v___x_6958_);
v_identName_6961_ = lean_ctor_get(v_k_6954_, 1);
lean_inc_ref(v_identName_6961_);
lean_dec_ref_known(v_k_6954_, 2);
v_val_6962_ = lean_ctor_get(v_definition_x3f_6959_, 0);
lean_inc(v_val_6962_);
lean_dec_ref_known(v_definition_x3f_6959_, 1);
v___x_6963_ = l_String_toName(v_identName_6961_);
lean_inc_ref(v_filterMapIdent_6948_);
v___x_6964_ = lean_apply_1(v_filterMapIdent_6948_, v___x_6963_);
if (lean_obj_tag(v___x_6964_) == 1)
{
lean_object* v_val_6965_; lean_object* v___x_6966_; lean_object* v___x_6967_; lean_object* v___x_6968_; 
v_val_6965_ = lean_ctor_get(v___x_6964_, 0);
lean_inc(v_val_6965_);
lean_dec_ref_known(v___x_6964_, 1);
v___x_6966_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6962_);
lean_dec(v_val_6962_);
lean_inc_ref(v_fst_6950_);
lean_inc(v_a_6949_);
v___x_6967_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6967_, 0, v_a_6949_);
lean_ctor_set(v___x_6967_, 1, v_fst_6950_);
lean_ctor_set(v___x_6967_, 2, v_val_6965_);
lean_ctor_set(v___x_6967_, 3, v___x_6966_);
v___x_6968_ = lean_array_push(v_a_6960_, v___x_6967_);
v_init_6951_ = v___x_6968_;
v_x_6952_ = v_r_6957_;
goto _start;
}
else
{
lean_dec(v___x_6964_);
lean_dec(v_val_6962_);
v_init_6951_ = v_a_6960_;
v_x_6952_ = v_r_6957_;
goto _start;
}
}
else
{
lean_object* v_a_6971_; 
lean_dec_ref_known(v_k_6954_, 2);
lean_dec(v_definition_x3f_6959_);
v_a_6971_ = lean_ctor_get(v___x_6958_, 0);
lean_inc(v_a_6971_);
lean_dec_ref(v___x_6958_);
v_init_6951_ = v_a_6971_;
v_x_6952_ = v_r_6957_;
goto _start;
}
}
else
{
lean_object* v_a_6973_; 
lean_dec(v_v_6955_);
lean_dec(v_k_6954_);
v_a_6973_ = lean_ctor_get(v___x_6958_, 0);
lean_inc(v_a_6973_);
lean_dec_ref(v___x_6958_);
v_init_6951_ = v_a_6973_;
v_x_6952_ = v_r_6957_;
goto _start;
}
}
else
{
lean_object* v___x_6975_; 
lean_dec_ref(v_fst_6950_);
lean_dec(v_a_6949_);
lean_dec_ref(v_filterMapIdent_6948_);
v___x_6975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6975_, 0, v_init_6951_);
return v___x_6975_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6976_, lean_object* v_a_6977_, lean_object* v_fst_6978_, lean_object* v_init_6979_, lean_object* v_x_6980_, lean_object* v___y_6981_){
_start:
{
lean_object* v_res_6982_; 
v_res_6982_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6976_, v_a_6977_, v_fst_6978_, v_init_6979_, v_x_6980_);
return v_res_6982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6983_, lean_object* v_cancelTk_x3f_6984_, lean_object* v_init_6985_, lean_object* v_x_6986_){
_start:
{
lean_object* v_d_6989_; 
if (lean_obj_tag(v_x_6986_) == 0)
{
lean_object* v_k_6991_; lean_object* v_v_6992_; lean_object* v_l_6993_; lean_object* v_r_6994_; lean_object* v___x_6995_; lean_object* v_val_6997_; lean_object* v___x_7000_; 
v_k_6991_ = lean_ctor_get(v_x_6986_, 1);
lean_inc(v_k_6991_);
v_v_6992_ = lean_ctor_get(v_x_6986_, 2);
lean_inc(v_v_6992_);
v_l_6993_ = lean_ctor_get(v_x_6986_, 3);
lean_inc(v_l_6993_);
v_r_6994_ = lean_ctor_get(v_x_6986_, 4);
lean_inc(v_r_6994_);
lean_dec_ref_known(v_x_6986_, 5);
v___x_6995_ = lean_box(0);
lean_inc(v_cancelTk_x3f_6984_);
lean_inc_ref(v_filterMapIdent_6983_);
v___x_7000_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6983_, v_cancelTk_x3f_6984_, v_init_6985_, v_l_6993_);
if (lean_obj_tag(v___x_7000_) == 0)
{
lean_object* v_a_7001_; 
lean_dec(v_r_6994_);
lean_dec(v_v_6992_);
lean_dec(v_k_6991_);
lean_dec(v_cancelTk_x3f_6984_);
lean_dec_ref(v_filterMapIdent_6983_);
v_a_7001_ = lean_ctor_get(v___x_7000_, 0);
lean_inc(v_a_7001_);
lean_dec_ref_known(v___x_7000_, 1);
v_d_6989_ = v_a_7001_;
goto v___jp_6988_;
}
else
{
lean_object* v_snd_7002_; lean_object* v_a_7003_; lean_object* v_fst_7004_; lean_object* v_fst_7005_; lean_object* v_snd_7006_; lean_object* v___x_7008_; uint8_t v_isShared_7009_; uint8_t v_isSharedCheck_7026_; 
v_snd_7002_ = lean_ctor_get(v_v_6992_, 1);
lean_inc(v_snd_7002_);
v_a_7003_ = lean_ctor_get(v___x_7000_, 0);
lean_inc(v_a_7003_);
lean_dec_ref_known(v___x_7000_, 1);
v_fst_7004_ = lean_ctor_get(v_v_6992_, 0);
lean_inc(v_fst_7004_);
lean_dec(v_v_6992_);
v_fst_7005_ = lean_ctor_get(v_snd_7002_, 0);
lean_inc(v_fst_7005_);
lean_dec(v_snd_7002_);
v_snd_7006_ = lean_ctor_get(v_a_7003_, 1);
v_isSharedCheck_7026_ = !lean_is_exclusive(v_a_7003_);
if (v_isSharedCheck_7026_ == 0)
{
lean_object* v_unused_7027_; 
v_unused_7027_ = lean_ctor_get(v_a_7003_, 0);
lean_dec(v_unused_7027_);
v___x_7008_ = v_a_7003_;
v_isShared_7009_ = v_isSharedCheck_7026_;
goto v_resetjp_7007_;
}
else
{
lean_inc(v_snd_7006_);
lean_dec(v_a_7003_);
v___x_7008_ = lean_box(0);
v_isShared_7009_ = v_isSharedCheck_7026_;
goto v_resetjp_7007_;
}
v_resetjp_7007_:
{
if (lean_obj_tag(v_cancelTk_x3f_6984_) == 1)
{
lean_object* v_val_7013_; uint8_t v___x_7014_; 
v_val_7013_ = lean_ctor_get(v_cancelTk_x3f_6984_, 0);
v___x_7014_ = l_IO_CancelToken_isSet(v_val_7013_);
if (v___x_7014_ == 0)
{
lean_del_object(v___x_7008_);
goto v___jp_7010_;
}
else
{
lean_object* v___x_7016_; uint8_t v_isShared_7017_; uint8_t v_isSharedCheck_7024_; 
lean_dec(v_fst_7005_);
lean_dec(v_fst_7004_);
lean_dec(v_r_6994_);
lean_dec(v_k_6991_);
lean_dec_ref(v_filterMapIdent_6983_);
v_isSharedCheck_7024_ = !lean_is_exclusive(v_cancelTk_x3f_6984_);
if (v_isSharedCheck_7024_ == 0)
{
lean_object* v_unused_7025_; 
v_unused_7025_ = lean_ctor_get(v_cancelTk_x3f_6984_, 0);
lean_dec(v_unused_7025_);
v___x_7016_ = v_cancelTk_x3f_6984_;
v_isShared_7017_ = v_isSharedCheck_7024_;
goto v_resetjp_7015_;
}
else
{
lean_dec(v_cancelTk_x3f_6984_);
v___x_7016_ = lean_box(0);
v_isShared_7017_ = v_isSharedCheck_7024_;
goto v_resetjp_7015_;
}
v_resetjp_7015_:
{
lean_object* v___x_7019_; 
lean_inc(v_snd_7006_);
if (v_isShared_7017_ == 0)
{
lean_ctor_set(v___x_7016_, 0, v_snd_7006_);
v___x_7019_ = v___x_7016_;
goto v_reusejp_7018_;
}
else
{
lean_object* v_reuseFailAlloc_7023_; 
v_reuseFailAlloc_7023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7023_, 0, v_snd_7006_);
v___x_7019_ = v_reuseFailAlloc_7023_;
goto v_reusejp_7018_;
}
v_reusejp_7018_:
{
lean_object* v___x_7021_; 
if (v_isShared_7009_ == 0)
{
lean_ctor_set(v___x_7008_, 0, v___x_7019_);
v___x_7021_ = v___x_7008_;
goto v_reusejp_7020_;
}
else
{
lean_object* v_reuseFailAlloc_7022_; 
v_reuseFailAlloc_7022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7022_, 0, v___x_7019_);
lean_ctor_set(v_reuseFailAlloc_7022_, 1, v_snd_7006_);
v___x_7021_ = v_reuseFailAlloc_7022_;
goto v_reusejp_7020_;
}
v_reusejp_7020_:
{
v_d_6989_ = v___x_7021_;
goto v___jp_6988_;
}
}
}
}
}
else
{
lean_del_object(v___x_7008_);
goto v___jp_7010_;
}
v___jp_7010_:
{
lean_object* v___x_7011_; lean_object* v_a_7012_; 
lean_inc_ref(v_filterMapIdent_6983_);
v___x_7011_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6983_, v_k_6991_, v_fst_7004_, v_snd_7006_, v_fst_7005_);
v_a_7012_ = lean_ctor_get(v___x_7011_, 0);
lean_inc(v_a_7012_);
lean_dec_ref(v___x_7011_);
v_val_6997_ = v_a_7012_;
goto v___jp_6996_;
}
}
}
v___jp_6996_:
{
lean_object* v___x_6998_; 
v___x_6998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6998_, 0, v___x_6995_);
lean_ctor_set(v___x_6998_, 1, v_val_6997_);
v_init_6985_ = v___x_6998_;
v_x_6986_ = v_r_6994_;
goto _start;
}
}
else
{
lean_object* v___x_7028_; 
lean_dec(v_cancelTk_x3f_6984_);
lean_dec_ref(v_filterMapIdent_6983_);
v___x_7028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7028_, 0, v_init_6985_);
return v___x_7028_;
}
v___jp_6988_:
{
lean_object* v___x_6990_; 
v___x_6990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6990_, 0, v_d_6989_);
return v___x_6990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_7029_, lean_object* v_cancelTk_x3f_7030_, lean_object* v_init_7031_, lean_object* v_x_7032_, lean_object* v___y_7033_){
_start:
{
lean_object* v_res_7034_; 
v_res_7034_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7029_, v_cancelTk_x3f_7030_, v_init_7031_, v_x_7032_);
return v_res_7034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_7040_, lean_object* v_filterMapIdent_7041_, lean_object* v_cancelTk_x3f_7042_){
_start:
{
lean_object* v_val_7045_; lean_object* v___x_7049_; lean_object* v___x_7050_; lean_object* v___x_7051_; lean_object* v_a_7052_; 
v___x_7049_ = l_Lean_Server_References_allRefs(v_self_7040_);
v___x_7050_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_7051_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7041_, v_cancelTk_x3f_7042_, v___x_7050_, v___x_7049_);
v_a_7052_ = lean_ctor_get(v___x_7051_, 0);
lean_inc(v_a_7052_);
lean_dec_ref(v___x_7051_);
v_val_7045_ = v_a_7052_;
goto v___jp_7044_;
v___jp_7044_:
{
lean_object* v_fst_7046_; 
v_fst_7046_ = lean_ctor_get(v_val_7045_, 0);
if (lean_obj_tag(v_fst_7046_) == 0)
{
lean_object* v_snd_7047_; 
v_snd_7047_ = lean_ctor_get(v_val_7045_, 1);
lean_inc(v_snd_7047_);
lean_dec_ref(v_val_7045_);
return v_snd_7047_;
}
else
{
lean_object* v_val_7048_; 
lean_inc_ref(v_fst_7046_);
lean_dec_ref(v_val_7045_);
v_val_7048_ = lean_ctor_get(v_fst_7046_, 0);
lean_inc(v_val_7048_);
lean_dec_ref_known(v_fst_7046_, 1);
return v_val_7048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_7053_, lean_object* v_filterMapIdent_7054_, lean_object* v_cancelTk_x3f_7055_, lean_object* v_a_7056_){
_start:
{
lean_object* v_res_7057_; 
v_res_7057_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7053_, v_filterMapIdent_7054_, v_cancelTk_x3f_7055_);
return v_res_7057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_7058_, lean_object* v_self_7059_, lean_object* v_filterMapIdent_7060_, lean_object* v_cancelTk_x3f_7061_){
_start:
{
lean_object* v___x_7063_; 
v___x_7063_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7059_, v_filterMapIdent_7060_, v_cancelTk_x3f_7061_);
return v___x_7063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_7064_, lean_object* v_self_7065_, lean_object* v_filterMapIdent_7066_, lean_object* v_cancelTk_x3f_7067_, lean_object* v_a_7068_){
_start:
{
lean_object* v_res_7069_; 
v_res_7069_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_7064_, v_self_7065_, v_filterMapIdent_7066_, v_cancelTk_x3f_7067_);
return v_res_7069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_7070_, lean_object* v_filterMapIdent_7071_, lean_object* v_a_7072_, lean_object* v_fst_7073_, lean_object* v_init_7074_, lean_object* v_x_7075_){
_start:
{
lean_object* v___x_7077_; 
v___x_7077_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_7071_, v_a_7072_, v_fst_7073_, v_init_7074_, v_x_7075_);
return v___x_7077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_7078_, lean_object* v_filterMapIdent_7079_, lean_object* v_a_7080_, lean_object* v_fst_7081_, lean_object* v_init_7082_, lean_object* v_x_7083_, lean_object* v___y_7084_){
_start:
{
lean_object* v_res_7085_; 
v_res_7085_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_7078_, v_filterMapIdent_7079_, v_a_7080_, v_fst_7081_, v_init_7082_, v_x_7083_);
return v_res_7085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_7086_, lean_object* v_filterMapIdent_7087_, lean_object* v_cancelTk_x3f_7088_, lean_object* v_init_7089_, lean_object* v_x_7090_){
_start:
{
lean_object* v___x_7092_; 
v___x_7092_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7087_, v_cancelTk_x3f_7088_, v_init_7089_, v_x_7090_);
return v___x_7092_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7093_, lean_object* v_filterMapIdent_7094_, lean_object* v_cancelTk_x3f_7095_, lean_object* v_init_7096_, lean_object* v_x_7097_, lean_object* v___y_7098_){
_start:
{
lean_object* v_res_7099_; 
v_res_7099_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7093_, v_filterMapIdent_7094_, v_cancelTk_x3f_7095_, v_init_7096_, v_x_7097_);
return v_res_7099_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7100_){
_start:
{
lean_object* v___x_7101_; lean_object* v___x_7102_; 
v___x_7101_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7102_ = lean_panic_fn_borrowed(v___x_7101_, v_msg_7100_);
return v___x_7102_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7106_; lean_object* v___x_7107_; lean_object* v___x_7108_; lean_object* v___x_7109_; lean_object* v___x_7110_; lean_object* v___x_7111_; 
v___x_7106_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7107_ = lean_unsigned_to_nat(14u);
v___x_7108_ = lean_unsigned_to_nat(22u);
v___x_7109_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7110_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7111_ = l_mkPanicMessageWithDecl(v___x_7110_, v___x_7109_, v___x_7108_, v___x_7107_, v___x_7106_);
return v___x_7111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7112_, lean_object* v_init_7113_, lean_object* v_x_7114_){
_start:
{
if (lean_obj_tag(v_x_7114_) == 0)
{
lean_object* v_k_7115_; lean_object* v_v_7116_; lean_object* v_l_7117_; lean_object* v_r_7118_; lean_object* v___x_7119_; lean_object* v_a_7120_; lean_object* v_fst_7121_; lean_object* v_snd_7122_; lean_object* v___y_7124_; lean_object* v_index_7139_; lean_object* v___x_7140_; 
v_k_7115_ = lean_ctor_get(v_x_7114_, 1);
v_v_7116_ = lean_ctor_get(v_x_7114_, 2);
v_l_7117_ = lean_ctor_get(v_x_7114_, 3);
v_r_7118_ = lean_ctor_get(v_x_7114_, 4);
v___x_7119_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7112_, v_init_7113_, v_l_7117_);
v_a_7120_ = lean_ctor_get(v___x_7119_, 0);
lean_inc(v_a_7120_);
lean_dec_ref(v___x_7119_);
v_fst_7121_ = lean_ctor_get(v_v_7116_, 0);
v_snd_7122_ = lean_ctor_get(v_v_7116_, 1);
v_index_7139_ = lean_ctor_get(v_snd_7122_, 1);
v___x_7140_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7139_, v_requestedMod_7112_);
if (lean_obj_tag(v___x_7140_) == 1)
{
lean_object* v_val_7141_; lean_object* v___x_7142_; 
v_val_7141_ = lean_ctor_get(v___x_7140_, 0);
lean_inc(v_val_7141_);
lean_dec_ref_known(v___x_7140_, 1);
v___x_7142_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7141_);
lean_dec(v_val_7141_);
if (lean_obj_tag(v___x_7142_) == 0)
{
lean_object* v___x_7143_; lean_object* v___x_7144_; 
v___x_7143_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7144_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7143_);
v___y_7124_ = v___x_7144_;
goto v___jp_7123_;
}
else
{
lean_object* v_val_7145_; 
v_val_7145_ = lean_ctor_get(v___x_7142_, 0);
lean_inc(v_val_7145_);
lean_dec_ref_known(v___x_7142_, 1);
v___y_7124_ = v_val_7145_;
goto v___jp_7123_;
}
}
else
{
lean_dec(v___x_7140_);
v_init_7113_ = v_a_7120_;
v_x_7114_ = v_r_7118_;
goto _start;
}
v___jp_7123_:
{
uint8_t v_isAll_7125_; uint8_t v_isPrivate_7126_; uint8_t v_metaKind_7127_; lean_object* v___x_7129_; uint8_t v_isShared_7130_; uint8_t v_isSharedCheck_7136_; 
v_isAll_7125_ = lean_ctor_get_uint8(v___y_7124_, sizeof(void*)*2);
v_isPrivate_7126_ = lean_ctor_get_uint8(v___y_7124_, sizeof(void*)*2 + 1);
v_metaKind_7127_ = lean_ctor_get_uint8(v___y_7124_, sizeof(void*)*2 + 2);
v_isSharedCheck_7136_ = !lean_is_exclusive(v___y_7124_);
if (v_isSharedCheck_7136_ == 0)
{
lean_object* v_unused_7137_; lean_object* v_unused_7138_; 
v_unused_7137_ = lean_ctor_get(v___y_7124_, 1);
lean_dec(v_unused_7137_);
v_unused_7138_ = lean_ctor_get(v___y_7124_, 0);
lean_dec(v_unused_7138_);
v___x_7129_ = v___y_7124_;
v_isShared_7130_ = v_isSharedCheck_7136_;
goto v_resetjp_7128_;
}
else
{
lean_dec(v___y_7124_);
v___x_7129_ = lean_box(0);
v_isShared_7130_ = v_isSharedCheck_7136_;
goto v_resetjp_7128_;
}
v_resetjp_7128_:
{
lean_object* v___x_7132_; 
lean_inc(v_fst_7121_);
lean_inc(v_k_7115_);
if (v_isShared_7130_ == 0)
{
lean_ctor_set(v___x_7129_, 1, v_fst_7121_);
lean_ctor_set(v___x_7129_, 0, v_k_7115_);
v___x_7132_ = v___x_7129_;
goto v_reusejp_7131_;
}
else
{
lean_object* v_reuseFailAlloc_7135_; 
v_reuseFailAlloc_7135_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7135_, 0, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7135_, 1, v_fst_7121_);
lean_ctor_set_uint8(v_reuseFailAlloc_7135_, sizeof(void*)*2, v_isAll_7125_);
lean_ctor_set_uint8(v_reuseFailAlloc_7135_, sizeof(void*)*2 + 1, v_isPrivate_7126_);
lean_ctor_set_uint8(v_reuseFailAlloc_7135_, sizeof(void*)*2 + 2, v_metaKind_7127_);
v___x_7132_ = v_reuseFailAlloc_7135_;
goto v_reusejp_7131_;
}
v_reusejp_7131_:
{
lean_object* v___x_7133_; 
v___x_7133_ = lean_array_push(v_a_7120_, v___x_7132_);
v_init_7113_ = v___x_7133_;
v_x_7114_ = v_r_7118_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7147_; 
v___x_7147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7147_, 0, v_init_7113_);
return v___x_7147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object* v_requestedMod_7148_, lean_object* v_init_7149_, lean_object* v_x_7150_){
_start:
{
lean_object* v_res_7151_; 
v_res_7151_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7148_, v_init_7149_, v_x_7150_);
lean_dec(v_x_7150_);
lean_dec(v_requestedMod_7148_);
return v_res_7151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object* v_self_7152_, lean_object* v_requestedMod_7153_){
_start:
{
lean_object* v_result_7154_; lean_object* v___x_7155_; lean_object* v___x_7156_; lean_object* v_a_7157_; 
v_result_7154_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_7155_ = l_Lean_Server_References_allDirectImports(v_self_7152_);
v___x_7156_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7153_, v_result_7154_, v___x_7155_);
lean_dec(v___x_7155_);
v_a_7157_ = lean_ctor_get(v___x_7156_, 0);
lean_inc(v_a_7157_);
lean_dec_ref(v___x_7156_);
return v_a_7157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object* v_self_7158_, lean_object* v_requestedMod_7159_){
_start:
{
lean_object* v_res_7160_; 
v_res_7160_ = l_Lean_Server_References_importedBy(v_self_7158_, v_requestedMod_7159_);
lean_dec(v_requestedMod_7159_);
return v_res_7160_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Internal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Import(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_References(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Lsp_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_References(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* initialize_Lean_Elab_Import(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_References(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_References(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_References(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_References(builtin);
}
#ifdef __cplusplus
}
#endif

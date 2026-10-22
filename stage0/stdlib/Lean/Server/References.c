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
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
v___x_117_ = lean_nat_add(v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec(v___y_115_);
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
lean_ctor_set(v___x_97_, 3, v___y_114_);
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
lean_ctor_set(v_reuseFailAlloc_122_, 3, v___y_114_);
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
v___y_114_ = v___x_129_;
v___y_115_ = v___x_130_;
v___y_116_ = v_size_131_;
goto v___jp_113_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___y_114_ = v___x_129_;
v___y_115_ = v___x_130_;
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
v___x_257_ = lean_nat_add(v___y_254_, v___y_256_);
lean_dec(v___y_256_);
lean_dec(v___y_254_);
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
lean_ctor_set(v___x_237_, 3, v___y_255_);
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
lean_ctor_set(v_reuseFailAlloc_262_, 3, v___y_255_);
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
v___y_254_ = v___x_269_;
v___y_255_ = v___x_268_;
v___y_256_ = v_size_270_;
goto v___jp_253_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_unsigned_to_nat(0u);
v___y_254_ = v___x_269_;
v___y_255_ = v___x_268_;
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
lean_object* v_v_365_; lean_object* v_ci_366_; lean_object* v_range_367_; lean_object* v_toCommandContextInfo_368_; lean_object* v_parentDecl_x3f_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_bs_x27_372_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_388_; 
v_v_365_ = lean_array_uget_borrowed(v_bs_360_, v_i_359_);
v_ci_366_ = lean_ctor_get(v_v_365_, 4);
v_range_367_ = lean_ctor_get(v_v_365_, 2);
lean_inc_ref(v_range_367_);
v_toCommandContextInfo_368_ = lean_ctor_get(v_ci_366_, 0);
lean_inc_ref(v_toCommandContextInfo_368_);
v_parentDecl_x3f_369_ = lean_ctor_get(v_ci_366_, 1);
lean_inc(v_parentDecl_x3f_369_);
v___x_370_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_371_ = lean_unsigned_to_nat(0u);
v_bs_x27_372_ = lean_array_uset(v_bs_360_, v_i_359_, v___x_371_);
if (lean_obj_tag(v_parentDecl_x3f_369_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
v___y_388_ = v___x_408_;
goto v___jp_387_;
}
else
{
lean_object* v_val_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_val_409_ = lean_ctor_get(v_parentDecl_x3f_369_, 0);
lean_inc(v_val_409_);
v___x_410_ = l_Lean_Name_toString(v_val_409_, v___x_363_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
v___y_388_ = v___x_411_;
goto v___jp_387_;
}
v___jp_373_:
{
lean_object* v___x_376_; size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; 
v___x_376_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_367_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v_range_367_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_359_, v___x_377_);
v___x_379_ = lean_array_uset(v_bs_x27_372_, v_i_359_, v___x_376_);
v_i_359_ = v___x_378_;
v_bs_360_ = v___x_379_;
v___y_361_ = v___y_375_;
goto _start;
}
v___jp_381_:
{
if (lean_obj_tag(v___y_382_) == 1)
{
if (lean_obj_tag(v___y_383_) == 1)
{
lean_object* v_val_384_; lean_object* v_val_385_; lean_object* v___x_386_; 
v_val_384_ = lean_ctor_get(v___y_382_, 0);
v_val_385_ = lean_ctor_get(v___y_383_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v___y_383_, 1);
lean_inc(v_val_384_);
v___x_386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_val_384_, v_val_385_, v___y_361_);
v___y_374_ = v___y_382_;
v___y_375_ = v___x_386_;
goto v___jp_373_;
}
else
{
lean_dec(v___y_383_);
v___y_374_ = v___y_382_;
v___y_375_ = v___y_361_;
goto v___jp_373_;
}
}
else
{
lean_dec(v___y_383_);
v___y_374_ = v___y_382_;
v___y_375_ = v___y_361_;
goto v___jp_373_;
}
}
v___jp_387_:
{
lean_object* v_cmdEnv_x3f_389_; 
v_cmdEnv_x3f_389_ = lean_ctor_get(v_toCommandContextInfo_368_, 1);
lean_inc(v_cmdEnv_x3f_389_);
lean_dec_ref(v_toCommandContextInfo_368_);
if (lean_obj_tag(v_cmdEnv_x3f_389_) == 0)
{
lean_object* v___x_390_; 
lean_dec(v_parentDecl_x3f_369_);
v___x_390_ = lean_box(0);
v___y_382_ = v___y_388_;
v___y_383_ = v___x_390_;
goto v___jp_381_;
}
else
{
if (lean_obj_tag(v_parentDecl_x3f_369_) == 0)
{
lean_object* v___x_391_; 
lean_dec_ref_known(v_cmdEnv_x3f_389_, 1);
v___x_391_ = lean_box(0);
v___y_382_ = v___y_388_;
v___y_383_ = v___x_391_;
goto v___jp_381_;
}
else
{
lean_object* v_val_392_; lean_object* v_val_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; 
v_val_392_ = lean_ctor_get(v_cmdEnv_x3f_389_, 0);
lean_inc(v_val_392_);
lean_dec_ref_known(v_cmdEnv_x3f_389_, 1);
v_val_393_ = lean_ctor_get(v_parentDecl_x3f_369_, 0);
lean_inc(v_val_393_);
lean_dec_ref_known(v_parentDecl_x3f_369_, 1);
v___x_394_ = l_Lean_declRangeExt;
v___x_395_ = lean_box(1);
v___x_396_ = 0;
v___x_397_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_370_, v___x_394_, v_val_392_, v_val_393_, v___x_395_, v___x_396_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_box(0);
v___y_382_ = v___y_388_;
v___y_383_ = v___x_398_;
goto v___jp_381_;
}
else
{
lean_object* v_val_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_407_; 
v_val_399_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_407_ == 0)
{
v___x_401_ = v___x_397_;
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_val_399_);
lean_dec(v___x_397_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_val_399_);
lean_dec(v_val_399_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_403_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
v___y_382_ = v___y_388_;
v___y_383_ = v___x_405_;
goto v___jp_381_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1___boxed(lean_object* v_sz_412_, lean_object* v_i_413_, lean_object* v_bs_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
size_t v_sz_boxed_417_; size_t v_i_boxed_418_; lean_object* v_res_419_; 
v_sz_boxed_417_ = lean_unbox_usize(v_sz_412_);
lean_dec(v_sz_412_);
v_i_boxed_418_ = lean_unbox_usize(v_i_413_);
lean_dec(v_i_413_);
v_res_419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1(v_sz_boxed_417_, v_i_boxed_418_, v_bs_414_, v___y_415_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_toLspRefInfo(lean_object* v_i_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_definition_423_; lean_object* v_usages_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_496_; 
v_definition_423_ = lean_ctor_get(v_i_420_, 0);
v_usages_424_ = lean_ctor_get(v_i_420_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_i_420_);
if (v_isSharedCheck_496_ == 0)
{
v___x_426_ = v_i_420_;
v_isShared_427_ = v_isSharedCheck_496_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_usages_424_);
lean_inc(v_definition_423_);
lean_dec(v_i_420_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_496_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_fst_429_; lean_object* v_snd_430_; 
if (lean_obj_tag(v_definition_423_) == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_box(0);
v_fst_429_ = v___x_446_;
v_snd_430_ = v_a_421_;
goto v___jp_428_;
}
else
{
lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_495_; 
v_val_447_ = lean_ctor_get(v_definition_423_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_definition_423_);
if (v_isSharedCheck_495_ == 0)
{
v___x_449_ = v_definition_423_;
v_isShared_450_ = v_isSharedCheck_495_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_dec(v_definition_423_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_495_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_range_451_; lean_object* v_ci_452_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v_toCommandContextInfo_466_; lean_object* v_parentDecl_x3f_467_; lean_object* v___x_468_; lean_object* v___y_470_; 
v_range_451_ = lean_ctor_get(v_val_447_, 2);
lean_inc_ref(v_range_451_);
v_ci_452_ = lean_ctor_get(v_val_447_, 4);
lean_inc_ref(v_ci_452_);
lean_dec(v_val_447_);
v_toCommandContextInfo_466_ = lean_ctor_get(v_ci_452_, 0);
lean_inc_ref(v_toCommandContextInfo_466_);
v_parentDecl_x3f_467_ = lean_ctor_get(v_ci_452_, 1);
lean_inc(v_parentDecl_x3f_467_);
lean_dec_ref(v_ci_452_);
v___x_468_ = l_Lean_instInhabitedDeclarationRanges_default;
if (lean_obj_tag(v_parentDecl_x3f_467_) == 0)
{
lean_object* v___x_490_; 
v___x_490_ = lean_box(0);
v___y_470_ = v___x_490_;
goto v___jp_469_;
}
else
{
lean_object* v_val_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_val_491_ = lean_ctor_get(v_parentDecl_x3f_467_, 0);
v___x_492_ = 1;
lean_inc(v_val_491_);
v___x_493_ = l_Lean_Name_toString(v_val_491_, v___x_492_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
v___y_470_ = v___x_494_;
goto v___jp_469_;
}
v___jp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_451_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v_range_451_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_456_);
v___x_458_ = v___x_449_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
v_fst_429_ = v___x_458_;
v_snd_430_ = v___y_455_;
goto v___jp_428_;
}
}
v___jp_460_:
{
if (lean_obj_tag(v___y_461_) == 1)
{
if (lean_obj_tag(v___y_462_) == 1)
{
lean_object* v_val_463_; lean_object* v_val_464_; lean_object* v___x_465_; 
v_val_463_ = lean_ctor_get(v___y_461_, 0);
v_val_464_ = lean_ctor_get(v___y_462_, 0);
lean_inc(v_val_464_);
lean_dec_ref_known(v___y_462_, 1);
lean_inc(v_val_463_);
v___x_465_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_val_463_, v_val_464_, v_a_421_);
v___y_454_ = v___y_461_;
v___y_455_ = v___x_465_;
goto v___jp_453_;
}
else
{
lean_dec(v___y_462_);
v___y_454_ = v___y_461_;
v___y_455_ = v_a_421_;
goto v___jp_453_;
}
}
else
{
lean_dec(v___y_462_);
v___y_454_ = v___y_461_;
v___y_455_ = v_a_421_;
goto v___jp_453_;
}
}
v___jp_469_:
{
lean_object* v_cmdEnv_x3f_471_; 
v_cmdEnv_x3f_471_ = lean_ctor_get(v_toCommandContextInfo_466_, 1);
lean_inc(v_cmdEnv_x3f_471_);
lean_dec_ref(v_toCommandContextInfo_466_);
if (lean_obj_tag(v_cmdEnv_x3f_471_) == 0)
{
lean_object* v___x_472_; 
lean_dec(v_parentDecl_x3f_467_);
v___x_472_ = lean_box(0);
v___y_461_ = v___y_470_;
v___y_462_ = v___x_472_;
goto v___jp_460_;
}
else
{
if (lean_obj_tag(v_parentDecl_x3f_467_) == 0)
{
lean_object* v___x_473_; 
lean_dec_ref_known(v_cmdEnv_x3f_471_, 1);
v___x_473_ = lean_box(0);
v___y_461_ = v___y_470_;
v___y_462_ = v___x_473_;
goto v___jp_460_;
}
else
{
lean_object* v_val_474_; lean_object* v_val_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; 
v_val_474_ = lean_ctor_get(v_cmdEnv_x3f_471_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v_cmdEnv_x3f_471_, 1);
v_val_475_ = lean_ctor_get(v_parentDecl_x3f_467_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v_parentDecl_x3f_467_, 1);
v___x_476_ = l_Lean_declRangeExt;
v___x_477_ = lean_box(1);
v___x_478_ = 0;
v___x_479_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_468_, v___x_476_, v_val_474_, v_val_475_, v___x_477_, v___x_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_box(0);
v___y_461_ = v___y_470_;
v___y_462_ = v___x_480_;
goto v___jp_460_;
}
else
{
lean_object* v_val_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_val_481_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_489_ == 0)
{
v___x_483_ = v___x_479_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_val_481_);
lean_dec(v___x_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_val_481_);
lean_dec(v_val_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v___y_461_ = v___y_470_;
v___y_462_ = v___x_487_;
goto v___jp_460_;
}
}
}
}
}
}
}
}
v___jp_428_:
{
size_t v_sz_431_; size_t v___x_432_; lean_object* v___x_433_; lean_object* v_fst_434_; lean_object* v_snd_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_445_; 
v_sz_431_ = lean_array_size(v_usages_424_);
v___x_432_ = ((size_t)0ULL);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1(v_sz_431_, v___x_432_, v_usages_424_, v_snd_430_);
v_fst_434_ = lean_ctor_get(v___x_433_, 0);
v_snd_435_ = lean_ctor_get(v___x_433_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_445_ == 0)
{
v___x_437_ = v___x_433_;
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_snd_435_);
lean_inc(v_fst_434_);
lean_dec(v___x_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_fst_434_);
lean_ctor_set(v___x_426_, 0, v_fst_429_);
v___x_440_ = v___x_426_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fst_429_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_fst_434_);
v___x_440_ = v_reuseFailAlloc_444_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_442_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_440_);
v___x_442_ = v___x_437_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_snd_435_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_toLspRefInfo___boxed(lean_object* v_i_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Server_RefInfo_toLspRefInfo(v_i_497_, v_a_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0(lean_object* v_00_u03b2_501_, lean_object* v_k_502_, lean_object* v_v_503_, lean_object* v_t_504_, lean_object* v_hl_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_502_, v_v_503_, v_t_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(lean_object* v_ref_507_, lean_object* v_x_508_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((lean_object*)(l_Lean_Server_RefInfo_empty));
v___x_510_ = l_Lean_Server_RefInfo_addRef(v___x_509_, v_ref_507_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_val_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_520_; 
v_val_512_ = lean_ctor_get(v_x_508_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_508_);
if (v_isSharedCheck_520_ == 0)
{
v___x_514_ = v_x_508_;
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_val_512_);
lean_dec(v_x_508_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = l_Lean_Server_RefInfo_addRef(v_val_512_, v_ref_507_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(lean_object* v_ref_521_, lean_object* v_k_522_, lean_object* v_t_523_){
_start:
{
if (lean_obj_tag(v_t_523_) == 0)
{
lean_object* v_size_524_; lean_object* v_k_525_; lean_object* v_v_526_; lean_object* v_l_527_; lean_object* v_r_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_543_; 
v_size_524_ = lean_ctor_get(v_t_523_, 0);
v_k_525_ = lean_ctor_get(v_t_523_, 1);
v_v_526_ = lean_ctor_get(v_t_523_, 2);
v_l_527_ = lean_ctor_get(v_t_523_, 3);
v_r_528_ = lean_ctor_get(v_t_523_, 4);
v_isSharedCheck_543_ = !lean_is_exclusive(v_t_523_);
if (v_isSharedCheck_543_ == 0)
{
v___x_530_ = v_t_523_;
v_isShared_531_ = v_isSharedCheck_543_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_r_528_);
lean_inc(v_l_527_);
lean_inc(v_v_526_);
lean_inc(v_k_525_);
lean_inc(v_size_524_);
lean_dec(v_t_523_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_543_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
uint8_t v___x_532_; 
v___x_532_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_522_, v_k_525_);
switch(v___x_532_)
{
case 0:
{
lean_object* v_impl_533_; lean_object* v___x_534_; 
lean_del_object(v___x_530_);
lean_dec(v_size_524_);
v_impl_533_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_521_, v_k_522_, v_l_527_);
v___x_534_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_525_, v_v_526_, v_impl_533_, v_r_528_);
return v___x_534_;
}
case 1:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_val_537_; lean_object* v___x_539_; 
lean_dec(v_k_525_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v_v_526_);
v___x_536_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(v_ref_521_, v___x_535_);
v_val_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_val_537_);
lean_dec(v___x_536_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 2, v_val_537_);
lean_ctor_set(v___x_530_, 1, v_k_522_);
v___x_539_ = v___x_530_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_size_524_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_k_522_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_val_537_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v_l_527_);
lean_ctor_set(v_reuseFailAlloc_540_, 4, v_r_528_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
default: 
{
lean_object* v_impl_541_; lean_object* v___x_542_; 
lean_del_object(v___x_530_);
lean_dec(v_size_524_);
v_impl_541_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_521_, v_k_522_, v_r_528_);
v___x_542_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_525_, v_v_526_, v_l_527_, v_impl_541_);
return v___x_542_;
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_val_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_544_ = lean_box(0);
v___x_545_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(v_ref_521_, v___x_544_);
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec(v___x_545_);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_k_522_);
lean_ctor_set(v___x_548_, 2, v_val_546_);
lean_ctor_set(v___x_548_, 3, v_t_523_);
lean_ctor_set(v___x_548_, 4, v_t_523_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_addRef(lean_object* v_self_549_, lean_object* v_ref_550_){
_start:
{
lean_object* v_ident_551_; lean_object* v___x_552_; 
v_ident_551_ = lean_ctor_get(v_ref_550_, 0);
lean_inc_ref(v_ident_551_);
v___x_552_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_550_, v_ident_551_, v_self_549_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0(lean_object* v_ref_553_, lean_object* v_k_554_, lean_object* v_t_555_, lean_object* v_hl_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_553_, v_k_554_, v_t_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(lean_object* v_k_558_, lean_object* v_v_559_, lean_object* v_t_560_){
_start:
{
if (lean_obj_tag(v_t_560_) == 0)
{
lean_object* v_size_561_; lean_object* v_k_562_; lean_object* v_v_563_; lean_object* v_l_564_; lean_object* v_r_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_845_; 
v_size_561_ = lean_ctor_get(v_t_560_, 0);
v_k_562_ = lean_ctor_get(v_t_560_, 1);
v_v_563_ = lean_ctor_get(v_t_560_, 2);
v_l_564_ = lean_ctor_get(v_t_560_, 3);
v_r_565_ = lean_ctor_get(v_t_560_, 4);
v_isSharedCheck_845_ = !lean_is_exclusive(v_t_560_);
if (v_isSharedCheck_845_ == 0)
{
v___x_567_ = v_t_560_;
v_isShared_568_ = v_isSharedCheck_845_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_r_565_);
lean_inc(v_l_564_);
lean_inc(v_v_563_);
lean_inc(v_k_562_);
lean_inc(v_size_561_);
lean_dec(v_t_560_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_845_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
uint8_t v___x_569_; 
v___x_569_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_558_, v_k_562_);
switch(v___x_569_)
{
case 0:
{
lean_object* v_impl_570_; lean_object* v___x_571_; 
lean_dec(v_size_561_);
v_impl_570_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_558_, v_v_559_, v_l_564_);
v___x_571_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_565_) == 0)
{
lean_object* v_size_572_; lean_object* v_size_573_; lean_object* v_k_574_; lean_object* v_v_575_; lean_object* v_l_576_; lean_object* v_r_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_size_572_ = lean_ctor_get(v_r_565_, 0);
v_size_573_ = lean_ctor_get(v_impl_570_, 0);
v_k_574_ = lean_ctor_get(v_impl_570_, 1);
v_v_575_ = lean_ctor_get(v_impl_570_, 2);
v_l_576_ = lean_ctor_get(v_impl_570_, 3);
v_r_577_ = lean_ctor_get(v_impl_570_, 4);
lean_inc(v_r_577_);
v___x_578_ = lean_unsigned_to_nat(3u);
v___x_579_ = lean_nat_mul(v___x_578_, v_size_572_);
v___x_580_ = lean_nat_dec_lt(v___x_579_, v_size_573_);
lean_dec(v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
lean_dec(v_r_577_);
v___x_581_ = lean_nat_add(v___x_571_, v_size_573_);
v___x_582_ = lean_nat_add(v___x_581_, v_size_572_);
lean_dec(v___x_581_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 3, v_impl_570_);
lean_ctor_set(v___x_567_, 0, v___x_582_);
v___x_584_ = v___x_567_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_impl_570_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_r_565_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
else
{
lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_651_; 
lean_inc(v_l_576_);
lean_inc(v_v_575_);
lean_inc(v_k_574_);
lean_inc(v_size_573_);
v_isSharedCheck_651_ = !lean_is_exclusive(v_impl_570_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; 
v_unused_652_ = lean_ctor_get(v_impl_570_, 4);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v_impl_570_, 3);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_impl_570_, 2);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_impl_570_, 1);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_impl_570_, 0);
lean_dec(v_unused_656_);
v___x_587_ = v_impl_570_;
v_isShared_588_ = v_isSharedCheck_651_;
goto v_resetjp_586_;
}
else
{
lean_dec(v_impl_570_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_651_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_size_589_; lean_object* v_size_590_; lean_object* v_k_591_; lean_object* v_v_592_; lean_object* v_l_593_; lean_object* v_r_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_size_589_ = lean_ctor_get(v_l_576_, 0);
v_size_590_ = lean_ctor_get(v_r_577_, 0);
v_k_591_ = lean_ctor_get(v_r_577_, 1);
v_v_592_ = lean_ctor_get(v_r_577_, 2);
v_l_593_ = lean_ctor_get(v_r_577_, 3);
v_r_594_ = lean_ctor_get(v_r_577_, 4);
v___x_595_ = lean_unsigned_to_nat(2u);
v___x_596_ = lean_nat_mul(v___x_595_, v_size_589_);
v___x_597_ = lean_nat_dec_lt(v_size_590_, v___x_596_);
lean_dec(v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_626_; 
lean_inc(v_r_594_);
lean_inc(v_l_593_);
lean_inc(v_v_592_);
lean_inc(v_k_591_);
v_isSharedCheck_626_ = !lean_is_exclusive(v_r_577_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; lean_object* v_unused_628_; lean_object* v_unused_629_; lean_object* v_unused_630_; lean_object* v_unused_631_; 
v_unused_627_ = lean_ctor_get(v_r_577_, 4);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_r_577_, 3);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_r_577_, 2);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_r_577_, 1);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_r_577_, 0);
lean_dec(v_unused_631_);
v___x_599_ = v_r_577_;
v_isShared_600_ = v_isSharedCheck_626_;
goto v_resetjp_598_;
}
else
{
lean_dec(v_r_577_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_626_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___x_614_; lean_object* v___y_616_; 
v___x_601_ = lean_nat_add(v___x_571_, v_size_573_);
lean_dec(v_size_573_);
v___x_602_ = lean_nat_add(v___x_601_, v_size_572_);
lean_dec(v___x_601_);
v___x_614_ = lean_nat_add(v___x_571_, v_size_589_);
if (lean_obj_tag(v_l_593_) == 0)
{
lean_object* v_size_624_; 
v_size_624_ = lean_ctor_get(v_l_593_, 0);
lean_inc(v_size_624_);
v___y_616_ = v_size_624_;
goto v___jp_615_;
}
else
{
lean_object* v___x_625_; 
v___x_625_ = lean_unsigned_to_nat(0u);
v___y_616_ = v___x_625_;
goto v___jp_615_;
}
v___jp_603_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = lean_nat_add(v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec(v___y_605_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 4, v_r_565_);
lean_ctor_set(v___x_599_, 3, v_r_594_);
lean_ctor_set(v___x_599_, 2, v_v_563_);
lean_ctor_set(v___x_599_, 1, v_k_562_);
lean_ctor_set(v___x_599_, 0, v___x_607_);
v___x_609_ = v___x_599_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_r_594_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_r_565_);
v___x_609_ = v_reuseFailAlloc_613_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 4, v___x_609_);
lean_ctor_set(v___x_587_, 3, v___y_604_);
lean_ctor_set(v___x_587_, 2, v_v_592_);
lean_ctor_set(v___x_587_, 1, v_k_591_);
lean_ctor_set(v___x_587_, 0, v___x_602_);
v___x_611_ = v___x_587_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_591_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_592_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v___y_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
v___jp_615_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_nat_add(v___x_614_, v___y_616_);
lean_dec(v___y_616_);
lean_dec(v___x_614_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v_l_593_);
lean_ctor_set(v___x_567_, 3, v_l_576_);
lean_ctor_set(v___x_567_, 2, v_v_575_);
lean_ctor_set(v___x_567_, 1, v_k_574_);
lean_ctor_set(v___x_567_, 0, v___x_617_);
v___x_619_ = v___x_567_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_k_574_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_v_575_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_l_576_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_l_593_);
v___x_619_ = v_reuseFailAlloc_623_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; 
v___x_620_ = lean_nat_add(v___x_571_, v_size_572_);
if (lean_obj_tag(v_r_594_) == 0)
{
lean_object* v_size_621_; 
v_size_621_ = lean_ctor_get(v_r_594_, 0);
lean_inc(v_size_621_);
v___y_604_ = v___x_619_;
v___y_605_ = v___x_620_;
v___y_606_ = v_size_621_;
goto v___jp_603_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___y_604_ = v___x_619_;
v___y_605_ = v___x_620_;
v___y_606_ = v___x_622_;
goto v___jp_603_;
}
}
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_del_object(v___x_567_);
v___x_632_ = lean_nat_add(v___x_571_, v_size_573_);
lean_dec(v_size_573_);
v___x_633_ = lean_nat_add(v___x_632_, v_size_572_);
lean_dec(v___x_632_);
v___x_634_ = lean_nat_add(v___x_571_, v_size_572_);
v___x_635_ = lean_nat_add(v___x_634_, v_size_590_);
lean_dec(v___x_634_);
lean_inc_ref(v_r_565_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 4, v_r_565_);
lean_ctor_set(v___x_587_, 3, v_r_577_);
lean_ctor_set(v___x_587_, 2, v_v_563_);
lean_ctor_set(v___x_587_, 1, v_k_562_);
lean_ctor_set(v___x_587_, 0, v___x_635_);
v___x_637_ = v___x_587_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_r_577_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_r_565_);
v___x_637_ = v_reuseFailAlloc_650_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_isSharedCheck_644_ = !lean_is_exclusive(v_r_565_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; lean_object* v_unused_649_; 
v_unused_645_ = lean_ctor_get(v_r_565_, 4);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_r_565_, 3);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_r_565_, 2);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_r_565_, 1);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v_r_565_, 0);
lean_dec(v_unused_649_);
v___x_639_ = v_r_565_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_dec(v_r_565_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 4, v___x_637_);
lean_ctor_set(v___x_639_, 3, v_l_576_);
lean_ctor_set(v___x_639_, 2, v_v_575_);
lean_ctor_set(v___x_639_, 1, v_k_574_);
lean_ctor_set(v___x_639_, 0, v___x_633_);
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_k_574_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_v_575_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_l_576_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v___x_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_657_; 
v_l_657_ = lean_ctor_get(v_impl_570_, 3);
if (lean_obj_tag(v_l_657_) == 0)
{
lean_object* v_r_658_; lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_671_; 
lean_inc_ref(v_l_657_);
v_r_658_ = lean_ctor_get(v_impl_570_, 4);
v_k_659_ = lean_ctor_get(v_impl_570_, 1);
v_v_660_ = lean_ctor_get(v_impl_570_, 2);
v_isSharedCheck_671_ = !lean_is_exclusive(v_impl_570_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; lean_object* v_unused_673_; 
v_unused_672_ = lean_ctor_get(v_impl_570_, 3);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v_impl_570_, 0);
lean_dec(v_unused_673_);
v___x_662_ = v_impl_570_;
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_r_658_);
lean_inc(v_v_660_);
lean_inc(v_k_659_);
lean_dec(v_impl_570_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_671_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_658_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 3, v_r_658_);
lean_ctor_set(v___x_662_, 2, v_v_563_);
lean_ctor_set(v___x_662_, 1, v_k_562_);
lean_ctor_set(v___x_662_, 0, v___x_571_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v_r_658_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v_r_658_);
v___x_666_ = v_reuseFailAlloc_670_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_668_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v___x_666_);
lean_ctor_set(v___x_567_, 3, v_l_657_);
lean_ctor_set(v___x_567_, 2, v_v_660_);
lean_ctor_set(v___x_567_, 1, v_k_659_);
lean_ctor_set(v___x_567_, 0, v___x_664_);
v___x_668_ = v___x_567_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_l_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v_r_674_; 
v_r_674_ = lean_ctor_get(v_impl_570_, 4);
lean_inc(v_r_674_);
if (lean_obj_tag(v_r_674_) == 0)
{
lean_object* v_k_675_; lean_object* v_v_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_699_; 
lean_inc(v_l_657_);
v_k_675_ = lean_ctor_get(v_impl_570_, 1);
v_v_676_ = lean_ctor_get(v_impl_570_, 2);
v_isSharedCheck_699_ = !lean_is_exclusive(v_impl_570_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; lean_object* v_unused_701_; lean_object* v_unused_702_; 
v_unused_700_ = lean_ctor_get(v_impl_570_, 4);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_impl_570_, 3);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_impl_570_, 0);
lean_dec(v_unused_702_);
v___x_678_ = v_impl_570_;
v_isShared_679_ = v_isSharedCheck_699_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_v_676_);
lean_inc(v_k_675_);
lean_dec(v_impl_570_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_699_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_k_680_; lean_object* v_v_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_695_; 
v_k_680_ = lean_ctor_get(v_r_674_, 1);
v_v_681_ = lean_ctor_get(v_r_674_, 2);
v_isSharedCheck_695_ = !lean_is_exclusive(v_r_674_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; 
v_unused_696_ = lean_ctor_get(v_r_674_, 4);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_r_674_, 3);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_r_674_, 0);
lean_dec(v_unused_698_);
v___x_683_ = v_r_674_;
v_isShared_684_ = v_isSharedCheck_695_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_v_681_);
lean_inc(v_k_680_);
lean_dec(v_r_674_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_695_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = lean_unsigned_to_nat(3u);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 4, v_l_657_);
lean_ctor_set(v___x_683_, 3, v_l_657_);
lean_ctor_set(v___x_683_, 2, v_v_676_);
lean_ctor_set(v___x_683_, 1, v_k_675_);
lean_ctor_set(v___x_683_, 0, v___x_571_);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_k_675_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_v_676_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_l_657_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_l_657_);
v___x_687_ = v_reuseFailAlloc_694_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v_l_657_);
lean_ctor_set(v___x_678_, 2, v_v_563_);
lean_ctor_set(v___x_678_, 1, v_k_562_);
lean_ctor_set(v___x_678_, 0, v___x_571_);
v___x_689_ = v___x_678_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_l_657_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_l_657_);
v___x_689_ = v_reuseFailAlloc_693_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v___x_689_);
lean_ctor_set(v___x_567_, 3, v___x_687_);
lean_ctor_set(v___x_567_, 2, v_v_681_);
lean_ctor_set(v___x_567_, 1, v_k_680_);
lean_ctor_set(v___x_567_, 0, v___x_685_);
v___x_691_ = v___x_567_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_680_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_681_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_unsigned_to_nat(2u);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v_r_674_);
lean_ctor_set(v___x_567_, 3, v_impl_570_);
lean_ctor_set(v___x_567_, 0, v___x_703_);
v___x_705_ = v___x_567_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_impl_570_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v_r_674_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
case 1:
{
lean_object* v___x_708_; 
lean_dec(v_v_563_);
lean_dec(v_k_562_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 2, v_v_559_);
lean_ctor_set(v___x_567_, 1, v_k_558_);
v___x_708_ = v___x_567_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_size_561_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_k_558_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_v_559_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_l_564_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_r_565_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
default: 
{
lean_object* v_impl_710_; lean_object* v___x_711_; 
lean_dec(v_size_561_);
v_impl_710_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_558_, v_v_559_, v_r_565_);
v___x_711_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_564_) == 0)
{
lean_object* v_size_712_; lean_object* v_size_713_; lean_object* v_k_714_; lean_object* v_v_715_; lean_object* v_l_716_; lean_object* v_r_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_size_712_ = lean_ctor_get(v_l_564_, 0);
v_size_713_ = lean_ctor_get(v_impl_710_, 0);
v_k_714_ = lean_ctor_get(v_impl_710_, 1);
v_v_715_ = lean_ctor_get(v_impl_710_, 2);
v_l_716_ = lean_ctor_get(v_impl_710_, 3);
lean_inc(v_l_716_);
v_r_717_ = lean_ctor_get(v_impl_710_, 4);
v___x_718_ = lean_unsigned_to_nat(3u);
v___x_719_ = lean_nat_mul(v___x_718_, v_size_712_);
v___x_720_ = lean_nat_dec_lt(v___x_719_, v_size_713_);
lean_dec(v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
lean_dec(v_l_716_);
v___x_721_ = lean_nat_add(v___x_711_, v_size_712_);
v___x_722_ = lean_nat_add(v___x_721_, v_size_713_);
lean_dec(v___x_721_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v_impl_710_);
lean_ctor_set(v___x_567_, 0, v___x_722_);
v___x_724_ = v___x_567_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_l_564_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_impl_710_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
else
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_789_; 
lean_inc(v_r_717_);
lean_inc(v_v_715_);
lean_inc(v_k_714_);
lean_inc(v_size_713_);
v_isSharedCheck_789_ = !lean_is_exclusive(v_impl_710_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; lean_object* v_unused_791_; lean_object* v_unused_792_; lean_object* v_unused_793_; lean_object* v_unused_794_; 
v_unused_790_ = lean_ctor_get(v_impl_710_, 4);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_impl_710_, 3);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_impl_710_, 2);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_impl_710_, 1);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_impl_710_, 0);
lean_dec(v_unused_794_);
v___x_727_ = v_impl_710_;
v_isShared_728_ = v_isSharedCheck_789_;
goto v_resetjp_726_;
}
else
{
lean_dec(v_impl_710_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_789_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_size_729_; lean_object* v_k_730_; lean_object* v_v_731_; lean_object* v_l_732_; lean_object* v_r_733_; lean_object* v_size_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_size_729_ = lean_ctor_get(v_l_716_, 0);
v_k_730_ = lean_ctor_get(v_l_716_, 1);
v_v_731_ = lean_ctor_get(v_l_716_, 2);
v_l_732_ = lean_ctor_get(v_l_716_, 3);
v_r_733_ = lean_ctor_get(v_l_716_, 4);
v_size_734_ = lean_ctor_get(v_r_717_, 0);
v___x_735_ = lean_unsigned_to_nat(2u);
v___x_736_ = lean_nat_mul(v___x_735_, v_size_734_);
v___x_737_ = lean_nat_dec_lt(v_size_729_, v___x_736_);
lean_dec(v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_765_; 
lean_inc(v_r_733_);
lean_inc(v_l_732_);
lean_inc(v_v_731_);
lean_inc(v_k_730_);
v_isSharedCheck_765_ = !lean_is_exclusive(v_l_716_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; lean_object* v_unused_770_; 
v_unused_766_ = lean_ctor_get(v_l_716_, 4);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_l_716_, 3);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_l_716_, 2);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_l_716_, 1);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_l_716_, 0);
lean_dec(v_unused_770_);
v___x_739_ = v_l_716_;
v_isShared_740_ = v_isSharedCheck_765_;
goto v_resetjp_738_;
}
else
{
lean_dec(v_l_716_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_765_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_755_; 
v___x_741_ = lean_nat_add(v___x_711_, v_size_712_);
v___x_742_ = lean_nat_add(v___x_741_, v_size_713_);
lean_dec(v_size_713_);
if (lean_obj_tag(v_l_732_) == 0)
{
lean_object* v_size_763_; 
v_size_763_ = lean_ctor_get(v_l_732_, 0);
lean_inc(v_size_763_);
v___y_755_ = v_size_763_;
goto v___jp_754_;
}
else
{
lean_object* v___x_764_; 
v___x_764_ = lean_unsigned_to_nat(0u);
v___y_755_ = v___x_764_;
goto v___jp_754_;
}
v___jp_743_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_nat_add(v___y_744_, v___y_746_);
lean_dec(v___y_746_);
lean_dec(v___y_744_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 4, v_r_717_);
lean_ctor_set(v___x_739_, 3, v_r_733_);
lean_ctor_set(v___x_739_, 2, v_v_715_);
lean_ctor_set(v___x_739_, 1, v_k_714_);
lean_ctor_set(v___x_739_, 0, v___x_747_);
v___x_749_ = v___x_739_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_r_733_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v_r_717_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 4, v___x_749_);
lean_ctor_set(v___x_727_, 3, v___y_745_);
lean_ctor_set(v___x_727_, 2, v_v_731_);
lean_ctor_set(v___x_727_, 1, v_k_730_);
lean_ctor_set(v___x_727_, 0, v___x_742_);
v___x_751_ = v___x_727_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_k_730_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_v_731_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v___y_745_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
v___jp_754_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = lean_nat_add(v___x_741_, v___y_755_);
lean_dec(v___y_755_);
lean_dec(v___x_741_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v_l_732_);
lean_ctor_set(v___x_567_, 0, v___x_756_);
v___x_758_ = v___x_567_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_l_564_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_l_732_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; 
v___x_759_ = lean_nat_add(v___x_711_, v_size_734_);
if (lean_obj_tag(v_r_733_) == 0)
{
lean_object* v_size_760_; 
v_size_760_ = lean_ctor_get(v_r_733_, 0);
lean_inc(v_size_760_);
v___y_744_ = v___x_759_;
v___y_745_ = v___x_758_;
v___y_746_ = v_size_760_;
goto v___jp_743_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = lean_unsigned_to_nat(0u);
v___y_744_ = v___x_759_;
v___y_745_ = v___x_758_;
v___y_746_ = v___x_761_;
goto v___jp_743_;
}
}
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_del_object(v___x_567_);
v___x_771_ = lean_nat_add(v___x_711_, v_size_712_);
v___x_772_ = lean_nat_add(v___x_771_, v_size_713_);
lean_dec(v_size_713_);
v___x_773_ = lean_nat_add(v___x_771_, v_size_729_);
lean_dec(v___x_771_);
lean_inc_ref(v_l_564_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 4, v_l_716_);
lean_ctor_set(v___x_727_, 3, v_l_564_);
lean_ctor_set(v___x_727_, 2, v_v_563_);
lean_ctor_set(v___x_727_, 1, v_k_562_);
lean_ctor_set(v___x_727_, 0, v___x_773_);
v___x_775_ = v___x_727_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_l_564_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v_l_716_);
v___x_775_ = v_reuseFailAlloc_788_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_isSharedCheck_782_ = !lean_is_exclusive(v_l_564_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; lean_object* v_unused_784_; lean_object* v_unused_785_; lean_object* v_unused_786_; lean_object* v_unused_787_; 
v_unused_783_ = lean_ctor_get(v_l_564_, 4);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_l_564_, 3);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_l_564_, 2);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_l_564_, 1);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_l_564_, 0);
lean_dec(v_unused_787_);
v___x_777_ = v_l_564_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_dec(v_l_564_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 4, v_r_717_);
lean_ctor_set(v___x_777_, 3, v___x_775_);
lean_ctor_set(v___x_777_, 2, v_v_715_);
lean_ctor_set(v___x_777_, 1, v_k_714_);
lean_ctor_set(v___x_777_, 0, v___x_772_);
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_r_717_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_795_; 
v_l_795_ = lean_ctor_get(v_impl_710_, 3);
lean_inc(v_l_795_);
if (lean_obj_tag(v_l_795_) == 0)
{
lean_object* v_r_796_; lean_object* v_k_797_; lean_object* v_v_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_821_; 
v_r_796_ = lean_ctor_get(v_impl_710_, 4);
v_k_797_ = lean_ctor_get(v_impl_710_, 1);
v_v_798_ = lean_ctor_get(v_impl_710_, 2);
v_isSharedCheck_821_ = !lean_is_exclusive(v_impl_710_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; lean_object* v_unused_823_; 
v_unused_822_ = lean_ctor_get(v_impl_710_, 3);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_impl_710_, 0);
lean_dec(v_unused_823_);
v___x_800_ = v_impl_710_;
v_isShared_801_ = v_isSharedCheck_821_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_r_796_);
lean_inc(v_v_798_);
lean_inc(v_k_797_);
lean_dec(v_impl_710_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_821_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_k_802_; lean_object* v_v_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_817_; 
v_k_802_ = lean_ctor_get(v_l_795_, 1);
v_v_803_ = lean_ctor_get(v_l_795_, 2);
v_isSharedCheck_817_ = !lean_is_exclusive(v_l_795_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_818_ = lean_ctor_get(v_l_795_, 4);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_l_795_, 3);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_l_795_, 0);
lean_dec(v_unused_820_);
v___x_805_ = v_l_795_;
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_v_803_);
lean_inc(v_k_802_);
lean_dec(v_l_795_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_796_, 2);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 4, v_r_796_);
lean_ctor_set(v___x_805_, 3, v_r_796_);
lean_ctor_set(v___x_805_, 2, v_v_563_);
lean_ctor_set(v___x_805_, 1, v_k_562_);
lean_ctor_set(v___x_805_, 0, v___x_711_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_r_796_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_r_796_);
v___x_809_ = v_reuseFailAlloc_816_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
lean_inc(v_r_796_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 3, v_r_796_);
lean_ctor_set(v___x_800_, 0, v___x_711_);
v___x_811_ = v___x_800_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_k_797_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_v_798_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_r_796_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_r_796_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v___x_811_);
lean_ctor_set(v___x_567_, 3, v___x_809_);
lean_ctor_set(v___x_567_, 2, v_v_803_);
lean_ctor_set(v___x_567_, 1, v_k_802_);
lean_ctor_set(v___x_567_, 0, v___x_807_);
v___x_813_ = v___x_567_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
else
{
lean_object* v_r_824_; 
v_r_824_ = lean_ctor_get(v_impl_710_, 4);
lean_inc(v_r_824_);
if (lean_obj_tag(v_r_824_) == 0)
{
lean_object* v_k_825_; lean_object* v_v_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_837_; 
v_k_825_ = lean_ctor_get(v_impl_710_, 1);
v_v_826_ = lean_ctor_get(v_impl_710_, 2);
v_isSharedCheck_837_ = !lean_is_exclusive(v_impl_710_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; 
v_unused_838_ = lean_ctor_get(v_impl_710_, 4);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_impl_710_, 3);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_impl_710_, 0);
lean_dec(v_unused_840_);
v___x_828_ = v_impl_710_;
v_isShared_829_ = v_isSharedCheck_837_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_v_826_);
lean_inc(v_k_825_);
lean_dec(v_impl_710_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_837_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_unsigned_to_nat(3u);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 4, v_l_795_);
lean_ctor_set(v___x_828_, 2, v_v_563_);
lean_ctor_set(v___x_828_, 1, v_k_562_);
lean_ctor_set(v___x_828_, 0, v___x_711_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_l_795_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v_l_795_);
v___x_832_ = v_reuseFailAlloc_836_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_834_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v_r_824_);
lean_ctor_set(v___x_567_, 3, v___x_832_);
lean_ctor_set(v___x_567_, 2, v_v_826_);
lean_ctor_set(v___x_567_, 1, v_k_825_);
lean_ctor_set(v___x_567_, 0, v___x_830_);
v___x_834_ = v___x_567_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_k_825_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_v_826_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v_r_824_);
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
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_unsigned_to_nat(2u);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 4, v_impl_710_);
lean_ctor_set(v___x_567_, 3, v_r_824_);
lean_ctor_set(v___x_567_, 0, v___x_841_);
v___x_843_ = v___x_567_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v_r_824_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v_impl_710_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
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
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_k_558_);
lean_ctor_set(v___x_847_, 2, v_v_559_);
lean_ctor_set(v___x_847_, 3, v_t_560_);
lean_ctor_set(v___x_847_, 4, v_t_560_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(lean_object* v_init_848_, lean_object* v_x_849_, lean_object* v___y_850_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_object* v_k_852_; lean_object* v_v_853_; lean_object* v_l_854_; lean_object* v_r_855_; lean_object* v___x_856_; lean_object* v_fst_857_; lean_object* v_snd_858_; lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v_fst_861_; lean_object* v_snd_862_; lean_object* v___x_863_; 
v_k_852_ = lean_ctor_get(v_x_849_, 1);
lean_inc(v_k_852_);
v_v_853_ = lean_ctor_get(v_x_849_, 2);
lean_inc(v_v_853_);
v_l_854_ = lean_ctor_get(v_x_849_, 3);
lean_inc(v_l_854_);
v_r_855_ = lean_ctor_get(v_x_849_, 4);
lean_inc(v_r_855_);
lean_dec_ref_known(v_x_849_, 5);
v___x_856_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(v_init_848_, v_l_854_, v___y_850_);
v_fst_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_fst_857_);
v_snd_858_ = lean_ctor_get(v___x_856_, 1);
lean_inc(v_snd_858_);
lean_dec_ref(v___x_856_);
v_a_859_ = lean_ctor_get(v_fst_857_, 0);
lean_inc(v_a_859_);
lean_dec(v_fst_857_);
v___x_860_ = l_Lean_Server_RefInfo_toLspRefInfo(v_v_853_, v_snd_858_);
v_fst_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_fst_861_);
v_snd_862_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_snd_862_);
lean_dec_ref(v___x_860_);
v___x_863_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_852_, v_fst_861_, v_a_859_);
v_init_848_ = v___x_863_;
v_x_849_ = v_r_855_;
v___y_850_ = v_snd_862_;
goto _start;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v_init_848_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v___y_850_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1___boxed(lean_object* v_init_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(v_init_867_, v_x_868_, v___y_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object* v_refs_872_){
_start:
{
lean_object* v_refs_x27_874_; lean_object* v___x_875_; lean_object* v_fst_876_; lean_object* v_snd_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_887_; 
v_refs_x27_874_ = lean_box(1);
v___x_875_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(v_refs_x27_874_, v_refs_872_, v_refs_x27_874_);
v_fst_876_ = lean_ctor_get(v___x_875_, 0);
v_snd_877_ = lean_ctor_get(v___x_875_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_887_ == 0)
{
v___x_879_ = v___x_875_;
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_snd_877_);
lean_inc(v_fst_876_);
lean_dec(v___x_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_d_882_; lean_object* v_a_886_; 
v_a_886_ = lean_ctor_get(v_fst_876_, 0);
lean_inc(v_a_886_);
lean_dec(v_fst_876_);
v_d_882_ = v_a_886_;
goto v___jp_881_;
v___jp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_d_882_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_d_882_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_snd_877_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs___boxed(lean_object* v_refs_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v_refs_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0(lean_object* v_00_u03b2_891_, lean_object* v_k_892_, lean_object* v_v_893_, lean_object* v_t_894_, lean_object* v_hl_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_892_, v_v_893_, v_t_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_merge(lean_object* v_a_903_, lean_object* v_b_904_){
_start:
{
lean_object* v_definition_x3f_905_; lean_object* v_usages_906_; lean_object* v___y_908_; 
v_definition_x3f_905_ = lean_ctor_get(v_b_904_, 0);
lean_inc(v_definition_x3f_905_);
v_usages_906_ = lean_ctor_get(v_b_904_, 1);
lean_inc_ref(v_usages_906_);
lean_dec_ref(v_b_904_);
if (lean_obj_tag(v_definition_x3f_905_) == 0)
{
lean_object* v_definition_x3f_919_; 
v_definition_x3f_919_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_definition_x3f_919_);
v___y_908_ = v_definition_x3f_919_;
goto v___jp_907_;
}
else
{
v___y_908_ = v_definition_x3f_905_;
goto v___jp_907_;
}
v___jp_907_:
{
lean_object* v_usages_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_917_; 
v_usages_909_ = lean_ctor_get(v_a_903_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_a_903_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v_a_903_, 0);
lean_dec(v_unused_918_);
v___x_911_ = v_a_903_;
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_usages_909_);
lean_dec(v_a_903_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_913_ = l_Array_append___redArg(v_usages_909_, v_usages_906_);
lean_dec_ref(v_usages_906_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_913_);
lean_ctor_set(v___x_911_, 0, v___y_908_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___y_908_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(uint8_t v_includeStop_920_, lean_object* v_range_921_, lean_object* v_pos_922_){
_start:
{
lean_object* v_start_923_; lean_object* v_end_924_; uint8_t v___x_925_; 
v_start_923_ = lean_ctor_get(v_range_921_, 0);
v_end_924_ = lean_ctor_get(v_range_921_, 1);
v___x_925_ = l_Lean_Lsp_instOrdPosition_ord(v_start_923_, v_pos_922_);
if (v___x_925_ == 2)
{
uint8_t v___x_926_; 
v___x_926_ = 0;
return v___x_926_;
}
else
{
if (v_includeStop_920_ == 0)
{
uint8_t v___x_927_; 
v___x_927_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_922_, v_end_924_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; 
v___x_928_ = 1;
return v___x_928_;
}
else
{
return v_includeStop_920_;
}
}
else
{
uint8_t v___x_929_; 
v___x_929_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_922_, v_end_924_);
if (v___x_929_ == 2)
{
uint8_t v___x_930_; 
v___x_930_ = 0;
return v___x_930_;
}
else
{
return v_includeStop_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains___boxed(lean_object* v_includeStop_931_, lean_object* v_range_932_, lean_object* v_pos_933_){
_start:
{
uint8_t v_includeStop_boxed_934_; uint8_t v_res_935_; lean_object* v_r_936_; 
v_includeStop_boxed_934_ = lean_unbox(v_includeStop_931_);
v_res_935_ = l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(v_includeStop_boxed_934_, v_range_932_, v_pos_933_);
lean_dec_ref(v_pos_933_);
lean_dec_ref(v_range_932_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(uint8_t v_includeStop_940_, lean_object* v_pos_941_, lean_object* v_as_942_, size_t v_sz_943_, size_t v_i_944_, lean_object* v_b_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_944_, v_sz_943_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v_b_945_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; lean_object* v_a_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
lean_dec_ref(v_b_945_);
v___x_948_ = lean_box(0);
v_a_949_ = lean_array_uget_borrowed(v_as_942_, v_i_944_);
v___x_950_ = l_Lean_Lsp_RefInfo_Location_range(v_a_949_);
v___x_951_ = l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(v_includeStop_940_, v___x_950_, v_pos_941_);
lean_dec_ref(v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; size_t v___x_953_; size_t v___x_954_; 
v___x_952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___closed__0));
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_add(v_i_944_, v___x_953_);
v_i_944_ = v___x_954_;
v_b_945_ = v___x_952_;
goto _start;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_inc(v_a_949_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_a_949_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_948_);
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___boxed(lean_object* v_includeStop_959_, lean_object* v_pos_960_, lean_object* v_as_961_, lean_object* v_sz_962_, lean_object* v_i_963_, lean_object* v_b_964_){
_start:
{
uint8_t v_includeStop_boxed_965_; size_t v_sz_boxed_966_; size_t v_i_boxed_967_; lean_object* v_res_968_; 
v_includeStop_boxed_965_ = lean_unbox(v_includeStop_959_);
v_sz_boxed_966_ = lean_unbox_usize(v_sz_962_);
lean_dec(v_sz_962_);
v_i_boxed_967_ = lean_unbox_usize(v_i_963_);
lean_dec(v_i_963_);
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(v_includeStop_boxed_965_, v_pos_960_, v_as_961_, v_sz_boxed_966_, v_i_boxed_967_, v_b_964_);
lean_dec_ref(v_as_961_);
lean_dec_ref(v_pos_960_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(lean_object* v_self_969_, lean_object* v_pos_970_, uint8_t v_includeStop_971_){
_start:
{
lean_object* v_definition_x3f_972_; lean_object* v_usages_973_; 
v_definition_x3f_972_ = lean_ctor_get(v_self_969_, 0);
v_usages_973_ = lean_ctor_get(v_self_969_, 1);
if (lean_obj_tag(v_definition_x3f_972_) == 1)
{
lean_object* v_val_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_val_982_ = lean_ctor_get(v_definition_x3f_972_, 0);
v___x_983_ = l_Lean_Lsp_RefInfo_Location_range(v_val_982_);
v___x_984_ = l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(v_includeStop_971_, v___x_983_, v_pos_970_);
lean_dec_ref(v___x_983_);
if (v___x_984_ == 0)
{
goto v___jp_974_;
}
else
{
lean_inc_ref(v_definition_x3f_972_);
return v_definition_x3f_972_;
}
}
else
{
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_975_; lean_object* v___x_976_; size_t v_sz_977_; size_t v___x_978_; lean_object* v___x_979_; 
v___x_975_ = lean_box(0);
v___x_976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___closed__0));
v_sz_977_ = lean_array_size(v_usages_973_);
v___x_978_ = ((size_t)0ULL);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(v_includeStop_971_, v_pos_970_, v_usages_973_, v_sz_977_, v___x_978_, v___x_976_);
if (lean_obj_tag(v___x_979_) == 0)
{
return v___x_975_;
}
else
{
lean_object* v_val_980_; lean_object* v_fst_981_; 
v_val_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v___x_979_, 1);
v_fst_981_ = lean_ctor_get(v_val_980_, 0);
lean_inc(v_fst_981_);
lean_dec(v_val_980_);
if (lean_obj_tag(v_fst_981_) == 0)
{
return v___x_975_;
}
else
{
return v_fst_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_findReferenceLocation_x3f___boxed(lean_object* v_self_985_, lean_object* v_pos_986_, lean_object* v_includeStop_987_){
_start:
{
uint8_t v_includeStop_boxed_988_; lean_object* v_res_989_; 
v_includeStop_boxed_988_ = lean_unbox(v_includeStop_987_);
v_res_989_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_self_985_, v_pos_986_, v_includeStop_boxed_988_);
lean_dec_ref(v_pos_986_);
lean_dec_ref(v_self_985_);
return v_res_989_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_RefInfo_contains(lean_object* v_self_990_, lean_object* v_pos_991_, uint8_t v_includeStop_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_self_990_, v_pos_991_, v_includeStop_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
uint8_t v___x_994_; 
v___x_994_ = 0;
return v___x_994_;
}
else
{
uint8_t v___x_995_; 
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = 1;
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_contains___boxed(lean_object* v_self_996_, lean_object* v_pos_997_, lean_object* v_includeStop_998_){
_start:
{
uint8_t v_includeStop_boxed_999_; uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_includeStop_boxed_999_ = lean_unbox(v_includeStop_998_);
v_res_1000_ = l_Lean_Lsp_RefInfo_contains(v_self_996_, v_pos_997_, v_includeStop_boxed_999_);
lean_dec_ref(v_pos_997_);
lean_dec_ref(v_self_996_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(lean_object* v_pos_1002_, uint8_t v_includeStop_1003_, lean_object* v_init_1004_, lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v_k_1006_; lean_object* v_v_1007_; lean_object* v_l_1008_; lean_object* v_r_1009_; lean_object* v___x_1010_; lean_object* v_a_1011_; uint8_t v___x_1012_; 
v_k_1006_ = lean_ctor_get(v_x_1005_, 1);
lean_inc(v_k_1006_);
v_v_1007_ = lean_ctor_get(v_x_1005_, 2);
lean_inc(v_v_1007_);
v_l_1008_ = lean_ctor_get(v_x_1005_, 3);
lean_inc(v_l_1008_);
v_r_1009_ = lean_ctor_get(v_x_1005_, 4);
lean_inc(v_r_1009_);
lean_dec_ref_known(v_x_1005_, 5);
v___x_1010_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1002_, v_includeStop_1003_, v_init_1004_, v_l_1008_);
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = l_Lean_Lsp_RefInfo_contains(v_v_1007_, v_pos_1002_, v_includeStop_1003_);
lean_dec(v_v_1007_);
if (v___x_1012_ == 0)
{
lean_dec(v_k_1006_);
v_init_1004_ = v_a_1011_;
v_x_1005_ = v_r_1009_;
goto _start;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_array_push(v_a_1011_, v_k_1006_);
v_init_1004_ = v___x_1014_;
v_x_1005_ = v_r_1009_;
goto _start;
}
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_init_1004_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0___boxed(lean_object* v_pos_1017_, lean_object* v_includeStop_1018_, lean_object* v_init_1019_, lean_object* v_x_1020_){
_start:
{
uint8_t v_includeStop_boxed_1021_; lean_object* v_res_1022_; 
v_includeStop_boxed_1021_ = lean_unbox(v_includeStop_1018_);
v_res_1022_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1017_, v_includeStop_boxed_1021_, v_init_1019_, v_x_1020_);
lean_dec_ref(v_pos_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt(lean_object* v_self_1025_, lean_object* v_pos_1026_, uint8_t v_includeStop_1027_){
_start:
{
lean_object* v_result_1028_; lean_object* v___x_1029_; lean_object* v_a_1030_; 
v_result_1028_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_1029_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1026_, v_includeStop_1027_, v_result_1028_, v_self_1025_);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
return v_a_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt___boxed(lean_object* v_self_1031_, lean_object* v_pos_1032_, lean_object* v_includeStop_1033_){
_start:
{
uint8_t v_includeStop_boxed_1034_; lean_object* v_res_1035_; 
v_includeStop_boxed_1034_ = lean_unbox(v_includeStop_1033_);
v_res_1035_ = l_Lean_Lsp_ModuleRefs_findAt(v_self_1031_, v_pos_1032_, v_includeStop_boxed_1034_);
lean_dec_ref(v_pos_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(lean_object* v_pos_1039_, uint8_t v_includeStop_1040_, lean_object* v_init_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v_d_1044_; 
if (lean_obj_tag(v_x_1042_) == 0)
{
lean_object* v_v_1047_; lean_object* v_l_1048_; lean_object* v_r_1049_; lean_object* v___x_1050_; lean_object* v_val_1051_; 
v_v_1047_ = lean_ctor_get(v_x_1042_, 2);
v_l_1048_ = lean_ctor_get(v_x_1042_, 3);
v_r_1049_ = lean_ctor_get(v_x_1042_, 4);
v___x_1050_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1039_, v_includeStop_1040_, v_init_1041_, v_l_1048_);
v_val_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_val_1051_);
lean_dec(v___x_1050_);
if (lean_obj_tag(v_val_1051_) == 0)
{
lean_object* v_a_1052_; 
v_a_1052_ = lean_ctor_get(v_val_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v_val_1051_, 1);
v_d_1044_ = v_a_1052_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref_known(v_val_1051_, 1);
v___x_1053_ = lean_box(0);
v___x_1054_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_v_1047_, v_pos_1039_, v_includeStop_1040_);
if (lean_obj_tag(v___x_1054_) == 1)
{
lean_object* v_val_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1064_; 
v_val_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_val_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = l_Lean_Lsp_RefInfo_Location_range(v_val_1055_);
lean_dec(v_val_1055_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___x_1053_);
v_d_1044_ = v___x_1062_;
goto v___jp_1043_;
}
}
}
else
{
lean_object* v___x_1065_; 
lean_dec(v___x_1054_);
v___x_1065_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0));
v_init_1041_ = v___x_1065_;
v_x_1042_ = v_r_1049_;
goto _start;
}
}
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_init_1041_);
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
v___jp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_d_1044_);
v___x_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___boxed(lean_object* v_pos_1069_, lean_object* v_includeStop_1070_, lean_object* v_init_1071_, lean_object* v_x_1072_){
_start:
{
uint8_t v_includeStop_boxed_1073_; lean_object* v_res_1074_; 
v_includeStop_boxed_1073_ = lean_unbox(v_includeStop_1070_);
v_res_1074_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1069_, v_includeStop_boxed_1073_, v_init_1071_, v_x_1072_);
lean_dec(v_x_1072_);
lean_dec_ref(v_pos_1069_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f(lean_object* v_self_1075_, lean_object* v_pos_1076_, uint8_t v_includeStop_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v_val_1080_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_val_1084_; lean_object* v_a_1085_; 
v___x_1078_ = lean_box(0);
v___x_1082_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0));
v___x_1083_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1076_, v_includeStop_1077_, v___x_1082_, v_self_1075_);
v_val_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_val_1084_);
lean_dec(v___x_1083_);
v_a_1085_ = lean_ctor_get(v_val_1084_, 0);
lean_inc(v_a_1085_);
lean_dec(v_val_1084_);
v_val_1080_ = v_a_1085_;
goto v___jp_1079_;
v___jp_1079_:
{
lean_object* v_fst_1081_; 
v_fst_1081_ = lean_ctor_get(v_val_1080_, 0);
lean_inc(v_fst_1081_);
lean_dec_ref(v_val_1080_);
if (lean_obj_tag(v_fst_1081_) == 0)
{
return v___x_1078_;
}
else
{
return v_fst_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f___boxed(lean_object* v_self_1086_, lean_object* v_pos_1087_, lean_object* v_includeStop_1088_){
_start:
{
uint8_t v_includeStop_boxed_1089_; lean_object* v_res_1090_; 
v_includeStop_boxed_1089_ = lean_unbox(v_includeStop_1088_);
v_res_1090_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_self_1086_, v_pos_1087_, v_includeStop_boxed_1089_);
lean_dec_ref(v_pos_1087_);
lean_dec(v_self_1086_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(lean_object* v_j_1091_, lean_object* v_k_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = l_Lean_Json_getObjValD(v_j_1091_, v_k_1092_);
v___x_1094_ = l_Lean_Json_getNat_x3f(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0___boxed(lean_object* v_j_1095_, lean_object* v_k_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(v_j_1095_, v_k_1096_);
lean_dec_ref(v_k_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(lean_object* v_j_1098_, lean_object* v_k_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = l_Lean_Json_getObjValD(v_j_1098_, v_k_1099_);
v___x_1101_ = l_Lean_Name_fromJson_x3f(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1___boxed(lean_object* v_j_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(v_j_1102_, v_k_1103_);
lean_dec_ref(v_k_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(lean_object* v_init_1109_, lean_object* v_x_1110_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 0)
{
lean_object* v_k_1111_; lean_object* v_v_1112_; lean_object* v_l_1113_; lean_object* v_r_1114_; lean_object* v___x_1115_; 
v_k_1111_ = lean_ctor_get(v_x_1110_, 1);
lean_inc(v_k_1111_);
v_v_1112_ = lean_ctor_get(v_x_1110_, 2);
lean_inc(v_v_1112_);
v_l_1113_ = lean_ctor_get(v_x_1110_, 3);
lean_inc(v_l_1113_);
v_r_1114_ = lean_ctor_get(v_x_1110_, 4);
lean_inc(v_r_1114_);
lean_dec_ref_known(v_x_1110_, 5);
v___x_1115_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(v_init_1109_, v_l_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_dec(v_r_1114_);
lean_dec(v_v_1112_);
lean_dec(v_k_1111_);
return v___x_1115_;
}
else
{
if (lean_obj_tag(v_v_1112_) == 4)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1230_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1230_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1230_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_elems_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_elems_1120_ = lean_ctor_get(v_v_1112_, 0);
lean_inc_ref(v_elems_1120_);
lean_dec_ref_known(v_v_1112_, 1);
v___x_1121_ = lean_array_get_size(v_elems_1120_);
v___x_1122_ = lean_unsigned_to_nat(8u);
v___x_1123_ = lean_nat_dec_eq(v___x_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
lean_dec_ref(v_elems_1120_);
lean_dec(v_a_1116_);
lean_dec(v_r_1114_);
lean_dec(v_k_1111_);
v___x_1124_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__0));
v___x_1125_ = l_Nat_reprFast(v___x_1121_);
v___x_1126_ = lean_string_append(v___x_1124_, v___x_1125_);
lean_dec_ref(v___x_1125_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1126_);
v___x_1128_ = v___x_1118_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_del_object(v___x_1118_);
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_array_get_borrowed(v___x_1130_, v_elems_1120_, v___x_1131_);
lean_inc(v___x_1132_);
v___x_1133_ = l_Lean_Json_getNat_x3f(v___x_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_elems_1120_);
lean_dec(v_a_1116_);
lean_dec(v_r_1114_);
lean_dec(v_k_1111_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_a_1142_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1143_ = lean_unsigned_to_nat(1u);
v___x_1144_ = lean_array_get_borrowed(v___x_1130_, v_elems_1120_, v___x_1143_);
lean_inc(v___x_1144_);
v___x_1145_ = l_Lean_Json_getNat_x3f(v___x_1144_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_a_1142_);
lean_dec_ref(v_elems_1120_);
lean_dec(v_a_1116_);
lean_dec(v_r_1114_);
lean_dec(v_k_1111_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_a_1154_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1155_ = lean_unsigned_to_nat(2u);
v___x_1156_ = lean_array_get_borrowed(v___x_1130_, v_elems_1120_, v___x_1155_);
lean_inc(v___x_1156_);
v___x_1157_ = l_Lean_Json_getNat_x3f(v___x_1156_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_a_1154_);
lean_dec(v_a_1142_);
lean_dec_ref(v_elems_1120_);
lean_dec(v_a_1116_);
lean_dec(v_r_1114_);
lean_dec(v_k_1111_);
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_a_1166_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1167_ = lean_unsigned_to_nat(3u);
v___x_1168_ = lean_array_get_borrowed(v___x_1130_, v_elems_1120_, v___x_1167_);
lean_inc(v___x_1168_);
v___x_1169_ = l_Lean_Json_getNat_x3f(v___x_1168_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_a_1166_);
lean_dec(v_a_1154_);
lean_dec(v_a_1142_);
lean_dec_ref(v_elems_1120_);
lean_dec(v_a_1116_);
lean_dec(v_r_1114_);
lean_dec(v_k_1111_);
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_a_1178_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1179_ = lean_unsigned_to_nat(4u);
v___x_1180_ = lean_array_get_borrowed(v___x_1130_, v_elems_1120_, v___x_1179_);
lean_inc(v___x_1180_);
v___x_1181_ = l_Lean_Json_getNat_x3f(v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_a_1178_);
lean_dec(v_a_1166_);
lean_dec(v_a_1154_);
lean_dec(v_a_1142_);
lean_dec_ref(v_elems_1120_);
lean_dec(v_a_1116_);
lean_dec(v_r_1114_);
lean_dec(v_k_1111_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_a_1190_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1191_ = lean_unsigned_to_nat(5u);
v___x_1192_ = lean_array_get_borrowed(v___x_1130_, v_elems_1120_, v___x_1191_);
lean_inc(v___x_1192_);
v___x_1193_ = l_Lean_Json_getNat_x3f(v___x_1192_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_a_1190_);
lean_dec(v_a_1178_);
lean_dec(v_a_1166_);
lean_dec(v_a_1154_);
lean_dec(v_a_1142_);
lean_dec_ref(v_elems_1120_);
lean_dec(v_a_1116_);
lean_dec(v_r_1114_);
lean_dec(v_k_1111_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_a_1202_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1203_ = lean_unsigned_to_nat(6u);
v___x_1204_ = lean_array_get_borrowed(v___x_1130_, v_elems_1120_, v___x_1203_);
lean_inc(v___x_1204_);
v___x_1205_ = l_Lean_Json_getNat_x3f(v___x_1204_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_a_1202_);
lean_dec(v_a_1190_);
lean_dec(v_a_1178_);
lean_dec(v_a_1166_);
lean_dec(v_a_1154_);
lean_dec(v_a_1142_);
lean_dec_ref(v_elems_1120_);
lean_dec(v_a_1116_);
lean_dec(v_r_1114_);
lean_dec(v_k_1111_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_a_1214_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1215_ = lean_unsigned_to_nat(7u);
v___x_1216_ = lean_array_get(v___x_1130_, v_elems_1120_, v___x_1215_);
lean_dec_ref(v_elems_1120_);
v___x_1217_ = l_Lean_Json_getNat_x3f(v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_a_1214_);
lean_dec(v_a_1202_);
lean_dec(v_a_1190_);
lean_dec(v_a_1178_);
lean_dec(v_a_1166_);
lean_dec(v_a_1154_);
lean_dec(v_a_1142_);
lean_dec(v_a_1116_);
lean_dec(v_r_1114_);
lean_dec(v_k_1111_);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_a_1226_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1227_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1227_, 0, v_a_1142_);
lean_ctor_set(v___x_1227_, 1, v_a_1154_);
lean_ctor_set(v___x_1227_, 2, v_a_1166_);
lean_ctor_set(v___x_1227_, 3, v_a_1178_);
lean_ctor_set(v___x_1227_, 4, v_a_1190_);
lean_ctor_set(v___x_1227_, 5, v_a_1202_);
lean_ctor_set(v___x_1227_, 6, v_a_1214_);
lean_ctor_set(v___x_1227_, 7, v_a_1226_);
v___x_1228_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_1111_, v___x_1227_, v_a_1116_);
v_init_1109_ = v___x_1228_;
v_x_1110_ = v_r_1114_;
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
lean_object* v___x_1231_; 
lean_dec_ref_known(v___x_1115_, 1);
lean_dec(v_r_1114_);
lean_dec(v_v_1112_);
lean_dec(v_k_1111_);
v___x_1231_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__2));
return v___x_1231_;
}
}
}
else
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_init_1109_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(lean_object* v_j_1233_, lean_object* v_k_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = l_Lean_Json_getObjValD(v_j_1233_, v_k_1234_);
v___x_1236_ = l_Lean_Json_getObj_x3f(v___x_1235_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_a_1245_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1246_ = lean_box(1);
v___x_1247_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(v___x_1246_, v_a_1245_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4___boxed(lean_object* v_j_1248_, lean_object* v_k_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(v_j_1248_, v_k_1249_);
lean_dec_ref(v_k_1249_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(size_t v_sz_1251_, size_t v_i_1252_, lean_object* v_bs_1253_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_lt(v_i_1252_, v_sz_1251_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_bs_1253_);
return v___x_1255_;
}
else
{
lean_object* v_v_1256_; lean_object* v___x_1257_; lean_object* v_bs_x27_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v_v_1256_ = lean_array_uget(v_bs_1253_, v_i_1252_);
v___x_1257_ = lean_unsigned_to_nat(0u);
v_bs_x27_1258_ = lean_array_uset(v_bs_1253_, v_i_1252_, v___x_1257_);
v___x_1259_ = ((size_t)1ULL);
v___x_1260_ = lean_usize_add(v_i_1252_, v___x_1259_);
v___x_1261_ = lean_array_uset(v_bs_x27_1258_, v_i_1252_, v_v_1256_);
v_i_1252_ = v___x_1260_;
v_bs_1253_ = v___x_1261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13___boxed(lean_object* v_sz_1263_, lean_object* v_i_1264_, lean_object* v_bs_1265_){
_start:
{
size_t v_sz_boxed_1266_; size_t v_i_boxed_1267_; lean_object* v_res_1268_; 
v_sz_boxed_1266_ = lean_unbox_usize(v_sz_1263_);
lean_dec(v_sz_1263_);
v_i_boxed_1267_ = lean_unbox_usize(v_i_1264_);
lean_dec(v_i_1264_);
v_res_1268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(v_sz_boxed_1266_, v_i_boxed_1267_, v_bs_1265_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(lean_object* v_x_1271_){
_start:
{
if (lean_obj_tag(v_x_1271_) == 4)
{
lean_object* v_elems_1272_; size_t v_sz_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v_elems_1272_ = lean_ctor_get(v_x_1271_, 0);
lean_inc_ref(v_elems_1272_);
lean_dec_ref_known(v_x_1271_, 1);
v_sz_1273_ = lean_array_size(v_elems_1272_);
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(v_sz_1273_, v___x_1274_, v_elems_1272_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1276_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1277_ = lean_unsigned_to_nat(80u);
v___x_1278_ = l_Lean_Json_pretty(v_x_1271_, v___x_1277_);
v___x_1279_ = lean_string_append(v___x_1276_, v___x_1278_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1281_ = lean_string_append(v___x_1279_, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(size_t v_sz_1283_, size_t v_i_1284_, lean_object* v_bs_1285_){
_start:
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_usize_dec_lt(v_i_1284_, v_sz_1283_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_bs_1285_);
return v___x_1287_;
}
else
{
lean_object* v_v_1288_; lean_object* v___x_1289_; 
v_v_1288_ = lean_array_uget_borrowed(v_bs_1285_, v_i_1284_);
lean_inc(v_v_1288_);
v___x_1289_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(v_v_1288_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_bs_1285_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1299_; lean_object* v_bs_x27_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v_a_1298_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1289_, 1);
v___x_1299_ = lean_unsigned_to_nat(0u);
v_bs_x27_1300_ = lean_array_uset(v_bs_1285_, v_i_1284_, v___x_1299_);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_i_1284_, v___x_1301_);
v___x_1303_ = lean_array_uset(v_bs_x27_1300_, v_i_1284_, v_a_1298_);
v_i_1284_ = v___x_1302_;
v_bs_1285_ = v___x_1303_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9___boxed(lean_object* v_sz_1305_, lean_object* v_i_1306_, lean_object* v_bs_1307_){
_start:
{
size_t v_sz_boxed_1308_; size_t v_i_boxed_1309_; lean_object* v_res_1310_; 
v_sz_boxed_1308_ = lean_unbox_usize(v_sz_1305_);
lean_dec(v_sz_1305_);
v_i_boxed_1309_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(v_sz_boxed_1308_, v_i_boxed_1309_, v_bs_1307_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(lean_object* v_x_1311_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 4)
{
lean_object* v_elems_1312_; size_t v_sz_1313_; size_t v___x_1314_; lean_object* v___x_1315_; 
v_elems_1312_ = lean_ctor_get(v_x_1311_, 0);
lean_inc_ref(v_elems_1312_);
lean_dec_ref_known(v_x_1311_, 1);
v_sz_1313_ = lean_array_size(v_elems_1312_);
v___x_1314_ = ((size_t)0ULL);
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(v_sz_1313_, v___x_1314_, v_elems_1312_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1316_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1317_ = lean_unsigned_to_nat(80u);
v___x_1318_ = l_Lean_Json_pretty(v_x_1311_, v___x_1317_);
v___x_1319_ = lean_string_append(v___x_1316_, v___x_1318_);
lean_dec_ref(v___x_1318_);
v___x_1320_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1321_ = lean_string_append(v___x_1319_, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(lean_object* v_j_1323_, lean_object* v_k_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = l_Lean_Json_getObjValD(v_j_1323_, v_k_1324_);
v___x_1326_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4___boxed(lean_object* v_j_1327_, lean_object* v_k_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(v_j_1327_, v_k_1328_);
lean_dec_ref(v_k_1328_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(size_t v_sz_1332_, size_t v_i_1333_, lean_object* v_bs_1334_){
_start:
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_usize_dec_lt(v_i_1333_, v_sz_1332_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_bs_1334_);
return v___x_1336_;
}
else
{
lean_object* v_v_1337_; lean_object* v___x_1338_; lean_object* v_bs_x27_1339_; lean_object* v_a_1341_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1412_; 
v_v_1337_ = lean_array_uget(v_bs_1334_, v_i_1333_);
v___x_1338_ = lean_unsigned_to_nat(0u);
v_bs_x27_1339_ = lean_array_uset(v_bs_1334_, v_i_1333_, v___x_1338_);
v___x_1346_ = lean_array_get_size(v_v_1337_);
v___x_1347_ = lean_unsigned_to_nat(4u);
v___x_1412_ = lean_nat_dec_eq(v___x_1346_, v___x_1347_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(5u);
v___x_1414_ = lean_nat_dec_eq(v___x_1346_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec_ref(v_bs_x27_1339_);
lean_dec(v_v_1337_);
v___x_1415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1416_ = l_Nat_reprFast(v___x_1346_);
v___x_1417_ = lean_string_append(v___x_1415_, v___x_1416_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
else
{
goto v___jp_1348_;
}
}
else
{
goto v___jp_1348_;
}
v___jp_1340_:
{
size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_add(v_i_1333_, v___x_1342_);
v___x_1344_ = lean_array_uset(v_bs_x27_1339_, v_i_1333_, v_a_1341_);
v_i_1333_ = v___x_1343_;
v_bs_1334_ = v___x_1344_;
goto _start;
}
v___jp_1348_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_array_fget_borrowed(v_v_1337_, v___x_1338_);
lean_inc(v___x_1349_);
v___x_1350_ = l_Lean_Json_getNat_x3f(v___x_1349_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_bs_x27_1339_);
lean_dec(v_v_1337_);
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_a_1359_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1360_ = lean_unsigned_to_nat(1u);
v___x_1361_ = lean_array_fget_borrowed(v_v_1337_, v___x_1360_);
lean_inc(v___x_1361_);
v___x_1362_ = l_Lean_Json_getNat_x3f(v___x_1361_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_a_1359_);
lean_dec_ref(v_bs_x27_1339_);
lean_dec(v_v_1337_);
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_a_1371_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1372_ = lean_unsigned_to_nat(2u);
v___x_1373_ = lean_array_fget_borrowed(v_v_1337_, v___x_1372_);
lean_inc(v___x_1373_);
v___x_1374_ = l_Lean_Json_getNat_x3f(v___x_1373_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v_a_1371_);
lean_dec(v_a_1359_);
lean_dec_ref(v_bs_x27_1339_);
lean_dec(v_v_1337_);
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_a_1383_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1384_ = lean_unsigned_to_nat(3u);
v___x_1385_ = lean_array_fget_borrowed(v_v_1337_, v___x_1384_);
lean_inc(v___x_1385_);
v___x_1386_ = l_Lean_Json_getNat_x3f(v___x_1385_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_a_1383_);
lean_dec(v_a_1371_);
lean_dec(v_a_1359_);
lean_dec_ref(v_bs_x27_1339_);
lean_dec(v_v_1337_);
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_a_1395_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1396_ = lean_unsigned_to_nat(5u);
v___x_1397_ = lean_nat_dec_eq(v___x_1346_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec(v_v_1337_);
v___x_1398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
v___x_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1399_, 0, v_a_1359_);
lean_ctor_set(v___x_1399_, 1, v_a_1371_);
lean_ctor_set(v___x_1399_, 2, v_a_1383_);
lean_ctor_set(v___x_1399_, 3, v_a_1395_);
lean_ctor_set(v___x_1399_, 4, v___x_1398_);
v_a_1341_ = v___x_1399_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_array_fget(v_v_1337_, v___x_1347_);
lean_dec(v_v_1337_);
v___x_1401_ = l_Lean_Json_getStr_x3f(v___x_1400_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_a_1395_);
lean_dec(v_a_1383_);
lean_dec(v_a_1371_);
lean_dec(v_a_1359_);
lean_dec_ref(v_bs_x27_1339_);
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1411_; 
v_a_1410_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1401_, 1);
v___x_1411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1411_, 0, v_a_1359_);
lean_ctor_set(v___x_1411_, 1, v_a_1371_);
lean_ctor_set(v___x_1411_, 2, v_a_1383_);
lean_ctor_set(v___x_1411_, 3, v_a_1395_);
lean_ctor_set(v___x_1411_, 4, v_a_1410_);
v_a_1341_ = v___x_1411_;
goto v___jp_1340_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___boxed(lean_object* v_sz_1419_, lean_object* v_i_1420_, lean_object* v_bs_1421_){
_start:
{
size_t v_sz_boxed_1422_; size_t v_i_boxed_1423_; lean_object* v_res_1424_; 
v_sz_boxed_1422_ = lean_unbox_usize(v_sz_1419_);
lean_dec(v_sz_1419_);
v_i_boxed_1423_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_res_1424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_boxed_1422_, v_i_boxed_1423_, v_bs_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(lean_object* v_x_1427_){
_start:
{
if (lean_obj_tag(v_x_1427_) == 0)
{
lean_object* v___x_1428_; 
v___x_1428_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0));
return v___x_1428_;
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(v_x_1427_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1446_; 
v_a_1438_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1440_ = v___x_1429_;
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1429_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1438_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1442_);
v___x_1444_ = v___x_1440_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(lean_object* v_j_1447_, lean_object* v_k_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = l_Lean_Json_getObjValD(v_j_1447_, v_k_1448_);
v___x_1450_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6___boxed(lean_object* v_j_1451_, lean_object* v_k_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_j_1451_, v_k_1452_);
lean_dec_ref(v_k_1452_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(lean_object* v_init_1456_, lean_object* v_x_1457_){
_start:
{
if (lean_obj_tag(v_x_1457_) == 0)
{
lean_object* v_k_1458_; lean_object* v_v_1459_; lean_object* v_l_1460_; lean_object* v_r_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1621_; 
v_k_1458_ = lean_ctor_get(v_x_1457_, 1);
v_v_1459_ = lean_ctor_get(v_x_1457_, 2);
v_l_1460_ = lean_ctor_get(v_x_1457_, 3);
v_r_1461_ = lean_ctor_get(v_x_1457_, 4);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_x_1457_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v_x_1457_, 0);
lean_dec(v_unused_1622_);
v___x_1463_ = v_x_1457_;
v_isShared_1464_ = v_isSharedCheck_1621_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_r_1461_);
lean_inc(v_l_1460_);
lean_inc(v_v_1459_);
lean_inc(v_k_1458_);
lean_dec(v_x_1457_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1621_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v_init_1456_, v_l_1460_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
lean_dec(v_k_1458_);
return v___x_1465_;
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1620_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1620_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1620_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Json_parse(v_k_1458_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1480_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1479_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v_definition_x3f_1491_; lean_object* v_a_1519_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1489_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1523_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
lean_inc(v_v_1459_);
v___x_1524_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_v_1459_, v___x_1523_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_a_1489_);
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1619_; 
v_a_1533_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1535_ = v___x_1524_;
v_isShared_1536_ = v_isSharedCheck_1619_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1524_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1619_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
if (lean_obj_tag(v_a_1533_) == 0)
{
lean_object* v___x_1537_; 
lean_del_object(v___x_1535_);
lean_del_object(v___x_1468_);
lean_del_object(v___x_1463_);
v___x_1537_ = lean_box(0);
v_definition_x3f_1491_ = v___x_1537_;
goto v___jp_1490_;
}
else
{
lean_object* v_val_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1610_; 
v_val_1538_ = lean_ctor_get(v_a_1533_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v_a_1533_, 1);
v___x_1539_ = lean_array_get_size(v_val_1538_);
v___x_1540_ = lean_unsigned_to_nat(4u);
v___x_1610_ = lean_nat_dec_eq(v___x_1539_, v___x_1540_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = lean_unsigned_to_nat(5u);
v___x_1612_ = lean_nat_dec_eq(v___x_1539_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
lean_dec(v_val_1538_);
lean_dec(v_a_1489_);
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
v___x_1613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1614_ = l_Nat_reprFast(v___x_1539_);
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
lean_dec_ref(v___x_1614_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1615_);
v___x_1617_ = v___x_1535_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
else
{
lean_del_object(v___x_1535_);
goto v___jp_1541_;
}
}
else
{
lean_del_object(v___x_1535_);
goto v___jp_1541_;
}
v___jp_1541_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = lean_array_fget_borrowed(v_val_1538_, v___x_1542_);
lean_inc(v___x_1543_);
v___x_1544_ = l_Lean_Json_getNat_x3f(v___x_1543_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_val_1538_);
lean_dec(v_a_1489_);
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_a_1553_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_array_fget_borrowed(v_val_1538_, v___x_1554_);
lean_inc(v___x_1555_);
v___x_1556_ = l_Lean_Json_getNat_x3f(v___x_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_a_1553_);
lean_dec(v_val_1538_);
lean_dec(v_a_1489_);
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1565_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1566_ = lean_unsigned_to_nat(2u);
v___x_1567_ = lean_array_fget_borrowed(v_val_1538_, v___x_1566_);
lean_inc(v___x_1567_);
v___x_1568_ = l_Lean_Json_getNat_x3f(v___x_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_a_1565_);
lean_dec(v_a_1553_);
lean_dec(v_val_1538_);
lean_dec(v_a_1489_);
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_a_1577_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1578_ = lean_unsigned_to_nat(3u);
v___x_1579_ = lean_array_fget_borrowed(v_val_1538_, v___x_1578_);
lean_inc(v___x_1579_);
v___x_1580_ = l_Lean_Json_getNat_x3f(v___x_1579_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1577_);
lean_dec(v_a_1565_);
lean_dec(v_a_1553_);
lean_dec(v_val_1538_);
lean_dec(v_a_1489_);
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v_a_1589_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1590_ = lean_unsigned_to_nat(5u);
v___x_1591_ = lean_nat_dec_eq(v___x_1539_, v___x_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1594_; 
lean_dec(v_val_1538_);
v___x_1592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v___x_1592_);
lean_ctor_set(v___x_1463_, 3, v_a_1589_);
lean_ctor_set(v___x_1463_, 2, v_a_1577_);
lean_ctor_set(v___x_1463_, 1, v_a_1565_);
lean_ctor_set(v___x_1463_, 0, v_a_1553_);
v___x_1594_ = v___x_1463_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1553_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_a_1565_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_a_1577_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_a_1589_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
v_a_1519_ = v___x_1594_;
goto v___jp_1518_;
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_array_fget(v_val_1538_, v___x_1540_);
lean_dec(v_val_1538_);
v___x_1597_ = l_Lean_Json_getStr_x3f(v___x_1596_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_a_1589_);
lean_dec(v_a_1577_);
lean_dec(v_a_1565_);
lean_dec(v_a_1553_);
lean_dec(v_a_1489_);
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_del_object(v___x_1463_);
lean_dec(v_r_1461_);
lean_dec(v_v_1459_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; 
v_a_1606_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1597_, 1);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v_a_1606_);
lean_ctor_set(v___x_1463_, 3, v_a_1589_);
lean_ctor_set(v___x_1463_, 2, v_a_1577_);
lean_ctor_set(v___x_1463_, 1, v_a_1565_);
lean_ctor_set(v___x_1463_, 0, v_a_1553_);
v___x_1608_ = v___x_1463_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1553_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_a_1565_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_a_1577_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_a_1589_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_a_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
v_a_1519_ = v___x_1608_;
goto v___jp_1518_;
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
v___jp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v___x_1493_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(v_v_1459_, v___x_1492_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_definition_x3f_1491_);
lean_dec(v_a_1489_);
lean_dec(v_a_1466_);
lean_dec(v_r_1461_);
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_object* v_a_1502_; size_t v_sz_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v_a_1502_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1493_, 1);
v_sz_1503_ = lean_array_size(v_a_1502_);
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_1503_, v___x_1504_, v_a_1502_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_definition_x3f_1491_);
lean_dec(v_a_1489_);
lean_dec(v_a_1466_);
lean_dec(v_r_1461_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_a_1514_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_definition_x3f_1491_);
lean_ctor_set(v___x_1515_, 1, v_a_1514_);
v___x_1516_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_a_1489_, v___x_1515_, v_a_1466_);
v_init_1456_ = v___x_1516_;
v_x_1457_ = v_r_1461_;
goto _start;
}
}
}
v___jp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v_a_1519_);
v___x_1521_ = v___x_1468_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
v_definition_x3f_1491_ = v___x_1521_;
goto v___jp_1490_;
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
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_init_1456_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(lean_object* v_j_1624_, lean_object* v_k_1625_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = l_Lean_Json_getObjValD(v_j_1624_, v_k_1625_);
v___x_1627_ = l_Lean_Json_getObj_x3f(v___x_1626_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_a_1636_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1627_, 1);
v___x_1637_ = lean_box(1);
v___x_1638_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v___x_1637_, v_a_1636_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3___boxed(lean_object* v_j_1639_, lean_object* v_k_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_j_1639_, v_k_1640_);
lean_dec_ref(v_k_1640_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1645_, size_t v_i_1646_, lean_object* v_bs_1647_){
_start:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_usize_dec_lt(v_i_1646_, v_sz_1645_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v_bs_1647_);
return v___x_1651_;
}
else
{
lean_object* v_v_1652_; 
v_v_1652_ = lean_array_uget_borrowed(v_bs_1647_, v_i_1646_);
if (lean_obj_tag(v_v_1652_) == 4)
{
lean_object* v_elems_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v_elems_1653_ = lean_ctor_get(v_v_1652_, 0);
v___x_1654_ = lean_array_get_size(v_elems_1653_);
v___x_1655_ = lean_unsigned_to_nat(4u);
v___x_1656_ = lean_nat_dec_eq(v___x_1654_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_dec_ref(v_bs_1647_);
goto v___jp_1648_;
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = lean_array_fget_borrowed(v_elems_1653_, v___x_1657_);
lean_inc(v___x_1658_);
v___x_1659_ = l_Lean_Json_getStr_x3f(v___x_1658_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_bs_1647_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_a_1668_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_array_fget_borrowed(v_elems_1653_, v___x_1669_);
v___x_1671_ = l_Lean_Json_getBool_x3f(v___x_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_a_1668_);
lean_dec_ref(v_bs_1647_);
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_a_1680_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1681_ = lean_unsigned_to_nat(2u);
v___x_1682_ = lean_array_fget_borrowed(v_elems_1653_, v___x_1681_);
v___x_1683_ = l_Lean_Json_getBool_x3f(v___x_1682_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec(v_a_1680_);
lean_dec(v_a_1668_);
lean_dec_ref(v_bs_1647_);
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_a_1692_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1683_, 1);
v___x_1693_ = lean_unsigned_to_nat(3u);
v___x_1694_ = lean_array_fget_borrowed(v_elems_1653_, v___x_1693_);
v___x_1695_ = l_Lean_Json_getBool_x3f(v___x_1694_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_a_1692_);
lean_dec(v_a_1680_);
lean_dec(v_a_1668_);
lean_dec_ref(v_bs_1647_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v_bs_x27_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; uint8_t v___x_1708_; uint8_t v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v_a_1704_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1695_, 1);
v_bs_x27_1705_ = lean_array_uset(v_bs_1647_, v_i_1646_, v___x_1657_);
v___x_1706_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1706_, 0, v_a_1668_);
v___x_1707_ = lean_unbox(v_a_1680_);
lean_dec(v_a_1680_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*1, v___x_1707_);
v___x_1708_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*1 + 1, v___x_1708_);
v___x_1709_ = lean_unbox(v_a_1704_);
lean_dec(v_a_1704_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*1 + 2, v___x_1709_);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1646_, v___x_1710_);
v___x_1712_ = lean_array_uset(v_bs_x27_1705_, v_i_1646_, v___x_1706_);
v_i_1646_ = v___x_1711_;
v_bs_1647_ = v___x_1712_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1647_);
goto v___jp_1648_;
}
}
v___jp_1648_:
{
lean_object* v___x_1649_; 
v___x_1649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1));
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1714_, lean_object* v_i_1715_, lean_object* v_bs_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; lean_object* v_res_1719_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1714_);
lean_dec(v_sz_1714_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1717_, v_i_boxed_1718_, v_bs_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(lean_object* v_x_1720_){
_start:
{
if (lean_obj_tag(v_x_1720_) == 4)
{
lean_object* v_elems_1721_; size_t v_sz_1722_; size_t v___x_1723_; lean_object* v___x_1724_; 
v_elems_1721_ = lean_ctor_get(v_x_1720_, 0);
lean_inc_ref(v_elems_1721_);
lean_dec_ref_known(v_x_1720_, 1);
v_sz_1722_ = lean_array_size(v_elems_1721_);
v___x_1723_ = ((size_t)0ULL);
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_1722_, v___x_1723_, v_elems_1721_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1725_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1726_ = lean_unsigned_to_nat(80u);
v___x_1727_ = l_Lean_Json_pretty(v_x_1720_, v___x_1726_);
v___x_1728_ = lean_string_append(v___x_1725_, v___x_1727_);
lean_dec_ref(v___x_1727_);
v___x_1729_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1730_ = lean_string_append(v___x_1728_, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(lean_object* v_j_1732_, lean_object* v_k_1733_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = l_Lean_Json_getObjValD(v_j_1732_, v_k_1733_);
v___x_1735_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(v___x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2___boxed(lean_object* v_j_1736_, lean_object* v_k_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_j_1736_, v_k_1737_);
lean_dec_ref(v_k_1737_);
return v_res_1738_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = 1;
v___x_1748_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__4));
v___x_1749_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1748_, v___x_1747_);
return v___x_1749_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__6));
v___x_1752_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__5, &l_Lean_Server_instFromJsonIlean_fromJson___closed__5_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5);
v___x_1753_ = lean_string_append(v___x_1752_, v___x_1751_);
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = 1;
v___x_1757_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__8));
v___x_1758_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1757_, v___x_1756_);
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__9, &l_Lean_Server_instFromJsonIlean_fromJson___closed__9_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9);
v___x_1760_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1761_ = lean_string_append(v___x_1760_, v___x_1759_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1764_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__10, &l_Lean_Server_instFromJsonIlean_fromJson___closed__10_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10);
v___x_1765_ = lean_string_append(v___x_1764_, v___x_1763_);
return v___x_1765_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = 1;
v___x_1770_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__14));
v___x_1771_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1770_, v___x_1769_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__15, &l_Lean_Server_instFromJsonIlean_fromJson___closed__15_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15);
v___x_1773_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1774_ = lean_string_append(v___x_1773_, v___x_1772_);
return v___x_1774_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1776_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__16, &l_Lean_Server_instFromJsonIlean_fromJson___closed__16_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16);
v___x_1777_ = lean_string_append(v___x_1776_, v___x_1775_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = 1;
v___x_1782_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__19));
v___x_1783_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1782_, v___x_1781_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__20, &l_Lean_Server_instFromJsonIlean_fromJson___closed__20_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20);
v___x_1785_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1786_ = lean_string_append(v___x_1785_, v___x_1784_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1787_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1788_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__21, &l_Lean_Server_instFromJsonIlean_fromJson___closed__21_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21);
v___x_1789_ = lean_string_append(v___x_1788_, v___x_1787_);
return v___x_1789_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = 1;
v___x_1794_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__24));
v___x_1795_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__25, &l_Lean_Server_instFromJsonIlean_fromJson___closed__25_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25);
v___x_1797_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1798_ = lean_string_append(v___x_1797_, v___x_1796_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1800_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__26, &l_Lean_Server_instFromJsonIlean_fromJson___closed__26_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26);
v___x_1801_ = lean_string_append(v___x_1800_, v___x_1799_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30(void){
_start:
{
uint8_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = 1;
v___x_1806_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__29));
v___x_1807_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1806_, v___x_1805_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__30, &l_Lean_Server_instFromJsonIlean_fromJson___closed__30_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30);
v___x_1809_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1810_ = lean_string_append(v___x_1809_, v___x_1808_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1812_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__31, &l_Lean_Server_instFromJsonIlean_fromJson___closed__31_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31);
v___x_1813_ = lean_string_append(v___x_1812_, v___x_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonIlean_fromJson(lean_object* v_json_1814_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
lean_inc(v_json_1814_);
v___x_1816_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(v_json_1814_, v___x_1815_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_json_1814_);
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1821_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__12, &l_Lean_Server_instFromJsonIlean_fromJson___closed__12_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12);
v___x_1822_ = lean_string_append(v___x_1821_, v_a_1817_);
lean_dec(v_a_1817_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1822_);
v___x_1824_ = v___x_1819_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_a_1827_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1816_, 1);
v___x_1828_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
lean_inc(v_json_1814_);
v___x_1829_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(v_json_1814_, v___x_1828_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_a_1827_);
lean_dec(v_json_1814_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1834_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__17, &l_Lean_Server_instFromJsonIlean_fromJson___closed__17_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17);
v___x_1835_ = lean_string_append(v___x_1834_, v_a_1830_);
lean_dec(v_a_1830_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1835_);
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v_a_1840_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1841_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
lean_inc(v_json_1814_);
v___x_1842_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_json_1814_, v___x_1841_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_a_1840_);
lean_dec(v_a_1827_);
lean_dec(v_json_1814_);
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1852_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1852_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1847_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__22, &l_Lean_Server_instFromJsonIlean_fromJson___closed__22_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22);
v___x_1848_ = lean_string_append(v___x_1847_, v_a_1843_);
lean_dec(v_a_1843_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1848_);
v___x_1850_ = v___x_1845_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_a_1853_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1854_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
lean_inc(v_json_1814_);
v___x_1855_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_json_1814_, v___x_1854_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_a_1853_);
lean_dec(v_a_1840_);
lean_dec(v_a_1827_);
lean_dec(v_json_1814_);
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1860_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__27, &l_Lean_Server_instFromJsonIlean_fromJson___closed__27_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27);
v___x_1861_ = lean_string_append(v___x_1860_, v_a_1856_);
lean_dec(v_a_1856_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1861_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_a_1866_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1867_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_1868_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(v_json_1814_, v___x_1867_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_a_1866_);
lean_dec(v_a_1853_);
lean_dec(v_a_1840_);
lean_dec(v_a_1827_);
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1873_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__32, &l_Lean_Server_instFromJsonIlean_fromJson___closed__32_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32);
v___x_1874_ = lean_string_append(v___x_1873_, v_a_1869_);
lean_dec(v_a_1869_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1887_; 
v_a_1879_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1881_ = v___x_1868_;
v_isShared_1882_ = v_isSharedCheck_1887_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1868_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1887_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1883_, 0, v_a_1827_);
lean_ctor_set(v___x_1883_, 1, v_a_1840_);
lean_ctor_set(v___x_1883_, 2, v_a_1853_);
lean_ctor_set(v___x_1883_, 3, v_a_1866_);
lean_ctor_set(v___x_1883_, 4, v_a_1879_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(size_t v_sz_1890_, size_t v_i_1891_, lean_object* v_bs_1892_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_usize_dec_lt(v_i_1891_, v_sz_1890_);
if (v___x_1893_ == 0)
{
return v_bs_1892_;
}
else
{
lean_object* v_v_1894_; lean_object* v_module_1895_; uint8_t v_isPrivate_1896_; uint8_t v_isAll_1897_; uint8_t v_isMeta_1898_; lean_object* v___x_1899_; lean_object* v_bs_x27_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; size_t v___x_1912_; size_t v___x_1913_; lean_object* v___x_1914_; 
v_v_1894_ = lean_array_uget_borrowed(v_bs_1892_, v_i_1891_);
v_module_1895_ = lean_ctor_get(v_v_1894_, 0);
lean_inc_ref(v_module_1895_);
v_isPrivate_1896_ = lean_ctor_get_uint8(v_v_1894_, sizeof(void*)*1);
v_isAll_1897_ = lean_ctor_get_uint8(v_v_1894_, sizeof(void*)*1 + 1);
v_isMeta_1898_ = lean_ctor_get_uint8(v_v_1894_, sizeof(void*)*1 + 2);
v___x_1899_ = lean_unsigned_to_nat(0u);
v_bs_x27_1900_ = lean_array_uset(v_bs_1892_, v_i_1891_, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1901_, 0, v_module_1895_);
v___x_1902_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1902_, 0, v_isPrivate_1896_);
v___x_1903_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1903_, 0, v_isAll_1897_);
v___x_1904_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1904_, 0, v_isMeta_1898_);
v___x_1905_ = lean_unsigned_to_nat(4u);
v___x_1906_ = lean_mk_empty_array_with_capacity(v___x_1905_);
v___x_1907_ = lean_array_push(v___x_1906_, v___x_1901_);
v___x_1908_ = lean_array_push(v___x_1907_, v___x_1902_);
v___x_1909_ = lean_array_push(v___x_1908_, v___x_1903_);
v___x_1910_ = lean_array_push(v___x_1909_, v___x_1904_);
v___x_1911_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
v___x_1912_ = ((size_t)1ULL);
v___x_1913_ = lean_usize_add(v_i_1891_, v___x_1912_);
v___x_1914_ = lean_array_uset(v_bs_x27_1900_, v_i_1891_, v___x_1911_);
v_i_1891_ = v___x_1913_;
v_bs_1892_ = v___x_1914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6___boxed(lean_object* v_sz_1916_, lean_object* v_i_1917_, lean_object* v_bs_1918_){
_start:
{
size_t v_sz_boxed_1919_; size_t v_i_boxed_1920_; lean_object* v_res_1921_; 
v_sz_boxed_1919_ = lean_unbox_usize(v_sz_1916_);
lean_dec(v_sz_1916_);
v_i_boxed_1920_ = lean_unbox_usize(v_i_1917_);
lean_dec(v_i_1917_);
v_res_1921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_boxed_1919_, v_i_boxed_1920_, v_bs_1918_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(lean_object* v_a_1922_){
_start:
{
size_t v_sz_1923_; size_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_sz_1923_ = lean_array_size(v_a_1922_);
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_1923_, v___x_1924_, v_a_1922_);
v___x_1926_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
if (lean_obj_tag(v_a_1927_) == 0)
{
lean_object* v___x_1929_; 
v___x_1929_ = l_List_reverse___redArg(v_a_1928_);
return v___x_1929_;
}
else
{
lean_object* v_head_1930_; lean_object* v_tail_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1941_; 
v_head_1930_ = lean_ctor_get(v_a_1927_, 0);
v_tail_1931_ = lean_ctor_get(v_a_1927_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_a_1927_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1933_ = v_a_1927_;
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_tail_1931_);
lean_inc(v_head_1930_);
lean_dec(v_a_1927_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1935_ = l_Lean_JsonNumber_fromNat(v_head_1930_);
v___x_1936_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v_a_1928_);
lean_ctor_set(v___x_1933_, 0, v___x_1936_);
v___x_1938_ = v___x_1933_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_a_1928_);
v___x_1938_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
v_a_1927_ = v_tail_1931_;
v_a_1928_ = v___x_1938_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(size_t v_sz_1942_, size_t v_i_1943_, lean_object* v_bs_1944_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_usize_dec_lt(v_i_1943_, v_sz_1942_);
if (v___x_1945_ == 0)
{
return v_bs_1944_;
}
else
{
lean_object* v_v_1946_; lean_object* v___x_1947_; lean_object* v_bs_x27_1948_; size_t v___x_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
v_v_1946_ = lean_array_uget(v_bs_1944_, v_i_1943_);
v___x_1947_ = lean_unsigned_to_nat(0u);
v_bs_x27_1948_ = lean_array_uset(v_bs_1944_, v_i_1943_, v___x_1947_);
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_add(v_i_1943_, v___x_1949_);
v___x_1951_ = lean_array_uset(v_bs_x27_1948_, v_i_1943_, v_v_1946_);
v_i_1943_ = v___x_1950_;
v_bs_1944_ = v___x_1951_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11___boxed(lean_object* v_sz_1953_, lean_object* v_i_1954_, lean_object* v_bs_1955_){
_start:
{
size_t v_sz_boxed_1956_; size_t v_i_boxed_1957_; lean_object* v_res_1958_; 
v_sz_boxed_1956_ = lean_unbox_usize(v_sz_1953_);
lean_dec(v_sz_1953_);
v_i_boxed_1957_ = lean_unbox_usize(v_i_1954_);
lean_dec(v_i_1954_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_boxed_1956_, v_i_boxed_1957_, v_bs_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(lean_object* v_a_1959_){
_start:
{
size_t v_sz_1960_; size_t v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_sz_1960_ = lean_array_size(v_a_1959_);
v___x_1961_ = ((size_t)0ULL);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_1960_, v___x_1961_, v_a_1959_);
v___x_1963_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_array_mk(v_a_1964_);
v___x_1966_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(v___x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(lean_object* v_x_1967_){
_start:
{
if (lean_obj_tag(v_x_1967_) == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_box(0);
return v___x_1968_;
}
else
{
lean_object* v_val_1969_; lean_object* v___x_1970_; 
v_val_1969_ = lean_ctor_get(v_x_1967_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v_x_1967_, 1);
v___x_1970_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_val_1969_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(size_t v_sz_1971_, size_t v_i_1972_, lean_object* v_bs_1973_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_lt(v_i_1972_, v_sz_1971_);
if (v___x_1974_ == 0)
{
return v_bs_1973_;
}
else
{
lean_object* v_v_1975_; lean_object* v_startPosLine_1976_; lean_object* v_startPosCharacter_1977_; lean_object* v_endPosLine_1978_; lean_object* v_endPosCharacter_1979_; lean_object* v___x_1980_; lean_object* v_bs_x27_1981_; lean_object* v___y_1983_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v_range_1993_; lean_object* v___x_1994_; 
v_v_1975_ = lean_array_uget(v_bs_1973_, v_i_1972_);
v_startPosLine_1976_ = lean_ctor_get(v_v_1975_, 0);
v_startPosCharacter_1977_ = lean_ctor_get(v_v_1975_, 1);
v_endPosLine_1978_ = lean_ctor_get(v_v_1975_, 2);
v_endPosCharacter_1979_ = lean_ctor_get(v_v_1975_, 3);
v___x_1980_ = lean_unsigned_to_nat(0u);
v_bs_x27_1981_ = lean_array_uset(v_bs_1973_, v_i_1972_, v___x_1980_);
v___x_1988_ = lean_box(0);
lean_inc(v_endPosCharacter_1979_);
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_endPosCharacter_1979_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
lean_inc(v_endPosLine_1978_);
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_endPosLine_1978_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
lean_inc(v_startPosCharacter_1977_);
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v_startPosCharacter_1977_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
lean_inc(v_startPosLine_1976_);
v___x_1992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1992_, 0, v_startPosLine_1976_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v_range_1993_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_1992_, v___x_1988_);
v___x_1994_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_1975_);
lean_dec(v_v_1975_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = l_List_appendTR___redArg(v_range_1993_, v___x_1988_);
v___y_1983_ = v___x_1995_;
goto v___jp_1982_;
}
else
{
lean_object* v_val_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2005_; 
v_val_1996_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1998_ = v___x_1994_;
v_isShared_1999_ = v_isSharedCheck_2005_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_val_1996_);
lean_dec(v___x_1994_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2005_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 3);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_val_1996_);
v___x_2001_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___x_1988_);
v___x_2003_ = l_List_appendTR___redArg(v_range_1993_, v___x_2002_);
v___y_1983_ = v___x_2003_;
goto v___jp_1982_;
}
}
}
v___jp_1982_:
{
size_t v___x_1984_; size_t v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = ((size_t)1ULL);
v___x_1985_ = lean_usize_add(v_i_1972_, v___x_1984_);
v___x_1986_ = lean_array_uset(v_bs_x27_1981_, v_i_1972_, v___y_1983_);
v_i_1972_ = v___x_1985_;
v_bs_1973_ = v___x_1986_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2___boxed(lean_object* v_sz_2006_, lean_object* v_i_2007_, lean_object* v_bs_2008_){
_start:
{
size_t v_sz_boxed_2009_; size_t v_i_boxed_2010_; lean_object* v_res_2011_; 
v_sz_boxed_2009_ = lean_unbox_usize(v_sz_2006_);
lean_dec(v_sz_2006_);
v_i_boxed_2010_ = lean_unbox_usize(v_i_2007_);
lean_dec(v_i_2007_);
v_res_2011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_boxed_2009_, v_i_boxed_2010_, v_bs_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(size_t v_sz_2012_, size_t v_i_2013_, lean_object* v_bs_2014_){
_start:
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_usize_dec_lt(v_i_2013_, v_sz_2012_);
if (v___x_2015_ == 0)
{
return v_bs_2014_;
}
else
{
lean_object* v_v_2016_; lean_object* v___x_2017_; lean_object* v_bs_x27_2018_; lean_object* v___x_2019_; size_t v___x_2020_; size_t v___x_2021_; lean_object* v___x_2022_; 
v_v_2016_ = lean_array_uget(v_bs_2014_, v_i_2013_);
v___x_2017_ = lean_unsigned_to_nat(0u);
v_bs_x27_2018_ = lean_array_uset(v_bs_2014_, v_i_2013_, v___x_2017_);
v___x_2019_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_v_2016_);
v___x_2020_ = ((size_t)1ULL);
v___x_2021_ = lean_usize_add(v_i_2013_, v___x_2020_);
v___x_2022_ = lean_array_uset(v_bs_x27_2018_, v_i_2013_, v___x_2019_);
v_i_2013_ = v___x_2021_;
v_bs_2014_ = v___x_2022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4___boxed(lean_object* v_sz_2024_, lean_object* v_i_2025_, lean_object* v_bs_2026_){
_start:
{
size_t v_sz_boxed_2027_; size_t v_i_boxed_2028_; lean_object* v_res_2029_; 
v_sz_boxed_2027_ = lean_unbox_usize(v_sz_2024_);
lean_dec(v_sz_2024_);
v_i_boxed_2028_ = lean_unbox_usize(v_i_2025_);
lean_dec(v_i_2025_);
v_res_2029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_boxed_2027_, v_i_boxed_2028_, v_bs_2026_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(lean_object* v_a_2030_){
_start:
{
size_t v_sz_2031_; size_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_sz_2031_ = lean_array_size(v_a_2030_);
v___x_2032_ = ((size_t)0ULL);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_2031_, v___x_2032_, v_a_2030_);
v___x_2034_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
if (lean_obj_tag(v_a_2035_) == 0)
{
lean_object* v___x_2037_; 
v___x_2037_ = l_List_reverse___redArg(v_a_2036_);
return v___x_2037_;
}
else
{
lean_object* v_head_2038_; lean_object* v_snd_2039_; lean_object* v_tail_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2109_; 
v_head_2038_ = lean_ctor_get(v_a_2035_, 0);
lean_inc(v_head_2038_);
v_snd_2039_ = lean_ctor_get(v_head_2038_, 1);
lean_inc(v_snd_2039_);
v_tail_2040_ = lean_ctor_get(v_a_2035_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_a_2035_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; 
v_unused_2110_ = lean_ctor_get(v_a_2035_, 0);
lean_dec(v_unused_2110_);
v___x_2042_ = v_a_2035_;
v_isShared_2043_ = v_isSharedCheck_2109_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_tail_2040_);
lean_dec(v_a_2035_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2109_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v_fst_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2107_; 
v_fst_2044_ = lean_ctor_get(v_head_2038_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_head_2038_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v_head_2038_, 1);
lean_dec(v_unused_2108_);
v___x_2046_ = v_head_2038_;
v_isShared_2047_ = v_isSharedCheck_2107_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_fst_2044_);
lean_dec(v_head_2038_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2107_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_definition_x3f_2048_; lean_object* v_usages_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2106_; 
v_definition_x3f_2048_ = lean_ctor_get(v_snd_2039_, 0);
v_usages_2049_ = lean_ctor_get(v_snd_2039_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_snd_2039_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2051_ = v_snd_2039_;
v_isShared_2052_ = v_isSharedCheck_2106_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_usages_2049_);
lean_inc(v_definition_x3f_2048_);
lean_dec(v_snd_2039_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2106_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___y_2057_; lean_object* v___y_2080_; 
v___x_2053_ = l_Lean_Lsp_RefIdent_toJson(v_fst_2044_);
v___x_2054_ = l_Lean_Json_compress(v___x_2053_);
v___x_2055_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
if (lean_obj_tag(v_definition_x3f_2048_) == 0)
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_box(0);
v___y_2057_ = v___x_2082_;
goto v___jp_2056_;
}
else
{
lean_object* v_val_2083_; lean_object* v_startPosLine_2084_; lean_object* v_startPosCharacter_2085_; lean_object* v_endPosLine_2086_; lean_object* v_endPosCharacter_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v_range_2093_; lean_object* v___x_2094_; 
v_val_2083_ = lean_ctor_get(v_definition_x3f_2048_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v_definition_x3f_2048_, 1);
v_startPosLine_2084_ = lean_ctor_get(v_val_2083_, 0);
v_startPosCharacter_2085_ = lean_ctor_get(v_val_2083_, 1);
v_endPosLine_2086_ = lean_ctor_get(v_val_2083_, 2);
v_endPosCharacter_2087_ = lean_ctor_get(v_val_2083_, 3);
v___x_2088_ = lean_box(0);
lean_inc(v_endPosCharacter_2087_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v_endPosCharacter_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
lean_inc(v_endPosLine_2086_);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v_endPosLine_2086_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
lean_inc(v_startPosCharacter_2085_);
v___x_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2091_, 0, v_startPosCharacter_2085_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
lean_inc(v_startPosLine_2084_);
v___x_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2092_, 0, v_startPosLine_2084_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v_range_2093_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_2092_, v___x_2088_);
v___x_2094_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_2083_);
lean_dec(v_val_2083_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; 
v___x_2095_ = l_List_appendTR___redArg(v_range_2093_, v___x_2088_);
v___y_2080_ = v___x_2095_;
goto v___jp_2079_;
}
else
{
lean_object* v_val_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2105_; 
v_val_2096_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2098_ = v___x_2094_;
v_isShared_2099_ = v_isSharedCheck_2105_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_val_2096_);
lean_dec(v___x_2094_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2105_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 3);
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_val_2096_);
v___x_2101_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v___x_2088_);
v___x_2103_ = l_List_appendTR___redArg(v_range_2093_, v___x_2102_);
v___y_2080_ = v___x_2103_;
goto v___jp_2079_;
}
}
}
}
v___jp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = l_Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(v___y_2057_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v___x_2058_);
lean_ctor_set(v___x_2046_, 0, v___x_2055_);
v___x_2060_ = v___x_2046_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; size_t v_sz_2062_; size_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2061_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v_sz_2062_ = lean_array_size(v_usages_2049_);
v___x_2063_ = ((size_t)0ULL);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_2062_, v___x_2063_, v_usages_2049_);
v___x_2065_ = l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(v___x_2064_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2065_);
lean_ctor_set(v___x_2051_, 0, v___x_2061_);
v___x_2067_ = v___x_2051_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_box(0);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 1, v___x_2068_);
lean_ctor_set(v___x_2042_, 0, v___x_2067_);
v___x_2070_ = v___x_2042_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2060_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = l_Lean_Json_mkObj(v___x_2071_);
lean_dec_ref_known(v___x_2071_, 2);
v___x_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2054_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v_a_2036_);
v_a_2035_ = v_tail_2040_;
v_a_2036_ = v___x_2074_;
goto _start;
}
}
}
}
v___jp_2079_:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___y_2080_);
v___y_2057_ = v___x_2081_;
goto v___jp_2056_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(lean_object* v_init_2111_, lean_object* v_x_2112_){
_start:
{
if (lean_obj_tag(v_x_2112_) == 0)
{
lean_object* v_k_2113_; lean_object* v_v_2114_; lean_object* v_l_2115_; lean_object* v_r_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_k_2113_ = lean_ctor_get(v_x_2112_, 1);
v_v_2114_ = lean_ctor_get(v_x_2112_, 2);
v_l_2115_ = lean_ctor_get(v_x_2112_, 3);
v_r_2116_ = lean_ctor_get(v_x_2112_, 4);
v___x_2117_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2111_, v_r_2116_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v_k_2113_);
lean_ctor_set(v___x_2118_, 1, v_v_2114_);
v___x_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v___x_2117_);
v_init_2111_ = v___x_2119_;
v_x_2112_ = v_l_2115_;
goto _start;
}
else
{
return v_init_2111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5___boxed(lean_object* v_init_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2121_, v_x_2122_);
lean_dec(v_x_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
if (lean_obj_tag(v_a_2124_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = l_List_reverse___redArg(v_a_2125_);
return v___x_2126_;
}
else
{
lean_object* v_head_2127_; lean_object* v_snd_2128_; lean_object* v_tail_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2181_; 
v_head_2127_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_head_2127_);
v_snd_2128_ = lean_ctor_get(v_head_2127_, 1);
lean_inc(v_snd_2128_);
v_tail_2129_ = lean_ctor_get(v_a_2124_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_a_2124_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v_a_2124_, 0);
lean_dec(v_unused_2182_);
v___x_2131_ = v_a_2124_;
v_isShared_2132_ = v_isSharedCheck_2181_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_tail_2129_);
lean_dec(v_a_2124_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2181_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v_fst_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2179_; 
v_fst_2133_ = lean_ctor_get(v_head_2127_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_head_2127_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; 
v_unused_2180_ = lean_ctor_get(v_head_2127_, 1);
lean_dec(v_unused_2180_);
v___x_2135_ = v_head_2127_;
v_isShared_2136_ = v_isSharedCheck_2179_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_fst_2133_);
lean_dec(v_head_2127_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2179_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_rangeStartPosLine_2137_; lean_object* v_rangeStartPosCharacter_2138_; lean_object* v_rangeEndPosLine_2139_; lean_object* v_rangeEndPosCharacter_2140_; lean_object* v_selectionRangeStartPosLine_2141_; lean_object* v_selectionRangeStartPosCharacter_2142_; lean_object* v_selectionRangeEndPosLine_2143_; lean_object* v_selectionRangeEndPosCharacter_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v_rangeStartPosLine_2137_ = lean_ctor_get(v_snd_2128_, 0);
lean_inc(v_rangeStartPosLine_2137_);
v_rangeStartPosCharacter_2138_ = lean_ctor_get(v_snd_2128_, 1);
lean_inc(v_rangeStartPosCharacter_2138_);
v_rangeEndPosLine_2139_ = lean_ctor_get(v_snd_2128_, 2);
lean_inc(v_rangeEndPosLine_2139_);
v_rangeEndPosCharacter_2140_ = lean_ctor_get(v_snd_2128_, 3);
lean_inc(v_rangeEndPosCharacter_2140_);
v_selectionRangeStartPosLine_2141_ = lean_ctor_get(v_snd_2128_, 4);
lean_inc(v_selectionRangeStartPosLine_2141_);
v_selectionRangeStartPosCharacter_2142_ = lean_ctor_get(v_snd_2128_, 5);
lean_inc(v_selectionRangeStartPosCharacter_2142_);
v_selectionRangeEndPosLine_2143_ = lean_ctor_get(v_snd_2128_, 6);
lean_inc(v_selectionRangeEndPosLine_2143_);
v_selectionRangeEndPosCharacter_2144_ = lean_ctor_get(v_snd_2128_, 7);
lean_inc(v_selectionRangeEndPosCharacter_2144_);
lean_dec(v_snd_2128_);
v___x_2145_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_2137_);
v___x_2146_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
v___x_2147_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_2138_);
v___x_2148_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
v___x_2149_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_2139_);
v___x_2150_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
v___x_2151_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_2140_);
v___x_2152_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
v___x_2153_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_2141_);
v___x_2154_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
v___x_2155_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_2142_);
v___x_2156_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
v___x_2157_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_2143_);
v___x_2158_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
v___x_2159_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_2144_);
v___x_2160_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
v___x_2161_ = lean_unsigned_to_nat(8u);
v___x_2162_ = lean_mk_empty_array_with_capacity(v___x_2161_);
v___x_2163_ = lean_array_push(v___x_2162_, v___x_2146_);
v___x_2164_ = lean_array_push(v___x_2163_, v___x_2148_);
v___x_2165_ = lean_array_push(v___x_2164_, v___x_2150_);
v___x_2166_ = lean_array_push(v___x_2165_, v___x_2152_);
v___x_2167_ = lean_array_push(v___x_2166_, v___x_2154_);
v___x_2168_ = lean_array_push(v___x_2167_, v___x_2156_);
v___x_2169_ = lean_array_push(v___x_2168_, v___x_2158_);
v___x_2170_ = lean_array_push(v___x_2169_, v___x_2160_);
v___x_2171_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 1, v___x_2171_);
v___x_2173_ = v___x_2135_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_fst_2133_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 1, v_a_2125_);
lean_ctor_set(v___x_2131_, 0, v___x_2173_);
v___x_2175_ = v___x_2131_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_a_2125_);
v___x_2175_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
v_a_2124_ = v_tail_2129_;
v_a_2125_ = v___x_2175_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
if (lean_obj_tag(v_a_2183_) == 0)
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_array_to_list(v_a_2184_);
return v___x_2185_;
}
else
{
lean_object* v_head_2186_; lean_object* v_tail_2187_; lean_object* v___x_2188_; 
v_head_2186_ = lean_ctor_get(v_a_2183_, 0);
lean_inc(v_head_2186_);
v_tail_2187_ = lean_ctor_get(v_a_2183_, 1);
lean_inc(v_tail_2187_);
lean_dec_ref_known(v_a_2183_, 2);
v___x_2188_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2184_, v_head_2186_);
v_a_2183_ = v_tail_2187_;
v_a_2184_ = v___x_2188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(lean_object* v_init_2190_, lean_object* v_x_2191_){
_start:
{
if (lean_obj_tag(v_x_2191_) == 0)
{
lean_object* v_k_2192_; lean_object* v_v_2193_; lean_object* v_l_2194_; lean_object* v_r_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_k_2192_ = lean_ctor_get(v_x_2191_, 1);
v_v_2193_ = lean_ctor_get(v_x_2191_, 2);
v_l_2194_ = lean_ctor_get(v_x_2191_, 3);
v_r_2195_ = lean_ctor_get(v_x_2191_, 4);
v___x_2196_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2190_, v_r_2195_);
lean_inc(v_v_2193_);
lean_inc(v_k_2192_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_k_2192_);
lean_ctor_set(v___x_2197_, 1, v_v_2193_);
v___x_2198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
lean_ctor_set(v___x_2198_, 1, v___x_2196_);
v_init_2190_ = v___x_2198_;
v_x_2191_ = v_l_2194_;
goto _start;
}
else
{
return v_init_2190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7___boxed(lean_object* v_init_2200_, lean_object* v_x_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2200_, v_x_2201_);
lean_dec(v_x_2201_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonIlean_toJson(lean_object* v_x_2205_){
_start:
{
lean_object* v_version_2206_; lean_object* v_module_2207_; lean_object* v_directImports_2208_; lean_object* v_references_2209_; lean_object* v_decls_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_version_2206_ = lean_ctor_get(v_x_2205_, 0);
lean_inc(v_version_2206_);
v_module_2207_ = lean_ctor_get(v_x_2205_, 1);
lean_inc(v_module_2207_);
v_directImports_2208_ = lean_ctor_get(v_x_2205_, 2);
lean_inc_ref(v_directImports_2208_);
v_references_2209_ = lean_ctor_get(v_x_2205_, 3);
lean_inc(v_references_2209_);
v_decls_2210_ = lean_ctor_get(v_x_2205_, 4);
lean_inc(v_decls_2210_);
lean_dec_ref(v_x_2205_);
v___x_2211_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
v___x_2212_ = l_Lean_JsonNumber_fromNat(v_version_2206_);
v___x_2213_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2211_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
v___x_2218_ = 1;
v___x_2219_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_2207_, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2217_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2215_);
v___x_2223_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
v___x_2224_ = l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(v_directImports_2208_);
v___x_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v___x_2215_);
v___x_2227_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
v___x_2228_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v___x_2215_, v_references_2209_);
lean_dec(v_references_2209_);
v___x_2229_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(v___x_2228_, v___x_2215_);
v___x_2230_ = l_Lean_Json_mkObj(v___x_2229_);
lean_dec(v___x_2229_);
v___x_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2227_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2215_);
v___x_2233_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_2234_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v___x_2215_, v_decls_2210_);
lean_dec(v_decls_2210_);
v___x_2235_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(v___x_2234_, v___x_2215_);
v___x_2236_ = l_Lean_Json_mkObj(v___x_2235_);
lean_dec(v___x_2235_);
v___x_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2233_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v___x_2215_);
v___x_2239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___x_2215_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2232_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2226_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2222_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2216_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = ((lean_object*)(l_Lean_Server_instToJsonIlean_toJson___closed__0));
v___x_2245_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(v___x_2243_, v___x_2244_);
v___x_2246_ = l_Lean_Json_mkObj(v___x_2245_);
lean_dec(v___x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1(lean_object* v_compactedIleanPath_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___closed__0));
v___x_2256_ = lean_compacted_region_read(v_compactedIleanPath_2253_, v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___boxed(lean_object* v_compactedIleanPath_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1(v_compactedIleanPath_2257_);
lean_dec_ref(v_compactedIleanPath_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_loadCompacted_x3f(lean_object* v_ileanPath_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2267_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc_ref(v_ileanPath_2265_);
v___x_2268_ = l_System_FilePath_extension(v_ileanPath_2265_);
v___x_2269_ = ((lean_object*)(l_Lean_Server_Ilean_loadCompacted_x3f___closed__1));
v___x_2270_ = l_Option_instDecidableEq___redArg(v___x_2267_, v___x_2268_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2271_ = ((lean_object*)(l_Lean_Server_Ilean_loadCompacted_x3f___closed__2));
v___x_2272_ = lean_string_append(v___x_2271_, v_ileanPath_2265_);
lean_dec_ref(v_ileanPath_2265_);
v___x_2273_ = ((lean_object*)(l_Lean_Server_Ilean_loadCompacted_x3f___closed__3));
v___x_2274_ = lean_string_append(v___x_2272_, v___x_2273_);
v___x_2275_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
return v___x_2276_;
}
else
{
lean_object* v___x_2277_; lean_object* v_compactedIleanPath_2278_; lean_object* v___x_2279_; 
v___x_2277_ = ((lean_object*)(l_Lean_Server_Ilean_compactedExt___closed__0));
lean_inc_ref(v_ileanPath_2265_);
v_compactedIleanPath_2278_ = l_System_FilePath_withExtension(v_ileanPath_2265_, v___x_2277_);
v___x_2279_ = lean_io_metadata(v_compactedIleanPath_2278_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v_modified_2281_; lean_object* v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v_modified_2281_ = lean_ctor_get(v_a_2280_, 1);
lean_inc_ref(v_modified_2281_);
lean_dec(v_a_2280_);
v___x_2282_ = lean_io_metadata(v_ileanPath_2265_);
lean_dec_ref(v_ileanPath_2265_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2313_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2313_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2313_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_modified_2287_; uint8_t v___x_2288_; 
v_modified_2287_ = lean_ctor_get(v_a_2283_, 1);
lean_inc_ref(v_modified_2287_);
lean_dec(v_a_2283_);
v___x_2288_ = l_IO_FS_instOrdSystemTime_ord(v_modified_2281_, v_modified_2287_);
lean_dec_ref(v_modified_2287_);
lean_dec_ref(v_modified_2281_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
lean_dec_ref(v_compactedIleanPath_2278_);
v___x_2289_ = lean_box(0);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2289_);
v___x_2291_ = v___x_2285_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_del_object(v___x_2285_);
v___x_2293_ = ((lean_object*)(l___private_Lean_Server_References_0__Lean_Server_Ilean_loadCompacted_x3f_unsafe__1___closed__0));
v___x_2294_ = lean_compacted_region_read(v_compactedIleanPath_2278_, v___x_2293_);
lean_dec_ref(v_compactedIleanPath_2278_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2304_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2304_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2304_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_fst_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v_fst_2299_ = lean_ctor_get(v_a_2295_, 0);
lean_inc(v_fst_2299_);
lean_dec(v_a_2295_);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_fst_2299_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2300_);
v___x_2302_ = v___x_2297_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
v_a_2305_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2294_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2294_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_modified_2281_);
lean_dec_ref(v_compactedIleanPath_2278_);
v_a_2314_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2282_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2282_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2329_; 
lean_dec_ref(v_compactedIleanPath_2278_);
lean_dec_ref(v_ileanPath_2265_);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2279_, 0);
lean_dec(v_unused_2330_);
v___x_2323_ = v___x_2279_;
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
else
{
lean_dec(v___x_2279_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = lean_box(0);
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2325_);
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_loadCompacted_x3f___boxed(lean_object* v_ileanPath_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_Server_Ilean_loadCompacted_x3f(v_ileanPath_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load(lean_object* v_path_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_IO_FS_readFile(v_path_2335_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2359_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2359_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2359_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v_a_2343_; lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Json_parse(v_a_2338_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; 
lean_del_object(v___x_2340_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v_a_2343_ = v_a_2351_;
goto v___jp_2342_;
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2353_; 
v_a_2352_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2350_, 1);
v___x_2353_ = l_Lean_Server_instFromJsonIlean_fromJson(v_a_2352_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; 
lean_del_object(v___x_2340_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v_a_2343_ = v_a_2354_;
goto v___jp_2342_;
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; 
v_a_2355_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2353_, 1);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v_a_2355_);
v___x_2357_ = v___x_2340_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
v___jp_2342_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2344_ = ((lean_object*)(l_Lean_Server_Ilean_load___closed__0));
v___x_2345_ = lean_string_append(v___x_2344_, v_path_2335_);
v___x_2346_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_2347_ = lean_string_append(v___x_2345_, v___x_2346_);
v___x_2348_ = lean_string_append(v___x_2347_, v_a_2343_);
lean_dec_ref(v_a_2343_);
v___x_2349_ = l_Lean_IO_throwServerError___redArg(v___x_2348_);
return v___x_2349_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2337_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2337_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load___boxed(lean_object* v_path_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_Server_Ilean_load(v_path_2368_);
lean_dec_ref(v_path_2368_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f(lean_object* v_env_2371_, lean_object* v_declName_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2371_, v_declName_2372_);
if (lean_obj_tag(v___x_2373_) == 1)
{
lean_object* v_val_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2386_; 
v_val_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_val_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2378_ = l_Lean_Environment_allImportedModuleNames(v_env_2371_);
v___x_2379_ = lean_array_get_size(v___x_2378_);
v___x_2380_ = lean_nat_dec_lt(v_val_2374_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
lean_dec_ref(v___x_2378_);
lean_del_object(v___x_2376_);
lean_dec(v_val_2374_);
v___x_2381_ = lean_box(0);
return v___x_2381_;
}
else
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2382_ = lean_array_fget(v___x_2378_, v_val_2374_);
lean_dec(v_val_2374_);
lean_dec_ref(v___x_2378_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2382_);
v___x_2384_ = v___x_2376_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v___x_2387_; lean_object* v_mainModule_2388_; lean_object* v___x_2389_; 
lean_dec(v___x_2373_);
v___x_2387_ = l_Lean_Environment_header(v_env_2371_);
v_mainModule_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_mainModule_2388_);
lean_dec_ref(v___x_2387_);
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_mainModule_2388_);
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f___boxed(lean_object* v_env_2390_, lean_object* v_declName_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2390_, v_declName_2391_);
lean_dec(v_declName_2391_);
lean_dec_ref(v_env_2390_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf(lean_object* v_ci_2393_, lean_object* v_i_2394_){
_start:
{
switch(lean_obj_tag(v_i_2394_))
{
case 1:
{
lean_object* v_i_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2436_; 
v_i_2395_ = lean_ctor_get(v_i_2394_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_i_2394_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2397_ = v_i_2394_;
v_isShared_2398_ = v_isSharedCheck_2436_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_i_2395_);
lean_dec(v_i_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2436_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_expr_2399_; 
v_expr_2399_ = lean_ctor_get(v_i_2395_, 3);
lean_inc_ref(v_expr_2399_);
switch(lean_obj_tag(v_expr_2399_))
{
case 4:
{
lean_object* v_toCommandContextInfo_2400_; uint8_t v_isBinder_2401_; lean_object* v_declName_2402_; lean_object* v_env_2403_; lean_object* v___x_2404_; 
lean_del_object(v___x_2397_);
v_toCommandContextInfo_2400_ = lean_ctor_get(v_ci_2393_, 0);
v_isBinder_2401_ = lean_ctor_get_uint8(v_i_2395_, sizeof(void*)*4);
lean_dec_ref(v_i_2395_);
v_declName_2402_ = lean_ctor_get(v_expr_2399_, 0);
lean_inc(v_declName_2402_);
lean_dec_ref_known(v_expr_2399_, 2);
v_env_2403_ = lean_ctor_get(v_toCommandContextInfo_2400_, 0);
v___x_2404_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2403_, v_declName_2402_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v___x_2405_; 
lean_dec(v_declName_2402_);
v___x_2405_ = lean_box(0);
return v___x_2405_;
}
else
{
lean_object* v_val_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2419_; 
v_val_2406_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2408_ = v___x_2404_;
v_isShared_2409_ = v_isSharedCheck_2419_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_val_2406_);
lean_dec(v___x_2404_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2419_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2410_ = 1;
v___x_2411_ = l_Lean_Name_toString(v_val_2406_, v___x_2410_);
v___x_2412_ = l_Lean_Name_toString(v_declName_2402_, v___x_2410_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_box(v_isBinder_2401_);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2415_);
v___x_2417_ = v___x_2408_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
case 1:
{
lean_object* v_toCommandContextInfo_2420_; uint8_t v_isBinder_2421_; lean_object* v_fvarId_2422_; lean_object* v_env_2423_; lean_object* v___x_2424_; lean_object* v_mainModule_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v_toCommandContextInfo_2420_ = lean_ctor_get(v_ci_2393_, 0);
v_isBinder_2421_ = lean_ctor_get_uint8(v_i_2395_, sizeof(void*)*4);
lean_dec_ref(v_i_2395_);
v_fvarId_2422_ = lean_ctor_get(v_expr_2399_, 0);
lean_inc(v_fvarId_2422_);
lean_dec_ref_known(v_expr_2399_, 1);
v_env_2423_ = lean_ctor_get(v_toCommandContextInfo_2420_, 0);
v___x_2424_ = l_Lean_Environment_header(v_env_2423_);
v_mainModule_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_mainModule_2425_);
lean_dec_ref(v___x_2424_);
v___x_2426_ = 1;
v___x_2427_ = l_Lean_Name_toString(v_mainModule_2425_, v___x_2426_);
v___x_2428_ = l_Lean_Name_toString(v_fvarId_2422_, v___x_2426_);
v___x_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = lean_box(v_isBinder_2421_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2431_);
v___x_2433_ = v___x_2397_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
default: 
{
lean_object* v___x_2435_; 
lean_dec_ref(v_expr_2399_);
lean_del_object(v___x_2397_);
lean_dec_ref(v_i_2395_);
v___x_2435_ = lean_box(0);
return v___x_2435_;
}
}
}
}
case 7:
{
lean_object* v_toCommandContextInfo_2437_; lean_object* v_i_2438_; lean_object* v_env_2439_; lean_object* v_projName_2440_; lean_object* v___x_2441_; 
v_toCommandContextInfo_2437_ = lean_ctor_get(v_ci_2393_, 0);
v_i_2438_ = lean_ctor_get(v_i_2394_, 0);
lean_inc_ref(v_i_2438_);
lean_dec_ref_known(v_i_2394_, 1);
v_env_2439_ = lean_ctor_get(v_toCommandContextInfo_2437_, 0);
v_projName_2440_ = lean_ctor_get(v_i_2438_, 0);
lean_inc(v_projName_2440_);
lean_dec_ref(v_i_2438_);
v___x_2441_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2439_, v_projName_2440_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v___x_2442_; 
lean_dec(v_projName_2440_);
v___x_2442_ = lean_box(0);
return v___x_2442_;
}
else
{
lean_object* v_val_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2457_; 
v_val_2443_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2445_ = v___x_2441_;
v_isShared_2446_ = v_isSharedCheck_2457_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_val_2443_);
lean_dec(v___x_2441_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2457_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2447_ = 1;
v___x_2448_ = l_Lean_Name_toString(v_val_2443_, v___x_2447_);
v___x_2449_ = l_Lean_Name_toString(v_projName_2440_, v___x_2447_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = 0;
v___x_2452_ = lean_box(v___x_2451_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2450_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2453_);
v___x_2455_ = v___x_2445_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
case 5:
{
lean_object* v_toCommandContextInfo_2458_; lean_object* v_i_2459_; lean_object* v_env_2460_; lean_object* v_declName_2461_; lean_object* v___x_2462_; 
v_toCommandContextInfo_2458_ = lean_ctor_get(v_ci_2393_, 0);
v_i_2459_ = lean_ctor_get(v_i_2394_, 0);
lean_inc_ref(v_i_2459_);
lean_dec_ref_known(v_i_2394_, 1);
v_env_2460_ = lean_ctor_get(v_toCommandContextInfo_2458_, 0);
v_declName_2461_ = lean_ctor_get(v_i_2459_, 2);
lean_inc(v_declName_2461_);
lean_dec_ref(v_i_2459_);
v___x_2462_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2460_, v_declName_2461_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v___x_2463_; 
lean_dec(v_declName_2461_);
v___x_2463_ = lean_box(0);
return v___x_2463_;
}
else
{
lean_object* v_val_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2478_; 
v_val_2464_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2466_ = v___x_2462_;
v_isShared_2467_ = v_isSharedCheck_2478_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_val_2464_);
lean_dec(v___x_2462_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2478_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2468_ = 1;
v___x_2469_ = l_Lean_Name_toString(v_val_2464_, v___x_2468_);
v___x_2470_ = l_Lean_Name_toString(v_declName_2461_, v___x_2468_);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = 0;
v___x_2473_ = lean_box(v___x_2472_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2471_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2474_);
v___x_2476_ = v___x_2466_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
case 17:
{
lean_object* v_toCommandContextInfo_2479_; lean_object* v_i_2480_; lean_object* v_env_2481_; lean_object* v_name_2482_; lean_object* v___x_2483_; 
v_toCommandContextInfo_2479_ = lean_ctor_get(v_ci_2393_, 0);
v_i_2480_ = lean_ctor_get(v_i_2394_, 0);
lean_inc_ref(v_i_2480_);
lean_dec_ref_known(v_i_2394_, 1);
v_env_2481_ = lean_ctor_get(v_toCommandContextInfo_2479_, 0);
v_name_2482_ = lean_ctor_get(v_i_2480_, 1);
lean_inc(v_name_2482_);
lean_dec_ref(v_i_2480_);
v___x_2483_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2481_, v_name_2482_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v___x_2484_; 
lean_dec(v_name_2482_);
v___x_2484_ = lean_box(0);
return v___x_2484_;
}
else
{
lean_object* v_val_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2499_; 
v_val_2485_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2487_ = v___x_2483_;
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_val_2485_);
lean_dec(v___x_2483_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
uint8_t v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2489_ = 1;
v___x_2490_ = l_Lean_Name_toString(v_val_2485_, v___x_2489_);
v___x_2491_ = l_Lean_Name_toString(v_name_2482_, v___x_2489_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = 0;
v___x_2494_ = lean_box(v___x_2493_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2492_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2495_);
v___x_2497_ = v___x_2487_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
default: 
{
lean_object* v___x_2500_; 
lean_dec_ref(v_i_2394_);
v___x_2500_ = lean_box(0);
return v___x_2500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf___boxed(lean_object* v_ci_2501_, lean_object* v_i_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_Server_identOf(v_ci_2501_, v_i_2502_);
lean_dec_ref(v_ci_2501_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(uint8_t v___x_2504_, lean_object* v_x_2505_, lean_object* v_x_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_box(v___x_2504_);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___y_2508_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed(lean_object* v___x_2511_, lean_object* v_x_2512_, lean_object* v_x_2513_, lean_object* v_x_2514_, lean_object* v___y_2515_){
_start:
{
uint8_t v___x_3525__boxed_2516_; lean_object* v_res_2517_; 
v___x_3525__boxed_2516_ = lean_unbox(v___x_2511_);
v_res_2517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(v___x_3525__boxed_2516_, v_x_2512_, v_x_2513_, v_x_2514_, v___y_2515_);
lean_dec_ref(v_x_2514_);
lean_dec_ref(v_x_2513_);
lean_dec_ref(v_x_2512_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(lean_object* v_text_2518_, lean_object* v_ci_2519_, lean_object* v_info_2520_, lean_object* v_x_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2523_; 
lean_inc_ref(v_info_2520_);
v___x_2523_ = l_Lean_Server_identOf(v_ci_2519_, v_info_2520_);
if (lean_obj_tag(v___x_2523_) == 1)
{
lean_object* v_val_2524_; lean_object* v_fst_2525_; lean_object* v_snd_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2551_; 
v_val_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v_fst_2525_ = lean_ctor_get(v_val_2524_, 0);
v_snd_2526_ = lean_ctor_get(v_val_2524_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_val_2524_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2528_ = v_val_2524_;
v_isShared_2529_ = v_isSharedCheck_2551_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_snd_2526_);
lean_inc(v_fst_2525_);
lean_dec(v_val_2524_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2551_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Elab_Info_range_x3f(v_info_2520_);
if (lean_obj_tag(v___x_2530_) == 1)
{
lean_object* v_val_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_val_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_val_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = l_Lean_Elab_Info_stx(v_info_2520_);
v___x_2533_ = l_Lean_Syntax_getHeadInfo(v___x_2532_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_dec_ref_known(v___x_2533_, 4);
v___x_2534_ = lean_box(0);
v___x_2535_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_2536_ = l_Lean_Syntax_Range_toLspRange(v_text_2518_, v_val_2531_);
v___x_2537_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2537_, 0, v_fst_2525_);
lean_ctor_set(v___x_2537_, 1, v___x_2535_);
lean_ctor_set(v___x_2537_, 2, v___x_2536_);
lean_ctor_set(v___x_2537_, 3, v___x_2532_);
lean_ctor_set(v___x_2537_, 4, v_ci_2519_);
lean_ctor_set(v___x_2537_, 5, v_info_2520_);
v___x_2538_ = lean_unbox(v_snd_2526_);
lean_dec(v_snd_2526_);
lean_ctor_set_uint8(v___x_2537_, sizeof(void*)*6, v___x_2538_);
v___x_2539_ = lean_array_push(v___y_2522_, v___x_2537_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2539_);
lean_ctor_set(v___x_2528_, 0, v___x_2534_);
v___x_2541_ = v___x_2528_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_dec(v___x_2533_);
lean_dec(v___x_2532_);
lean_dec(v_val_2531_);
lean_dec(v_snd_2526_);
lean_dec(v_fst_2525_);
lean_dec_ref(v_info_2520_);
lean_dec_ref(v_ci_2519_);
lean_dec_ref(v_text_2518_);
v___x_2543_ = lean_box(0);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___y_2522_);
lean_ctor_set(v___x_2528_, 0, v___x_2543_);
v___x_2545_ = v___x_2528_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v___y_2522_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_dec(v___x_2530_);
lean_dec(v_snd_2526_);
lean_dec(v_fst_2525_);
lean_dec_ref(v_info_2520_);
lean_dec_ref(v_ci_2519_);
lean_dec_ref(v_text_2518_);
v___x_2547_ = lean_box(0);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___y_2522_);
lean_ctor_set(v___x_2528_, 0, v___x_2547_);
v___x_2549_ = v___x_2528_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v___y_2522_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v___x_2523_);
lean_dec_ref(v_info_2520_);
lean_dec_ref(v_ci_2519_);
lean_dec_ref(v_text_2518_);
v___x_2552_ = lean_box(0);
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
lean_ctor_set(v___x_2553_, 1, v___y_2522_);
return v___x_2553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed(lean_object* v_text_2554_, lean_object* v_ci_2555_, lean_object* v_info_2556_, lean_object* v_x_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(v_text_2554_, v_ci_2555_, v_info_2556_, v_x_2557_, v___y_2558_);
lean_dec_ref(v_x_2557_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v___f_2574_; lean_object* v___f_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___f_2581_; lean_object* v___f_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_3116__overap_2591_; lean_object* v___x_2592_; 
v___f_2569_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_2570_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_2571_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_2572_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_2573_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_2574_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_2575_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___f_2569_);
lean_ctor_set(v___x_2576_, 1, v___f_2570_);
v___x_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___f_2571_);
lean_ctor_set(v___x_2577_, 2, v___f_2572_);
lean_ctor_set(v___x_2577_, 3, v___f_2573_);
lean_ctor_set(v___x_2577_, 4, v___f_2574_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
lean_ctor_set(v___x_2578_, 1, v___f_2575_);
lean_inc_ref_n(v___x_2578_, 6);
v___f_2579_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2579_, 0, v___x_2578_);
v___f_2580_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2580_, 0, v___x_2578_);
v___f_2581_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2581_, 0, v___x_2578_);
v___f_2582_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2582_, 0, v___x_2578_);
v___x_2583_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2583_, 0, lean_box(0));
lean_closure_set(v___x_2583_, 1, lean_box(0));
lean_closure_set(v___x_2583_, 2, v___x_2578_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___f_2579_);
v___x_2585_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2585_, 0, lean_box(0));
lean_closure_set(v___x_2585_, 1, lean_box(0));
lean_closure_set(v___x_2585_, 2, v___x_2578_);
v___x_2586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
lean_ctor_set(v___x_2586_, 2, v___f_2580_);
lean_ctor_set(v___x_2586_, 3, v___f_2581_);
lean_ctor_set(v___x_2586_, 4, v___f_2582_);
v___x_2587_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2587_, 0, lean_box(0));
lean_closure_set(v___x_2587_, 1, lean_box(0));
lean_closure_set(v___x_2587_, 2, v___x_2578_);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = lean_box(0);
v___x_2590_ = l_instInhabitedOfMonad___redArg(v___x_2588_, v___x_2589_);
v___x_3116__overap_2591_ = lean_panic_fn_borrowed(v___x_2590_, v_msg_2567_);
lean_dec(v___x_2590_);
v___x_2592_ = lean_apply_1(v___x_3116__overap_2591_, v___y_2568_);
return v___x_2592_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2596_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2));
v___x_2597_ = lean_unsigned_to_nat(21u);
v___x_2598_ = lean_unsigned_to_nat(65u);
v___x_2599_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1));
v___x_2600_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0));
v___x_2601_ = l_mkPanicMessageWithDecl(v___x_2600_, v___x_2599_, v___x_2598_, v___x_2597_, v___x_2596_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object* v_preNode_2602_, lean_object* v_postNode_2603_, lean_object* v_x_2604_, lean_object* v_x_2605_, lean_object* v___y_2606_){
_start:
{
switch(lean_obj_tag(v_x_2605_))
{
case 0:
{
lean_object* v_i_2607_; lean_object* v_t_2608_; lean_object* v___x_2609_; 
v_i_2607_ = lean_ctor_get(v_x_2605_, 0);
lean_inc_ref(v_i_2607_);
v_t_2608_ = lean_ctor_get(v_x_2605_, 1);
lean_inc_ref(v_t_2608_);
lean_dec_ref_known(v_x_2605_, 2);
v___x_2609_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2607_, v_x_2604_);
v_x_2604_ = v___x_2609_;
v_x_2605_ = v_t_2608_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_2604_) == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
lean_dec_ref_known(v_x_2605_, 2);
lean_dec_ref(v_postNode_2603_);
lean_dec_ref(v_preNode_2602_);
v___x_2611_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_2612_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v___x_2611_, v___y_2606_);
return v___x_2612_;
}
else
{
lean_object* v_i_2613_; lean_object* v_children_2614_; lean_object* v_val_2615_; lean_object* v___x_2616_; lean_object* v_fst_2617_; uint8_t v___x_2618_; 
v_i_2613_ = lean_ctor_get(v_x_2605_, 0);
lean_inc_ref_n(v_i_2613_, 2);
v_children_2614_ = lean_ctor_get(v_x_2605_, 1);
lean_inc_ref_n(v_children_2614_, 2);
lean_dec_ref_known(v_x_2605_, 2);
v_val_2615_ = lean_ctor_get(v_x_2604_, 0);
lean_inc_n(v_val_2615_, 2);
lean_inc_ref(v_preNode_2602_);
v___x_2616_ = lean_apply_4(v_preNode_2602_, v_val_2615_, v_i_2613_, v_children_2614_, v___y_2606_);
v_fst_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_fst_2617_);
v___x_2618_ = lean_unbox(v_fst_2617_);
lean_dec(v_fst_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v_preNode_2602_);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_x_2604_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v_x_2604_, 0);
lean_dec(v_unused_2638_);
v___x_2620_ = v_x_2604_;
v_isShared_2621_ = v_isSharedCheck_2637_;
goto v_resetjp_2619_;
}
else
{
lean_dec(v_x_2604_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2637_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v_snd_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v_fst_2625_; lean_object* v_snd_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2636_; 
v_snd_2622_ = lean_ctor_get(v___x_2616_, 1);
lean_inc(v_snd_2622_);
lean_dec_ref(v___x_2616_);
v___x_2623_ = lean_box(0);
v___x_2624_ = lean_apply_5(v_postNode_2603_, v_val_2615_, v_i_2613_, v_children_2614_, v___x_2623_, v_snd_2622_);
v_fst_2625_ = lean_ctor_get(v___x_2624_, 0);
v_snd_2626_ = lean_ctor_get(v___x_2624_, 1);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2628_ = v___x_2624_;
v_isShared_2629_ = v_isSharedCheck_2636_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_snd_2626_);
lean_inc(v_fst_2625_);
lean_dec(v___x_2624_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2636_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v_fst_2625_);
v___x_2631_ = v___x_2620_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_fst_2625_);
v___x_2631_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2631_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_snd_2626_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
else
{
lean_object* v_snd_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v___x_2646_; lean_object* v_fst_2647_; lean_object* v_snd_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2656_; 
v_snd_2639_ = lean_ctor_get(v___x_2616_, 1);
lean_inc(v_snd_2639_);
lean_dec_ref(v___x_2616_);
v___x_2640_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2604_, v_i_2613_);
v___x_2641_ = l_Lean_PersistentArray_toList___redArg(v_children_2614_);
v___x_2642_ = lean_box(0);
lean_inc_ref(v_postNode_2603_);
v___x_2643_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2602_, v_postNode_2603_, v___x_2640_, v___x_2641_, v___x_2642_, v_snd_2639_);
v_fst_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_fst_2644_);
v_snd_2645_ = lean_ctor_get(v___x_2643_, 1);
lean_inc(v_snd_2645_);
lean_dec_ref(v___x_2643_);
v___x_2646_ = lean_apply_5(v_postNode_2603_, v_val_2615_, v_i_2613_, v_children_2614_, v_fst_2644_, v_snd_2645_);
v_fst_2647_ = lean_ctor_get(v___x_2646_, 0);
v_snd_2648_ = lean_ctor_get(v___x_2646_, 1);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2650_ = v___x_2646_;
v_isShared_2651_ = v_isSharedCheck_2656_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_snd_2648_);
lean_inc(v_fst_2647_);
lean_dec(v___x_2646_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2656_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_fst_2647_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2652_);
v___x_2654_ = v___x_2650_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_snd_2648_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
default: 
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_dec_ref_known(v_x_2605_, 1);
lean_dec(v_x_2604_);
lean_dec_ref(v_postNode_2603_);
lean_dec_ref(v_preNode_2602_);
v___x_2657_ = lean_box(0);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v___y_2606_);
return v___x_2658_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_2659_, lean_object* v_postNode_2660_, lean_object* v___x_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v___y_2664_){
_start:
{
if (lean_obj_tag(v_x_2662_) == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec(v___x_2661_);
lean_dec_ref(v_postNode_2660_);
lean_dec_ref(v_preNode_2659_);
v___x_2665_ = l_List_reverse___redArg(v_x_2663_);
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v___y_2664_);
return v___x_2666_;
}
else
{
lean_object* v_head_2667_; lean_object* v_tail_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2679_; 
v_head_2667_ = lean_ctor_get(v_x_2662_, 0);
v_tail_2668_ = lean_ctor_get(v_x_2662_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_x_2662_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2670_ = v_x_2662_;
v_isShared_2671_ = v_isSharedCheck_2679_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_tail_2668_);
lean_inc(v_head_2667_);
lean_dec(v_x_2662_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2679_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v_fst_2673_; lean_object* v_snd_2674_; lean_object* v___x_2676_; 
lean_inc(v___x_2661_);
lean_inc_ref(v_postNode_2660_);
lean_inc_ref(v_preNode_2659_);
v___x_2672_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2659_, v_postNode_2660_, v___x_2661_, v_head_2667_, v___y_2664_);
v_fst_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_fst_2673_);
v_snd_2674_ = lean_ctor_get(v___x_2672_, 1);
lean_inc(v_snd_2674_);
lean_dec_ref(v___x_2672_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v_x_2663_);
lean_ctor_set(v___x_2670_, 0, v_fst_2673_);
v___x_2676_ = v___x_2670_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_fst_2673_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_x_2663_);
v___x_2676_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
v_x_2662_ = v_tail_2668_;
v_x_2663_ = v___x_2676_;
v___y_2664_ = v_snd_2674_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object* v_postNode_2680_, lean_object* v_ci_2681_, lean_object* v_i_2682_, lean_object* v_cs_2683_, lean_object* v_x_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_apply_4(v_postNode_2680_, v_ci_2681_, v_i_2682_, v_cs_2683_, v___y_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object* v_postNode_2687_, lean_object* v_ci_2688_, lean_object* v_i_2689_, lean_object* v_cs_2690_, lean_object* v_x_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(v_postNode_2687_, v_ci_2688_, v_i_2689_, v_cs_2690_, v_x_2691_, v___y_2692_);
lean_dec(v_x_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object* v_preNode_2694_, lean_object* v_postNode_2695_, lean_object* v_ctx_x3f_2696_, lean_object* v_t_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___f_2699_; lean_object* v___x_2700_; lean_object* v_snd_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2709_; 
v___f_2699_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2699_, 0, v_postNode_2695_);
v___x_2700_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2694_, v___f_2699_, v_ctx_x3f_2696_, v_t_2697_, v___y_2698_);
v_snd_2701_ = lean_ctor_get(v___x_2700_, 1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2709_ == 0)
{
lean_object* v_unused_2710_; 
v_unused_2710_ = lean_ctor_get(v___x_2700_, 0);
lean_dec(v_unused_2710_);
v___x_2703_ = v___x_2700_;
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_snd_2701_);
lean_dec(v___x_2700_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2705_ = lean_box(0);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2705_);
v___x_2707_ = v___x_2703_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_snd_2701_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(lean_object* v_text_2711_, lean_object* v_as_2712_, size_t v_sz_2713_, size_t v_i_2714_, lean_object* v_b_2715_, lean_object* v___y_2716_){
_start:
{
uint8_t v___x_2717_; 
v___x_2717_ = lean_usize_dec_lt(v_i_2714_, v_sz_2713_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
lean_dec_ref(v_text_2711_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_b_2715_);
lean_ctor_set(v___x_2718_, 1, v___y_2716_);
return v___x_2718_;
}
else
{
lean_object* v___x_2719_; lean_object* v___f_2720_; lean_object* v___f_2721_; lean_object* v_a_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v_snd_2725_; lean_object* v___x_2726_; size_t v___x_2727_; size_t v___x_2728_; 
v___x_2719_ = lean_box(v___x_2717_);
v___f_2720_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2720_, 0, v___x_2719_);
lean_inc_ref(v_text_2711_);
v___f_2721_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2721_, 0, v_text_2711_);
v_a_2722_ = lean_array_uget_borrowed(v_as_2712_, v_i_2714_);
v___x_2723_ = lean_box(0);
lean_inc(v_a_2722_);
v___x_2724_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(v___f_2720_, v___f_2721_, v___x_2723_, v_a_2722_, v___y_2716_);
v_snd_2725_ = lean_ctor_get(v___x_2724_, 1);
lean_inc(v_snd_2725_);
lean_dec_ref(v___x_2724_);
v___x_2726_ = lean_box(0);
v___x_2727_ = ((size_t)1ULL);
v___x_2728_ = lean_usize_add(v_i_2714_, v___x_2727_);
v_i_2714_ = v___x_2728_;
v_b_2715_ = v___x_2726_;
v___y_2716_ = v_snd_2725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___boxed(lean_object* v_text_2730_, lean_object* v_as_2731_, lean_object* v_sz_2732_, lean_object* v_i_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2732_);
lean_dec(v_sz_2732_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2730_, v_as_2731_, v_sz_boxed_2736_, v_i_boxed_2737_, v_b_2734_, v___y_2735_);
lean_dec_ref(v_as_2731_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences(lean_object* v_text_2739_, lean_object* v_trees_2740_){
_start:
{
lean_object* v___x_2741_; size_t v_sz_2742_; size_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v_snd_2746_; 
v___x_2741_ = lean_box(0);
v_sz_2742_ = lean_array_size(v_trees_2740_);
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2739_, v_trees_2740_, v_sz_2742_, v___x_2743_, v___x_2741_, v___x_2744_);
v_snd_2746_ = lean_ctor_get(v___x_2745_, 1);
lean_inc(v_snd_2746_);
lean_dec_ref(v___x_2745_);
return v_snd_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences___boxed(lean_object* v_text_2747_, lean_object* v_trees_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Server_findReferences(v_text_2747_, v_trees_2748_);
lean_dec_ref(v_trees_2748_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2750_, lean_object* v_msg_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v_msg_2751_, v___y_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object* v_00_u03b1_2754_, lean_object* v_preNode_2755_, lean_object* v_postNode_2756_, lean_object* v_x_2757_, lean_object* v_x_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2755_, v_postNode_2756_, v_x_2757_, v_x_2758_, v___y_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2761_, lean_object* v_preNode_2762_, lean_object* v_postNode_2763_, lean_object* v___x_2764_, lean_object* v_x_2765_, lean_object* v_x_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2762_, v_postNode_2763_, v___x_2764_, v_x_2765_, v_x_2766_, v___y_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(lean_object* v_a_2769_, lean_object* v_x_2770_){
_start:
{
lean_object* v_key_2771_; lean_object* v_value_2772_; lean_object* v_tail_2773_; uint8_t v___x_2774_; 
v_key_2771_ = lean_ctor_get(v_x_2770_, 0);
v_value_2772_ = lean_ctor_get(v_x_2770_, 1);
v_tail_2773_ = lean_ctor_get(v_x_2770_, 2);
v___x_2774_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2771_, v_a_2769_);
if (v___x_2774_ == 0)
{
v_x_2770_ = v_tail_2773_;
goto _start;
}
else
{
lean_inc(v_value_2772_);
return v_value_2772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg___boxed(lean_object* v_a_2776_, lean_object* v_x_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2776_, v_x_2777_);
lean_dec(v_x_2777_);
lean_dec_ref(v_a_2776_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(lean_object* v_m_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v_buckets_2781_; lean_object* v___x_2782_; uint64_t v___x_2783_; uint64_t v___x_2784_; uint64_t v___x_2785_; uint64_t v_fold_2786_; uint64_t v___x_2787_; uint64_t v___x_2788_; uint64_t v___x_2789_; size_t v___x_2790_; size_t v___x_2791_; size_t v___x_2792_; size_t v___x_2793_; size_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_buckets_2781_ = lean_ctor_get(v_m_2779_, 1);
v___x_2782_ = lean_array_get_size(v_buckets_2781_);
v___x_2783_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2780_);
v___x_2784_ = 32ULL;
v___x_2785_ = lean_uint64_shift_right(v___x_2783_, v___x_2784_);
v_fold_2786_ = lean_uint64_xor(v___x_2783_, v___x_2785_);
v___x_2787_ = 16ULL;
v___x_2788_ = lean_uint64_shift_right(v_fold_2786_, v___x_2787_);
v___x_2789_ = lean_uint64_xor(v_fold_2786_, v___x_2788_);
v___x_2790_ = lean_uint64_to_usize(v___x_2789_);
v___x_2791_ = lean_usize_of_nat(v___x_2782_);
v___x_2792_ = ((size_t)1ULL);
v___x_2793_ = lean_usize_sub(v___x_2791_, v___x_2792_);
v___x_2794_ = lean_usize_land(v___x_2790_, v___x_2793_);
v___x_2795_ = lean_array_uget_borrowed(v_buckets_2781_, v___x_2794_);
v___x_2796_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2780_, v___x_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg___boxed(lean_object* v_m_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2797_, v_a_2798_);
lean_dec_ref(v_a_2798_);
lean_dec_ref(v_m_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(lean_object* v_a_2800_, lean_object* v_x_2801_){
_start:
{
if (lean_obj_tag(v_x_2801_) == 0)
{
uint8_t v___x_2802_; 
v___x_2802_ = 0;
return v___x_2802_;
}
else
{
lean_object* v_key_2803_; lean_object* v_tail_2804_; uint8_t v___x_2805_; 
v_key_2803_ = lean_ctor_get(v_x_2801_, 0);
v_tail_2804_ = lean_ctor_get(v_x_2801_, 2);
v___x_2805_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2803_, v_a_2800_);
if (v___x_2805_ == 0)
{
v_x_2801_ = v_tail_2804_;
goto _start;
}
else
{
return v___x_2805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg___boxed(lean_object* v_a_2807_, lean_object* v_x_2808_){
_start:
{
uint8_t v_res_2809_; lean_object* v_r_2810_; 
v_res_2809_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2807_, v_x_2808_);
lean_dec(v_x_2808_);
lean_dec_ref(v_a_2807_);
v_r_2810_ = lean_box(v_res_2809_);
return v_r_2810_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(lean_object* v_m_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_buckets_2813_; lean_object* v___x_2814_; uint64_t v___x_2815_; uint64_t v___x_2816_; uint64_t v___x_2817_; uint64_t v_fold_2818_; uint64_t v___x_2819_; uint64_t v___x_2820_; uint64_t v___x_2821_; size_t v___x_2822_; size_t v___x_2823_; size_t v___x_2824_; size_t v___x_2825_; size_t v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_buckets_2813_ = lean_ctor_get(v_m_2811_, 1);
v___x_2814_ = lean_array_get_size(v_buckets_2813_);
v___x_2815_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2812_);
v___x_2816_ = 32ULL;
v___x_2817_ = lean_uint64_shift_right(v___x_2815_, v___x_2816_);
v_fold_2818_ = lean_uint64_xor(v___x_2815_, v___x_2817_);
v___x_2819_ = 16ULL;
v___x_2820_ = lean_uint64_shift_right(v_fold_2818_, v___x_2819_);
v___x_2821_ = lean_uint64_xor(v_fold_2818_, v___x_2820_);
v___x_2822_ = lean_uint64_to_usize(v___x_2821_);
v___x_2823_ = lean_usize_of_nat(v___x_2814_);
v___x_2824_ = ((size_t)1ULL);
v___x_2825_ = lean_usize_sub(v___x_2823_, v___x_2824_);
v___x_2826_ = lean_usize_land(v___x_2822_, v___x_2825_);
v___x_2827_ = lean_array_uget_borrowed(v_buckets_2813_, v___x_2826_);
v___x_2828_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2812_, v___x_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg___boxed(lean_object* v_m_2829_, lean_object* v_a_2830_){
_start:
{
uint8_t v_res_2831_; lean_object* v_r_2832_; 
v_res_2831_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2829_, v_a_2830_);
lean_dec_ref(v_a_2830_);
lean_dec_ref(v_m_2829_);
v_r_2832_ = lean_box(v_res_2831_);
return v_r_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(lean_object* v_idMap_2833_, lean_object* v_a_2834_){
_start:
{
uint8_t v___x_2835_; 
v___x_2835_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_idMap_2833_, v_a_2834_);
if (v___x_2835_ == 0)
{
return v_a_2834_;
}
else
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_idMap_2833_, v_a_2834_);
lean_dec_ref(v_a_2834_);
v_a_2834_ = v___x_2836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg___boxed(lean_object* v_idMap_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2838_, v_a_2839_);
lean_dec_ref(v_idMap_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object* v_idMap_2841_, lean_object* v_id_2842_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2841_, v_id_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object* v_idMap_2844_, lean_object* v_id_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(v_idMap_2844_, v_id_2845_);
lean_dec_ref(v_idMap_2844_);
return v_res_2846_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object* v_00_u03b2_2847_, lean_object* v_m_2848_, lean_object* v_a_2849_){
_start:
{
uint8_t v___x_2850_; 
v___x_2850_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2848_, v_a_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object* v_00_u03b2_2851_, lean_object* v_m_2852_, lean_object* v_a_2853_){
_start:
{
uint8_t v_res_2854_; lean_object* v_r_2855_; 
v_res_2854_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(v_00_u03b2_2851_, v_m_2852_, v_a_2853_);
lean_dec_ref(v_a_2853_);
lean_dec_ref(v_m_2852_);
v_r_2855_ = lean_box(v_res_2854_);
return v_r_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object* v_00_u03b2_2856_, lean_object* v_m_2857_, lean_object* v_a_2858_, lean_object* v_hma_2859_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2857_, v_a_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object* v_00_u03b2_2861_, lean_object* v_m_2862_, lean_object* v_a_2863_, lean_object* v_hma_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(v_00_u03b2_2861_, v_m_2862_, v_a_2863_, v_hma_2864_);
lean_dec_ref(v_a_2863_);
lean_dec_ref(v_m_2862_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object* v_idMap_2866_, lean_object* v_inst_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2866_, v_a_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object* v_idMap_2870_, lean_object* v_inst_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2870_, v_inst_2871_, v_a_2872_);
lean_dec_ref(v_idMap_2870_);
return v_res_2873_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(lean_object* v_00_u03b2_2874_, lean_object* v_a_2875_, lean_object* v_x_2876_){
_start:
{
uint8_t v___x_2877_; 
v___x_2877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2875_, v_x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2878_, lean_object* v_a_2879_, lean_object* v_x_2880_){
_start:
{
uint8_t v_res_2881_; lean_object* v_r_2882_; 
v_res_2881_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(v_00_u03b2_2878_, v_a_2879_, v_x_2880_);
lean_dec(v_x_2880_);
lean_dec_ref(v_a_2879_);
v_r_2882_ = lean_box(v_res_2881_);
return v_r_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(lean_object* v_00_u03b2_2883_, lean_object* v_a_2884_, lean_object* v_x_2885_, lean_object* v_x_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2884_, v_x_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2888_, lean_object* v_a_2889_, lean_object* v_x_2890_, lean_object* v_x_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(v_00_u03b2_2888_, v_a_2889_, v_x_2890_, v_x_2891_);
lean_dec(v_x_2890_);
lean_dec_ref(v_a_2889_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
if (lean_obj_tag(v_a_2893_) == 0)
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_a_2894_);
return v___x_2895_;
}
else
{
if (lean_obj_tag(v_a_2894_) == 0)
{
lean_object* v_tail_2896_; 
v_tail_2896_ = lean_ctor_get(v_a_2893_, 2);
lean_inc(v_tail_2896_);
lean_dec_ref_known(v_a_2893_, 3);
v_a_2893_ = v_tail_2896_;
goto _start;
}
else
{
lean_object* v_key_2898_; 
v_key_2898_ = lean_ctor_get(v_a_2893_, 0);
if (lean_obj_tag(v_key_2898_) == 0)
{
lean_object* v_tail_2899_; 
lean_inc_ref(v_key_2898_);
lean_dec_ref_known(v_a_2894_, 2);
v_tail_2899_ = lean_ctor_get(v_a_2893_, 2);
lean_inc(v_tail_2899_);
lean_dec_ref_known(v_a_2893_, 3);
v_a_2893_ = v_tail_2899_;
v_a_2894_ = v_key_2898_;
goto _start;
}
else
{
lean_object* v_tail_2901_; 
v_tail_2901_ = lean_ctor_get(v_a_2893_, 2);
lean_inc(v_tail_2901_);
lean_dec_ref_known(v_a_2893_, 3);
v_a_2893_ = v_tail_2901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(lean_object* v_as_2903_, size_t v_sz_2904_, size_t v_i_2905_, lean_object* v_b_2906_){
_start:
{
uint8_t v___x_2907_; 
v___x_2907_ = lean_usize_dec_lt(v_i_2905_, v_sz_2904_);
if (v___x_2907_ == 0)
{
return v_b_2906_;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2909_; 
v_a_2908_ = lean_array_uget_borrowed(v_as_2903_, v_i_2905_);
lean_inc(v_a_2908_);
v___x_2909_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(v_a_2908_, v_b_2906_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 1);
return v_a_2910_;
}
else
{
lean_object* v_a_2911_; size_t v___x_2912_; size_t v___x_2913_; 
v_a_2911_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2909_, 1);
v___x_2912_ = ((size_t)1ULL);
v___x_2913_ = lean_usize_add(v_i_2905_, v___x_2912_);
v_i_2905_ = v___x_2913_;
v_b_2906_ = v_a_2911_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5___boxed(lean_object* v_as_2915_, lean_object* v_sz_2916_, lean_object* v_i_2917_, lean_object* v_b_2918_){
_start:
{
size_t v_sz_boxed_2919_; size_t v_i_boxed_2920_; lean_object* v_res_2921_; 
v_sz_boxed_2919_ = lean_unbox_usize(v_sz_2916_);
lean_dec(v_sz_2916_);
v_i_boxed_2920_ = lean_unbox_usize(v_i_2917_);
lean_dec(v_i_2917_);
v_res_2921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_as_2915_, v_sz_boxed_2919_, v_i_boxed_2920_, v_b_2918_);
lean_dec_ref(v_as_2915_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(lean_object* v_a_2922_, lean_object* v_b_2923_, lean_object* v_x_2924_){
_start:
{
if (lean_obj_tag(v_x_2924_) == 0)
{
lean_dec(v_b_2923_);
lean_dec_ref(v_a_2922_);
return v_x_2924_;
}
else
{
lean_object* v_key_2925_; lean_object* v_value_2926_; lean_object* v_tail_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2939_; 
v_key_2925_ = lean_ctor_get(v_x_2924_, 0);
v_value_2926_ = lean_ctor_get(v_x_2924_, 1);
v_tail_2927_ = lean_ctor_get(v_x_2924_, 2);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_x_2924_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2929_ = v_x_2924_;
v_isShared_2930_ = v_isSharedCheck_2939_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_tail_2927_);
lean_inc(v_value_2926_);
lean_inc(v_key_2925_);
lean_dec(v_x_2924_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2939_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
uint8_t v___x_2931_; 
v___x_2931_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2925_, v_a_2922_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2932_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2922_, v_b_2923_, v_tail_2927_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 2, v___x_2932_);
v___x_2934_ = v___x_2929_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_key_2925_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_value_2926_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
else
{
lean_object* v___x_2937_; 
lean_dec(v_value_2926_);
lean_dec(v_key_2925_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v_b_2923_);
lean_ctor_set(v___x_2929_, 0, v_a_2922_);
v___x_2937_ = v___x_2929_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2922_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_b_2923_);
lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_tail_2927_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(lean_object* v_x_2940_, lean_object* v_x_2941_){
_start:
{
if (lean_obj_tag(v_x_2941_) == 0)
{
return v_x_2940_;
}
else
{
lean_object* v_key_2942_; lean_object* v_value_2943_; lean_object* v_tail_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2967_; 
v_key_2942_ = lean_ctor_get(v_x_2941_, 0);
v_value_2943_ = lean_ctor_get(v_x_2941_, 1);
v_tail_2944_ = lean_ctor_get(v_x_2941_, 2);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_x_2941_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2946_ = v_x_2941_;
v_isShared_2947_ = v_isSharedCheck_2967_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_tail_2944_);
lean_inc(v_value_2943_);
lean_inc(v_key_2942_);
lean_dec(v_x_2941_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2967_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; uint64_t v___x_2949_; uint64_t v___x_2950_; uint64_t v___x_2951_; uint64_t v_fold_2952_; uint64_t v___x_2953_; uint64_t v___x_2954_; uint64_t v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; size_t v___x_2958_; size_t v___x_2959_; size_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2948_ = lean_array_get_size(v_x_2940_);
v___x_2949_ = l_Lean_Lsp_instHashableRefIdent_hash(v_key_2942_);
v___x_2950_ = 32ULL;
v___x_2951_ = lean_uint64_shift_right(v___x_2949_, v___x_2950_);
v_fold_2952_ = lean_uint64_xor(v___x_2949_, v___x_2951_);
v___x_2953_ = 16ULL;
v___x_2954_ = lean_uint64_shift_right(v_fold_2952_, v___x_2953_);
v___x_2955_ = lean_uint64_xor(v_fold_2952_, v___x_2954_);
v___x_2956_ = lean_uint64_to_usize(v___x_2955_);
v___x_2957_ = lean_usize_of_nat(v___x_2948_);
v___x_2958_ = ((size_t)1ULL);
v___x_2959_ = lean_usize_sub(v___x_2957_, v___x_2958_);
v___x_2960_ = lean_usize_land(v___x_2956_, v___x_2959_);
v___x_2961_ = lean_array_uget_borrowed(v_x_2940_, v___x_2960_);
lean_inc(v___x_2961_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 2, v___x_2961_);
v___x_2963_ = v___x_2946_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_key_2942_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_value_2943_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_array_uset(v_x_2940_, v___x_2960_, v___x_2963_);
v_x_2940_ = v___x_2964_;
v_x_2941_ = v_tail_2944_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(lean_object* v_i_2968_, lean_object* v_source_2969_, lean_object* v_target_2970_){
_start:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = lean_array_get_size(v_source_2969_);
v___x_2972_ = lean_nat_dec_lt(v_i_2968_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_dec_ref(v_source_2969_);
lean_dec(v_i_2968_);
return v_target_2970_;
}
else
{
lean_object* v_es_2973_; lean_object* v___x_2974_; lean_object* v_source_2975_; lean_object* v_target_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_es_2973_ = lean_array_fget(v_source_2969_, v_i_2968_);
v___x_2974_ = lean_box(0);
v_source_2975_ = lean_array_fset(v_source_2969_, v_i_2968_, v___x_2974_);
v_target_2976_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_target_2970_, v_es_2973_);
v___x_2977_ = lean_unsigned_to_nat(1u);
v___x_2978_ = lean_nat_add(v_i_2968_, v___x_2977_);
lean_dec(v_i_2968_);
v_i_2968_ = v___x_2978_;
v_source_2969_ = v_source_2975_;
v_target_2970_ = v_target_2976_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(lean_object* v_data_2980_){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v_nbuckets_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2981_ = lean_array_get_size(v_data_2980_);
v___x_2982_ = lean_unsigned_to_nat(2u);
v_nbuckets_2983_ = lean_nat_mul(v___x_2981_, v___x_2982_);
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2985_ = lean_box(0);
v___x_2986_ = lean_mk_array(v_nbuckets_2983_, v___x_2985_);
v___x_2987_ = lean_array_propagate_mark(v_data_2980_, v___x_2986_);
v___x_2988_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2984_, v_data_2980_, v___x_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object* v_m_2989_, lean_object* v_a_2990_, lean_object* v_b_2991_){
_start:
{
lean_object* v_size_2992_; lean_object* v_buckets_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3036_; 
v_size_2992_ = lean_ctor_get(v_m_2989_, 0);
v_buckets_2993_ = lean_ctor_get(v_m_2989_, 1);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_m_2989_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_2995_ = v_m_2989_;
v_isShared_2996_ = v_isSharedCheck_3036_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_buckets_2993_);
lean_inc(v_size_2992_);
lean_dec(v_m_2989_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3036_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; uint64_t v___x_2998_; uint64_t v___x_2999_; uint64_t v___x_3000_; uint64_t v_fold_3001_; uint64_t v___x_3002_; uint64_t v___x_3003_; uint64_t v___x_3004_; size_t v___x_3005_; size_t v___x_3006_; size_t v___x_3007_; size_t v___x_3008_; size_t v___x_3009_; lean_object* v_bkt_3010_; uint8_t v___x_3011_; 
v___x_2997_ = lean_array_get_size(v_buckets_2993_);
v___x_2998_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2990_);
v___x_2999_ = 32ULL;
v___x_3000_ = lean_uint64_shift_right(v___x_2998_, v___x_2999_);
v_fold_3001_ = lean_uint64_xor(v___x_2998_, v___x_3000_);
v___x_3002_ = 16ULL;
v___x_3003_ = lean_uint64_shift_right(v_fold_3001_, v___x_3002_);
v___x_3004_ = lean_uint64_xor(v_fold_3001_, v___x_3003_);
v___x_3005_ = lean_uint64_to_usize(v___x_3004_);
v___x_3006_ = lean_usize_of_nat(v___x_2997_);
v___x_3007_ = ((size_t)1ULL);
v___x_3008_ = lean_usize_sub(v___x_3006_, v___x_3007_);
v___x_3009_ = lean_usize_land(v___x_3005_, v___x_3008_);
v_bkt_3010_ = lean_array_uget_borrowed(v_buckets_2993_, v___x_3009_);
v___x_3011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2990_, v_bkt_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; lean_object* v_size_x27_3013_; lean_object* v___x_3014_; lean_object* v_buckets_x27_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3012_ = lean_unsigned_to_nat(1u);
v_size_x27_3013_ = lean_nat_add(v_size_2992_, v___x_3012_);
lean_dec(v_size_2992_);
lean_inc(v_bkt_3010_);
v___x_3014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3014_, 0, v_a_2990_);
lean_ctor_set(v___x_3014_, 1, v_b_2991_);
lean_ctor_set(v___x_3014_, 2, v_bkt_3010_);
v_buckets_x27_3015_ = lean_array_uset(v_buckets_2993_, v___x_3009_, v___x_3014_);
v___x_3016_ = lean_unsigned_to_nat(4u);
v___x_3017_ = lean_nat_mul(v_size_x27_3013_, v___x_3016_);
v___x_3018_ = lean_unsigned_to_nat(3u);
v___x_3019_ = lean_nat_div(v___x_3017_, v___x_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_array_get_size(v_buckets_x27_3015_);
v___x_3021_ = lean_nat_dec_le(v___x_3019_, v___x_3020_);
lean_dec(v___x_3019_);
if (v___x_3021_ == 0)
{
lean_object* v_val_3022_; lean_object* v___x_3024_; 
v_val_3022_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3015_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v_val_3022_);
lean_ctor_set(v___x_2995_, 0, v_size_x27_3013_);
v___x_3024_ = v___x_2995_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_size_x27_3013_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_val_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
else
{
lean_object* v___x_3027_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v_buckets_x27_3015_);
lean_ctor_set(v___x_2995_, 0, v_size_x27_3013_);
v___x_3027_ = v___x_2995_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_size_x27_3013_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_buckets_x27_3015_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
else
{
lean_object* v___x_3029_; lean_object* v_buckets_x27_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
lean_inc(v_bkt_3010_);
v___x_3029_ = lean_box(0);
v_buckets_x27_3030_ = lean_array_uset(v_buckets_2993_, v___x_3009_, v___x_3029_);
v___x_3031_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2990_, v_b_2991_, v_bkt_3010_);
v___x_3032_ = lean_array_uset(v_buckets_x27_3030_, v___x_3009_, v___x_3031_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v___x_3032_);
v___x_3034_ = v___x_2995_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_size_2992_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object* v___x_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
if (lean_obj_tag(v_a_3038_) == 0)
{
lean_object* v___x_3040_; 
lean_dec_ref(v___x_3037_);
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_a_3039_);
return v___x_3040_;
}
else
{
lean_object* v_key_3041_; lean_object* v_tail_3042_; uint8_t v___x_3043_; 
v_key_3041_ = lean_ctor_get(v_a_3038_, 0);
lean_inc(v_key_3041_);
v_tail_3042_ = lean_ctor_get(v_a_3038_, 2);
lean_inc(v_tail_3042_);
lean_dec_ref_known(v_a_3038_, 3);
v___x_3043_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3041_, v___x_3037_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; 
lean_inc_ref(v___x_3037_);
v___x_3044_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3039_, v_key_3041_, v___x_3037_);
v_a_3038_ = v_tail_3042_;
v_a_3039_ = v___x_3044_;
goto _start;
}
else
{
lean_dec(v_key_3041_);
v_a_3038_ = v_tail_3042_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object* v___x_3047_, lean_object* v_as_3048_, size_t v_sz_3049_, size_t v_i_3050_, lean_object* v_b_3051_){
_start:
{
uint8_t v___x_3052_; 
v___x_3052_ = lean_usize_dec_lt(v_i_3050_, v_sz_3049_);
if (v___x_3052_ == 0)
{
lean_dec_ref(v___x_3047_);
return v_b_3051_;
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3054_; 
v_a_3053_ = lean_array_uget_borrowed(v_as_3048_, v_i_3050_);
lean_inc(v_a_3053_);
lean_inc_ref(v___x_3047_);
v___x_3054_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(v___x_3047_, v_a_3053_, v_b_3051_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; 
lean_dec_ref(v___x_3047_);
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref_known(v___x_3054_, 1);
return v_a_3055_;
}
else
{
lean_object* v_a_3056_; size_t v___x_3057_; size_t v___x_3058_; 
v_a_3056_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3054_, 1);
v___x_3057_ = ((size_t)1ULL);
v___x_3058_ = lean_usize_add(v_i_3050_, v___x_3057_);
v_i_3050_ = v___x_3058_;
v_b_3051_ = v_a_3056_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object* v___x_3060_, lean_object* v_as_3061_, lean_object* v_sz_3062_, lean_object* v_i_3063_, lean_object* v_b_3064_){
_start:
{
size_t v_sz_boxed_3065_; size_t v_i_boxed_3066_; lean_object* v_res_3067_; 
v_sz_boxed_3065_ = lean_unbox_usize(v_sz_3062_);
lean_dec(v_sz_3062_);
v_i_boxed_3066_ = lean_unbox_usize(v_i_3063_);
lean_dec(v_i_3063_);
v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3060_, v_as_3061_, v_sz_boxed_3065_, v_i_boxed_3066_, v_b_3064_);
lean_dec_ref(v_as_3061_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
if (lean_obj_tag(v_a_3068_) == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_a_3069_);
return v___x_3070_;
}
else
{
lean_object* v_value_3071_; lean_object* v_key_3072_; lean_object* v_tail_3073_; lean_object* v_buckets_3074_; size_t v_sz_3075_; size_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_value_3071_ = lean_ctor_get(v_a_3068_, 1);
lean_inc(v_value_3071_);
v_key_3072_ = lean_ctor_get(v_a_3068_, 0);
lean_inc(v_key_3072_);
v_tail_3073_ = lean_ctor_get(v_a_3068_, 2);
lean_inc(v_tail_3073_);
lean_dec_ref_known(v_a_3068_, 3);
v_buckets_3074_ = lean_ctor_get(v_value_3071_, 1);
lean_inc_ref(v_buckets_3074_);
lean_dec(v_value_3071_);
v_sz_3075_ = lean_array_size(v_buckets_3074_);
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_buckets_3074_, v_sz_3075_, v___x_3076_, v_key_3072_);
v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3077_, v_buckets_3074_, v_sz_3075_, v___x_3076_, v_a_3069_);
lean_dec_ref(v_buckets_3074_);
v_a_3068_ = v_tail_3073_;
v_a_3069_ = v___x_3078_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object* v_as_3080_, size_t v_sz_3081_, size_t v_i_3082_, lean_object* v_b_3083_){
_start:
{
uint8_t v___x_3084_; 
v___x_3084_ = lean_usize_dec_lt(v_i_3082_, v_sz_3081_);
if (v___x_3084_ == 0)
{
return v_b_3083_;
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3086_; 
v_a_3085_ = lean_array_uget_borrowed(v_as_3080_, v_i_3082_);
lean_inc(v_a_3085_);
v___x_3086_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(v_a_3085_, v_b_3083_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
return v_a_3087_;
}
else
{
lean_object* v_a_3088_; size_t v___x_3089_; size_t v___x_3090_; 
v_a_3088_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3086_, 1);
v___x_3089_ = ((size_t)1ULL);
v___x_3090_ = lean_usize_add(v_i_3082_, v___x_3089_);
v_i_3082_ = v___x_3090_;
v_b_3083_ = v_a_3088_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object* v_as_3092_, lean_object* v_sz_3093_, lean_object* v_i_3094_, lean_object* v_b_3095_){
_start:
{
size_t v_sz_boxed_3096_; size_t v_i_boxed_3097_; lean_object* v_res_3098_; 
v_sz_boxed_3096_ = lean_unbox_usize(v_sz_3093_);
lean_dec(v_sz_3093_);
v_i_boxed_3097_ = lean_unbox_usize(v_i_3094_);
lean_dec(v_i_3094_);
v_res_3098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_as_3092_, v_sz_boxed_3096_, v_i_boxed_3097_, v_b_3095_);
lean_dec_ref(v_as_3092_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object* v_a_3099_, lean_object* v_x_3100_){
_start:
{
if (lean_obj_tag(v_x_3100_) == 0)
{
return v_x_3100_;
}
else
{
lean_object* v_key_3101_; lean_object* v_value_3102_; lean_object* v_tail_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3112_; 
v_key_3101_ = lean_ctor_get(v_x_3100_, 0);
v_value_3102_ = lean_ctor_get(v_x_3100_, 1);
v_tail_3103_ = lean_ctor_get(v_x_3100_, 2);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_x_3100_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3105_ = v_x_3100_;
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_tail_3103_);
lean_inc(v_value_3102_);
lean_inc(v_key_3101_);
lean_dec(v_x_3100_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
uint8_t v___x_3107_; 
v___x_3107_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3101_, v_a_3099_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3108_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3099_, v_tail_3103_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 2, v___x_3108_);
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_key_3101_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_value_3102_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
else
{
lean_del_object(v___x_3105_);
lean_dec(v_value_3102_);
lean_dec(v_key_3101_);
return v_tail_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object* v_a_3113_, lean_object* v_x_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3113_, v_x_3114_);
lean_dec_ref(v_a_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object* v_m_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_size_3118_; lean_object* v_buckets_3119_; lean_object* v___x_3120_; uint64_t v___x_3121_; uint64_t v___x_3122_; uint64_t v___x_3123_; uint64_t v_fold_3124_; uint64_t v___x_3125_; uint64_t v___x_3126_; uint64_t v___x_3127_; size_t v___x_3128_; size_t v___x_3129_; size_t v___x_3130_; size_t v___x_3131_; size_t v___x_3132_; lean_object* v_bkt_3133_; uint8_t v___x_3134_; 
v_size_3118_ = lean_ctor_get(v_m_3116_, 0);
v_buckets_3119_ = lean_ctor_get(v_m_3116_, 1);
v___x_3120_ = lean_array_get_size(v_buckets_3119_);
v___x_3121_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3117_);
v___x_3122_ = 32ULL;
v___x_3123_ = lean_uint64_shift_right(v___x_3121_, v___x_3122_);
v_fold_3124_ = lean_uint64_xor(v___x_3121_, v___x_3123_);
v___x_3125_ = 16ULL;
v___x_3126_ = lean_uint64_shift_right(v_fold_3124_, v___x_3125_);
v___x_3127_ = lean_uint64_xor(v_fold_3124_, v___x_3126_);
v___x_3128_ = lean_uint64_to_usize(v___x_3127_);
v___x_3129_ = lean_usize_of_nat(v___x_3120_);
v___x_3130_ = ((size_t)1ULL);
v___x_3131_ = lean_usize_sub(v___x_3129_, v___x_3130_);
v___x_3132_ = lean_usize_land(v___x_3128_, v___x_3131_);
v_bkt_3133_ = lean_array_uget_borrowed(v_buckets_3119_, v___x_3132_);
v___x_3134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3117_, v_bkt_3133_);
if (v___x_3134_ == 0)
{
return v_m_3116_;
}
else
{
lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3147_; 
lean_inc(v_bkt_3133_);
lean_inc_ref(v_buckets_3119_);
lean_inc(v_size_3118_);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_m_3116_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; lean_object* v_unused_3149_; 
v_unused_3148_ = lean_ctor_get(v_m_3116_, 1);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_m_3116_, 0);
lean_dec(v_unused_3149_);
v___x_3136_ = v_m_3116_;
v_isShared_3137_ = v_isSharedCheck_3147_;
goto v_resetjp_3135_;
}
else
{
lean_dec(v_m_3116_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3147_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v_buckets_x27_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3138_ = lean_box(0);
v_buckets_x27_3139_ = lean_array_uset(v_buckets_3119_, v___x_3132_, v___x_3138_);
v___x_3140_ = lean_unsigned_to_nat(1u);
v___x_3141_ = lean_nat_sub(v_size_3118_, v___x_3140_);
lean_dec(v_size_3118_);
v___x_3142_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3117_, v_bkt_3133_);
v___x_3143_ = lean_array_uset(v_buckets_x27_3139_, v___x_3132_, v___x_3142_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 1, v___x_3143_);
lean_ctor_set(v___x_3136_, 0, v___x_3141_);
v___x_3145_ = v___x_3136_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object* v_m_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3150_, v_a_3151_);
lean_dec_ref(v_a_3151_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object* v_m_3153_, lean_object* v_a_3154_, lean_object* v_b_3155_){
_start:
{
lean_object* v_size_3156_; lean_object* v_buckets_3157_; lean_object* v___x_3158_; uint64_t v___x_3159_; uint64_t v___x_3160_; uint64_t v___x_3161_; uint64_t v_fold_3162_; uint64_t v___x_3163_; uint64_t v___x_3164_; uint64_t v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; size_t v___x_3168_; size_t v___x_3169_; size_t v___x_3170_; lean_object* v_bkt_3171_; uint8_t v___x_3172_; 
v_size_3156_ = lean_ctor_get(v_m_3153_, 0);
v_buckets_3157_ = lean_ctor_get(v_m_3153_, 1);
v___x_3158_ = lean_array_get_size(v_buckets_3157_);
v___x_3159_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3154_);
v___x_3160_ = 32ULL;
v___x_3161_ = lean_uint64_shift_right(v___x_3159_, v___x_3160_);
v_fold_3162_ = lean_uint64_xor(v___x_3159_, v___x_3161_);
v___x_3163_ = 16ULL;
v___x_3164_ = lean_uint64_shift_right(v_fold_3162_, v___x_3163_);
v___x_3165_ = lean_uint64_xor(v_fold_3162_, v___x_3164_);
v___x_3166_ = lean_uint64_to_usize(v___x_3165_);
v___x_3167_ = lean_usize_of_nat(v___x_3158_);
v___x_3168_ = ((size_t)1ULL);
v___x_3169_ = lean_usize_sub(v___x_3167_, v___x_3168_);
v___x_3170_ = lean_usize_land(v___x_3166_, v___x_3169_);
v_bkt_3171_ = lean_array_uget_borrowed(v_buckets_3157_, v___x_3170_);
v___x_3172_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3154_, v_bkt_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3193_; 
lean_inc_ref(v_buckets_3157_);
lean_inc(v_size_3156_);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_m_3153_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; lean_object* v_unused_3195_; 
v_unused_3194_ = lean_ctor_get(v_m_3153_, 1);
lean_dec(v_unused_3194_);
v_unused_3195_ = lean_ctor_get(v_m_3153_, 0);
lean_dec(v_unused_3195_);
v___x_3174_ = v_m_3153_;
v_isShared_3175_ = v_isSharedCheck_3193_;
goto v_resetjp_3173_;
}
else
{
lean_dec(v_m_3153_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3193_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v_size_x27_3177_; lean_object* v___x_3178_; lean_object* v_buckets_x27_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3176_ = lean_unsigned_to_nat(1u);
v_size_x27_3177_ = lean_nat_add(v_size_3156_, v___x_3176_);
lean_dec(v_size_3156_);
lean_inc(v_bkt_3171_);
v___x_3178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3178_, 0, v_a_3154_);
lean_ctor_set(v___x_3178_, 1, v_b_3155_);
lean_ctor_set(v___x_3178_, 2, v_bkt_3171_);
v_buckets_x27_3179_ = lean_array_uset(v_buckets_3157_, v___x_3170_, v___x_3178_);
v___x_3180_ = lean_unsigned_to_nat(4u);
v___x_3181_ = lean_nat_mul(v_size_x27_3177_, v___x_3180_);
v___x_3182_ = lean_unsigned_to_nat(3u);
v___x_3183_ = lean_nat_div(v___x_3181_, v___x_3182_);
lean_dec(v___x_3181_);
v___x_3184_ = lean_array_get_size(v_buckets_x27_3179_);
v___x_3185_ = lean_nat_dec_le(v___x_3183_, v___x_3184_);
lean_dec(v___x_3183_);
if (v___x_3185_ == 0)
{
lean_object* v_val_3186_; lean_object* v___x_3188_; 
v_val_3186_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3179_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 1, v_val_3186_);
lean_ctor_set(v___x_3174_, 0, v_size_x27_3177_);
v___x_3188_ = v___x_3174_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_size_x27_3177_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_val_3186_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
else
{
lean_object* v___x_3191_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 1, v_buckets_x27_3179_);
lean_ctor_set(v___x_3174_, 0, v_size_x27_3177_);
v___x_3191_ = v___x_3174_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_size_x27_3177_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_buckets_x27_3179_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_dec(v_b_3155_);
lean_dec_ref(v_a_3154_);
return v_m_3153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object* v_a_3196_, lean_object* v_fallback_3197_, lean_object* v_x_3198_){
_start:
{
if (lean_obj_tag(v_x_3198_) == 0)
{
lean_inc(v_fallback_3197_);
return v_fallback_3197_;
}
else
{
lean_object* v_key_3199_; lean_object* v_value_3200_; lean_object* v_tail_3201_; uint8_t v___x_3202_; 
v_key_3199_ = lean_ctor_get(v_x_3198_, 0);
v_value_3200_ = lean_ctor_get(v_x_3198_, 1);
v_tail_3201_ = lean_ctor_get(v_x_3198_, 2);
v___x_3202_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3199_, v_a_3196_);
if (v___x_3202_ == 0)
{
v_x_3198_ = v_tail_3201_;
goto _start;
}
else
{
lean_inc(v_value_3200_);
return v_value_3200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object* v_a_3204_, lean_object* v_fallback_3205_, lean_object* v_x_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3204_, v_fallback_3205_, v_x_3206_);
lean_dec(v_x_3206_);
lean_dec(v_fallback_3205_);
lean_dec_ref(v_a_3204_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object* v_m_3208_, lean_object* v_a_3209_, lean_object* v_fallback_3210_){
_start:
{
lean_object* v_buckets_3211_; lean_object* v___x_3212_; uint64_t v___x_3213_; uint64_t v___x_3214_; uint64_t v___x_3215_; uint64_t v_fold_3216_; uint64_t v___x_3217_; uint64_t v___x_3218_; uint64_t v___x_3219_; size_t v___x_3220_; size_t v___x_3221_; size_t v___x_3222_; size_t v___x_3223_; size_t v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_buckets_3211_ = lean_ctor_get(v_m_3208_, 1);
v___x_3212_ = lean_array_get_size(v_buckets_3211_);
v___x_3213_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3209_);
v___x_3214_ = 32ULL;
v___x_3215_ = lean_uint64_shift_right(v___x_3213_, v___x_3214_);
v_fold_3216_ = lean_uint64_xor(v___x_3213_, v___x_3215_);
v___x_3217_ = 16ULL;
v___x_3218_ = lean_uint64_shift_right(v_fold_3216_, v___x_3217_);
v___x_3219_ = lean_uint64_xor(v_fold_3216_, v___x_3218_);
v___x_3220_ = lean_uint64_to_usize(v___x_3219_);
v___x_3221_ = lean_usize_of_nat(v___x_3212_);
v___x_3222_ = ((size_t)1ULL);
v___x_3223_ = lean_usize_sub(v___x_3221_, v___x_3222_);
v___x_3224_ = lean_usize_land(v___x_3220_, v___x_3223_);
v___x_3225_ = lean_array_uget_borrowed(v_buckets_3211_, v___x_3224_);
v___x_3226_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3209_, v_fallback_3210_, v___x_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object* v_m_3227_, lean_object* v_a_3228_, lean_object* v_fallback_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3227_, v_a_3228_, v_fallback_3229_);
lean_dec(v_fallback_3229_);
lean_dec_ref(v_a_3228_);
lean_dec_ref(v_m_3227_);
return v_res_3230_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = lean_box(0);
v___x_3232_ = lean_unsigned_to_nat(16u);
v___x_3233_ = lean_mk_array(v___x_3232_, v___x_3231_);
return v___x_3233_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3234_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0);
v___x_3235_ = lean_unsigned_to_nat(0u);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
lean_ctor_set(v___x_3236_, 1, v___x_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object* v_idMap_3237_, lean_object* v_classesById_3238_, lean_object* v_id_3239_){
_start:
{
lean_object* v_representative_3240_; lean_object* v___x_3241_; lean_object* v_class_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v_class_3245_; lean_object* v___x_3246_; 
lean_inc_ref(v_id_3239_);
v_representative_3240_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_3237_, v_id_3239_);
v___x_3241_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_class_3242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_classesById_3238_, v_representative_3240_, v___x_3241_);
v___x_3243_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_classesById_3238_, v_representative_3240_);
v___x_3244_ = lean_box(0);
v_class_3245_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_class_3242_, v_id_3239_, v___x_3244_);
v___x_3246_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v___x_3243_, v_representative_3240_, v_class_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object* v_idMap_3247_, lean_object* v_classesById_3248_, lean_object* v_id_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3247_, v_classesById_3248_, v_id_3249_);
lean_dec_ref(v_idMap_3247_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object* v_idMap_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
if (lean_obj_tag(v_a_3252_) == 0)
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_a_3253_);
return v___x_3254_;
}
else
{
lean_object* v_key_3255_; lean_object* v_value_3256_; lean_object* v_tail_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_key_3255_ = lean_ctor_get(v_a_3252_, 0);
lean_inc(v_key_3255_);
v_value_3256_ = lean_ctor_get(v_a_3252_, 1);
lean_inc(v_value_3256_);
v_tail_3257_ = lean_ctor_get(v_a_3252_, 2);
lean_inc(v_tail_3257_);
lean_dec_ref_known(v_a_3252_, 3);
v___x_3258_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3251_, v_a_3253_, v_key_3255_);
v___x_3259_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3251_, v___x_3258_, v_value_3256_);
v_a_3252_ = v_tail_3257_;
v_a_3253_ = v___x_3259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object* v_idMap_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3261_, v_a_3262_, v_a_3263_);
lean_dec_ref(v_idMap_3261_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object* v_idMap_3265_, lean_object* v_as_3266_, size_t v_sz_3267_, size_t v_i_3268_, lean_object* v_b_3269_){
_start:
{
uint8_t v___x_3270_; 
v___x_3270_ = lean_usize_dec_lt(v_i_3268_, v_sz_3267_);
if (v___x_3270_ == 0)
{
return v_b_3269_;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3272_; 
v_a_3271_ = lean_array_uget_borrowed(v_as_3266_, v_i_3268_);
lean_inc(v_a_3271_);
v___x_3272_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3265_, v_a_3271_, v_b_3269_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref_known(v___x_3272_, 1);
return v_a_3273_;
}
else
{
lean_object* v_a_3274_; size_t v___x_3275_; size_t v___x_3276_; 
v_a_3274_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3272_, 1);
v___x_3275_ = ((size_t)1ULL);
v___x_3276_ = lean_usize_add(v_i_3268_, v___x_3275_);
v_i_3268_ = v___x_3276_;
v_b_3269_ = v_a_3274_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object* v_idMap_3278_, lean_object* v_as_3279_, lean_object* v_sz_3280_, lean_object* v_i_3281_, lean_object* v_b_3282_){
_start:
{
size_t v_sz_boxed_3283_; size_t v_i_boxed_3284_; lean_object* v_res_3285_; 
v_sz_boxed_3283_ = lean_unbox_usize(v_sz_3280_);
lean_dec(v_sz_3280_);
v_i_boxed_3284_ = lean_unbox_usize(v_i_3281_);
lean_dec(v_i_3281_);
v_res_3285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3278_, v_as_3279_, v_sz_boxed_3283_, v_i_boxed_3284_, v_b_3282_);
lean_dec_ref(v_as_3279_);
lean_dec_ref(v_idMap_3278_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object* v_idMap_3286_){
_start:
{
lean_object* v_buckets_3287_; lean_object* v_classesById_3288_; size_t v_sz_3289_; size_t v___x_3290_; lean_object* v___x_3291_; lean_object* v_buckets_3292_; size_t v_sz_3293_; lean_object* v___x_3294_; 
v_buckets_3287_ = lean_ctor_get(v_idMap_3286_, 1);
v_classesById_3288_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_sz_3289_ = lean_array_size(v_buckets_3287_);
v___x_3290_ = ((size_t)0ULL);
v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3286_, v_buckets_3287_, v_sz_3289_, v___x_3290_, v_classesById_3288_);
v_buckets_3292_ = lean_ctor_get(v___x_3291_, 1);
lean_inc_ref(v_buckets_3292_);
lean_dec_ref(v___x_3291_);
v_sz_3293_ = lean_array_size(v_buckets_3292_);
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_buckets_3292_, v_sz_3293_, v___x_3290_, v_classesById_3288_);
lean_dec_ref(v_buckets_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object* v_idMap_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v_idMap_3295_);
lean_dec_ref(v_idMap_3295_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object* v_00_u03b2_3297_, lean_object* v_m_3298_, lean_object* v_a_3299_, lean_object* v_fallback_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3298_, v_a_3299_, v_fallback_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object* v_00_u03b2_3302_, lean_object* v_m_3303_, lean_object* v_a_3304_, lean_object* v_fallback_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(v_00_u03b2_3302_, v_m_3303_, v_a_3304_, v_fallback_3305_);
lean_dec(v_fallback_3305_);
lean_dec_ref(v_a_3304_);
lean_dec_ref(v_m_3303_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object* v_00_u03b2_3307_, lean_object* v_m_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3308_, v_a_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object* v_00_u03b2_3311_, lean_object* v_m_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(v_00_u03b2_3311_, v_m_3312_, v_a_3313_);
lean_dec_ref(v_a_3313_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object* v_00_u03b2_3315_, lean_object* v_m_3316_, lean_object* v_a_3317_, lean_object* v_b_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_m_3316_, v_a_3317_, v_b_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object* v_00_u03b2_3320_, lean_object* v_m_3321_, lean_object* v_a_3322_, lean_object* v_b_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_m_3321_, v_a_3322_, v_b_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object* v_00_u03b2_3325_, lean_object* v_a_3326_, lean_object* v_fallback_3327_, lean_object* v_x_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3326_, v_fallback_3327_, v_x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3330_, lean_object* v_a_3331_, lean_object* v_fallback_3332_, lean_object* v_x_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(v_00_u03b2_3330_, v_a_3331_, v_fallback_3332_, v_x_3333_);
lean_dec(v_x_3333_);
lean_dec(v_fallback_3332_);
lean_dec_ref(v_a_3331_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object* v_00_u03b2_3335_, lean_object* v_a_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3336_, v_x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3339_, lean_object* v_a_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(v_00_u03b2_3339_, v_a_3340_, v_x_3341_);
lean_dec_ref(v_a_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object* v_00_u03b2_3343_, lean_object* v_data_3344_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_data_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object* v_00_u03b2_3346_, lean_object* v_a_3347_, lean_object* v_b_3348_, lean_object* v_x_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_3347_, v_b_3348_, v_x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3351_, lean_object* v_i_3352_, lean_object* v_source_3353_, lean_object* v_target_3354_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v_i_3352_, v_source_3353_, v_target_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object* v_00_u03b2_3356_, lean_object* v_x_3357_, lean_object* v_x_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_x_3357_, v_x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object* v_id_3360_, lean_object* v_baseId_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3363_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3362_, v_id_3360_);
v___x_3364_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3362_, v_baseId_3361_);
v___x_3365_ = l_Lean_Lsp_instBEqRefIdent_beq(v___x_3364_, v___x_3363_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = lean_box(0);
v___x_3367_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3362_, v___x_3363_, v___x_3364_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3366_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
return v___x_3368_;
}
else
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec_ref(v___x_3364_);
lean_dec_ref(v___x_3363_);
v___x_3369_ = lean_box(0);
v___x_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
lean_ctor_set(v___x_3370_, 1, v_a_3362_);
return v___x_3370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object* v_ci_3371_, lean_object* v_info_3372_, lean_object* v_x_3373_, lean_object* v___y_3374_){
_start:
{
if (lean_obj_tag(v_info_3372_) == 11)
{
lean_object* v_toCommandContextInfo_3375_; lean_object* v_i_3376_; lean_object* v_env_3377_; lean_object* v___x_3378_; lean_object* v_mainModule_3379_; lean_object* v_id_3380_; lean_object* v_baseId_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_toCommandContextInfo_3375_ = lean_ctor_get(v_ci_3371_, 0);
v_i_3376_ = lean_ctor_get(v_info_3372_, 0);
lean_inc_ref(v_i_3376_);
lean_dec_ref_known(v_info_3372_, 1);
v_env_3377_ = lean_ctor_get(v_toCommandContextInfo_3375_, 0);
v___x_3378_ = l_Lean_Environment_header(v_env_3377_);
v_mainModule_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_mainModule_3379_);
lean_dec_ref(v___x_3378_);
v_id_3380_ = lean_ctor_get(v_i_3376_, 1);
lean_inc(v_id_3380_);
v_baseId_3381_ = lean_ctor_get(v_i_3376_, 2);
lean_inc(v_baseId_3381_);
lean_dec_ref(v_i_3376_);
v___x_3382_ = 1;
v___x_3383_ = l_Lean_Name_toString(v_mainModule_3379_, v___x_3382_);
v___x_3384_ = l_Lean_Name_toString(v_id_3380_, v___x_3382_);
lean_inc_ref(v___x_3383_);
v___x_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = l_Lean_Name_toString(v_baseId_3381_, v___x_3382_);
v___x_3387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3383_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v___x_3385_, v___x_3387_, v___y_3374_);
return v___x_3388_;
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
lean_dec_ref(v_info_3372_);
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v___y_3374_);
return v___x_3390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object* v_ci_3391_, lean_object* v_info_3392_, lean_object* v_x_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(v_ci_3391_, v_info_3392_, v_x_3393_, v___y_3394_);
lean_dec_ref(v_x_3393_);
lean_dec_ref(v_ci_3391_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object* v_x_3396_, lean_object* v_x_3397_, lean_object* v_x_3398_, lean_object* v___y_3399_){
_start:
{
uint8_t v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = 1;
v___x_3401_ = lean_box(v___x_3400_);
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___y_3399_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object* v_x_3403_, lean_object* v_x_3404_, lean_object* v_x_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(v_x_3403_, v_x_3404_, v_x_3405_, v___y_3406_);
lean_dec_ref(v_x_3405_);
lean_dec_ref(v_x_3404_);
lean_dec_ref(v_x_3403_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v___f_3410_; lean_object* v___f_3411_; lean_object* v___f_3412_; lean_object* v___f_3413_; lean_object* v___f_3414_; lean_object* v___f_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___f_3420_; lean_object* v___f_3421_; lean_object* v___f_3422_; lean_object* v___f_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3750__overap_3432_; lean_object* v___x_3433_; 
v___f_3410_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3411_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3412_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3413_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3414_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3415_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3416_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___f_3410_);
lean_ctor_set(v___x_3417_, 1, v___f_3411_);
v___x_3418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
lean_ctor_set(v___x_3418_, 1, v___f_3412_);
lean_ctor_set(v___x_3418_, 2, v___f_3413_);
lean_ctor_set(v___x_3418_, 3, v___f_3414_);
lean_ctor_set(v___x_3418_, 4, v___f_3415_);
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
lean_ctor_set(v___x_3419_, 1, v___f_3416_);
lean_inc_ref_n(v___x_3419_, 6);
v___f_3420_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3420_, 0, v___x_3419_);
v___f_3421_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3421_, 0, v___x_3419_);
v___f_3422_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3422_, 0, v___x_3419_);
v___f_3423_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3423_, 0, v___x_3419_);
v___x_3424_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3424_, 0, lean_box(0));
lean_closure_set(v___x_3424_, 1, lean_box(0));
lean_closure_set(v___x_3424_, 2, v___x_3419_);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v___f_3420_);
v___x_3426_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3426_, 0, lean_box(0));
lean_closure_set(v___x_3426_, 1, lean_box(0));
lean_closure_set(v___x_3426_, 2, v___x_3419_);
v___x_3427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
lean_ctor_set(v___x_3427_, 2, v___f_3421_);
lean_ctor_set(v___x_3427_, 3, v___f_3422_);
lean_ctor_set(v___x_3427_, 4, v___f_3423_);
v___x_3428_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3428_, 0, lean_box(0));
lean_closure_set(v___x_3428_, 1, lean_box(0));
lean_closure_set(v___x_3428_, 2, v___x_3419_);
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = lean_box(0);
v___x_3431_ = l_instInhabitedOfMonad___redArg(v___x_3429_, v___x_3430_);
v___x_3750__overap_3432_ = lean_panic_fn_borrowed(v___x_3431_, v_msg_3408_);
lean_dec(v___x_3431_);
v___x_3433_ = lean_apply_1(v___x_3750__overap_3432_, v___y_3409_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3434_, lean_object* v_postNode_3435_, lean_object* v_x_3436_, lean_object* v_x_3437_, lean_object* v___y_3438_){
_start:
{
switch(lean_obj_tag(v_x_3437_))
{
case 0:
{
lean_object* v_i_3439_; lean_object* v_t_3440_; lean_object* v___x_3441_; 
v_i_3439_ = lean_ctor_get(v_x_3437_, 0);
lean_inc_ref(v_i_3439_);
v_t_3440_ = lean_ctor_get(v_x_3437_, 1);
lean_inc_ref(v_t_3440_);
lean_dec_ref_known(v_x_3437_, 2);
v___x_3441_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3439_, v_x_3436_);
v_x_3436_ = v___x_3441_;
v_x_3437_ = v_t_3440_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3436_) == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec_ref_known(v_x_3437_, 2);
lean_dec_ref(v_postNode_3435_);
lean_dec_ref(v_preNode_3434_);
v___x_3443_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3444_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3443_, v___y_3438_);
return v___x_3444_;
}
else
{
lean_object* v_i_3445_; lean_object* v_children_3446_; lean_object* v_val_3447_; lean_object* v___x_3448_; lean_object* v_fst_3449_; uint8_t v___x_3450_; 
v_i_3445_ = lean_ctor_get(v_x_3437_, 0);
lean_inc_ref_n(v_i_3445_, 2);
v_children_3446_ = lean_ctor_get(v_x_3437_, 1);
lean_inc_ref_n(v_children_3446_, 2);
lean_dec_ref_known(v_x_3437_, 2);
v_val_3447_ = lean_ctor_get(v_x_3436_, 0);
lean_inc_n(v_val_3447_, 2);
lean_inc_ref(v_preNode_3434_);
v___x_3448_ = lean_apply_4(v_preNode_3434_, v_val_3447_, v_i_3445_, v_children_3446_, v___y_3438_);
v_fst_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_fst_3449_);
v___x_3450_ = lean_unbox(v_fst_3449_);
lean_dec(v_fst_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_preNode_3434_);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_x_3436_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; 
v_unused_3470_ = lean_ctor_get(v_x_3436_, 0);
lean_dec(v_unused_3470_);
v___x_3452_ = v_x_3436_;
v_isShared_3453_ = v_isSharedCheck_3469_;
goto v_resetjp_3451_;
}
else
{
lean_dec(v_x_3436_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3469_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_snd_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v_fst_3457_; lean_object* v_snd_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3468_; 
v_snd_3454_ = lean_ctor_get(v___x_3448_, 1);
lean_inc(v_snd_3454_);
lean_dec_ref(v___x_3448_);
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_apply_5(v_postNode_3435_, v_val_3447_, v_i_3445_, v_children_3446_, v___x_3455_, v_snd_3454_);
v_fst_3457_ = lean_ctor_get(v___x_3456_, 0);
v_snd_3458_ = lean_ctor_get(v___x_3456_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3460_ = v___x_3456_;
v_isShared_3461_ = v_isSharedCheck_3468_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_snd_3458_);
lean_inc(v_fst_3457_);
lean_dec(v___x_3456_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3468_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v_fst_3457_);
v___x_3463_ = v___x_3452_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_fst_3457_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3463_);
v___x_3465_ = v___x_3460_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_snd_3458_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
else
{
lean_object* v_snd_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v_fst_3476_; lean_object* v_snd_3477_; lean_object* v___x_3478_; lean_object* v_fst_3479_; lean_object* v_snd_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3488_; 
v_snd_3471_ = lean_ctor_get(v___x_3448_, 1);
lean_inc(v_snd_3471_);
lean_dec_ref(v___x_3448_);
v___x_3472_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3436_, v_i_3445_);
v___x_3473_ = l_Lean_PersistentArray_toList___redArg(v_children_3446_);
v___x_3474_ = lean_box(0);
lean_inc_ref(v_postNode_3435_);
v___x_3475_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3434_, v_postNode_3435_, v___x_3472_, v___x_3473_, v___x_3474_, v_snd_3471_);
v_fst_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_fst_3476_);
v_snd_3477_ = lean_ctor_get(v___x_3475_, 1);
lean_inc(v_snd_3477_);
lean_dec_ref(v___x_3475_);
v___x_3478_ = lean_apply_5(v_postNode_3435_, v_val_3447_, v_i_3445_, v_children_3446_, v_fst_3476_, v_snd_3477_);
v_fst_3479_ = lean_ctor_get(v___x_3478_, 0);
v_snd_3480_ = lean_ctor_get(v___x_3478_, 1);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3482_ = v___x_3478_;
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_snd_3480_);
lean_inc(v_fst_3479_);
lean_dec(v___x_3478_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_fst_3479_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3484_);
v___x_3486_ = v___x_3482_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_snd_3480_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
default: 
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec_ref_known(v_x_3437_, 1);
lean_dec(v_x_3436_);
lean_dec_ref(v_postNode_3435_);
lean_dec_ref(v_preNode_3434_);
v___x_3489_ = lean_box(0);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___y_3438_);
return v___x_3490_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3491_, lean_object* v_postNode_3492_, lean_object* v___x_3493_, lean_object* v_x_3494_, lean_object* v_x_3495_, lean_object* v___y_3496_){
_start:
{
if (lean_obj_tag(v_x_3494_) == 0)
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
lean_dec(v___x_3493_);
lean_dec_ref(v_postNode_3492_);
lean_dec_ref(v_preNode_3491_);
v___x_3497_ = l_List_reverse___redArg(v_x_3495_);
v___x_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
lean_ctor_set(v___x_3498_, 1, v___y_3496_);
return v___x_3498_;
}
else
{
lean_object* v_head_3499_; lean_object* v_tail_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3511_; 
v_head_3499_ = lean_ctor_get(v_x_3494_, 0);
v_tail_3500_ = lean_ctor_get(v_x_3494_, 1);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_x_3494_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3502_ = v_x_3494_;
v_isShared_3503_ = v_isSharedCheck_3511_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_tail_3500_);
lean_inc(v_head_3499_);
lean_dec(v_x_3494_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3511_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v_fst_3505_; lean_object* v_snd_3506_; lean_object* v___x_3508_; 
lean_inc(v___x_3493_);
lean_inc_ref(v_postNode_3492_);
lean_inc_ref(v_preNode_3491_);
v___x_3504_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3491_, v_postNode_3492_, v___x_3493_, v_head_3499_, v___y_3496_);
v_fst_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_fst_3505_);
v_snd_3506_ = lean_ctor_get(v___x_3504_, 1);
lean_inc(v_snd_3506_);
lean_dec_ref(v___x_3504_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v_x_3495_);
lean_ctor_set(v___x_3502_, 0, v_fst_3505_);
v___x_3508_ = v___x_3502_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_fst_3505_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_x_3495_);
v___x_3508_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
v_x_3494_ = v_tail_3500_;
v_x_3495_ = v___x_3508_;
v___y_3496_ = v_snd_3506_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3512_, lean_object* v_ci_3513_, lean_object* v_i_3514_, lean_object* v_cs_3515_, lean_object* v_x_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = lean_apply_4(v_postNode_3512_, v_ci_3513_, v_i_3514_, v_cs_3515_, v___y_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3519_, lean_object* v_ci_3520_, lean_object* v_i_3521_, lean_object* v_cs_3522_, lean_object* v_x_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3519_, v_ci_3520_, v_i_3521_, v_cs_3522_, v_x_3523_, v___y_3524_);
lean_dec(v_x_3523_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3526_, lean_object* v_postNode_3527_, lean_object* v_ctx_x3f_3528_, lean_object* v_t_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v___f_3531_; lean_object* v___x_3532_; lean_object* v_snd_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3541_; 
v___f_3531_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3531_, 0, v_postNode_3527_);
v___x_3532_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3526_, v___f_3531_, v_ctx_x3f_3528_, v_t_3529_, v___y_3530_);
v_snd_3533_ = lean_ctor_get(v___x_3532_, 1);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; 
v_unused_3542_ = lean_ctor_get(v___x_3532_, 0);
lean_dec(v_unused_3542_);
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3541_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_snd_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3541_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3537_ = lean_box(0);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3537_);
v___x_3539_ = v___x_3535_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_snd_3533_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(lean_object* v_as_3545_, size_t v_i_3546_, size_t v_stop_3547_, lean_object* v_b_3548_, lean_object* v___y_3549_){
_start:
{
uint8_t v___x_3550_; 
v___x_3550_ = lean_usize_dec_eq(v_i_3546_, v_stop_3547_);
if (v___x_3550_ == 0)
{
lean_object* v___f_3551_; lean_object* v___f_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v_fst_3556_; lean_object* v_snd_3557_; size_t v___x_3558_; size_t v___x_3559_; 
v___f_3551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0));
v___f_3552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1));
v___x_3553_ = lean_array_uget_borrowed(v_as_3545_, v_i_3546_);
v___x_3554_ = lean_box(0);
lean_inc(v___x_3553_);
v___x_3555_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(v___f_3551_, v___f_3552_, v___x_3554_, v___x_3553_, v___y_3549_);
v_fst_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_fst_3556_);
v_snd_3557_ = lean_ctor_get(v___x_3555_, 1);
lean_inc(v_snd_3557_);
lean_dec_ref(v___x_3555_);
v___x_3558_ = ((size_t)1ULL);
v___x_3559_ = lean_usize_add(v_i_3546_, v___x_3558_);
v_i_3546_ = v___x_3559_;
v_b_3548_ = v_fst_3556_;
v___y_3549_ = v_snd_3557_;
goto _start;
}
else
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3561_, 0, v_b_3548_);
lean_ctor_set(v___x_3561_, 1, v___y_3549_);
return v___x_3561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___boxed(lean_object* v_as_3562_, lean_object* v_i_3563_, lean_object* v_stop_3564_, lean_object* v_b_3565_, lean_object* v___y_3566_){
_start:
{
size_t v_i_boxed_3567_; size_t v_stop_boxed_3568_; lean_object* v_res_3569_; 
v_i_boxed_3567_ = lean_unbox_usize(v_i_3563_);
lean_dec(v_i_3563_);
v_stop_boxed_3568_ = lean_unbox_usize(v_stop_3564_);
lean_dec(v_stop_3564_);
v_res_3569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_as_3562_, v_i_boxed_3567_, v_stop_boxed_3568_, v_b_3565_, v___y_3566_);
lean_dec_ref(v_as_3562_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(lean_object* v_a_3570_, lean_object* v_x_3571_){
_start:
{
if (lean_obj_tag(v_x_3571_) == 0)
{
lean_object* v___x_3572_; 
v___x_3572_ = lean_box(0);
return v___x_3572_;
}
else
{
lean_object* v_key_3573_; lean_object* v_value_3574_; lean_object* v_tail_3575_; uint8_t v___x_3576_; 
v_key_3573_ = lean_ctor_get(v_x_3571_, 0);
v_value_3574_ = lean_ctor_get(v_x_3571_, 1);
v_tail_3575_ = lean_ctor_get(v_x_3571_, 2);
v___x_3576_ = l_Lean_Lsp_instBEqRange_beq(v_key_3573_, v_a_3570_);
if (v___x_3576_ == 0)
{
v_x_3571_ = v_tail_3575_;
goto _start;
}
else
{
lean_object* v___x_3578_; 
lean_inc(v_value_3574_);
v___x_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3578_, 0, v_value_3574_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_3579_, lean_object* v_x_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3579_, v_x_3580_);
lean_dec(v_x_3580_);
lean_dec_ref(v_a_3579_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(lean_object* v_m_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v_buckets_3584_; lean_object* v___x_3585_; uint64_t v___x_3586_; uint64_t v___x_3587_; uint64_t v___x_3588_; uint64_t v_fold_3589_; uint64_t v___x_3590_; uint64_t v___x_3591_; uint64_t v___x_3592_; size_t v___x_3593_; size_t v___x_3594_; size_t v___x_3595_; size_t v___x_3596_; size_t v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_buckets_3584_ = lean_ctor_get(v_m_3582_, 1);
v___x_3585_ = lean_array_get_size(v_buckets_3584_);
v___x_3586_ = l_Lean_Lsp_instHashableRange_hash(v_a_3583_);
v___x_3587_ = 32ULL;
v___x_3588_ = lean_uint64_shift_right(v___x_3586_, v___x_3587_);
v_fold_3589_ = lean_uint64_xor(v___x_3586_, v___x_3588_);
v___x_3590_ = 16ULL;
v___x_3591_ = lean_uint64_shift_right(v_fold_3589_, v___x_3590_);
v___x_3592_ = lean_uint64_xor(v_fold_3589_, v___x_3591_);
v___x_3593_ = lean_uint64_to_usize(v___x_3592_);
v___x_3594_ = lean_usize_of_nat(v___x_3585_);
v___x_3595_ = ((size_t)1ULL);
v___x_3596_ = lean_usize_sub(v___x_3594_, v___x_3595_);
v___x_3597_ = lean_usize_land(v___x_3593_, v___x_3596_);
v___x_3598_ = lean_array_uget_borrowed(v_buckets_3584_, v___x_3597_);
v___x_3599_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3583_, v___x_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg___boxed(lean_object* v_m_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3600_, v_a_3601_);
lean_dec_ref(v_a_3601_);
lean_dec_ref(v_m_3600_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(lean_object* v_posMap_3603_, lean_object* v_as_3604_, size_t v_sz_3605_, size_t v_i_3606_, lean_object* v_b_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_a_3610_; lean_object* v_snd_3611_; uint8_t v___x_3615_; 
v___x_3615_ = lean_usize_dec_lt(v_i_3606_, v_sz_3605_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3616_, 0, v_b_3607_);
lean_ctor_set(v___x_3616_, 1, v___y_3608_);
return v___x_3616_;
}
else
{
lean_object* v_a_3617_; lean_object* v_ident_3618_; lean_object* v_range_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_a_3617_ = lean_array_uget_borrowed(v_as_3604_, v_i_3606_);
v_ident_3618_ = lean_ctor_get(v_a_3617_, 0);
v_range_3619_ = lean_ctor_get(v_a_3617_, 2);
v___x_3620_ = lean_box(0);
v___x_3621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_posMap_3603_, v_range_3619_);
if (lean_obj_tag(v___x_3621_) == 1)
{
lean_object* v_val_3622_; lean_object* v___x_3623_; lean_object* v_snd_3624_; 
v_val_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_val_3622_);
lean_dec_ref_known(v___x_3621_, 1);
lean_inc_ref(v_ident_3618_);
v___x_3623_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v_val_3622_, v_ident_3618_, v___y_3608_);
v_snd_3624_ = lean_ctor_get(v___x_3623_, 1);
lean_inc(v_snd_3624_);
lean_dec_ref(v___x_3623_);
v_a_3610_ = v___x_3620_;
v_snd_3611_ = v_snd_3624_;
goto v___jp_3609_;
}
else
{
lean_dec(v___x_3621_);
v_a_3610_ = v___x_3620_;
v_snd_3611_ = v___y_3608_;
goto v___jp_3609_;
}
}
v___jp_3609_:
{
size_t v___x_3612_; size_t v___x_3613_; 
v___x_3612_ = ((size_t)1ULL);
v___x_3613_ = lean_usize_add(v_i_3606_, v___x_3612_);
v_i_3606_ = v___x_3613_;
v_b_3607_ = v_a_3610_;
v___y_3608_ = v_snd_3611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2___boxed(lean_object* v_posMap_3625_, lean_object* v_as_3626_, lean_object* v_sz_3627_, lean_object* v_i_3628_, lean_object* v_b_3629_, lean_object* v___y_3630_){
_start:
{
size_t v_sz_boxed_3631_; size_t v_i_boxed_3632_; lean_object* v_res_3633_; 
v_sz_boxed_3631_ = lean_unbox_usize(v_sz_3627_);
lean_dec(v_sz_3627_);
v_i_boxed_3632_ = lean_unbox_usize(v_i_3628_);
lean_dec(v_i_3628_);
v_res_3633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3625_, v_as_3626_, v_sz_boxed_3631_, v_i_boxed_3632_, v_b_3629_, v___y_3630_);
lean_dec_ref(v_as_3626_);
lean_dec_ref(v_posMap_3625_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(lean_object* v_trees_3634_, lean_object* v_refs_3635_, lean_object* v_posMap_3636_){
_start:
{
lean_object* v___x_3637_; size_t v_sz_3638_; size_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v_snd_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3637_ = lean_box(0);
v_sz_3638_ = lean_array_size(v_refs_3635_);
v___x_3639_ = ((size_t)0ULL);
v___x_3640_ = lean_unsigned_to_nat(0u);
v___x_3641_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v___x_3642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3636_, v_refs_3635_, v_sz_3638_, v___x_3639_, v___x_3637_, v___x_3641_);
v_snd_3643_ = lean_ctor_get(v___x_3642_, 1);
lean_inc(v_snd_3643_);
lean_dec_ref(v___x_3642_);
v___x_3644_ = lean_array_get_size(v_trees_3634_);
v___x_3645_ = lean_nat_dec_lt(v___x_3640_, v___x_3644_);
if (v___x_3645_ == 0)
{
return v_snd_3643_;
}
else
{
size_t v___x_3646_; lean_object* v___x_3647_; lean_object* v_snd_3648_; 
v___x_3646_ = lean_usize_of_nat(v___x_3644_);
v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3634_, v___x_3639_, v___x_3646_, v___x_3637_, v_snd_3643_);
v_snd_3648_ = lean_ctor_get(v___x_3647_, 1);
lean_inc(v_snd_3648_);
lean_dec_ref(v___x_3647_);
return v_snd_3648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap___boxed(lean_object* v_trees_3649_, lean_object* v_refs_3650_, lean_object* v_posMap_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3649_, v_refs_3650_, v_posMap_3651_);
lean_dec_ref(v_posMap_3651_);
lean_dec_ref(v_refs_3650_);
lean_dec_ref(v_trees_3649_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(lean_object* v_00_u03b2_3653_, lean_object* v_m_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3654_, v_a_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___boxed(lean_object* v_00_u03b2_3657_, lean_object* v_m_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(v_00_u03b2_3657_, v_m_3658_, v_a_3659_);
lean_dec_ref(v_a_3659_);
lean_dec_ref(v_m_3658_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3661_, lean_object* v_msg_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v_msg_3662_, v___y_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object* v_00_u03b1_3665_, lean_object* v_preNode_3666_, lean_object* v_postNode_3667_, lean_object* v_x_3668_, lean_object* v_x_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3666_, v_postNode_3667_, v_x_3668_, v_x_3669_, v___y_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object* v_00_u03b2_3672_, lean_object* v_a_3673_, lean_object* v_x_3674_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3673_, v_x_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3676_, lean_object* v_a_3677_, lean_object* v_x_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(v_00_u03b2_3676_, v_a_3677_, v_x_3678_);
lean_dec(v_x_3678_);
lean_dec_ref(v_a_3677_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3680_, lean_object* v_preNode_3681_, lean_object* v_postNode_3682_, lean_object* v___x_3683_, lean_object* v_x_3684_, lean_object* v_x_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3681_, v_postNode_3682_, v___x_3683_, v_x_3684_, v_x_3685_, v___y_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(lean_object* v_a_3688_, lean_object* v_b_3689_, lean_object* v_x_3690_){
_start:
{
if (lean_obj_tag(v_x_3690_) == 0)
{
lean_dec(v_b_3689_);
lean_dec_ref(v_a_3688_);
return v_x_3690_;
}
else
{
lean_object* v_key_3691_; lean_object* v_value_3692_; lean_object* v_tail_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3705_; 
v_key_3691_ = lean_ctor_get(v_x_3690_, 0);
v_value_3692_ = lean_ctor_get(v_x_3690_, 1);
v_tail_3693_ = lean_ctor_get(v_x_3690_, 2);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_x_3690_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3695_ = v_x_3690_;
v_isShared_3696_ = v_isSharedCheck_3705_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_tail_3693_);
lean_inc(v_value_3692_);
lean_inc(v_key_3691_);
lean_dec(v_x_3690_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3705_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
uint8_t v___x_3697_; 
v___x_3697_ = l_Lean_Lsp_instBEqRange_beq(v_key_3691_, v_a_3688_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3698_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3688_, v_b_3689_, v_tail_3693_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 2, v___x_3698_);
v___x_3700_ = v___x_3695_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_key_3691_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_value_3692_);
lean_ctor_set(v_reuseFailAlloc_3701_, 2, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
else
{
lean_object* v___x_3703_; 
lean_dec(v_value_3692_);
lean_dec(v_key_3691_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 1, v_b_3689_);
lean_ctor_set(v___x_3695_, 0, v_a_3688_);
v___x_3703_ = v___x_3695_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3688_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_b_3689_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_tail_3693_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_3706_, lean_object* v_x_3707_){
_start:
{
if (lean_obj_tag(v_x_3707_) == 0)
{
return v_x_3706_;
}
else
{
lean_object* v_key_3708_; lean_object* v_value_3709_; lean_object* v_tail_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3733_; 
v_key_3708_ = lean_ctor_get(v_x_3707_, 0);
v_value_3709_ = lean_ctor_get(v_x_3707_, 1);
v_tail_3710_ = lean_ctor_get(v_x_3707_, 2);
v_isSharedCheck_3733_ = !lean_is_exclusive(v_x_3707_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3712_ = v_x_3707_;
v_isShared_3713_ = v_isSharedCheck_3733_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_tail_3710_);
lean_inc(v_value_3709_);
lean_inc(v_key_3708_);
lean_dec(v_x_3707_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3733_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3714_; uint64_t v___x_3715_; uint64_t v___x_3716_; uint64_t v___x_3717_; uint64_t v_fold_3718_; uint64_t v___x_3719_; uint64_t v___x_3720_; uint64_t v___x_3721_; size_t v___x_3722_; size_t v___x_3723_; size_t v___x_3724_; size_t v___x_3725_; size_t v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3714_ = lean_array_get_size(v_x_3706_);
v___x_3715_ = l_Lean_Lsp_instHashableRange_hash(v_key_3708_);
v___x_3716_ = 32ULL;
v___x_3717_ = lean_uint64_shift_right(v___x_3715_, v___x_3716_);
v_fold_3718_ = lean_uint64_xor(v___x_3715_, v___x_3717_);
v___x_3719_ = 16ULL;
v___x_3720_ = lean_uint64_shift_right(v_fold_3718_, v___x_3719_);
v___x_3721_ = lean_uint64_xor(v_fold_3718_, v___x_3720_);
v___x_3722_ = lean_uint64_to_usize(v___x_3721_);
v___x_3723_ = lean_usize_of_nat(v___x_3714_);
v___x_3724_ = ((size_t)1ULL);
v___x_3725_ = lean_usize_sub(v___x_3723_, v___x_3724_);
v___x_3726_ = lean_usize_land(v___x_3722_, v___x_3725_);
v___x_3727_ = lean_array_uget_borrowed(v_x_3706_, v___x_3726_);
lean_inc(v___x_3727_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 2, v___x_3727_);
v___x_3729_ = v___x_3712_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_key_3708_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_value_3709_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_array_uset(v_x_3706_, v___x_3726_, v___x_3729_);
v_x_3706_ = v___x_3730_;
v_x_3707_ = v_tail_3710_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3734_, lean_object* v_source_3735_, lean_object* v_target_3736_){
_start:
{
lean_object* v___x_3737_; uint8_t v___x_3738_; 
v___x_3737_ = lean_array_get_size(v_source_3735_);
v___x_3738_ = lean_nat_dec_lt(v_i_3734_, v___x_3737_);
if (v___x_3738_ == 0)
{
lean_dec_ref(v_source_3735_);
lean_dec(v_i_3734_);
return v_target_3736_;
}
else
{
lean_object* v_es_3739_; lean_object* v___x_3740_; lean_object* v_source_3741_; lean_object* v_target_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_es_3739_ = lean_array_fget(v_source_3735_, v_i_3734_);
v___x_3740_ = lean_box(0);
v_source_3741_ = lean_array_fset(v_source_3735_, v_i_3734_, v___x_3740_);
v_target_3742_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3736_, v_es_3739_);
v___x_3743_ = lean_unsigned_to_nat(1u);
v___x_3744_ = lean_nat_add(v_i_3734_, v___x_3743_);
lean_dec(v_i_3734_);
v_i_3734_ = v___x_3744_;
v_source_3735_ = v_source_3741_;
v_target_3736_ = v_target_3742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(lean_object* v_data_3746_){
_start:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v_nbuckets_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3747_ = lean_array_get_size(v_data_3746_);
v___x_3748_ = lean_unsigned_to_nat(2u);
v_nbuckets_3749_ = lean_nat_mul(v___x_3747_, v___x_3748_);
v___x_3750_ = lean_unsigned_to_nat(0u);
v___x_3751_ = lean_box(0);
v___x_3752_ = lean_mk_array(v_nbuckets_3749_, v___x_3751_);
v___x_3753_ = lean_array_propagate_mark(v_data_3746_, v___x_3752_);
v___x_3754_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v___x_3750_, v_data_3746_, v___x_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object* v_a_3755_, lean_object* v_x_3756_){
_start:
{
if (lean_obj_tag(v_x_3756_) == 0)
{
uint8_t v___x_3757_; 
v___x_3757_ = 0;
return v___x_3757_;
}
else
{
lean_object* v_key_3758_; lean_object* v_tail_3759_; uint8_t v___x_3760_; 
v_key_3758_ = lean_ctor_get(v_x_3756_, 0);
v_tail_3759_ = lean_ctor_get(v_x_3756_, 2);
v___x_3760_ = l_Lean_Lsp_instBEqRange_beq(v_key_3758_, v_a_3755_);
if (v___x_3760_ == 0)
{
v_x_3756_ = v_tail_3759_;
goto _start;
}
else
{
return v___x_3760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object* v_a_3762_, lean_object* v_x_3763_){
_start:
{
uint8_t v_res_3764_; lean_object* v_r_3765_; 
v_res_3764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3762_, v_x_3763_);
lean_dec(v_x_3763_);
lean_dec_ref(v_a_3762_);
v_r_3765_ = lean_box(v_res_3764_);
return v_r_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object* v_m_3766_, lean_object* v_a_3767_, lean_object* v_b_3768_){
_start:
{
lean_object* v_size_3769_; lean_object* v_buckets_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3813_; 
v_size_3769_ = lean_ctor_get(v_m_3766_, 0);
v_buckets_3770_ = lean_ctor_get(v_m_3766_, 1);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_m_3766_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3772_ = v_m_3766_;
v_isShared_3773_ = v_isSharedCheck_3813_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_buckets_3770_);
lean_inc(v_size_3769_);
lean_dec(v_m_3766_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3813_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; uint64_t v___x_3775_; uint64_t v___x_3776_; uint64_t v___x_3777_; uint64_t v_fold_3778_; uint64_t v___x_3779_; uint64_t v___x_3780_; uint64_t v___x_3781_; size_t v___x_3782_; size_t v___x_3783_; size_t v___x_3784_; size_t v___x_3785_; size_t v___x_3786_; lean_object* v_bkt_3787_; uint8_t v___x_3788_; 
v___x_3774_ = lean_array_get_size(v_buckets_3770_);
v___x_3775_ = l_Lean_Lsp_instHashableRange_hash(v_a_3767_);
v___x_3776_ = 32ULL;
v___x_3777_ = lean_uint64_shift_right(v___x_3775_, v___x_3776_);
v_fold_3778_ = lean_uint64_xor(v___x_3775_, v___x_3777_);
v___x_3779_ = 16ULL;
v___x_3780_ = lean_uint64_shift_right(v_fold_3778_, v___x_3779_);
v___x_3781_ = lean_uint64_xor(v_fold_3778_, v___x_3780_);
v___x_3782_ = lean_uint64_to_usize(v___x_3781_);
v___x_3783_ = lean_usize_of_nat(v___x_3774_);
v___x_3784_ = ((size_t)1ULL);
v___x_3785_ = lean_usize_sub(v___x_3783_, v___x_3784_);
v___x_3786_ = lean_usize_land(v___x_3782_, v___x_3785_);
v_bkt_3787_ = lean_array_uget_borrowed(v_buckets_3770_, v___x_3786_);
v___x_3788_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3767_, v_bkt_3787_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; lean_object* v_size_x27_3790_; lean_object* v___x_3791_; lean_object* v_buckets_x27_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3789_ = lean_unsigned_to_nat(1u);
v_size_x27_3790_ = lean_nat_add(v_size_3769_, v___x_3789_);
lean_dec(v_size_3769_);
lean_inc(v_bkt_3787_);
v___x_3791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3791_, 0, v_a_3767_);
lean_ctor_set(v___x_3791_, 1, v_b_3768_);
lean_ctor_set(v___x_3791_, 2, v_bkt_3787_);
v_buckets_x27_3792_ = lean_array_uset(v_buckets_3770_, v___x_3786_, v___x_3791_);
v___x_3793_ = lean_unsigned_to_nat(4u);
v___x_3794_ = lean_nat_mul(v_size_x27_3790_, v___x_3793_);
v___x_3795_ = lean_unsigned_to_nat(3u);
v___x_3796_ = lean_nat_div(v___x_3794_, v___x_3795_);
lean_dec(v___x_3794_);
v___x_3797_ = lean_array_get_size(v_buckets_x27_3792_);
v___x_3798_ = lean_nat_dec_le(v___x_3796_, v___x_3797_);
lean_dec(v___x_3796_);
if (v___x_3798_ == 0)
{
lean_object* v_val_3799_; lean_object* v___x_3801_; 
v_val_3799_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_buckets_x27_3792_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v_val_3799_);
lean_ctor_set(v___x_3772_, 0, v_size_x27_3790_);
v___x_3801_ = v___x_3772_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_size_x27_3790_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_val_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
else
{
lean_object* v___x_3804_; 
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v_buckets_x27_3792_);
lean_ctor_set(v___x_3772_, 0, v_size_x27_3790_);
v___x_3804_ = v___x_3772_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_size_x27_3790_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_buckets_x27_3792_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
else
{
lean_object* v___x_3806_; lean_object* v_buckets_x27_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
lean_inc(v_bkt_3787_);
v___x_3806_ = lean_box(0);
v_buckets_x27_3807_ = lean_array_uset(v_buckets_3770_, v___x_3786_, v___x_3806_);
v___x_3808_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3767_, v_b_3768_, v_bkt_3787_);
v___x_3809_ = lean_array_uset(v_buckets_x27_3807_, v___x_3786_, v___x_3808_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v___x_3809_);
v___x_3811_ = v___x_3772_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_size_3769_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object* v_as_3814_, size_t v_sz_3815_, size_t v_i_3816_, lean_object* v_b_3817_){
_start:
{
lean_object* v_a_3819_; uint8_t v___x_3823_; 
v___x_3823_ = lean_usize_dec_lt(v_i_3816_, v_sz_3815_);
if (v___x_3823_ == 0)
{
return v_b_3817_;
}
else
{
lean_object* v_a_3824_; uint8_t v_isBinder_3825_; 
v_a_3824_ = lean_array_uget_borrowed(v_as_3814_, v_i_3816_);
v_isBinder_3825_ = lean_ctor_get_uint8(v_a_3824_, sizeof(void*)*6);
if (v_isBinder_3825_ == 1)
{
lean_object* v_ident_3826_; lean_object* v_range_3827_; lean_object* v___x_3828_; 
v_ident_3826_ = lean_ctor_get(v_a_3824_, 0);
v_range_3827_ = lean_ctor_get(v_a_3824_, 2);
lean_inc_ref(v_ident_3826_);
lean_inc_ref(v_range_3827_);
v___x_3828_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_b_3817_, v_range_3827_, v_ident_3826_);
v_a_3819_ = v___x_3828_;
goto v___jp_3818_;
}
else
{
v_a_3819_ = v_b_3817_;
goto v___jp_3818_;
}
}
v___jp_3818_:
{
size_t v___x_3820_; size_t v___x_3821_; 
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = lean_usize_add(v_i_3816_, v___x_3820_);
v_i_3816_ = v___x_3821_;
v_b_3817_ = v_a_3819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object* v_as_3829_, lean_object* v_sz_3830_, lean_object* v_i_3831_, lean_object* v_b_3832_){
_start:
{
size_t v_sz_boxed_3833_; size_t v_i_boxed_3834_; lean_object* v_res_3835_; 
v_sz_boxed_3833_ = lean_unbox_usize(v_sz_3830_);
lean_dec(v_sz_3830_);
v_i_boxed_3834_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_res_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_as_3829_, v_sz_boxed_3833_, v_i_boxed_3834_, v_b_3832_);
lean_dec_ref(v_as_3829_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object* v___x_3836_, lean_object* v_as_3837_, size_t v_sz_3838_, size_t v_i_3839_, lean_object* v_b_3840_){
_start:
{
lean_object* v_a_3842_; uint8_t v___x_3846_; 
v___x_3846_ = lean_usize_dec_lt(v_i_3839_, v_sz_3838_);
if (v___x_3846_ == 0)
{
return v_b_3840_;
}
else
{
lean_object* v_a_3847_; lean_object* v_ident_3848_; lean_object* v_range_3849_; lean_object* v_stx_3850_; lean_object* v_ci_3851_; lean_object* v_info_3852_; uint8_t v_isBinder_3853_; uint8_t v___x_3854_; 
v_a_3847_ = lean_array_uget(v_as_3837_, v_i_3839_);
v_ident_3848_ = lean_ctor_get(v_a_3847_, 0);
v_range_3849_ = lean_ctor_get(v_a_3847_, 2);
v_stx_3850_ = lean_ctor_get(v_a_3847_, 3);
v_ci_3851_ = lean_ctor_get(v_a_3847_, 4);
v_info_3852_ = lean_ctor_get(v_a_3847_, 5);
v_isBinder_3853_ = lean_ctor_get_uint8(v_a_3847_, sizeof(void*)*6);
v___x_3854_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v___x_3836_, v_ident_3848_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; 
v___x_3855_ = lean_array_push(v_b_3840_, v_a_3847_);
v_a_3842_ = v___x_3855_;
goto v___jp_3841_;
}
else
{
lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3867_; 
lean_inc_ref(v_info_3852_);
lean_inc_ref(v_ci_3851_);
lean_inc(v_stx_3850_);
lean_inc_ref(v_range_3849_);
lean_inc_ref(v_ident_3848_);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_a_3847_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; lean_object* v_unused_3869_; lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; 
v_unused_3868_ = lean_ctor_get(v_a_3847_, 5);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v_a_3847_, 4);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v_a_3847_, 3);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_a_3847_, 2);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_a_3847_, 1);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_a_3847_, 0);
lean_dec(v_unused_3873_);
v___x_3857_ = v_a_3847_;
v_isShared_3858_ = v_isSharedCheck_3867_;
goto v_resetjp_3856_;
}
else
{
lean_dec(v_a_3847_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3867_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3864_; 
lean_inc_ref(v_ident_3848_);
v___x_3859_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v___x_3836_, v_ident_3848_);
v___x_3860_ = lean_unsigned_to_nat(1u);
v___x_3861_ = lean_mk_empty_array_with_capacity(v___x_3860_);
v___x_3862_ = lean_array_push(v___x_3861_, v_ident_3848_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 1, v___x_3862_);
lean_ctor_set(v___x_3857_, 0, v___x_3859_);
v___x_3864_ = v___x_3857_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3866_, 2, v_range_3849_);
lean_ctor_set(v_reuseFailAlloc_3866_, 3, v_stx_3850_);
lean_ctor_set(v_reuseFailAlloc_3866_, 4, v_ci_3851_);
lean_ctor_set(v_reuseFailAlloc_3866_, 5, v_info_3852_);
lean_ctor_set_uint8(v_reuseFailAlloc_3866_, sizeof(void*)*6, v_isBinder_3853_);
v___x_3864_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_array_push(v_b_3840_, v___x_3864_);
v_a_3842_ = v___x_3865_;
goto v___jp_3841_;
}
}
}
}
v___jp_3841_:
{
size_t v___x_3843_; size_t v___x_3844_; 
v___x_3843_ = ((size_t)1ULL);
v___x_3844_ = lean_usize_add(v_i_3839_, v___x_3843_);
v_i_3839_ = v___x_3844_;
v_b_3840_ = v_a_3842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object* v___x_3874_, lean_object* v_as_3875_, lean_object* v_sz_3876_, lean_object* v_i_3877_, lean_object* v_b_3878_){
_start:
{
size_t v_sz_boxed_3879_; size_t v_i_boxed_3880_; lean_object* v_res_3881_; 
v_sz_boxed_3879_ = lean_unbox_usize(v_sz_3876_);
lean_dec(v_sz_3876_);
v_i_boxed_3880_ = lean_unbox_usize(v_i_3877_);
lean_dec(v_i_3877_);
v_res_3881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3874_, v_as_3875_, v_sz_boxed_3879_, v_i_boxed_3880_, v_b_3878_);
lean_dec_ref(v_as_3875_);
lean_dec_ref(v___x_3874_);
return v_res_3881_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__0(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3882_ = lean_box(0);
v___x_3883_ = lean_unsigned_to_nat(16u);
v___x_3884_ = lean_mk_array(v___x_3883_, v___x_3882_);
return v___x_3884_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__1(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v_posMap_3887_; 
v___x_3885_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__0, &l_Lean_Server_combineIdents___closed__0_once, _init_l_Lean_Server_combineIdents___closed__0);
v___x_3886_ = lean_unsigned_to_nat(0u);
v_posMap_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_posMap_3887_, 0, v___x_3886_);
lean_ctor_set(v_posMap_3887_, 1, v___x_3885_);
return v_posMap_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object* v_trees_3888_, lean_object* v_refs_3889_){
_start:
{
lean_object* v_posMap_3890_; size_t v_sz_3891_; size_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_posMap_3890_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__1, &l_Lean_Server_combineIdents___closed__1_once, _init_l_Lean_Server_combineIdents___closed__1);
v_sz_3891_ = lean_array_size(v_refs_3889_);
v___x_3892_ = ((size_t)0ULL);
v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_refs_3889_, v_sz_3891_, v___x_3892_, v_posMap_3890_);
v___x_3894_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3888_, v_refs_3889_, v___x_3893_);
lean_dec_ref(v___x_3893_);
v___x_3895_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v___x_3894_);
lean_dec_ref(v___x_3894_);
v___x_3896_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_3897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3895_, v_refs_3889_, v_sz_3891_, v___x_3892_, v___x_3896_);
lean_dec_ref(v___x_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object* v_trees_3898_, lean_object* v_refs_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Server_combineIdents(v_trees_3898_, v_refs_3899_);
lean_dec_ref(v_refs_3899_);
lean_dec_ref(v_trees_3898_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object* v_00_u03b2_3901_, lean_object* v_m_3902_, lean_object* v_a_3903_, lean_object* v_b_3904_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_m_3902_, v_a_3903_, v_b_3904_);
return v___x_3905_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object* v_00_u03b2_3906_, lean_object* v_a_3907_, lean_object* v_x_3908_){
_start:
{
uint8_t v___x_3909_; 
v___x_3909_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3907_, v_x_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3910_, lean_object* v_a_3911_, lean_object* v_x_3912_){
_start:
{
uint8_t v_res_3913_; lean_object* v_r_3914_; 
v_res_3913_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(v_00_u03b2_3910_, v_a_3911_, v_x_3912_);
lean_dec(v_x_3912_);
lean_dec_ref(v_a_3911_);
v_r_3914_ = lean_box(v_res_3913_);
return v_r_3914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object* v_00_u03b2_3915_, lean_object* v_data_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_data_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object* v_00_u03b2_3918_, lean_object* v_a_3919_, lean_object* v_b_3920_, lean_object* v_x_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3919_, v_b_3920_, v_x_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3923_, lean_object* v_i_3924_, lean_object* v_source_3925_, lean_object* v_target_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v_i_3924_, v_source_3925_, v_target_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3928_, lean_object* v_x_3929_, lean_object* v_x_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3929_, v_x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object* v_hi_3932_, lean_object* v_pivot_3933_, lean_object* v_as_3934_, lean_object* v_i_3935_, lean_object* v_k_3936_){
_start:
{
uint8_t v___x_3937_; 
v___x_3937_ = lean_nat_dec_lt(v_k_3936_, v_hi_3932_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_dec(v_k_3936_);
v___x_3938_ = lean_array_fswap(v_as_3934_, v_i_3935_, v_hi_3932_);
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v_i_3935_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
return v___x_3939_;
}
else
{
lean_object* v___x_3940_; lean_object* v_range_3941_; lean_object* v_range_3942_; uint8_t v___x_3943_; 
v___x_3940_ = lean_array_fget_borrowed(v_as_3934_, v_k_3936_);
v_range_3941_ = lean_ctor_get(v___x_3940_, 2);
v_range_3942_ = lean_ctor_get(v_pivot_3933_, 2);
v___x_3943_ = l_Lean_Lsp_instOrdRange_ord(v_range_3941_, v_range_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3944_ = lean_array_fswap(v_as_3934_, v_i_3935_, v_k_3936_);
v___x_3945_ = lean_unsigned_to_nat(1u);
v___x_3946_ = lean_nat_add(v_i_3935_, v___x_3945_);
lean_dec(v_i_3935_);
v___x_3947_ = lean_nat_add(v_k_3936_, v___x_3945_);
lean_dec(v_k_3936_);
v_as_3934_ = v___x_3944_;
v_i_3935_ = v___x_3946_;
v_k_3936_ = v___x_3947_;
goto _start;
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = lean_unsigned_to_nat(1u);
v___x_3950_ = lean_nat_add(v_k_3936_, v___x_3949_);
lean_dec(v_k_3936_);
v_k_3936_ = v___x_3950_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object* v_hi_3952_, lean_object* v_pivot_3953_, lean_object* v_as_3954_, lean_object* v_i_3955_, lean_object* v_k_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3952_, v_pivot_3953_, v_as_3954_, v_i_3955_, v_k_3956_);
lean_dec_ref(v_pivot_3953_);
lean_dec(v_hi_3952_);
return v_res_3957_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3958_, lean_object* v_x1_3959_, lean_object* v_x2_3960_){
_start:
{
lean_object* v_range_3961_; lean_object* v_range_3962_; uint8_t v___x_3963_; 
v_range_3961_ = lean_ctor_get(v_x1_3959_, 2);
v_range_3962_ = lean_ctor_get(v_x2_3960_, 2);
v___x_3963_ = l_Lean_Lsp_instOrdRange_ord(v_range_3961_, v_range_3962_);
if (v___x_3963_ == 0)
{
return v___x_3958_;
}
else
{
uint8_t v___x_3964_; 
v___x_3964_ = 0;
return v___x_3964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3965_, lean_object* v_x1_3966_, lean_object* v_x2_3967_){
_start:
{
uint8_t v___x_2138__boxed_3968_; uint8_t v_res_3969_; lean_object* v_r_3970_; 
v___x_2138__boxed_3968_ = lean_unbox(v___x_3965_);
v_res_3969_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_2138__boxed_3968_, v_x1_3966_, v_x2_3967_);
lean_dec_ref(v_x2_3967_);
lean_dec_ref(v_x1_3966_);
v_r_3970_ = lean_box(v_res_3969_);
return v_r_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_n_3971_, lean_object* v_as_3972_, lean_object* v_lo_3973_, lean_object* v_hi_3974_){
_start:
{
lean_object* v___y_3976_; uint8_t v___x_3986_; 
v___x_3986_ = lean_nat_dec_lt(v_lo_3973_, v_hi_3974_);
if (v___x_3986_ == 0)
{
lean_dec(v_lo_3973_);
return v_as_3972_;
}
else
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v_mid_3989_; lean_object* v___y_3991_; lean_object* v___y_3997_; lean_object* v___x_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v___x_3987_ = lean_nat_add(v_lo_3973_, v_hi_3974_);
v___x_3988_ = lean_unsigned_to_nat(1u);
v_mid_3989_ = lean_nat_shiftr(v___x_3987_, v___x_3988_);
lean_dec(v___x_3987_);
v___x_4002_ = lean_array_fget_borrowed(v_as_3972_, v_mid_3989_);
v___x_4003_ = lean_array_fget_borrowed(v_as_3972_, v_lo_3973_);
v___x_4004_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3986_, v___x_4002_, v___x_4003_);
if (v___x_4004_ == 0)
{
v___y_3997_ = v_as_3972_;
goto v___jp_3996_;
}
else
{
lean_object* v___x_4005_; 
v___x_4005_ = lean_array_fswap(v_as_3972_, v_lo_3973_, v_mid_3989_);
v___y_3997_ = v___x_4005_;
goto v___jp_3996_;
}
v___jp_3990_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v___x_3992_ = lean_array_fget_borrowed(v___y_3991_, v_mid_3989_);
v___x_3993_ = lean_array_fget_borrowed(v___y_3991_, v_hi_3974_);
v___x_3994_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3986_, v___x_3992_, v___x_3993_);
if (v___x_3994_ == 0)
{
lean_dec(v_mid_3989_);
v___y_3976_ = v___y_3991_;
goto v___jp_3975_;
}
else
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_array_fswap(v___y_3991_, v_mid_3989_, v_hi_3974_);
lean_dec(v_mid_3989_);
v___y_3976_ = v___x_3995_;
goto v___jp_3975_;
}
}
v___jp_3996_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v___x_3998_ = lean_array_fget_borrowed(v___y_3997_, v_hi_3974_);
v___x_3999_ = lean_array_fget_borrowed(v___y_3997_, v_lo_3973_);
v___x_4000_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3986_, v___x_3998_, v___x_3999_);
if (v___x_4000_ == 0)
{
v___y_3991_ = v___y_3997_;
goto v___jp_3990_;
}
else
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_array_fswap(v___y_3997_, v_lo_3973_, v_hi_3974_);
v___y_3991_ = v___x_4001_;
goto v___jp_3990_;
}
}
}
v___jp_3975_:
{
lean_object* v_pivot_3977_; lean_object* v___x_3978_; lean_object* v_fst_3979_; lean_object* v_snd_3980_; uint8_t v___x_3981_; 
v_pivot_3977_ = lean_array_fget(v___y_3976_, v_hi_3974_);
lean_inc_n(v_lo_3973_, 2);
v___x_3978_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3974_, v_pivot_3977_, v___y_3976_, v_lo_3973_, v_lo_3973_);
lean_dec(v_pivot_3977_);
v_fst_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_fst_3979_);
v_snd_3980_ = lean_ctor_get(v___x_3978_, 1);
lean_inc(v_snd_3980_);
lean_dec_ref(v___x_3978_);
v___x_3981_ = lean_nat_dec_le(v_hi_3974_, v_fst_3979_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3982_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3971_, v_snd_3980_, v_lo_3973_, v_fst_3979_);
v___x_3983_ = lean_unsigned_to_nat(1u);
v___x_3984_ = lean_nat_add(v_fst_3979_, v___x_3983_);
lean_dec(v_fst_3979_);
v_as_3972_ = v___x_3982_;
v_lo_3973_ = v___x_3984_;
goto _start;
}
else
{
lean_dec(v_fst_3979_);
lean_dec(v_lo_3973_);
return v_snd_3980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_n_4006_, lean_object* v_as_4007_, lean_object* v_lo_4008_, lean_object* v_hi_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4006_, v_as_4007_, v_lo_4008_, v_hi_4009_);
lean_dec(v_hi_4009_);
lean_dec(v_n_4006_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object* v_x_4011_, lean_object* v_x_4012_){
_start:
{
if (lean_obj_tag(v_x_4012_) == 0)
{
return v_x_4011_;
}
else
{
lean_object* v_key_4013_; lean_object* v_snd_4014_; lean_object* v_value_4015_; lean_object* v_tail_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4056_; 
v_key_4013_ = lean_ctor_get(v_x_4012_, 0);
lean_inc(v_key_4013_);
v_snd_4014_ = lean_ctor_get(v_key_4013_, 1);
v_value_4015_ = lean_ctor_get(v_x_4012_, 1);
v_tail_4016_ = lean_ctor_get(v_x_4012_, 2);
v_isSharedCheck_4056_ = !lean_is_exclusive(v_x_4012_);
if (v_isSharedCheck_4056_ == 0)
{
lean_object* v_unused_4057_; 
v_unused_4057_ = lean_ctor_get(v_x_4012_, 0);
lean_dec(v_unused_4057_);
v___x_4018_ = v_x_4012_;
v_isShared_4019_ = v_isSharedCheck_4056_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_tail_4016_);
lean_inc(v_value_4015_);
lean_dec(v_x_4012_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4056_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v_fst_4020_; lean_object* v_fst_4021_; lean_object* v_snd_4022_; lean_object* v___x_4023_; uint64_t v___x_4024_; uint64_t v___y_4026_; uint64_t v___y_4048_; 
v_fst_4020_ = lean_ctor_get(v_key_4013_, 0);
v_fst_4021_ = lean_ctor_get(v_snd_4014_, 0);
v_snd_4022_ = lean_ctor_get(v_snd_4014_, 1);
v___x_4023_ = lean_array_get_size(v_x_4011_);
v___x_4024_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4020_);
if (lean_obj_tag(v_fst_4021_) == 0)
{
uint64_t v___x_4051_; 
v___x_4051_ = 11ULL;
v___y_4026_ = v___x_4051_;
goto v___jp_4025_;
}
else
{
lean_object* v_val_4052_; uint8_t v___x_4053_; 
v_val_4052_ = lean_ctor_get(v_fst_4021_, 0);
v___x_4053_ = lean_unbox(v_val_4052_);
if (v___x_4053_ == 0)
{
uint64_t v___x_4054_; 
v___x_4054_ = 13ULL;
v___y_4048_ = v___x_4054_;
goto v___jp_4047_;
}
else
{
uint64_t v___x_4055_; 
v___x_4055_ = 11ULL;
v___y_4048_ = v___x_4055_;
goto v___jp_4047_;
}
}
v___jp_4025_:
{
uint64_t v___x_4027_; uint64_t v___x_4028_; uint64_t v___x_4029_; uint64_t v___x_4030_; uint64_t v___x_4031_; uint64_t v_fold_4032_; uint64_t v___x_4033_; uint64_t v___x_4034_; uint64_t v___x_4035_; size_t v___x_4036_; size_t v___x_4037_; size_t v___x_4038_; size_t v___x_4039_; size_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4043_; 
v___x_4027_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4022_);
v___x_4028_ = lean_uint64_mix_hash(v___y_4026_, v___x_4027_);
v___x_4029_ = lean_uint64_mix_hash(v___x_4024_, v___x_4028_);
v___x_4030_ = 32ULL;
v___x_4031_ = lean_uint64_shift_right(v___x_4029_, v___x_4030_);
v_fold_4032_ = lean_uint64_xor(v___x_4029_, v___x_4031_);
v___x_4033_ = 16ULL;
v___x_4034_ = lean_uint64_shift_right(v_fold_4032_, v___x_4033_);
v___x_4035_ = lean_uint64_xor(v_fold_4032_, v___x_4034_);
v___x_4036_ = lean_uint64_to_usize(v___x_4035_);
v___x_4037_ = lean_usize_of_nat(v___x_4023_);
v___x_4038_ = ((size_t)1ULL);
v___x_4039_ = lean_usize_sub(v___x_4037_, v___x_4038_);
v___x_4040_ = lean_usize_land(v___x_4036_, v___x_4039_);
v___x_4041_ = lean_array_uget_borrowed(v_x_4011_, v___x_4040_);
lean_inc(v___x_4041_);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 2, v___x_4041_);
v___x_4043_ = v___x_4018_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_key_4013_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_value_4015_);
lean_ctor_set(v_reuseFailAlloc_4046_, 2, v___x_4041_);
v___x_4043_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_array_uset(v_x_4011_, v___x_4040_, v___x_4043_);
v_x_4011_ = v___x_4044_;
v_x_4012_ = v_tail_4016_;
goto _start;
}
}
v___jp_4047_:
{
uint64_t v___x_4049_; uint64_t v___x_4050_; 
v___x_4049_ = 13ULL;
v___x_4050_ = lean_uint64_mix_hash(v___y_4048_, v___x_4049_);
v___y_4026_ = v___x_4050_;
goto v___jp_4025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object* v_i_4058_, lean_object* v_source_4059_, lean_object* v_target_4060_){
_start:
{
lean_object* v___x_4061_; uint8_t v___x_4062_; 
v___x_4061_ = lean_array_get_size(v_source_4059_);
v___x_4062_ = lean_nat_dec_lt(v_i_4058_, v___x_4061_);
if (v___x_4062_ == 0)
{
lean_dec_ref(v_source_4059_);
lean_dec(v_i_4058_);
return v_target_4060_;
}
else
{
lean_object* v_es_4063_; lean_object* v___x_4064_; lean_object* v_source_4065_; lean_object* v_target_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v_es_4063_ = lean_array_fget(v_source_4059_, v_i_4058_);
v___x_4064_ = lean_box(0);
v_source_4065_ = lean_array_fset(v_source_4059_, v_i_4058_, v___x_4064_);
v_target_4066_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_target_4060_, v_es_4063_);
v___x_4067_ = lean_unsigned_to_nat(1u);
v___x_4068_ = lean_nat_add(v_i_4058_, v___x_4067_);
lean_dec(v_i_4058_);
v_i_4058_ = v___x_4068_;
v_source_4059_ = v_source_4065_;
v_target_4060_ = v_target_4066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object* v_data_4070_){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v_nbuckets_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4071_ = lean_array_get_size(v_data_4070_);
v___x_4072_ = lean_unsigned_to_nat(2u);
v_nbuckets_4073_ = lean_nat_mul(v___x_4071_, v___x_4072_);
v___x_4074_ = lean_unsigned_to_nat(0u);
v___x_4075_ = lean_box(0);
v___x_4076_ = lean_mk_array(v_nbuckets_4073_, v___x_4075_);
v___x_4077_ = lean_array_propagate_mark(v_data_4070_, v___x_4076_);
v___x_4078_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v___x_4074_, v_data_4070_, v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object* v_x_4079_, lean_object* v_x_4080_){
_start:
{
if (lean_obj_tag(v_x_4079_) == 0)
{
if (lean_obj_tag(v_x_4080_) == 0)
{
uint8_t v___x_4081_; 
v___x_4081_ = 1;
return v___x_4081_;
}
else
{
uint8_t v___x_4082_; 
v___x_4082_ = 0;
return v___x_4082_;
}
}
else
{
if (lean_obj_tag(v_x_4080_) == 0)
{
uint8_t v___x_4083_; 
v___x_4083_ = 0;
return v___x_4083_;
}
else
{
lean_object* v_val_4084_; uint8_t v___x_4085_; 
v_val_4084_ = lean_ctor_get(v_x_4080_, 0);
v___x_4085_ = lean_unbox(v_val_4084_);
if (v___x_4085_ == 0)
{
lean_object* v_val_4086_; uint8_t v___x_4087_; 
v_val_4086_ = lean_ctor_get(v_x_4079_, 0);
v___x_4087_ = lean_unbox(v_val_4086_);
if (v___x_4087_ == 0)
{
uint8_t v___x_4088_; 
v___x_4088_ = 1;
return v___x_4088_;
}
else
{
uint8_t v___x_4089_; 
v___x_4089_ = lean_unbox(v_val_4084_);
return v___x_4089_;
}
}
else
{
lean_object* v_val_4090_; uint8_t v___x_4091_; 
v_val_4090_ = lean_ctor_get(v_x_4079_, 0);
v___x_4091_ = lean_unbox(v_val_4090_);
return v___x_4091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object* v_x_4092_, lean_object* v_x_4093_){
_start:
{
uint8_t v_res_4094_; lean_object* v_r_4095_; 
v_res_4094_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_x_4092_, v_x_4093_);
lean_dec(v_x_4093_);
lean_dec(v_x_4092_);
v_r_4095_ = lean_box(v_res_4094_);
return v_r_4095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object* v_a_4096_, lean_object* v_x_4097_){
_start:
{
if (lean_obj_tag(v_x_4097_) == 0)
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4098_, 0, v_a_4096_);
return v___x_4098_;
}
else
{
lean_object* v_val_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4127_; 
v_val_4099_ = lean_ctor_get(v_x_4097_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_x_4097_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4101_ = v_x_4097_;
v_isShared_4102_ = v_isSharedCheck_4127_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_val_4099_);
lean_dec(v_x_4097_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4127_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v_ident_4103_; lean_object* v_aliases_4104_; lean_object* v_range_4105_; lean_object* v_stx_4106_; lean_object* v_ci_4107_; lean_object* v_info_4108_; uint8_t v_isBinder_4109_; lean_object* v_aliases_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4121_; 
v_ident_4103_ = lean_ctor_get(v_val_4099_, 0);
lean_inc_ref(v_ident_4103_);
v_aliases_4104_ = lean_ctor_get(v_val_4099_, 1);
lean_inc_ref(v_aliases_4104_);
v_range_4105_ = lean_ctor_get(v_val_4099_, 2);
lean_inc_ref(v_range_4105_);
v_stx_4106_ = lean_ctor_get(v_val_4099_, 3);
lean_inc(v_stx_4106_);
v_ci_4107_ = lean_ctor_get(v_val_4099_, 4);
lean_inc_ref(v_ci_4107_);
v_info_4108_ = lean_ctor_get(v_val_4099_, 5);
lean_inc_ref(v_info_4108_);
v_isBinder_4109_ = lean_ctor_get_uint8(v_val_4099_, sizeof(void*)*6);
lean_dec(v_val_4099_);
v_aliases_4110_ = lean_ctor_get(v_a_4096_, 1);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_a_4096_);
if (v_isSharedCheck_4121_ == 0)
{
lean_object* v_unused_4122_; lean_object* v_unused_4123_; lean_object* v_unused_4124_; lean_object* v_unused_4125_; lean_object* v_unused_4126_; 
v_unused_4122_ = lean_ctor_get(v_a_4096_, 5);
lean_dec(v_unused_4122_);
v_unused_4123_ = lean_ctor_get(v_a_4096_, 4);
lean_dec(v_unused_4123_);
v_unused_4124_ = lean_ctor_get(v_a_4096_, 3);
lean_dec(v_unused_4124_);
v_unused_4125_ = lean_ctor_get(v_a_4096_, 2);
lean_dec(v_unused_4125_);
v_unused_4126_ = lean_ctor_get(v_a_4096_, 0);
lean_dec(v_unused_4126_);
v___x_4112_ = v_a_4096_;
v_isShared_4113_ = v_isSharedCheck_4121_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_aliases_4110_);
lean_dec(v_a_4096_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4121_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4114_; lean_object* v___x_4116_; 
v___x_4114_ = l_Array_append___redArg(v_aliases_4104_, v_aliases_4110_);
lean_dec_ref(v_aliases_4110_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 5, v_info_4108_);
lean_ctor_set(v___x_4112_, 4, v_ci_4107_);
lean_ctor_set(v___x_4112_, 3, v_stx_4106_);
lean_ctor_set(v___x_4112_, 2, v_range_4105_);
lean_ctor_set(v___x_4112_, 1, v___x_4114_);
lean_ctor_set(v___x_4112_, 0, v_ident_4103_);
v___x_4116_ = v___x_4112_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_ident_4103_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4114_);
lean_ctor_set(v_reuseFailAlloc_4120_, 2, v_range_4105_);
lean_ctor_set(v_reuseFailAlloc_4120_, 3, v_stx_4106_);
lean_ctor_set(v_reuseFailAlloc_4120_, 4, v_ci_4107_);
lean_ctor_set(v_reuseFailAlloc_4120_, 5, v_info_4108_);
v___x_4116_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
lean_object* v___x_4118_; 
lean_ctor_set_uint8(v___x_4116_, sizeof(void*)*6, v_isBinder_4109_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4116_);
v___x_4118_ = v___x_4101_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4116_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_x_4130_){
_start:
{
if (lean_obj_tag(v_x_4130_) == 0)
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v_val_4133_; lean_object* v___x_4134_; 
v___x_4131_ = lean_box(0);
v___x_4132_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4128_, v___x_4131_);
v_val_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_val_4133_);
lean_dec(v___x_4132_);
v___x_4134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4134_, 0, v_a_4129_);
lean_ctor_set(v___x_4134_, 1, v_val_4133_);
lean_ctor_set(v___x_4134_, 2, v_x_4130_);
return v___x_4134_;
}
else
{
lean_object* v_key_4135_; lean_object* v_value_4136_; lean_object* v_tail_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4161_; 
v_key_4135_ = lean_ctor_get(v_x_4130_, 0);
v_value_4136_ = lean_ctor_get(v_x_4130_, 1);
v_tail_4137_ = lean_ctor_get(v_x_4130_, 2);
v_isSharedCheck_4161_ = !lean_is_exclusive(v_x_4130_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4139_ = v_x_4130_;
v_isShared_4140_ = v_isSharedCheck_4161_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_tail_4137_);
lean_inc(v_value_4136_);
lean_inc(v_key_4135_);
lean_dec(v_x_4130_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4161_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v_fst_4146_; lean_object* v_snd_4147_; lean_object* v_fst_4148_; lean_object* v_snd_4149_; uint8_t v___x_4150_; 
v_fst_4146_ = lean_ctor_get(v_key_4135_, 0);
v_snd_4147_ = lean_ctor_get(v_key_4135_, 1);
v_fst_4148_ = lean_ctor_get(v_a_4129_, 0);
v_snd_4149_ = lean_ctor_get(v_a_4129_, 1);
v___x_4150_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4146_, v_fst_4148_);
if (v___x_4150_ == 0)
{
goto v___jp_4141_;
}
else
{
lean_object* v_fst_4151_; lean_object* v_snd_4152_; lean_object* v_fst_4153_; lean_object* v_snd_4154_; uint8_t v___x_4155_; 
v_fst_4151_ = lean_ctor_get(v_snd_4147_, 0);
v_snd_4152_ = lean_ctor_get(v_snd_4147_, 1);
v_fst_4153_ = lean_ctor_get(v_snd_4149_, 0);
v_snd_4154_ = lean_ctor_get(v_snd_4149_, 1);
v___x_4155_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4151_, v_fst_4153_);
if (v___x_4155_ == 0)
{
goto v___jp_4141_;
}
else
{
uint8_t v___x_4156_; 
v___x_4156_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4152_, v_snd_4154_);
if (v___x_4156_ == 0)
{
goto v___jp_4141_;
}
else
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v_val_4159_; lean_object* v___x_4160_; 
lean_del_object(v___x_4139_);
lean_dec(v_key_4135_);
v___x_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_value_4136_);
v___x_4158_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4128_, v___x_4157_);
v_val_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_val_4159_);
lean_dec(v___x_4158_);
v___x_4160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4160_, 0, v_a_4129_);
lean_ctor_set(v___x_4160_, 1, v_val_4159_);
lean_ctor_set(v___x_4160_, 2, v_tail_4137_);
return v___x_4160_;
}
}
}
v___jp_4141_:
{
lean_object* v_tail_4142_; lean_object* v___x_4144_; 
v_tail_4142_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4128_, v_a_4129_, v_tail_4137_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 2, v_tail_4142_);
v___x_4144_ = v___x_4139_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_key_4135_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v_value_4136_);
lean_ctor_set(v_reuseFailAlloc_4145_, 2, v_tail_4142_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_a_4162_, lean_object* v_x_4163_){
_start:
{
if (lean_obj_tag(v_x_4163_) == 0)
{
uint8_t v___x_4164_; 
v___x_4164_ = 0;
return v___x_4164_;
}
else
{
lean_object* v_key_4165_; lean_object* v_tail_4166_; lean_object* v_fst_4167_; lean_object* v_snd_4168_; lean_object* v_fst_4169_; lean_object* v_snd_4170_; uint8_t v___x_4171_; 
v_key_4165_ = lean_ctor_get(v_x_4163_, 0);
v_tail_4166_ = lean_ctor_get(v_x_4163_, 2);
v_fst_4167_ = lean_ctor_get(v_key_4165_, 0);
v_snd_4168_ = lean_ctor_get(v_key_4165_, 1);
v_fst_4169_ = lean_ctor_get(v_a_4162_, 0);
v_snd_4170_ = lean_ctor_get(v_a_4162_, 1);
v___x_4171_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4167_, v_fst_4169_);
if (v___x_4171_ == 0)
{
v_x_4163_ = v_tail_4166_;
goto _start;
}
else
{
lean_object* v_fst_4173_; lean_object* v_snd_4174_; lean_object* v_fst_4175_; lean_object* v_snd_4176_; uint8_t v___x_4177_; 
v_fst_4173_ = lean_ctor_get(v_snd_4168_, 0);
v_snd_4174_ = lean_ctor_get(v_snd_4168_, 1);
v_fst_4175_ = lean_ctor_get(v_snd_4170_, 0);
v_snd_4176_ = lean_ctor_get(v_snd_4170_, 1);
v___x_4177_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4173_, v_fst_4175_);
if (v___x_4177_ == 0)
{
v_x_4163_ = v_tail_4166_;
goto _start;
}
else
{
uint8_t v___x_4179_; 
v___x_4179_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4174_, v_snd_4176_);
if (v___x_4179_ == 0)
{
v_x_4163_ = v_tail_4166_;
goto _start;
}
else
{
return v___x_4179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object* v_a_4181_, lean_object* v_x_4182_){
_start:
{
uint8_t v_res_4183_; lean_object* v_r_4184_; 
v_res_4183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4181_, v_x_4182_);
lean_dec(v_x_4182_);
lean_dec_ref(v_a_4181_);
v_r_4184_ = lean_box(v_res_4183_);
return v_r_4184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4185_, lean_object* v_m_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v___y_4189_; size_t v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v_snd_4195_; lean_object* v_size_4196_; lean_object* v_buckets_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4256_; 
v_snd_4195_ = lean_ctor_get(v_a_4187_, 1);
v_size_4196_ = lean_ctor_get(v_m_4186_, 0);
v_buckets_4197_ = lean_ctor_get(v_m_4186_, 1);
v_isSharedCheck_4256_ = !lean_is_exclusive(v_m_4186_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4199_ = v_m_4186_;
v_isShared_4200_ = v_isSharedCheck_4256_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_buckets_4197_);
lean_inc(v_size_4196_);
lean_dec(v_m_4186_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4256_;
goto v_resetjp_4198_;
}
v___jp_4188_:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = lean_array_uset(v___y_4191_, v___y_4190_, v___y_4189_);
v___x_4194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___y_4192_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
return v___x_4194_;
}
v_resetjp_4198_:
{
lean_object* v_fst_4201_; lean_object* v_fst_4202_; lean_object* v_snd_4203_; lean_object* v___x_4204_; uint64_t v___x_4205_; uint64_t v___y_4207_; uint64_t v___y_4248_; 
v_fst_4201_ = lean_ctor_get(v_a_4187_, 0);
v_fst_4202_ = lean_ctor_get(v_snd_4195_, 0);
v_snd_4203_ = lean_ctor_get(v_snd_4195_, 1);
v___x_4204_ = lean_array_get_size(v_buckets_4197_);
v___x_4205_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4201_);
if (lean_obj_tag(v_fst_4202_) == 0)
{
uint64_t v___x_4251_; 
v___x_4251_ = 11ULL;
v___y_4207_ = v___x_4251_;
goto v___jp_4206_;
}
else
{
lean_object* v_val_4252_; uint8_t v___x_4253_; 
v_val_4252_ = lean_ctor_get(v_fst_4202_, 0);
v___x_4253_ = lean_unbox(v_val_4252_);
if (v___x_4253_ == 0)
{
uint64_t v___x_4254_; 
v___x_4254_ = 13ULL;
v___y_4248_ = v___x_4254_;
goto v___jp_4247_;
}
else
{
uint64_t v___x_4255_; 
v___x_4255_ = 11ULL;
v___y_4248_ = v___x_4255_;
goto v___jp_4247_;
}
}
v___jp_4206_:
{
uint64_t v___x_4208_; uint64_t v___x_4209_; uint64_t v___x_4210_; uint64_t v___x_4211_; uint64_t v___x_4212_; uint64_t v_fold_4213_; uint64_t v___x_4214_; uint64_t v___x_4215_; uint64_t v___x_4216_; size_t v___x_4217_; size_t v___x_4218_; size_t v___x_4219_; size_t v___x_4220_; size_t v___x_4221_; lean_object* v_bkt_4222_; uint8_t v___x_4223_; 
v___x_4208_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4203_);
v___x_4209_ = lean_uint64_mix_hash(v___y_4207_, v___x_4208_);
v___x_4210_ = lean_uint64_mix_hash(v___x_4205_, v___x_4209_);
v___x_4211_ = 32ULL;
v___x_4212_ = lean_uint64_shift_right(v___x_4210_, v___x_4211_);
v_fold_4213_ = lean_uint64_xor(v___x_4210_, v___x_4212_);
v___x_4214_ = 16ULL;
v___x_4215_ = lean_uint64_shift_right(v_fold_4213_, v___x_4214_);
v___x_4216_ = lean_uint64_xor(v_fold_4213_, v___x_4215_);
v___x_4217_ = lean_uint64_to_usize(v___x_4216_);
v___x_4218_ = lean_usize_of_nat(v___x_4204_);
v___x_4219_ = ((size_t)1ULL);
v___x_4220_ = lean_usize_sub(v___x_4218_, v___x_4219_);
v___x_4221_ = lean_usize_land(v___x_4217_, v___x_4220_);
v_bkt_4222_ = lean_array_uget_borrowed(v_buckets_4197_, v___x_4221_);
v___x_4223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4187_, v_bkt_4222_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; lean_object* v_size_x27_4225_; lean_object* v___x_4226_; lean_object* v_buckets_x27_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; uint8_t v___x_4233_; 
v___x_4224_ = lean_unsigned_to_nat(1u);
v_size_x27_4225_ = lean_nat_add(v_size_4196_, v___x_4224_);
lean_dec(v_size_4196_);
lean_inc(v_bkt_4222_);
v___x_4226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4226_, 0, v_a_4187_);
lean_ctor_set(v___x_4226_, 1, v_a_4185_);
lean_ctor_set(v___x_4226_, 2, v_bkt_4222_);
v_buckets_x27_4227_ = lean_array_uset(v_buckets_4197_, v___x_4221_, v___x_4226_);
v___x_4228_ = lean_unsigned_to_nat(4u);
v___x_4229_ = lean_nat_mul(v_size_x27_4225_, v___x_4228_);
v___x_4230_ = lean_unsigned_to_nat(3u);
v___x_4231_ = lean_nat_div(v___x_4229_, v___x_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_array_get_size(v_buckets_x27_4227_);
v___x_4233_ = lean_nat_dec_le(v___x_4231_, v___x_4232_);
lean_dec(v___x_4231_);
if (v___x_4233_ == 0)
{
lean_object* v_val_4234_; lean_object* v___x_4236_; 
v_val_4234_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_buckets_x27_4227_);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 1, v_val_4234_);
lean_ctor_set(v___x_4199_, 0, v_size_x27_4225_);
v___x_4236_ = v___x_4199_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_size_x27_4225_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_val_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
else
{
lean_object* v___x_4239_; 
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 1, v_buckets_x27_4227_);
lean_ctor_set(v___x_4199_, 0, v_size_x27_4225_);
v___x_4239_ = v___x_4199_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_size_x27_4225_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_buckets_x27_4227_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
else
{
lean_object* v___x_4241_; lean_object* v_buckets_x27_4242_; lean_object* v_bkt_x27_4243_; uint8_t v___x_4244_; 
lean_inc(v_bkt_4222_);
lean_del_object(v___x_4199_);
v___x_4241_ = lean_box(0);
v_buckets_x27_4242_ = lean_array_uset(v_buckets_4197_, v___x_4221_, v___x_4241_);
lean_inc_ref(v_a_4187_);
v_bkt_x27_4243_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4185_, v_a_4187_, v_bkt_4222_);
v___x_4244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4187_, v_bkt_x27_4243_);
lean_dec_ref(v_a_4187_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = lean_unsigned_to_nat(1u);
v___x_4246_ = lean_nat_sub(v_size_4196_, v___x_4245_);
lean_dec(v_size_4196_);
v___y_4189_ = v_bkt_x27_4243_;
v___y_4190_ = v___x_4221_;
v___y_4191_ = v_buckets_x27_4242_;
v___y_4192_ = v___x_4246_;
goto v___jp_4188_;
}
else
{
v___y_4189_ = v_bkt_x27_4243_;
v___y_4190_ = v___x_4221_;
v___y_4191_ = v_buckets_x27_4242_;
v___y_4192_ = v_size_4196_;
goto v___jp_4188_;
}
}
}
v___jp_4247_:
{
uint64_t v___x_4249_; uint64_t v___x_4250_; 
v___x_4249_ = 13ULL;
v___x_4250_ = lean_uint64_mix_hash(v___y_4248_, v___x_4249_);
v___y_4207_ = v___x_4250_;
goto v___jp_4206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4257_, lean_object* v_as_4258_, size_t v_sz_4259_, size_t v_i_4260_, lean_object* v_b_4261_){
_start:
{
uint8_t v___x_4262_; 
v___x_4262_ = lean_usize_dec_lt(v_i_4260_, v_sz_4259_);
if (v___x_4262_ == 0)
{
return v_b_4261_;
}
else
{
lean_object* v_a_4263_; lean_object* v___y_4265_; 
v_a_4263_ = lean_array_uget_borrowed(v_as_4258_, v_i_4260_);
if (v_allowSimultaneousBinderUse_4257_ == 0)
{
lean_object* v___x_4274_; 
v___x_4274_ = lean_box(0);
v___y_4265_ = v___x_4274_;
goto v___jp_4264_;
}
else
{
uint8_t v_isBinder_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_isBinder_4275_ = lean_ctor_get_uint8(v_a_4263_, sizeof(void*)*6);
v___x_4276_ = lean_box(v_isBinder_4275_);
v___x_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
v___y_4265_ = v___x_4277_;
goto v___jp_4264_;
}
v___jp_4264_:
{
lean_object* v_ident_4266_; lean_object* v_range_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; size_t v___x_4271_; size_t v___x_4272_; 
v_ident_4266_ = lean_ctor_get(v_a_4263_, 0);
v_range_4267_ = lean_ctor_get(v_a_4263_, 2);
lean_inc_ref(v_range_4267_);
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___y_4265_);
lean_ctor_set(v___x_4268_, 1, v_range_4267_);
lean_inc_ref(v_ident_4266_);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v_ident_4266_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
lean_inc(v_a_4263_);
v___x_4270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4263_, v_b_4261_, v___x_4269_);
v___x_4271_ = ((size_t)1ULL);
v___x_4272_ = lean_usize_add(v_i_4260_, v___x_4271_);
v_i_4260_ = v___x_4272_;
v_b_4261_ = v___x_4270_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4278_, lean_object* v_as_4279_, lean_object* v_sz_4280_, lean_object* v_i_4281_, lean_object* v_b_4282_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4283_; size_t v_sz_boxed_4284_; size_t v_i_boxed_4285_; lean_object* v_res_4286_; 
v_allowSimultaneousBinderUse_boxed_4283_ = lean_unbox(v_allowSimultaneousBinderUse_4278_);
v_sz_boxed_4284_ = lean_unbox_usize(v_sz_4280_);
lean_dec(v_sz_4280_);
v_i_boxed_4285_ = lean_unbox_usize(v_i_4281_);
lean_dec(v_i_4281_);
v_res_4286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4283_, v_as_4279_, v_sz_boxed_4284_, v_i_boxed_4285_, v_b_4282_);
lean_dec_ref(v_as_4279_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4287_, lean_object* v_x_4288_){
_start:
{
if (lean_obj_tag(v_x_4288_) == 0)
{
return v_x_4287_;
}
else
{
lean_object* v_value_4289_; lean_object* v_tail_4290_; lean_object* v___x_4291_; 
v_value_4289_ = lean_ctor_get(v_x_4288_, 1);
lean_inc(v_value_4289_);
v_tail_4290_ = lean_ctor_get(v_x_4288_, 2);
lean_inc(v_tail_4290_);
lean_dec_ref_known(v_x_4288_, 3);
v___x_4291_ = lean_array_push(v_x_4287_, v_value_4289_);
v_x_4287_ = v___x_4291_;
v_x_4288_ = v_tail_4290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4293_, size_t v_i_4294_, size_t v_stop_4295_, lean_object* v_b_4296_){
_start:
{
uint8_t v___x_4297_; 
v___x_4297_ = lean_usize_dec_eq(v_i_4294_, v_stop_4295_);
if (v___x_4297_ == 0)
{
lean_object* v___x_4298_; lean_object* v___x_4299_; size_t v___x_4300_; size_t v___x_4301_; 
v___x_4298_ = lean_array_uget_borrowed(v_as_4293_, v_i_4294_);
lean_inc(v___x_4298_);
v___x_4299_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4296_, v___x_4298_);
v___x_4300_ = ((size_t)1ULL);
v___x_4301_ = lean_usize_add(v_i_4294_, v___x_4300_);
v_i_4294_ = v___x_4301_;
v_b_4296_ = v___x_4299_;
goto _start;
}
else
{
return v_b_4296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4303_, lean_object* v_i_4304_, lean_object* v_stop_4305_, lean_object* v_b_4306_){
_start:
{
size_t v_i_boxed_4307_; size_t v_stop_boxed_4308_; lean_object* v_res_4309_; 
v_i_boxed_4307_ = lean_unbox_usize(v_i_4304_);
lean_dec(v_i_4304_);
v_stop_boxed_4308_ = lean_unbox_usize(v_stop_4305_);
lean_dec(v_stop_4305_);
v_res_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4303_, v_i_boxed_4307_, v_stop_boxed_4308_, v_b_4306_);
lean_dec_ref(v_as_4303_);
return v_res_4309_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4310_ = lean_box(0);
v___x_4311_ = lean_unsigned_to_nat(16u);
v___x_4312_ = lean_mk_array(v___x_4311_, v___x_4310_);
return v___x_4312_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v_refsByIdAndRange_4315_; 
v___x_4313_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4314_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4315_, 0, v___x_4314_);
lean_ctor_set(v_refsByIdAndRange_4315_, 1, v___x_4313_);
return v_refsByIdAndRange_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4316_, uint8_t v_allowSimultaneousBinderUse_4317_){
_start:
{
lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4327_; lean_object* v___x_4334_; lean_object* v_refsByIdAndRange_4335_; size_t v_sz_4336_; size_t v___x_4337_; lean_object* v___x_4338_; lean_object* v_buckets_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v___x_4334_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4335_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4336_ = lean_array_size(v_refs_4316_);
v___x_4337_ = ((size_t)0ULL);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4317_, v_refs_4316_, v_sz_4336_, v___x_4337_, v_refsByIdAndRange_4335_);
v_buckets_4339_ = lean_ctor_get(v___x_4338_, 1);
lean_inc_ref(v_buckets_4339_);
lean_dec_ref(v___x_4338_);
v___x_4340_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4341_ = lean_array_get_size(v_buckets_4339_);
v___x_4342_ = lean_nat_dec_lt(v___x_4334_, v___x_4341_);
if (v___x_4342_ == 0)
{
lean_dec_ref(v_buckets_4339_);
v___y_4327_ = v___x_4340_;
goto v___jp_4326_;
}
else
{
size_t v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = lean_usize_of_nat(v___x_4341_);
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4339_, v___x_4337_, v___x_4343_, v___x_4340_);
lean_dec_ref(v_buckets_4339_);
v___y_4327_ = v___x_4344_;
goto v___jp_4326_;
}
v___jp_4318_:
{
uint8_t v___x_4323_; 
v___x_4323_ = lean_nat_dec_le(v___y_4322_, v___y_4320_);
if (v___x_4323_ == 0)
{
lean_object* v___x_4324_; 
lean_dec(v___y_4320_);
lean_inc(v___y_4322_);
v___x_4324_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4321_, v___y_4319_, v___y_4322_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec(v___y_4321_);
return v___x_4324_;
}
else
{
lean_object* v___x_4325_; 
v___x_4325_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4321_, v___y_4319_, v___y_4322_, v___y_4320_);
lean_dec(v___y_4320_);
lean_dec(v___y_4321_);
return v___x_4325_;
}
}
v___jp_4326_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; uint8_t v___x_4330_; 
v___x_4328_ = lean_array_get_size(v___y_4327_);
v___x_4329_ = lean_unsigned_to_nat(0u);
v___x_4330_ = lean_nat_dec_eq(v___x_4328_, v___x_4329_);
if (v___x_4330_ == 0)
{
lean_object* v___x_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4331_ = lean_unsigned_to_nat(1u);
v___x_4332_ = lean_nat_sub(v___x_4328_, v___x_4331_);
v___x_4333_ = lean_nat_dec_le(v___x_4329_, v___x_4332_);
if (v___x_4333_ == 0)
{
lean_inc(v___x_4332_);
v___y_4319_ = v___y_4327_;
v___y_4320_ = v___x_4332_;
v___y_4321_ = v___x_4328_;
v___y_4322_ = v___x_4332_;
goto v___jp_4318_;
}
else
{
v___y_4319_ = v___y_4327_;
v___y_4320_ = v___x_4332_;
v___y_4321_ = v___x_4328_;
v___y_4322_ = v___x_4329_;
goto v___jp_4318_;
}
}
else
{
return v___y_4327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object* v_refs_4345_, lean_object* v_allowSimultaneousBinderUse_4346_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4347_; lean_object* v_res_4348_; 
v_allowSimultaneousBinderUse_boxed_4347_ = lean_unbox(v_allowSimultaneousBinderUse_4346_);
v_res_4348_ = l_Lean_Server_dedupReferences(v_refs_4345_, v_allowSimultaneousBinderUse_boxed_4347_);
lean_dec_ref(v_refs_4345_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object* v_n_4349_, lean_object* v_as_4350_, lean_object* v_lo_4351_, lean_object* v_hi_4352_, lean_object* v_w_4353_, lean_object* v_hlo_4354_, lean_object* v_hhi_4355_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4349_, v_as_4350_, v_lo_4351_, v_hi_4352_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object* v_n_4357_, lean_object* v_as_4358_, lean_object* v_lo_4359_, lean_object* v_hi_4360_, lean_object* v_w_4361_, lean_object* v_hlo_4362_, lean_object* v_hhi_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(v_n_4357_, v_as_4358_, v_lo_4359_, v_hi_4360_, v_w_4361_, v_hlo_4362_, v_hhi_4363_);
lean_dec(v_hi_4360_);
lean_dec(v_n_4357_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(lean_object* v_n_4365_, lean_object* v_lo_4366_, lean_object* v_hi_4367_, lean_object* v_hhi_4368_, lean_object* v_pivot_4369_, lean_object* v_as_4370_, lean_object* v_i_4371_, lean_object* v_k_4372_, lean_object* v_ilo_4373_, lean_object* v_ik_4374_, lean_object* v_w_4375_){
_start:
{
lean_object* v___x_4376_; 
v___x_4376_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_4367_, v_pivot_4369_, v_as_4370_, v_i_4371_, v_k_4372_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___boxed(lean_object* v_n_4377_, lean_object* v_lo_4378_, lean_object* v_hi_4379_, lean_object* v_hhi_4380_, lean_object* v_pivot_4381_, lean_object* v_as_4382_, lean_object* v_i_4383_, lean_object* v_k_4384_, lean_object* v_ilo_4385_, lean_object* v_ik_4386_, lean_object* v_w_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(v_n_4377_, v_lo_4378_, v_hi_4379_, v_hhi_4380_, v_pivot_4381_, v_as_4382_, v_i_4383_, v_k_4384_, v_ilo_4385_, v_ik_4386_, v_w_4387_);
lean_dec_ref(v_pivot_4381_);
lean_dec(v_hi_4379_);
lean_dec(v_lo_4378_);
lean_dec(v_n_4377_);
return v_res_4388_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object* v_00_u03b2_4389_, lean_object* v_a_4390_, lean_object* v_x_4391_){
_start:
{
uint8_t v___x_4392_; 
v___x_4392_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4390_, v_x_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4393_, lean_object* v_a_4394_, lean_object* v_x_4395_){
_start:
{
uint8_t v_res_4396_; lean_object* v_r_4397_; 
v_res_4396_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(v_00_u03b2_4393_, v_a_4394_, v_x_4395_);
lean_dec(v_x_4395_);
lean_dec_ref(v_a_4394_);
v_r_4397_ = lean_box(v_res_4396_);
return v_r_4397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object* v_00_u03b2_4398_, lean_object* v_data_4399_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_data_4399_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4401_, lean_object* v_i_4402_, lean_object* v_source_4403_, lean_object* v_target_4404_){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v_i_4402_, v_source_4403_, v_target_4404_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4406_, lean_object* v_x_4407_, lean_object* v_x_4408_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_x_4407_, v_x_4408_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object* v_as_4410_, size_t v_i_4411_, size_t v_stop_4412_, lean_object* v_b_4413_){
_start:
{
uint8_t v___x_4414_; 
v___x_4414_ = lean_usize_dec_eq(v_i_4411_, v_stop_4412_);
if (v___x_4414_ == 0)
{
lean_object* v___x_4415_; lean_object* v___x_4416_; size_t v___x_4417_; size_t v___x_4418_; 
v___x_4415_ = lean_array_uget_borrowed(v_as_4410_, v_i_4411_);
lean_inc(v___x_4415_);
v___x_4416_ = l_Lean_Server_ModuleRefs_addRef(v_b_4413_, v___x_4415_);
v___x_4417_ = ((size_t)1ULL);
v___x_4418_ = lean_usize_add(v_i_4411_, v___x_4417_);
v_i_4411_ = v___x_4418_;
v_b_4413_ = v___x_4416_;
goto _start;
}
else
{
return v_b_4413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object* v_as_4420_, lean_object* v_i_4421_, lean_object* v_stop_4422_, lean_object* v_b_4423_){
_start:
{
size_t v_i_boxed_4424_; size_t v_stop_boxed_4425_; lean_object* v_res_4426_; 
v_i_boxed_4424_ = lean_unbox_usize(v_i_4421_);
lean_dec(v_i_4421_);
v_stop_boxed_4425_ = lean_unbox_usize(v_stop_4422_);
lean_dec(v_stop_4422_);
v_res_4426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_as_4420_, v_i_boxed_4424_, v_stop_boxed_4425_, v_b_4423_);
lean_dec_ref(v_as_4420_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object* v_as_4427_, size_t v_i_4428_, size_t v_stop_4429_, lean_object* v_b_4430_){
_start:
{
lean_object* v___y_4432_; uint8_t v___x_4436_; 
v___x_4436_ = lean_usize_dec_eq(v_i_4428_, v_stop_4429_);
if (v___x_4436_ == 0)
{
lean_object* v___x_4437_; lean_object* v_ident_4438_; 
v___x_4437_ = lean_array_uget_borrowed(v_as_4427_, v_i_4428_);
v_ident_4438_ = lean_ctor_get(v___x_4437_, 0);
if (lean_obj_tag(v_ident_4438_) == 1)
{
v___y_4432_ = v_b_4430_;
goto v___jp_4431_;
}
else
{
lean_object* v___x_4439_; 
lean_inc(v___x_4437_);
v___x_4439_ = lean_array_push(v_b_4430_, v___x_4437_);
v___y_4432_ = v___x_4439_;
goto v___jp_4431_;
}
}
else
{
return v_b_4430_;
}
v___jp_4431_:
{
size_t v___x_4433_; size_t v___x_4434_; 
v___x_4433_ = ((size_t)1ULL);
v___x_4434_ = lean_usize_add(v_i_4428_, v___x_4433_);
v_i_4428_ = v___x_4434_;
v_b_4430_ = v___y_4432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object* v_as_4440_, lean_object* v_i_4441_, lean_object* v_stop_4442_, lean_object* v_b_4443_){
_start:
{
size_t v_i_boxed_4444_; size_t v_stop_boxed_4445_; lean_object* v_res_4446_; 
v_i_boxed_4444_ = lean_unbox_usize(v_i_4441_);
lean_dec(v_i_4441_);
v_stop_boxed_4445_ = lean_unbox_usize(v_stop_4442_);
lean_dec(v_stop_4442_);
v_res_4446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_as_4440_, v_i_boxed_4444_, v_stop_boxed_4445_, v_b_4443_);
lean_dec_ref(v_as_4440_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object* v_text_4447_, lean_object* v_trees_4448_, uint8_t v_localVars_4449_, uint8_t v_allowSimultaneousBinderUse_4450_){
_start:
{
lean_object* v_refs_4452_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v_refs_4462_; 
v___x_4460_ = l_Lean_Server_findReferences(v_text_4447_, v_trees_4448_);
v___x_4461_ = l_Lean_Server_combineIdents(v_trees_4448_, v___x_4460_);
lean_dec_ref(v___x_4460_);
v_refs_4462_ = l_Lean_Server_dedupReferences(v___x_4461_, v_allowSimultaneousBinderUse_4450_);
lean_dec_ref(v___x_4461_);
if (v_localVars_4449_ == 0)
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; uint8_t v___x_4466_; 
v___x_4463_ = lean_unsigned_to_nat(0u);
v___x_4464_ = lean_array_get_size(v_refs_4462_);
v___x_4465_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4466_ = lean_nat_dec_lt(v___x_4463_, v___x_4464_);
if (v___x_4466_ == 0)
{
lean_dec_ref(v_refs_4462_);
v_refs_4452_ = v___x_4465_;
goto v___jp_4451_;
}
else
{
size_t v___x_4467_; size_t v___x_4468_; lean_object* v___x_4469_; 
v___x_4467_ = ((size_t)0ULL);
v___x_4468_ = lean_usize_of_nat(v___x_4464_);
v___x_4469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4462_, v___x_4467_, v___x_4468_, v___x_4465_);
lean_dec_ref(v_refs_4462_);
v_refs_4452_ = v___x_4469_;
goto v___jp_4451_;
}
}
else
{
v_refs_4452_ = v_refs_4462_;
goto v___jp_4451_;
}
v___jp_4451_:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; uint8_t v___x_4456_; 
v___x_4453_ = lean_box(1);
v___x_4454_ = lean_unsigned_to_nat(0u);
v___x_4455_ = lean_array_get_size(v_refs_4452_);
v___x_4456_ = lean_nat_dec_lt(v___x_4454_, v___x_4455_);
if (v___x_4456_ == 0)
{
lean_dec_ref(v_refs_4452_);
return v___x_4453_;
}
else
{
size_t v___x_4457_; size_t v___x_4458_; lean_object* v___x_4459_; 
v___x_4457_ = ((size_t)0ULL);
v___x_4458_ = lean_usize_of_nat(v___x_4455_);
v___x_4459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4452_, v___x_4457_, v___x_4458_, v___x_4453_);
lean_dec_ref(v_refs_4452_);
return v___x_4459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object* v_text_4470_, lean_object* v_trees_4471_, lean_object* v_localVars_4472_, lean_object* v_allowSimultaneousBinderUse_4473_){
_start:
{
uint8_t v_localVars_boxed_4474_; uint8_t v_allowSimultaneousBinderUse_boxed_4475_; lean_object* v_res_4476_; 
v_localVars_boxed_4474_ = lean_unbox(v_localVars_4472_);
v_allowSimultaneousBinderUse_boxed_4475_ = lean_unbox(v_allowSimultaneousBinderUse_4473_);
v_res_4476_ = l_Lean_Server_findModuleRefs(v_text_4470_, v_trees_4471_, v_localVars_boxed_4474_, v_allowSimultaneousBinderUse_boxed_4475_);
lean_dec_ref(v_trees_4471_);
return v_res_4476_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t v_a_4484_, uint8_t v_a_4485_){
_start:
{
switch(v_a_4484_)
{
case 0:
{
if (v_a_4485_ == 1)
{
uint8_t v___x_4486_; 
v___x_4486_ = 2;
return v___x_4486_;
}
else
{
return v_a_4485_;
}
}
case 1:
{
if (v_a_4485_ == 0)
{
uint8_t v___x_4487_; 
v___x_4487_ = 2;
return v___x_4487_;
}
else
{
return v_a_4485_;
}
}
default: 
{
return v_a_4484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object* v_a_4488_, lean_object* v_a_4489_){
_start:
{
uint8_t v_a_46__boxed_4490_; uint8_t v_a_47__boxed_4491_; uint8_t v_res_4492_; lean_object* v_r_4493_; 
v_a_46__boxed_4490_ = lean_unbox(v_a_4488_);
v_a_47__boxed_4491_ = lean_unbox(v_a_4489_);
v_res_4492_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_a_46__boxed_4490_, v_a_47__boxed_4491_);
v_r_4493_ = lean_box(v_res_4492_);
return v_r_4493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object* v_upperBound_4494_, lean_object* v_identicalImports_4495_, lean_object* v_a_4496_, lean_object* v_b_4497_){
_start:
{
uint8_t v___x_4498_; 
v___x_4498_ = lean_nat_dec_lt(v_a_4496_, v_upperBound_4494_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4499_; 
lean_dec(v_a_4496_);
v___x_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4499_, 0, v_b_4497_);
return v___x_4499_;
}
else
{
lean_object* v_module_4500_; lean_object* v_uri_4501_; uint8_t v_isAll_4502_; uint8_t v_isPrivate_4503_; uint8_t v_metaKind_4504_; lean_object* v___x_4505_; lean_object* v_module_4506_; lean_object* v_uri_4507_; uint8_t v_isAll_4508_; uint8_t v_isPrivate_4509_; uint8_t v_metaKind_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4530_; 
v_module_4500_ = lean_ctor_get(v_b_4497_, 0);
lean_inc(v_module_4500_);
v_uri_4501_ = lean_ctor_get(v_b_4497_, 1);
lean_inc_ref(v_uri_4501_);
v_isAll_4502_ = lean_ctor_get_uint8(v_b_4497_, sizeof(void*)*2);
v_isPrivate_4503_ = lean_ctor_get_uint8(v_b_4497_, sizeof(void*)*2 + 1);
v_metaKind_4504_ = lean_ctor_get_uint8(v_b_4497_, sizeof(void*)*2 + 2);
lean_dec_ref(v_b_4497_);
v___x_4505_ = lean_array_fget(v_identicalImports_4495_, v_a_4496_);
v_module_4506_ = lean_ctor_get(v___x_4505_, 0);
v_uri_4507_ = lean_ctor_get(v___x_4505_, 1);
v_isAll_4508_ = lean_ctor_get_uint8(v___x_4505_, sizeof(void*)*2);
v_isPrivate_4509_ = lean_ctor_get_uint8(v___x_4505_, sizeof(void*)*2 + 1);
v_metaKind_4510_ = lean_ctor_get_uint8(v___x_4505_, sizeof(void*)*2 + 2);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4512_ = v___x_4505_;
v_isShared_4513_ = v_isSharedCheck_4530_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_uri_4507_);
lean_inc(v_module_4506_);
lean_dec(v___x_4505_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4530_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
uint8_t v___y_4515_; uint8_t v___y_4516_; uint8_t v___y_4525_; uint8_t v___x_4526_; 
v___x_4526_ = lean_name_eq(v_module_4500_, v_module_4506_);
lean_dec(v_module_4506_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
lean_del_object(v___x_4512_);
lean_dec_ref(v_uri_4507_);
lean_dec_ref(v_uri_4501_);
lean_dec(v_module_4500_);
lean_dec(v_a_4496_);
v___x_4527_ = lean_box(0);
return v___x_4527_;
}
else
{
uint8_t v___x_4528_; 
v___x_4528_ = lean_string_dec_eq(v_uri_4501_, v_uri_4507_);
lean_dec_ref(v_uri_4507_);
if (v___x_4528_ == 0)
{
lean_object* v___x_4529_; 
lean_del_object(v___x_4512_);
lean_dec_ref(v_uri_4501_);
lean_dec(v_module_4500_);
lean_dec(v_a_4496_);
v___x_4529_ = lean_box(0);
return v___x_4529_;
}
else
{
if (v_isAll_4502_ == 0)
{
v___y_4525_ = v_isAll_4508_;
goto v___jp_4524_;
}
else
{
v___y_4525_ = v___x_4498_;
goto v___jp_4524_;
}
}
}
v___jp_4514_:
{
uint8_t v___x_4517_; lean_object* v___x_4519_; 
v___x_4517_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_metaKind_4504_, v_metaKind_4510_);
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 1, v_uri_4501_);
lean_ctor_set(v___x_4512_, 0, v_module_4500_);
v___x_4519_ = v___x_4512_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_module_4500_);
lean_ctor_set(v_reuseFailAlloc_4523_, 1, v_uri_4501_);
v___x_4519_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; 
lean_ctor_set_uint8(v___x_4519_, sizeof(void*)*2, v___y_4515_);
lean_ctor_set_uint8(v___x_4519_, sizeof(void*)*2 + 1, v___y_4516_);
lean_ctor_set_uint8(v___x_4519_, sizeof(void*)*2 + 2, v___x_4517_);
v___x_4520_ = lean_unsigned_to_nat(1u);
v___x_4521_ = lean_nat_add(v_a_4496_, v___x_4520_);
lean_dec(v_a_4496_);
v_a_4496_ = v___x_4521_;
v_b_4497_ = v___x_4519_;
goto _start;
}
}
v___jp_4524_:
{
if (v_isPrivate_4503_ == 0)
{
v___y_4515_ = v___y_4525_;
v___y_4516_ = v_isPrivate_4503_;
goto v___jp_4514_;
}
else
{
v___y_4515_ = v___y_4525_;
v___y_4516_ = v_isPrivate_4509_;
goto v___jp_4514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_4531_, lean_object* v_identicalImports_4532_, lean_object* v_a_4533_, lean_object* v_b_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4531_, v_identicalImports_4532_, v_a_4533_, v_b_4534_);
lean_dec_ref(v_identicalImports_4532_);
lean_dec(v_upperBound_4531_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object* v_identicalImports_4536_){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v___x_4537_ = lean_unsigned_to_nat(0u);
v___x_4538_ = lean_array_get_size(v_identicalImports_4536_);
v___x_4539_ = lean_nat_dec_lt(v___x_4537_, v___x_4538_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; 
v___x_4540_ = lean_box(0);
return v___x_4540_;
}
else
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4541_ = lean_unsigned_to_nat(1u);
v___x_4542_ = lean_array_fget_borrowed(v_identicalImports_4536_, v___x_4537_);
lean_inc(v___x_4542_);
v___x_4543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v___x_4538_, v_identicalImports_4536_, v___x_4541_, v___x_4542_);
return v___x_4543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object* v_identicalImports_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_identicalImports_4544_);
lean_dec_ref(v_identicalImports_4544_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object* v_upperBound_4546_, lean_object* v_identicalImports_4547_, lean_object* v_inst_4548_, lean_object* v_R_4549_, lean_object* v_a_4550_, lean_object* v_b_4551_, lean_object* v_c_4552_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4546_, v_identicalImports_4547_, v_a_4550_, v_b_4551_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object* v_upperBound_4554_, lean_object* v_identicalImports_4555_, lean_object* v_inst_4556_, lean_object* v_R_4557_, lean_object* v_a_4558_, lean_object* v_b_4559_, lean_object* v_c_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(v_upperBound_4554_, v_identicalImports_4555_, v_inst_4556_, v_R_4557_, v_a_4558_, v_b_4559_, v_c_4560_);
lean_dec_ref(v_identicalImports_4555_);
lean_dec(v_upperBound_4554_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object* v_x_4568_){
_start:
{
lean_object* v_module_4569_; 
v_module_4569_ = lean_ctor_get(v_x_4568_, 0);
lean_inc(v_module_4569_);
return v_module_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object* v_x_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_Server_DirectImports_convertImportInfos___lam__0(v_x_4570_);
lean_dec_ref(v_x_4570_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object* v_x_4572_, lean_object* v_x_4573_){
_start:
{
if (lean_obj_tag(v_x_4573_) == 0)
{
return v_x_4572_;
}
else
{
lean_object* v_key_4574_; lean_object* v_value_4575_; lean_object* v_tail_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v_key_4574_ = lean_ctor_get(v_x_4573_, 0);
v_value_4575_ = lean_ctor_get(v_x_4573_, 1);
v_tail_4576_ = lean_ctor_get(v_x_4573_, 2);
lean_inc(v_value_4575_);
lean_inc(v_key_4574_);
v___x_4577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4577_, 0, v_key_4574_);
lean_ctor_set(v___x_4577_, 1, v_value_4575_);
v___x_4578_ = lean_array_push(v_x_4572_, v___x_4577_);
v_x_4572_ = v___x_4578_;
v_x_4573_ = v_tail_4576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object* v_x_4580_, lean_object* v_x_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_x_4580_, v_x_4581_);
lean_dec(v_x_4581_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object* v_as_4583_, size_t v_i_4584_, size_t v_stop_4585_, lean_object* v_b_4586_){
_start:
{
uint8_t v___x_4587_; 
v___x_4587_ = lean_usize_dec_eq(v_i_4584_, v_stop_4585_);
if (v___x_4587_ == 0)
{
lean_object* v___x_4588_; lean_object* v___x_4589_; size_t v___x_4590_; size_t v___x_4591_; 
v___x_4588_ = lean_array_uget_borrowed(v_as_4583_, v_i_4584_);
v___x_4589_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_b_4586_, v___x_4588_);
v___x_4590_ = ((size_t)1ULL);
v___x_4591_ = lean_usize_add(v_i_4584_, v___x_4590_);
v_i_4584_ = v___x_4591_;
v_b_4586_ = v___x_4589_;
goto _start;
}
else
{
return v_b_4586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object* v_as_4593_, lean_object* v_i_4594_, lean_object* v_stop_4595_, lean_object* v_b_4596_){
_start:
{
size_t v_i_boxed_4597_; size_t v_stop_boxed_4598_; lean_object* v_res_4599_; 
v_i_boxed_4597_ = lean_unbox_usize(v_i_4594_);
lean_dec(v_i_4594_);
v_stop_boxed_4598_ = lean_unbox_usize(v_stop_4595_);
lean_dec(v_stop_4595_);
v_res_4599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_as_4593_, v_i_boxed_4597_, v_stop_boxed_4598_, v_b_4596_);
lean_dec_ref(v_as_4593_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object* v_as_4600_, size_t v_i_4601_, size_t v_stop_4602_, lean_object* v_b_4603_){
_start:
{
lean_object* v_a_4606_; uint8_t v___x_4610_; 
v___x_4610_ = lean_usize_dec_eq(v_i_4601_, v_stop_4602_);
if (v___x_4610_ == 0)
{
lean_object* v___x_4611_; lean_object* v_module_4612_; uint8_t v_isPrivate_4613_; uint8_t v_isAll_4614_; uint8_t v_isMeta_4615_; lean_object* v_module_4616_; lean_object* v___x_4617_; 
v___x_4611_ = lean_array_uget_borrowed(v_as_4600_, v_i_4601_);
v_module_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isPrivate_4613_ = lean_ctor_get_uint8(v___x_4611_, sizeof(void*)*1);
v_isAll_4614_ = lean_ctor_get_uint8(v___x_4611_, sizeof(void*)*1 + 1);
v_isMeta_4615_ = lean_ctor_get_uint8(v___x_4611_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4612_);
v_module_4616_ = l_String_toName(v_module_4612_);
lean_inc(v_module_4616_);
v___x_4617_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4616_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
lean_inc(v_a_4618_);
lean_dec_ref_known(v___x_4617_, 1);
if (lean_obj_tag(v_a_4618_) == 1)
{
lean_object* v_val_4619_; uint8_t v___y_4621_; 
v_val_4619_ = lean_ctor_get(v_a_4618_, 0);
lean_inc(v_val_4619_);
lean_dec_ref_known(v_a_4618_, 1);
if (v_isMeta_4615_ == 0)
{
uint8_t v___x_4624_; 
v___x_4624_ = 0;
v___y_4621_ = v___x_4624_;
goto v___jp_4620_;
}
else
{
uint8_t v___x_4625_; 
v___x_4625_ = 1;
v___y_4621_ = v___x_4625_;
goto v___jp_4620_;
}
v___jp_4620_:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4622_, 0, v_module_4616_);
lean_ctor_set(v___x_4622_, 1, v_val_4619_);
lean_ctor_set_uint8(v___x_4622_, sizeof(void*)*2, v_isAll_4614_);
lean_ctor_set_uint8(v___x_4622_, sizeof(void*)*2 + 1, v_isPrivate_4613_);
lean_ctor_set_uint8(v___x_4622_, sizeof(void*)*2 + 2, v___y_4621_);
v___x_4623_ = lean_array_push(v_b_4603_, v___x_4622_);
v_a_4606_ = v___x_4623_;
goto v___jp_4605_;
}
}
else
{
lean_dec(v_a_4618_);
lean_dec(v_module_4616_);
v_a_4606_ = v_b_4603_;
goto v___jp_4605_;
}
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4633_; 
lean_dec(v_module_4616_);
lean_dec_ref(v_b_4603_);
v_a_4626_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4628_ = v___x_4617_;
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4617_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4633_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
else
{
lean_object* v___x_4634_; 
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v_b_4603_);
return v___x_4634_;
}
v___jp_4605_:
{
size_t v___x_4607_; size_t v___x_4608_; 
v___x_4607_ = ((size_t)1ULL);
v___x_4608_ = lean_usize_add(v_i_4601_, v___x_4607_);
v_i_4601_ = v___x_4608_;
v_b_4603_ = v_a_4606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object* v_as_4635_, lean_object* v_i_4636_, lean_object* v_stop_4637_, lean_object* v_b_4638_, lean_object* v___y_4639_){
_start:
{
size_t v_i_boxed_4640_; size_t v_stop_boxed_4641_; lean_object* v_res_4642_; 
v_i_boxed_4640_ = lean_unbox_usize(v_i_4636_);
lean_dec(v_i_4636_);
v_stop_boxed_4641_ = lean_unbox_usize(v_stop_4637_);
lean_dec(v_stop_4637_);
v_res_4642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4635_, v_i_boxed_4640_, v_stop_boxed_4641_, v_b_4638_);
lean_dec_ref(v_as_4635_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object* v_as_4643_, lean_object* v_start_4644_, lean_object* v_stop_4645_){
_start:
{
lean_object* v___x_4647_; uint8_t v___x_4648_; 
v___x_4647_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_4648_ = lean_nat_dec_lt(v_start_4644_, v_stop_4645_);
if (v___x_4648_ == 0)
{
lean_object* v___x_4649_; 
v___x_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4647_);
return v___x_4649_;
}
else
{
lean_object* v___x_4650_; uint8_t v___x_4651_; 
v___x_4650_ = lean_array_get_size(v_as_4643_);
v___x_4651_ = lean_nat_dec_le(v_stop_4645_, v___x_4650_);
if (v___x_4651_ == 0)
{
uint8_t v___x_4652_; 
v___x_4652_ = lean_nat_dec_lt(v_start_4644_, v___x_4650_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; 
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4647_);
return v___x_4653_;
}
else
{
size_t v___x_4654_; size_t v___x_4655_; lean_object* v___x_4656_; 
v___x_4654_ = lean_usize_of_nat(v_start_4644_);
v___x_4655_ = lean_usize_of_nat(v___x_4650_);
v___x_4656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4643_, v___x_4654_, v___x_4655_, v___x_4647_);
return v___x_4656_;
}
}
else
{
size_t v___x_4657_; size_t v___x_4658_; lean_object* v___x_4659_; 
v___x_4657_ = lean_usize_of_nat(v_start_4644_);
v___x_4658_ = lean_usize_of_nat(v_stop_4645_);
v___x_4659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4643_, v___x_4657_, v___x_4658_, v___x_4647_);
return v___x_4659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object* v_as_4660_, lean_object* v_start_4661_, lean_object* v_stop_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_as_4660_, v_start_4661_, v_stop_4662_);
lean_dec(v_stop_4662_);
lean_dec(v_start_4661_);
lean_dec_ref(v_as_4660_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object* v_k_4665_, lean_object* v_v_4666_, lean_object* v_t_4667_){
_start:
{
if (lean_obj_tag(v_t_4667_) == 0)
{
lean_object* v_size_4668_; lean_object* v_k_4669_; lean_object* v_v_4670_; lean_object* v_l_4671_; lean_object* v_r_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4952_; 
v_size_4668_ = lean_ctor_get(v_t_4667_, 0);
v_k_4669_ = lean_ctor_get(v_t_4667_, 1);
v_v_4670_ = lean_ctor_get(v_t_4667_, 2);
v_l_4671_ = lean_ctor_get(v_t_4667_, 3);
v_r_4672_ = lean_ctor_get(v_t_4667_, 4);
v_isSharedCheck_4952_ = !lean_is_exclusive(v_t_4667_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4674_ = v_t_4667_;
v_isShared_4675_ = v_isSharedCheck_4952_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_r_4672_);
lean_inc(v_l_4671_);
lean_inc(v_v_4670_);
lean_inc(v_k_4669_);
lean_inc(v_size_4668_);
lean_dec(v_t_4667_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4952_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
uint8_t v___x_4676_; 
v___x_4676_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4665_, v_k_4669_);
switch(v___x_4676_)
{
case 0:
{
lean_object* v_impl_4677_; lean_object* v___x_4678_; 
lean_dec(v_size_4668_);
v_impl_4677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4665_, v_v_4666_, v_l_4671_);
v___x_4678_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4672_) == 0)
{
lean_object* v_size_4679_; lean_object* v_size_4680_; lean_object* v_k_4681_; lean_object* v_v_4682_; lean_object* v_l_4683_; lean_object* v_r_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; 
v_size_4679_ = lean_ctor_get(v_r_4672_, 0);
v_size_4680_ = lean_ctor_get(v_impl_4677_, 0);
v_k_4681_ = lean_ctor_get(v_impl_4677_, 1);
v_v_4682_ = lean_ctor_get(v_impl_4677_, 2);
v_l_4683_ = lean_ctor_get(v_impl_4677_, 3);
v_r_4684_ = lean_ctor_get(v_impl_4677_, 4);
lean_inc(v_r_4684_);
v___x_4685_ = lean_unsigned_to_nat(3u);
v___x_4686_ = lean_nat_mul(v___x_4685_, v_size_4679_);
v___x_4687_ = lean_nat_dec_lt(v___x_4686_, v_size_4680_);
lean_dec(v___x_4686_);
if (v___x_4687_ == 0)
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4691_; 
lean_dec(v_r_4684_);
v___x_4688_ = lean_nat_add(v___x_4678_, v_size_4680_);
v___x_4689_ = lean_nat_add(v___x_4688_, v_size_4679_);
lean_dec(v___x_4688_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 3, v_impl_4677_);
lean_ctor_set(v___x_4674_, 0, v___x_4689_);
v___x_4691_ = v___x_4674_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4689_);
lean_ctor_set(v_reuseFailAlloc_4692_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4692_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4692_, 3, v_impl_4677_);
lean_ctor_set(v_reuseFailAlloc_4692_, 4, v_r_4672_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
else
{
lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4758_; 
lean_inc(v_l_4683_);
lean_inc(v_v_4682_);
lean_inc(v_k_4681_);
lean_inc(v_size_4680_);
v_isSharedCheck_4758_ = !lean_is_exclusive(v_impl_4677_);
if (v_isSharedCheck_4758_ == 0)
{
lean_object* v_unused_4759_; lean_object* v_unused_4760_; lean_object* v_unused_4761_; lean_object* v_unused_4762_; lean_object* v_unused_4763_; 
v_unused_4759_ = lean_ctor_get(v_impl_4677_, 4);
lean_dec(v_unused_4759_);
v_unused_4760_ = lean_ctor_get(v_impl_4677_, 3);
lean_dec(v_unused_4760_);
v_unused_4761_ = lean_ctor_get(v_impl_4677_, 2);
lean_dec(v_unused_4761_);
v_unused_4762_ = lean_ctor_get(v_impl_4677_, 1);
lean_dec(v_unused_4762_);
v_unused_4763_ = lean_ctor_get(v_impl_4677_, 0);
lean_dec(v_unused_4763_);
v___x_4694_ = v_impl_4677_;
v_isShared_4695_ = v_isSharedCheck_4758_;
goto v_resetjp_4693_;
}
else
{
lean_dec(v_impl_4677_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4758_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v_size_4696_; lean_object* v_size_4697_; lean_object* v_k_4698_; lean_object* v_v_4699_; lean_object* v_l_4700_; lean_object* v_r_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; uint8_t v___x_4704_; 
v_size_4696_ = lean_ctor_get(v_l_4683_, 0);
v_size_4697_ = lean_ctor_get(v_r_4684_, 0);
v_k_4698_ = lean_ctor_get(v_r_4684_, 1);
v_v_4699_ = lean_ctor_get(v_r_4684_, 2);
v_l_4700_ = lean_ctor_get(v_r_4684_, 3);
v_r_4701_ = lean_ctor_get(v_r_4684_, 4);
v___x_4702_ = lean_unsigned_to_nat(2u);
v___x_4703_ = lean_nat_mul(v___x_4702_, v_size_4696_);
v___x_4704_ = lean_nat_dec_lt(v_size_4697_, v___x_4703_);
lean_dec(v___x_4703_);
if (v___x_4704_ == 0)
{
lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4733_; 
lean_inc(v_r_4701_);
lean_inc(v_l_4700_);
lean_inc(v_v_4699_);
lean_inc(v_k_4698_);
v_isSharedCheck_4733_ = !lean_is_exclusive(v_r_4684_);
if (v_isSharedCheck_4733_ == 0)
{
lean_object* v_unused_4734_; lean_object* v_unused_4735_; lean_object* v_unused_4736_; lean_object* v_unused_4737_; lean_object* v_unused_4738_; 
v_unused_4734_ = lean_ctor_get(v_r_4684_, 4);
lean_dec(v_unused_4734_);
v_unused_4735_ = lean_ctor_get(v_r_4684_, 3);
lean_dec(v_unused_4735_);
v_unused_4736_ = lean_ctor_get(v_r_4684_, 2);
lean_dec(v_unused_4736_);
v_unused_4737_ = lean_ctor_get(v_r_4684_, 1);
lean_dec(v_unused_4737_);
v_unused_4738_ = lean_ctor_get(v_r_4684_, 0);
lean_dec(v_unused_4738_);
v___x_4706_ = v_r_4684_;
v_isShared_4707_ = v_isSharedCheck_4733_;
goto v_resetjp_4705_;
}
else
{
lean_dec(v_r_4684_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4733_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; lean_object* v___x_4721_; lean_object* v___y_4723_; 
v___x_4708_ = lean_nat_add(v___x_4678_, v_size_4680_);
lean_dec(v_size_4680_);
v___x_4709_ = lean_nat_add(v___x_4708_, v_size_4679_);
lean_dec(v___x_4708_);
v___x_4721_ = lean_nat_add(v___x_4678_, v_size_4696_);
if (lean_obj_tag(v_l_4700_) == 0)
{
lean_object* v_size_4731_; 
v_size_4731_ = lean_ctor_get(v_l_4700_, 0);
lean_inc(v_size_4731_);
v___y_4723_ = v_size_4731_;
goto v___jp_4722_;
}
else
{
lean_object* v___x_4732_; 
v___x_4732_ = lean_unsigned_to_nat(0u);
v___y_4723_ = v___x_4732_;
goto v___jp_4722_;
}
v___jp_4710_:
{
lean_object* v___x_4714_; lean_object* v___x_4716_; 
v___x_4714_ = lean_nat_add(v___y_4712_, v___y_4713_);
lean_dec(v___y_4713_);
lean_dec(v___y_4712_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 4, v_r_4672_);
lean_ctor_set(v___x_4706_, 3, v_r_4701_);
lean_ctor_set(v___x_4706_, 2, v_v_4670_);
lean_ctor_set(v___x_4706_, 1, v_k_4669_);
lean_ctor_set(v___x_4706_, 0, v___x_4714_);
v___x_4716_ = v___x_4706_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4720_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4720_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4720_, 3, v_r_4701_);
lean_ctor_set(v_reuseFailAlloc_4720_, 4, v_r_4672_);
v___x_4716_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
lean_object* v___x_4718_; 
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 4, v___x_4716_);
lean_ctor_set(v___x_4694_, 3, v___y_4711_);
lean_ctor_set(v___x_4694_, 2, v_v_4699_);
lean_ctor_set(v___x_4694_, 1, v_k_4698_);
lean_ctor_set(v___x_4694_, 0, v___x_4709_);
v___x_4718_ = v___x_4694_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4709_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v_k_4698_);
lean_ctor_set(v_reuseFailAlloc_4719_, 2, v_v_4699_);
lean_ctor_set(v_reuseFailAlloc_4719_, 3, v___y_4711_);
lean_ctor_set(v_reuseFailAlloc_4719_, 4, v___x_4716_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
v___jp_4722_:
{
lean_object* v___x_4724_; lean_object* v___x_4726_; 
v___x_4724_ = lean_nat_add(v___x_4721_, v___y_4723_);
lean_dec(v___y_4723_);
lean_dec(v___x_4721_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 4, v_l_4700_);
lean_ctor_set(v___x_4674_, 3, v_l_4683_);
lean_ctor_set(v___x_4674_, 2, v_v_4682_);
lean_ctor_set(v___x_4674_, 1, v_k_4681_);
lean_ctor_set(v___x_4674_, 0, v___x_4724_);
v___x_4726_ = v___x_4674_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4724_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_k_4681_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_v_4682_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_l_4683_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_l_4700_);
v___x_4726_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
lean_object* v___x_4727_; 
v___x_4727_ = lean_nat_add(v___x_4678_, v_size_4679_);
if (lean_obj_tag(v_r_4701_) == 0)
{
lean_object* v_size_4728_; 
v_size_4728_ = lean_ctor_get(v_r_4701_, 0);
lean_inc(v_size_4728_);
v___y_4711_ = v___x_4726_;
v___y_4712_ = v___x_4727_;
v___y_4713_ = v_size_4728_;
goto v___jp_4710_;
}
else
{
lean_object* v___x_4729_; 
v___x_4729_ = lean_unsigned_to_nat(0u);
v___y_4711_ = v___x_4726_;
v___y_4712_ = v___x_4727_;
v___y_4713_ = v___x_4729_;
goto v___jp_4710_;
}
}
}
}
}
else
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4744_; 
lean_del_object(v___x_4674_);
v___x_4739_ = lean_nat_add(v___x_4678_, v_size_4680_);
lean_dec(v_size_4680_);
v___x_4740_ = lean_nat_add(v___x_4739_, v_size_4679_);
lean_dec(v___x_4739_);
v___x_4741_ = lean_nat_add(v___x_4678_, v_size_4679_);
v___x_4742_ = lean_nat_add(v___x_4741_, v_size_4697_);
lean_dec(v___x_4741_);
lean_inc_ref(v_r_4672_);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 4, v_r_4672_);
lean_ctor_set(v___x_4694_, 3, v_r_4684_);
lean_ctor_set(v___x_4694_, 2, v_v_4670_);
lean_ctor_set(v___x_4694_, 1, v_k_4669_);
lean_ctor_set(v___x_4694_, 0, v___x_4742_);
v___x_4744_ = v___x_4694_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4742_);
lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4757_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4757_, 3, v_r_4684_);
lean_ctor_set(v_reuseFailAlloc_4757_, 4, v_r_4672_);
v___x_4744_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
v_isSharedCheck_4751_ = !lean_is_exclusive(v_r_4672_);
if (v_isSharedCheck_4751_ == 0)
{
lean_object* v_unused_4752_; lean_object* v_unused_4753_; lean_object* v_unused_4754_; lean_object* v_unused_4755_; lean_object* v_unused_4756_; 
v_unused_4752_ = lean_ctor_get(v_r_4672_, 4);
lean_dec(v_unused_4752_);
v_unused_4753_ = lean_ctor_get(v_r_4672_, 3);
lean_dec(v_unused_4753_);
v_unused_4754_ = lean_ctor_get(v_r_4672_, 2);
lean_dec(v_unused_4754_);
v_unused_4755_ = lean_ctor_get(v_r_4672_, 1);
lean_dec(v_unused_4755_);
v_unused_4756_ = lean_ctor_get(v_r_4672_, 0);
lean_dec(v_unused_4756_);
v___x_4746_ = v_r_4672_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_dec(v_r_4672_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
lean_ctor_set(v___x_4746_, 4, v___x_4744_);
lean_ctor_set(v___x_4746_, 3, v_l_4683_);
lean_ctor_set(v___x_4746_, 2, v_v_4682_);
lean_ctor_set(v___x_4746_, 1, v_k_4681_);
lean_ctor_set(v___x_4746_, 0, v___x_4740_);
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4740_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_k_4681_);
lean_ctor_set(v_reuseFailAlloc_4750_, 2, v_v_4682_);
lean_ctor_set(v_reuseFailAlloc_4750_, 3, v_l_4683_);
lean_ctor_set(v_reuseFailAlloc_4750_, 4, v___x_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4764_; 
v_l_4764_ = lean_ctor_get(v_impl_4677_, 3);
if (lean_obj_tag(v_l_4764_) == 0)
{
lean_object* v_r_4765_; lean_object* v_k_4766_; lean_object* v_v_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4778_; 
lean_inc_ref(v_l_4764_);
v_r_4765_ = lean_ctor_get(v_impl_4677_, 4);
v_k_4766_ = lean_ctor_get(v_impl_4677_, 1);
v_v_4767_ = lean_ctor_get(v_impl_4677_, 2);
v_isSharedCheck_4778_ = !lean_is_exclusive(v_impl_4677_);
if (v_isSharedCheck_4778_ == 0)
{
lean_object* v_unused_4779_; lean_object* v_unused_4780_; 
v_unused_4779_ = lean_ctor_get(v_impl_4677_, 3);
lean_dec(v_unused_4779_);
v_unused_4780_ = lean_ctor_get(v_impl_4677_, 0);
lean_dec(v_unused_4780_);
v___x_4769_ = v_impl_4677_;
v_isShared_4770_ = v_isSharedCheck_4778_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_r_4765_);
lean_inc(v_v_4767_);
lean_inc(v_k_4766_);
lean_dec(v_impl_4677_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4778_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4771_; lean_object* v___x_4773_; 
v___x_4771_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4765_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 3, v_r_4765_);
lean_ctor_set(v___x_4769_, 2, v_v_4670_);
lean_ctor_set(v___x_4769_, 1, v_k_4669_);
lean_ctor_set(v___x_4769_, 0, v___x_4678_);
v___x_4773_ = v___x_4769_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4777_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4777_, 3, v_r_4765_);
lean_ctor_set(v_reuseFailAlloc_4777_, 4, v_r_4765_);
v___x_4773_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
lean_object* v___x_4775_; 
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 4, v___x_4773_);
lean_ctor_set(v___x_4674_, 3, v_l_4764_);
lean_ctor_set(v___x_4674_, 2, v_v_4767_);
lean_ctor_set(v___x_4674_, 1, v_k_4766_);
lean_ctor_set(v___x_4674_, 0, v___x_4771_);
v___x_4775_ = v___x_4674_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v___x_4771_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v_k_4766_);
lean_ctor_set(v_reuseFailAlloc_4776_, 2, v_v_4767_);
lean_ctor_set(v_reuseFailAlloc_4776_, 3, v_l_4764_);
lean_ctor_set(v_reuseFailAlloc_4776_, 4, v___x_4773_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
else
{
lean_object* v_r_4781_; 
v_r_4781_ = lean_ctor_get(v_impl_4677_, 4);
lean_inc(v_r_4781_);
if (lean_obj_tag(v_r_4781_) == 0)
{
lean_object* v_k_4782_; lean_object* v_v_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4806_; 
lean_inc(v_l_4764_);
v_k_4782_ = lean_ctor_get(v_impl_4677_, 1);
v_v_4783_ = lean_ctor_get(v_impl_4677_, 2);
v_isSharedCheck_4806_ = !lean_is_exclusive(v_impl_4677_);
if (v_isSharedCheck_4806_ == 0)
{
lean_object* v_unused_4807_; lean_object* v_unused_4808_; lean_object* v_unused_4809_; 
v_unused_4807_ = lean_ctor_get(v_impl_4677_, 4);
lean_dec(v_unused_4807_);
v_unused_4808_ = lean_ctor_get(v_impl_4677_, 3);
lean_dec(v_unused_4808_);
v_unused_4809_ = lean_ctor_get(v_impl_4677_, 0);
lean_dec(v_unused_4809_);
v___x_4785_ = v_impl_4677_;
v_isShared_4786_ = v_isSharedCheck_4806_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_v_4783_);
lean_inc(v_k_4782_);
lean_dec(v_impl_4677_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4806_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v_k_4787_; lean_object* v_v_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4802_; 
v_k_4787_ = lean_ctor_get(v_r_4781_, 1);
v_v_4788_ = lean_ctor_get(v_r_4781_, 2);
v_isSharedCheck_4802_ = !lean_is_exclusive(v_r_4781_);
if (v_isSharedCheck_4802_ == 0)
{
lean_object* v_unused_4803_; lean_object* v_unused_4804_; lean_object* v_unused_4805_; 
v_unused_4803_ = lean_ctor_get(v_r_4781_, 4);
lean_dec(v_unused_4803_);
v_unused_4804_ = lean_ctor_get(v_r_4781_, 3);
lean_dec(v_unused_4804_);
v_unused_4805_ = lean_ctor_get(v_r_4781_, 0);
lean_dec(v_unused_4805_);
v___x_4790_ = v_r_4781_;
v_isShared_4791_ = v_isSharedCheck_4802_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_v_4788_);
lean_inc(v_k_4787_);
lean_dec(v_r_4781_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4802_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4792_; lean_object* v___x_4794_; 
v___x_4792_ = lean_unsigned_to_nat(3u);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 4, v_l_4764_);
lean_ctor_set(v___x_4790_, 3, v_l_4764_);
lean_ctor_set(v___x_4790_, 2, v_v_4783_);
lean_ctor_set(v___x_4790_, 1, v_k_4782_);
lean_ctor_set(v___x_4790_, 0, v___x_4678_);
v___x_4794_ = v___x_4790_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4801_, 1, v_k_4782_);
lean_ctor_set(v_reuseFailAlloc_4801_, 2, v_v_4783_);
lean_ctor_set(v_reuseFailAlloc_4801_, 3, v_l_4764_);
lean_ctor_set(v_reuseFailAlloc_4801_, 4, v_l_4764_);
v___x_4794_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
lean_object* v___x_4796_; 
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 4, v_l_4764_);
lean_ctor_set(v___x_4785_, 2, v_v_4670_);
lean_ctor_set(v___x_4785_, 1, v_k_4669_);
lean_ctor_set(v___x_4785_, 0, v___x_4678_);
v___x_4796_ = v___x_4785_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4800_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4800_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4800_, 3, v_l_4764_);
lean_ctor_set(v_reuseFailAlloc_4800_, 4, v_l_4764_);
v___x_4796_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
lean_object* v___x_4798_; 
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 4, v___x_4796_);
lean_ctor_set(v___x_4674_, 3, v___x_4794_);
lean_ctor_set(v___x_4674_, 2, v_v_4788_);
lean_ctor_set(v___x_4674_, 1, v_k_4787_);
lean_ctor_set(v___x_4674_, 0, v___x_4792_);
v___x_4798_ = v___x_4674_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4799_, 1, v_k_4787_);
lean_ctor_set(v_reuseFailAlloc_4799_, 2, v_v_4788_);
lean_ctor_set(v_reuseFailAlloc_4799_, 3, v___x_4794_);
lean_ctor_set(v_reuseFailAlloc_4799_, 4, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
}
}
else
{
lean_object* v___x_4810_; lean_object* v___x_4812_; 
v___x_4810_ = lean_unsigned_to_nat(2u);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 4, v_r_4781_);
lean_ctor_set(v___x_4674_, 3, v_impl_4677_);
lean_ctor_set(v___x_4674_, 0, v___x_4810_);
v___x_4812_ = v___x_4674_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4810_);
lean_ctor_set(v_reuseFailAlloc_4813_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4813_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4813_, 3, v_impl_4677_);
lean_ctor_set(v_reuseFailAlloc_4813_, 4, v_r_4781_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4815_; 
lean_dec(v_v_4670_);
lean_dec(v_k_4669_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 2, v_v_4666_);
lean_ctor_set(v___x_4674_, 1, v_k_4665_);
v___x_4815_ = v___x_4674_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_size_4668_);
lean_ctor_set(v_reuseFailAlloc_4816_, 1, v_k_4665_);
lean_ctor_set(v_reuseFailAlloc_4816_, 2, v_v_4666_);
lean_ctor_set(v_reuseFailAlloc_4816_, 3, v_l_4671_);
lean_ctor_set(v_reuseFailAlloc_4816_, 4, v_r_4672_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
default: 
{
lean_object* v_impl_4817_; lean_object* v___x_4818_; 
lean_dec(v_size_4668_);
v_impl_4817_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4665_, v_v_4666_, v_r_4672_);
v___x_4818_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4671_) == 0)
{
lean_object* v_size_4819_; lean_object* v_size_4820_; lean_object* v_k_4821_; lean_object* v_v_4822_; lean_object* v_l_4823_; lean_object* v_r_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
v_size_4819_ = lean_ctor_get(v_l_4671_, 0);
v_size_4820_ = lean_ctor_get(v_impl_4817_, 0);
v_k_4821_ = lean_ctor_get(v_impl_4817_, 1);
v_v_4822_ = lean_ctor_get(v_impl_4817_, 2);
v_l_4823_ = lean_ctor_get(v_impl_4817_, 3);
lean_inc(v_l_4823_);
v_r_4824_ = lean_ctor_get(v_impl_4817_, 4);
v___x_4825_ = lean_unsigned_to_nat(3u);
v___x_4826_ = lean_nat_mul(v___x_4825_, v_size_4819_);
v___x_4827_ = lean_nat_dec_lt(v___x_4826_, v_size_4820_);
lean_dec(v___x_4826_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4831_; 
lean_dec(v_l_4823_);
v___x_4828_ = lean_nat_add(v___x_4818_, v_size_4819_);
v___x_4829_ = lean_nat_add(v___x_4828_, v_size_4820_);
lean_dec(v___x_4828_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 4, v_impl_4817_);
lean_ctor_set(v___x_4674_, 0, v___x_4829_);
v___x_4831_ = v___x_4674_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4829_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4832_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4832_, 3, v_l_4671_);
lean_ctor_set(v_reuseFailAlloc_4832_, 4, v_impl_4817_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
else
{
lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4896_; 
lean_inc(v_r_4824_);
lean_inc(v_v_4822_);
lean_inc(v_k_4821_);
lean_inc(v_size_4820_);
v_isSharedCheck_4896_ = !lean_is_exclusive(v_impl_4817_);
if (v_isSharedCheck_4896_ == 0)
{
lean_object* v_unused_4897_; lean_object* v_unused_4898_; lean_object* v_unused_4899_; lean_object* v_unused_4900_; lean_object* v_unused_4901_; 
v_unused_4897_ = lean_ctor_get(v_impl_4817_, 4);
lean_dec(v_unused_4897_);
v_unused_4898_ = lean_ctor_get(v_impl_4817_, 3);
lean_dec(v_unused_4898_);
v_unused_4899_ = lean_ctor_get(v_impl_4817_, 2);
lean_dec(v_unused_4899_);
v_unused_4900_ = lean_ctor_get(v_impl_4817_, 1);
lean_dec(v_unused_4900_);
v_unused_4901_ = lean_ctor_get(v_impl_4817_, 0);
lean_dec(v_unused_4901_);
v___x_4834_ = v_impl_4817_;
v_isShared_4835_ = v_isSharedCheck_4896_;
goto v_resetjp_4833_;
}
else
{
lean_dec(v_impl_4817_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4896_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v_size_4836_; lean_object* v_k_4837_; lean_object* v_v_4838_; lean_object* v_l_4839_; lean_object* v_r_4840_; lean_object* v_size_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; uint8_t v___x_4844_; 
v_size_4836_ = lean_ctor_get(v_l_4823_, 0);
v_k_4837_ = lean_ctor_get(v_l_4823_, 1);
v_v_4838_ = lean_ctor_get(v_l_4823_, 2);
v_l_4839_ = lean_ctor_get(v_l_4823_, 3);
v_r_4840_ = lean_ctor_get(v_l_4823_, 4);
v_size_4841_ = lean_ctor_get(v_r_4824_, 0);
v___x_4842_ = lean_unsigned_to_nat(2u);
v___x_4843_ = lean_nat_mul(v___x_4842_, v_size_4841_);
v___x_4844_ = lean_nat_dec_lt(v_size_4836_, v___x_4843_);
lean_dec(v___x_4843_);
if (v___x_4844_ == 0)
{
lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4872_; 
lean_inc(v_r_4840_);
lean_inc(v_l_4839_);
lean_inc(v_v_4838_);
lean_inc(v_k_4837_);
v_isSharedCheck_4872_ = !lean_is_exclusive(v_l_4823_);
if (v_isSharedCheck_4872_ == 0)
{
lean_object* v_unused_4873_; lean_object* v_unused_4874_; lean_object* v_unused_4875_; lean_object* v_unused_4876_; lean_object* v_unused_4877_; 
v_unused_4873_ = lean_ctor_get(v_l_4823_, 4);
lean_dec(v_unused_4873_);
v_unused_4874_ = lean_ctor_get(v_l_4823_, 3);
lean_dec(v_unused_4874_);
v_unused_4875_ = lean_ctor_get(v_l_4823_, 2);
lean_dec(v_unused_4875_);
v_unused_4876_ = lean_ctor_get(v_l_4823_, 1);
lean_dec(v_unused_4876_);
v_unused_4877_ = lean_ctor_get(v_l_4823_, 0);
lean_dec(v_unused_4877_);
v___x_4846_ = v_l_4823_;
v_isShared_4847_ = v_isSharedCheck_4872_;
goto v_resetjp_4845_;
}
else
{
lean_dec(v_l_4823_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4872_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___y_4851_; lean_object* v___y_4852_; lean_object* v___y_4853_; lean_object* v___y_4862_; 
v___x_4848_ = lean_nat_add(v___x_4818_, v_size_4819_);
v___x_4849_ = lean_nat_add(v___x_4848_, v_size_4820_);
lean_dec(v_size_4820_);
if (lean_obj_tag(v_l_4839_) == 0)
{
lean_object* v_size_4870_; 
v_size_4870_ = lean_ctor_get(v_l_4839_, 0);
lean_inc(v_size_4870_);
v___y_4862_ = v_size_4870_;
goto v___jp_4861_;
}
else
{
lean_object* v___x_4871_; 
v___x_4871_ = lean_unsigned_to_nat(0u);
v___y_4862_ = v___x_4871_;
goto v___jp_4861_;
}
v___jp_4850_:
{
lean_object* v___x_4854_; lean_object* v___x_4856_; 
v___x_4854_ = lean_nat_add(v___y_4852_, v___y_4853_);
lean_dec(v___y_4853_);
lean_dec(v___y_4852_);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 4, v_r_4824_);
lean_ctor_set(v___x_4846_, 3, v_r_4840_);
lean_ctor_set(v___x_4846_, 2, v_v_4822_);
lean_ctor_set(v___x_4846_, 1, v_k_4821_);
lean_ctor_set(v___x_4846_, 0, v___x_4854_);
v___x_4856_ = v___x_4846_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_k_4821_);
lean_ctor_set(v_reuseFailAlloc_4860_, 2, v_v_4822_);
lean_ctor_set(v_reuseFailAlloc_4860_, 3, v_r_4840_);
lean_ctor_set(v_reuseFailAlloc_4860_, 4, v_r_4824_);
v___x_4856_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
lean_object* v___x_4858_; 
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 4, v___x_4856_);
lean_ctor_set(v___x_4834_, 3, v___y_4851_);
lean_ctor_set(v___x_4834_, 2, v_v_4838_);
lean_ctor_set(v___x_4834_, 1, v_k_4837_);
lean_ctor_set(v___x_4834_, 0, v___x_4849_);
v___x_4858_ = v___x_4834_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4849_);
lean_ctor_set(v_reuseFailAlloc_4859_, 1, v_k_4837_);
lean_ctor_set(v_reuseFailAlloc_4859_, 2, v_v_4838_);
lean_ctor_set(v_reuseFailAlloc_4859_, 3, v___y_4851_);
lean_ctor_set(v_reuseFailAlloc_4859_, 4, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
v___jp_4861_:
{
lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4863_ = lean_nat_add(v___x_4848_, v___y_4862_);
lean_dec(v___y_4862_);
lean_dec(v___x_4848_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 4, v_l_4839_);
lean_ctor_set(v___x_4674_, 0, v___x_4863_);
v___x_4865_ = v___x_4674_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4863_);
lean_ctor_set(v_reuseFailAlloc_4869_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4869_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4869_, 3, v_l_4671_);
lean_ctor_set(v_reuseFailAlloc_4869_, 4, v_l_4839_);
v___x_4865_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
lean_object* v___x_4866_; 
v___x_4866_ = lean_nat_add(v___x_4818_, v_size_4841_);
if (lean_obj_tag(v_r_4840_) == 0)
{
lean_object* v_size_4867_; 
v_size_4867_ = lean_ctor_get(v_r_4840_, 0);
lean_inc(v_size_4867_);
v___y_4851_ = v___x_4865_;
v___y_4852_ = v___x_4866_;
v___y_4853_ = v_size_4867_;
goto v___jp_4850_;
}
else
{
lean_object* v___x_4868_; 
v___x_4868_ = lean_unsigned_to_nat(0u);
v___y_4851_ = v___x_4865_;
v___y_4852_ = v___x_4866_;
v___y_4853_ = v___x_4868_;
goto v___jp_4850_;
}
}
}
}
}
else
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
lean_del_object(v___x_4674_);
v___x_4878_ = lean_nat_add(v___x_4818_, v_size_4819_);
v___x_4879_ = lean_nat_add(v___x_4878_, v_size_4820_);
lean_dec(v_size_4820_);
v___x_4880_ = lean_nat_add(v___x_4878_, v_size_4836_);
lean_dec(v___x_4878_);
lean_inc_ref(v_l_4671_);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 4, v_l_4823_);
lean_ctor_set(v___x_4834_, 3, v_l_4671_);
lean_ctor_set(v___x_4834_, 2, v_v_4670_);
lean_ctor_set(v___x_4834_, 1, v_k_4669_);
lean_ctor_set(v___x_4834_, 0, v___x_4880_);
v___x_4882_ = v___x_4834_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4880_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4895_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4895_, 3, v_l_4671_);
lean_ctor_set(v_reuseFailAlloc_4895_, 4, v_l_4823_);
v___x_4882_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
v_isSharedCheck_4889_ = !lean_is_exclusive(v_l_4671_);
if (v_isSharedCheck_4889_ == 0)
{
lean_object* v_unused_4890_; lean_object* v_unused_4891_; lean_object* v_unused_4892_; lean_object* v_unused_4893_; lean_object* v_unused_4894_; 
v_unused_4890_ = lean_ctor_get(v_l_4671_, 4);
lean_dec(v_unused_4890_);
v_unused_4891_ = lean_ctor_get(v_l_4671_, 3);
lean_dec(v_unused_4891_);
v_unused_4892_ = lean_ctor_get(v_l_4671_, 2);
lean_dec(v_unused_4892_);
v_unused_4893_ = lean_ctor_get(v_l_4671_, 1);
lean_dec(v_unused_4893_);
v_unused_4894_ = lean_ctor_get(v_l_4671_, 0);
lean_dec(v_unused_4894_);
v___x_4884_ = v_l_4671_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_dec(v_l_4671_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 4, v_r_4824_);
lean_ctor_set(v___x_4884_, 3, v___x_4882_);
lean_ctor_set(v___x_4884_, 2, v_v_4822_);
lean_ctor_set(v___x_4884_, 1, v_k_4821_);
lean_ctor_set(v___x_4884_, 0, v___x_4879_);
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4888_, 1, v_k_4821_);
lean_ctor_set(v_reuseFailAlloc_4888_, 2, v_v_4822_);
lean_ctor_set(v_reuseFailAlloc_4888_, 3, v___x_4882_);
lean_ctor_set(v_reuseFailAlloc_4888_, 4, v_r_4824_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4902_; 
v_l_4902_ = lean_ctor_get(v_impl_4817_, 3);
lean_inc(v_l_4902_);
if (lean_obj_tag(v_l_4902_) == 0)
{
lean_object* v_r_4903_; lean_object* v_k_4904_; lean_object* v_v_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4928_; 
v_r_4903_ = lean_ctor_get(v_impl_4817_, 4);
v_k_4904_ = lean_ctor_get(v_impl_4817_, 1);
v_v_4905_ = lean_ctor_get(v_impl_4817_, 2);
v_isSharedCheck_4928_ = !lean_is_exclusive(v_impl_4817_);
if (v_isSharedCheck_4928_ == 0)
{
lean_object* v_unused_4929_; lean_object* v_unused_4930_; 
v_unused_4929_ = lean_ctor_get(v_impl_4817_, 3);
lean_dec(v_unused_4929_);
v_unused_4930_ = lean_ctor_get(v_impl_4817_, 0);
lean_dec(v_unused_4930_);
v___x_4907_ = v_impl_4817_;
v_isShared_4908_ = v_isSharedCheck_4928_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_r_4903_);
lean_inc(v_v_4905_);
lean_inc(v_k_4904_);
lean_dec(v_impl_4817_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4928_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v_k_4909_; lean_object* v_v_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4924_; 
v_k_4909_ = lean_ctor_get(v_l_4902_, 1);
v_v_4910_ = lean_ctor_get(v_l_4902_, 2);
v_isSharedCheck_4924_ = !lean_is_exclusive(v_l_4902_);
if (v_isSharedCheck_4924_ == 0)
{
lean_object* v_unused_4925_; lean_object* v_unused_4926_; lean_object* v_unused_4927_; 
v_unused_4925_ = lean_ctor_get(v_l_4902_, 4);
lean_dec(v_unused_4925_);
v_unused_4926_ = lean_ctor_get(v_l_4902_, 3);
lean_dec(v_unused_4926_);
v_unused_4927_ = lean_ctor_get(v_l_4902_, 0);
lean_dec(v_unused_4927_);
v___x_4912_ = v_l_4902_;
v_isShared_4913_ = v_isSharedCheck_4924_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_v_4910_);
lean_inc(v_k_4909_);
lean_dec(v_l_4902_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4924_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4914_; lean_object* v___x_4916_; 
v___x_4914_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4903_, 2);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 4, v_r_4903_);
lean_ctor_set(v___x_4912_, 3, v_r_4903_);
lean_ctor_set(v___x_4912_, 2, v_v_4670_);
lean_ctor_set(v___x_4912_, 1, v_k_4669_);
lean_ctor_set(v___x_4912_, 0, v___x_4818_);
v___x_4916_ = v___x_4912_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4818_);
lean_ctor_set(v_reuseFailAlloc_4923_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4923_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4923_, 3, v_r_4903_);
lean_ctor_set(v_reuseFailAlloc_4923_, 4, v_r_4903_);
v___x_4916_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
lean_object* v___x_4918_; 
lean_inc(v_r_4903_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 3, v_r_4903_);
lean_ctor_set(v___x_4907_, 0, v___x_4818_);
v___x_4918_ = v___x_4907_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4818_);
lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_k_4904_);
lean_ctor_set(v_reuseFailAlloc_4922_, 2, v_v_4905_);
lean_ctor_set(v_reuseFailAlloc_4922_, 3, v_r_4903_);
lean_ctor_set(v_reuseFailAlloc_4922_, 4, v_r_4903_);
v___x_4918_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
lean_object* v___x_4920_; 
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 4, v___x_4918_);
lean_ctor_set(v___x_4674_, 3, v___x_4916_);
lean_ctor_set(v___x_4674_, 2, v_v_4910_);
lean_ctor_set(v___x_4674_, 1, v_k_4909_);
lean_ctor_set(v___x_4674_, 0, v___x_4914_);
v___x_4920_ = v___x_4674_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4914_);
lean_ctor_set(v_reuseFailAlloc_4921_, 1, v_k_4909_);
lean_ctor_set(v_reuseFailAlloc_4921_, 2, v_v_4910_);
lean_ctor_set(v_reuseFailAlloc_4921_, 3, v___x_4916_);
lean_ctor_set(v_reuseFailAlloc_4921_, 4, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
}
}
else
{
lean_object* v_r_4931_; 
v_r_4931_ = lean_ctor_get(v_impl_4817_, 4);
lean_inc(v_r_4931_);
if (lean_obj_tag(v_r_4931_) == 0)
{
lean_object* v_k_4932_; lean_object* v_v_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4944_; 
v_k_4932_ = lean_ctor_get(v_impl_4817_, 1);
v_v_4933_ = lean_ctor_get(v_impl_4817_, 2);
v_isSharedCheck_4944_ = !lean_is_exclusive(v_impl_4817_);
if (v_isSharedCheck_4944_ == 0)
{
lean_object* v_unused_4945_; lean_object* v_unused_4946_; lean_object* v_unused_4947_; 
v_unused_4945_ = lean_ctor_get(v_impl_4817_, 4);
lean_dec(v_unused_4945_);
v_unused_4946_ = lean_ctor_get(v_impl_4817_, 3);
lean_dec(v_unused_4946_);
v_unused_4947_ = lean_ctor_get(v_impl_4817_, 0);
lean_dec(v_unused_4947_);
v___x_4935_ = v_impl_4817_;
v_isShared_4936_ = v_isSharedCheck_4944_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_v_4933_);
lean_inc(v_k_4932_);
lean_dec(v_impl_4817_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4944_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4937_; lean_object* v___x_4939_; 
v___x_4937_ = lean_unsigned_to_nat(3u);
if (v_isShared_4936_ == 0)
{
lean_ctor_set(v___x_4935_, 4, v_l_4902_);
lean_ctor_set(v___x_4935_, 2, v_v_4670_);
lean_ctor_set(v___x_4935_, 1, v_k_4669_);
lean_ctor_set(v___x_4935_, 0, v___x_4818_);
v___x_4939_ = v___x_4935_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4818_);
lean_ctor_set(v_reuseFailAlloc_4943_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4943_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4943_, 3, v_l_4902_);
lean_ctor_set(v_reuseFailAlloc_4943_, 4, v_l_4902_);
v___x_4939_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
lean_object* v___x_4941_; 
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 4, v_r_4931_);
lean_ctor_set(v___x_4674_, 3, v___x_4939_);
lean_ctor_set(v___x_4674_, 2, v_v_4933_);
lean_ctor_set(v___x_4674_, 1, v_k_4932_);
lean_ctor_set(v___x_4674_, 0, v___x_4937_);
v___x_4941_ = v___x_4674_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4937_);
lean_ctor_set(v_reuseFailAlloc_4942_, 1, v_k_4932_);
lean_ctor_set(v_reuseFailAlloc_4942_, 2, v_v_4933_);
lean_ctor_set(v_reuseFailAlloc_4942_, 3, v___x_4939_);
lean_ctor_set(v_reuseFailAlloc_4942_, 4, v_r_4931_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
}
else
{
lean_object* v___x_4948_; lean_object* v___x_4950_; 
v___x_4948_ = lean_unsigned_to_nat(2u);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 4, v_impl_4817_);
lean_ctor_set(v___x_4674_, 3, v_r_4931_);
lean_ctor_set(v___x_4674_, 0, v___x_4948_);
v___x_4950_ = v___x_4674_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4948_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4951_, 3, v_r_4931_);
lean_ctor_set(v_reuseFailAlloc_4951_, 4, v_impl_4817_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
return v___x_4950_;
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
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = lean_unsigned_to_nat(1u);
v___x_4954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4953_);
lean_ctor_set(v___x_4954_, 1, v_k_4665_);
lean_ctor_set(v___x_4954_, 2, v_v_4666_);
lean_ctor_set(v___x_4954_, 3, v_t_4667_);
lean_ctor_set(v___x_4954_, 4, v_t_4667_);
return v___x_4954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object* v_as_4955_, size_t v_sz_4956_, size_t v_i_4957_, lean_object* v_b_4958_){
_start:
{
uint8_t v___x_4959_; 
v___x_4959_ = lean_usize_dec_lt(v_i_4957_, v_sz_4956_);
if (v___x_4959_ == 0)
{
return v_b_4958_;
}
else
{
lean_object* v_a_4960_; lean_object* v_fst_4961_; lean_object* v_snd_4962_; lean_object* v_r_4963_; size_t v___x_4964_; size_t v___x_4965_; 
v_a_4960_ = lean_array_uget_borrowed(v_as_4955_, v_i_4957_);
v_fst_4961_ = lean_ctor_get(v_a_4960_, 0);
v_snd_4962_ = lean_ctor_get(v_a_4960_, 1);
lean_inc(v_snd_4962_);
lean_inc(v_fst_4961_);
v_r_4963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_fst_4961_, v_snd_4962_, v_b_4958_);
v___x_4964_ = ((size_t)1ULL);
v___x_4965_ = lean_usize_add(v_i_4957_, v___x_4964_);
v_i_4957_ = v___x_4965_;
v_b_4958_ = v_r_4963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object* v_as_4967_, lean_object* v_sz_4968_, lean_object* v_i_4969_, lean_object* v_b_4970_){
_start:
{
size_t v_sz_boxed_4971_; size_t v_i_boxed_4972_; lean_object* v_res_4973_; 
v_sz_boxed_4971_ = lean_unbox_usize(v_sz_4968_);
lean_dec(v_sz_4968_);
v_i_boxed_4972_ = lean_unbox_usize(v_i_4969_);
lean_dec(v_i_4969_);
v_res_4973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v_as_4967_, v_sz_boxed_4971_, v_i_boxed_4972_, v_b_4970_);
lean_dec_ref(v_as_4967_);
return v_res_4973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object* v_a_4976_, lean_object* v_x_4977_){
_start:
{
lean_object* v___y_4979_; 
if (lean_obj_tag(v_x_4977_) == 0)
{
lean_object* v___x_4982_; 
v___x_4982_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___y_4979_ = v___x_4982_;
goto v___jp_4978_;
}
else
{
lean_object* v_val_4983_; 
v_val_4983_ = lean_ctor_get(v_x_4977_, 0);
lean_inc(v_val_4983_);
lean_dec_ref_known(v_x_4977_, 1);
v___y_4979_ = v_val_4983_;
goto v___jp_4978_;
}
v___jp_4978_:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4980_ = lean_array_push(v___y_4979_, v_a_4976_);
v___x_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
return v___x_4981_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_x_4986_){
_start:
{
if (lean_obj_tag(v_x_4986_) == 0)
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v_val_4989_; lean_object* v___x_4990_; 
v___x_4987_ = lean_box(0);
v___x_4988_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4984_, v___x_4987_);
v_val_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc(v_val_4989_);
lean_dec(v___x_4988_);
v___x_4990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4990_, 0, v_a_4985_);
lean_ctor_set(v___x_4990_, 1, v_val_4989_);
lean_ctor_set(v___x_4990_, 2, v_x_4986_);
return v___x_4990_;
}
else
{
lean_object* v_key_4991_; lean_object* v_value_4992_; lean_object* v_tail_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5008_; 
v_key_4991_ = lean_ctor_get(v_x_4986_, 0);
v_value_4992_ = lean_ctor_get(v_x_4986_, 1);
v_tail_4993_ = lean_ctor_get(v_x_4986_, 2);
v_isSharedCheck_5008_ = !lean_is_exclusive(v_x_4986_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_4995_ = v_x_4986_;
v_isShared_4996_ = v_isSharedCheck_5008_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_tail_4993_);
lean_inc(v_value_4992_);
lean_inc(v_key_4991_);
lean_dec(v_x_4986_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5008_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
uint8_t v___x_4997_; 
v___x_4997_ = lean_name_eq(v_key_4991_, v_a_4985_);
if (v___x_4997_ == 0)
{
lean_object* v_tail_4998_; lean_object* v___x_5000_; 
v_tail_4998_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4984_, v_a_4985_, v_tail_4993_);
if (v_isShared_4996_ == 0)
{
lean_ctor_set(v___x_4995_, 2, v_tail_4998_);
v___x_5000_ = v___x_4995_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_key_4991_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v_value_4992_);
lean_ctor_set(v_reuseFailAlloc_5001_, 2, v_tail_4998_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
else
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v_val_5004_; lean_object* v___x_5006_; 
lean_dec(v_key_4991_);
v___x_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5002_, 0, v_value_4992_);
v___x_5003_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4984_, v___x_5002_);
v_val_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_val_5004_);
lean_dec(v___x_5003_);
if (v_isShared_4996_ == 0)
{
lean_ctor_set(v___x_4995_, 1, v_val_5004_);
lean_ctor_set(v___x_4995_, 0, v_a_4985_);
v___x_5006_ = v___x_4995_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_4985_);
lean_ctor_set(v_reuseFailAlloc_5007_, 1, v_val_5004_);
lean_ctor_set(v_reuseFailAlloc_5007_, 2, v_tail_4993_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_5009_, lean_object* v_x_5010_){
_start:
{
if (lean_obj_tag(v_x_5010_) == 0)
{
return v_x_5009_;
}
else
{
lean_object* v_key_5011_; lean_object* v_value_5012_; lean_object* v_tail_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5039_; 
v_key_5011_ = lean_ctor_get(v_x_5010_, 0);
v_value_5012_ = lean_ctor_get(v_x_5010_, 1);
v_tail_5013_ = lean_ctor_get(v_x_5010_, 2);
v_isSharedCheck_5039_ = !lean_is_exclusive(v_x_5010_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5015_ = v_x_5010_;
v_isShared_5016_ = v_isSharedCheck_5039_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_tail_5013_);
lean_inc(v_value_5012_);
lean_inc(v_key_5011_);
lean_dec(v_x_5010_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5039_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5017_; uint64_t v___y_5019_; 
v___x_5017_ = lean_array_get_size(v_x_5009_);
if (lean_obj_tag(v_key_5011_) == 0)
{
uint64_t v___x_5037_; 
v___x_5037_ = 1723ULL;
v___y_5019_ = v___x_5037_;
goto v___jp_5018_;
}
else
{
uint64_t v_hash_5038_; 
v_hash_5038_ = lean_ctor_get_uint64(v_key_5011_, sizeof(void*)*2);
v___y_5019_ = v_hash_5038_;
goto v___jp_5018_;
}
v___jp_5018_:
{
uint64_t v___x_5020_; uint64_t v___x_5021_; uint64_t v_fold_5022_; uint64_t v___x_5023_; uint64_t v___x_5024_; uint64_t v___x_5025_; size_t v___x_5026_; size_t v___x_5027_; size_t v___x_5028_; size_t v___x_5029_; size_t v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5033_; 
v___x_5020_ = 32ULL;
v___x_5021_ = lean_uint64_shift_right(v___y_5019_, v___x_5020_);
v_fold_5022_ = lean_uint64_xor(v___y_5019_, v___x_5021_);
v___x_5023_ = 16ULL;
v___x_5024_ = lean_uint64_shift_right(v_fold_5022_, v___x_5023_);
v___x_5025_ = lean_uint64_xor(v_fold_5022_, v___x_5024_);
v___x_5026_ = lean_uint64_to_usize(v___x_5025_);
v___x_5027_ = lean_usize_of_nat(v___x_5017_);
v___x_5028_ = ((size_t)1ULL);
v___x_5029_ = lean_usize_sub(v___x_5027_, v___x_5028_);
v___x_5030_ = lean_usize_land(v___x_5026_, v___x_5029_);
v___x_5031_ = lean_array_uget_borrowed(v_x_5009_, v___x_5030_);
lean_inc(v___x_5031_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 2, v___x_5031_);
v___x_5033_ = v___x_5015_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_key_5011_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v_value_5012_);
lean_ctor_set(v_reuseFailAlloc_5036_, 2, v___x_5031_);
v___x_5033_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
lean_object* v___x_5034_; 
v___x_5034_ = lean_array_uset(v_x_5009_, v___x_5030_, v___x_5033_);
v_x_5009_ = v___x_5034_;
v_x_5010_ = v_tail_5013_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object* v_i_5040_, lean_object* v_source_5041_, lean_object* v_target_5042_){
_start:
{
lean_object* v___x_5043_; uint8_t v___x_5044_; 
v___x_5043_ = lean_array_get_size(v_source_5041_);
v___x_5044_ = lean_nat_dec_lt(v_i_5040_, v___x_5043_);
if (v___x_5044_ == 0)
{
lean_dec_ref(v_source_5041_);
lean_dec(v_i_5040_);
return v_target_5042_;
}
else
{
lean_object* v_es_5045_; lean_object* v___x_5046_; lean_object* v_source_5047_; lean_object* v_target_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
v_es_5045_ = lean_array_fget(v_source_5041_, v_i_5040_);
v___x_5046_ = lean_box(0);
v_source_5047_ = lean_array_fset(v_source_5041_, v_i_5040_, v___x_5046_);
v_target_5048_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_target_5042_, v_es_5045_);
v___x_5049_ = lean_unsigned_to_nat(1u);
v___x_5050_ = lean_nat_add(v_i_5040_, v___x_5049_);
lean_dec(v_i_5040_);
v_i_5040_ = v___x_5050_;
v_source_5041_ = v_source_5047_;
v_target_5042_ = v_target_5048_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object* v_data_5052_){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v_nbuckets_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5053_ = lean_array_get_size(v_data_5052_);
v___x_5054_ = lean_unsigned_to_nat(2u);
v_nbuckets_5055_ = lean_nat_mul(v___x_5053_, v___x_5054_);
v___x_5056_ = lean_unsigned_to_nat(0u);
v___x_5057_ = lean_box(0);
v___x_5058_ = lean_mk_array(v_nbuckets_5055_, v___x_5057_);
v___x_5059_ = lean_array_propagate_mark(v_data_5052_, v___x_5058_);
v___x_5060_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_5056_, v_data_5052_, v___x_5059_);
return v___x_5060_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_5061_, lean_object* v_x_5062_){
_start:
{
if (lean_obj_tag(v_x_5062_) == 0)
{
uint8_t v___x_5063_; 
v___x_5063_ = 0;
return v___x_5063_;
}
else
{
lean_object* v_key_5064_; lean_object* v_tail_5065_; uint8_t v___x_5066_; 
v_key_5064_ = lean_ctor_get(v_x_5062_, 0);
v_tail_5065_ = lean_ctor_get(v_x_5062_, 2);
v___x_5066_ = lean_name_eq(v_key_5064_, v_a_5061_);
if (v___x_5066_ == 0)
{
v_x_5062_ = v_tail_5065_;
goto _start;
}
else
{
return v___x_5066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_5068_, lean_object* v_x_5069_){
_start:
{
uint8_t v_res_5070_; lean_object* v_r_5071_; 
v_res_5070_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5068_, v_x_5069_);
lean_dec(v_x_5069_);
lean_dec(v_a_5068_);
v_r_5071_ = lean_box(v_res_5070_);
return v_r_5071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_5072_, lean_object* v_m_5073_, lean_object* v_a_5074_){
_start:
{
lean_object* v___y_5076_; lean_object* v___y_5077_; size_t v___y_5078_; lean_object* v___y_5079_; lean_object* v_size_5082_; lean_object* v_buckets_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5130_; 
v_size_5082_ = lean_ctor_get(v_m_5073_, 0);
v_buckets_5083_ = lean_ctor_get(v_m_5073_, 1);
v_isSharedCheck_5130_ = !lean_is_exclusive(v_m_5073_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5085_ = v_m_5073_;
v_isShared_5086_ = v_isSharedCheck_5130_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_buckets_5083_);
lean_inc(v_size_5082_);
lean_dec(v_m_5073_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5130_;
goto v_resetjp_5084_;
}
v___jp_5075_:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5080_ = lean_array_uset(v___y_5076_, v___y_5078_, v___y_5077_);
v___x_5081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5081_, 0, v___y_5079_);
lean_ctor_set(v___x_5081_, 1, v___x_5080_);
return v___x_5081_;
}
v_resetjp_5084_:
{
lean_object* v___x_5087_; uint64_t v___y_5089_; 
v___x_5087_ = lean_array_get_size(v_buckets_5083_);
if (lean_obj_tag(v_a_5074_) == 0)
{
uint64_t v___x_5128_; 
v___x_5128_ = 1723ULL;
v___y_5089_ = v___x_5128_;
goto v___jp_5088_;
}
else
{
uint64_t v_hash_5129_; 
v_hash_5129_ = lean_ctor_get_uint64(v_a_5074_, sizeof(void*)*2);
v___y_5089_ = v_hash_5129_;
goto v___jp_5088_;
}
v___jp_5088_:
{
uint64_t v___x_5090_; uint64_t v___x_5091_; uint64_t v_fold_5092_; uint64_t v___x_5093_; uint64_t v___x_5094_; uint64_t v___x_5095_; size_t v___x_5096_; size_t v___x_5097_; size_t v___x_5098_; size_t v___x_5099_; size_t v___x_5100_; lean_object* v_bkt_5101_; uint8_t v___x_5102_; 
v___x_5090_ = 32ULL;
v___x_5091_ = lean_uint64_shift_right(v___y_5089_, v___x_5090_);
v_fold_5092_ = lean_uint64_xor(v___y_5089_, v___x_5091_);
v___x_5093_ = 16ULL;
v___x_5094_ = lean_uint64_shift_right(v_fold_5092_, v___x_5093_);
v___x_5095_ = lean_uint64_xor(v_fold_5092_, v___x_5094_);
v___x_5096_ = lean_uint64_to_usize(v___x_5095_);
v___x_5097_ = lean_usize_of_nat(v___x_5087_);
v___x_5098_ = ((size_t)1ULL);
v___x_5099_ = lean_usize_sub(v___x_5097_, v___x_5098_);
v___x_5100_ = lean_usize_land(v___x_5096_, v___x_5099_);
v_bkt_5101_ = lean_array_uget_borrowed(v_buckets_5083_, v___x_5100_);
v___x_5102_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5074_, v_bkt_5101_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v_size_x27_5106_; lean_object* v___x_5107_; lean_object* v_buckets_x27_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; uint8_t v___x_5114_; 
v___x_5103_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_5104_ = lean_array_push(v___x_5103_, v_a_5072_);
v___x_5105_ = lean_unsigned_to_nat(1u);
v_size_x27_5106_ = lean_nat_add(v_size_5082_, v___x_5105_);
lean_dec(v_size_5082_);
lean_inc(v_bkt_5101_);
v___x_5107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5107_, 0, v_a_5074_);
lean_ctor_set(v___x_5107_, 1, v___x_5104_);
lean_ctor_set(v___x_5107_, 2, v_bkt_5101_);
v_buckets_x27_5108_ = lean_array_uset(v_buckets_5083_, v___x_5100_, v___x_5107_);
v___x_5109_ = lean_unsigned_to_nat(4u);
v___x_5110_ = lean_nat_mul(v_size_x27_5106_, v___x_5109_);
v___x_5111_ = lean_unsigned_to_nat(3u);
v___x_5112_ = lean_nat_div(v___x_5110_, v___x_5111_);
lean_dec(v___x_5110_);
v___x_5113_ = lean_array_get_size(v_buckets_x27_5108_);
v___x_5114_ = lean_nat_dec_le(v___x_5112_, v___x_5113_);
lean_dec(v___x_5112_);
if (v___x_5114_ == 0)
{
lean_object* v_val_5115_; lean_object* v___x_5117_; 
v_val_5115_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5108_);
if (v_isShared_5086_ == 0)
{
lean_ctor_set(v___x_5085_, 1, v_val_5115_);
lean_ctor_set(v___x_5085_, 0, v_size_x27_5106_);
v___x_5117_ = v___x_5085_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_size_x27_5106_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v_val_5115_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
else
{
lean_object* v___x_5120_; 
if (v_isShared_5086_ == 0)
{
lean_ctor_set(v___x_5085_, 1, v_buckets_x27_5108_);
lean_ctor_set(v___x_5085_, 0, v_size_x27_5106_);
v___x_5120_ = v___x_5085_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_size_x27_5106_);
lean_ctor_set(v_reuseFailAlloc_5121_, 1, v_buckets_x27_5108_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
else
{
lean_object* v___x_5122_; lean_object* v_buckets_x27_5123_; lean_object* v_bkt_x27_5124_; uint8_t v___x_5125_; 
lean_inc(v_bkt_5101_);
lean_del_object(v___x_5085_);
v___x_5122_ = lean_box(0);
v_buckets_x27_5123_ = lean_array_uset(v_buckets_5083_, v___x_5100_, v___x_5122_);
lean_inc(v_a_5074_);
v_bkt_x27_5124_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5072_, v_a_5074_, v_bkt_5101_);
v___x_5125_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5074_, v_bkt_x27_5124_);
lean_dec(v_a_5074_);
if (v___x_5125_ == 0)
{
lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5126_ = lean_unsigned_to_nat(1u);
v___x_5127_ = lean_nat_sub(v_size_5082_, v___x_5126_);
lean_dec(v_size_5082_);
v___y_5076_ = v_buckets_x27_5123_;
v___y_5077_ = v_bkt_x27_5124_;
v___y_5078_ = v___x_5100_;
v___y_5079_ = v___x_5127_;
goto v___jp_5075_;
}
else
{
v___y_5076_ = v_buckets_x27_5123_;
v___y_5077_ = v_bkt_x27_5124_;
v___y_5078_ = v___x_5100_;
v___y_5079_ = v_size_5082_;
goto v___jp_5075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5131_, lean_object* v_as_5132_, size_t v_sz_5133_, size_t v_i_5134_, lean_object* v_b_5135_){
_start:
{
uint8_t v___x_5136_; 
v___x_5136_ = lean_usize_dec_lt(v_i_5134_, v_sz_5133_);
if (v___x_5136_ == 0)
{
lean_dec_ref(v_key_5131_);
return v_b_5135_;
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; size_t v___x_5140_; size_t v___x_5141_; 
v_a_5137_ = lean_array_uget_borrowed(v_as_5132_, v_i_5134_);
lean_inc_ref(v_key_5131_);
lean_inc_n(v_a_5137_, 2);
v___x_5138_ = lean_apply_1(v_key_5131_, v_a_5137_);
v___x_5139_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5137_, v_b_5135_, v___x_5138_);
v___x_5140_ = ((size_t)1ULL);
v___x_5141_ = lean_usize_add(v_i_5134_, v___x_5140_);
v_i_5134_ = v___x_5141_;
v_b_5135_ = v___x_5139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5143_, lean_object* v_as_5144_, lean_object* v_sz_5145_, lean_object* v_i_5146_, lean_object* v_b_5147_){
_start:
{
size_t v_sz_boxed_5148_; size_t v_i_boxed_5149_; lean_object* v_res_5150_; 
v_sz_boxed_5148_ = lean_unbox_usize(v_sz_5145_);
lean_dec(v_sz_5145_);
v_i_boxed_5149_ = lean_unbox_usize(v_i_5146_);
lean_dec(v_i_5146_);
v_res_5150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5143_, v_as_5144_, v_sz_boxed_5148_, v_i_boxed_5149_, v_b_5147_);
lean_dec_ref(v_as_5144_);
return v_res_5150_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5151_ = lean_box(0);
v___x_5152_ = lean_unsigned_to_nat(16u);
v___x_5153_ = lean_mk_array(v___x_5152_, v___x_5151_);
return v___x_5153_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v_groups_5156_; 
v___x_5154_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5155_ = lean_unsigned_to_nat(0u);
v_groups_5156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5156_, 0, v___x_5155_);
lean_ctor_set(v_groups_5156_, 1, v___x_5154_);
return v_groups_5156_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5157_, lean_object* v_xs_5158_){
_start:
{
lean_object* v_groups_5159_; size_t v_sz_5160_; size_t v___x_5161_; lean_object* v___x_5162_; 
v_groups_5159_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5160_ = lean_array_size(v_xs_5158_);
v___x_5161_ = ((size_t)0ULL);
v___x_5162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5157_, v_xs_5158_, v_sz_5160_, v___x_5161_, v_groups_5159_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5163_, lean_object* v_xs_5164_){
_start:
{
lean_object* v_res_5165_; 
v_res_5165_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5163_, v_xs_5164_);
lean_dec_ref(v_xs_5164_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5167_){
_start:
{
lean_object* v___f_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___f_5169_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5170_ = lean_unsigned_to_nat(0u);
v___x_5171_ = lean_array_get_size(v_infos_5167_);
v___x_5172_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5167_, v___x_5170_, v___x_5171_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5196_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5175_ = v___x_5172_;
v_isShared_5176_ = v_isSharedCheck_5196_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5172_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5196_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___y_5178_; lean_object* v___x_5187_; lean_object* v_size_5188_; lean_object* v_buckets_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; uint8_t v___x_5192_; 
v___x_5187_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5169_, v_a_5173_);
v_size_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_size_5188_);
v_buckets_5189_ = lean_ctor_get(v___x_5187_, 1);
lean_inc_ref(v_buckets_5189_);
lean_dec_ref(v___x_5187_);
v___x_5190_ = lean_mk_empty_array_with_capacity(v_size_5188_);
lean_dec(v_size_5188_);
v___x_5191_ = lean_array_get_size(v_buckets_5189_);
v___x_5192_ = lean_nat_dec_lt(v___x_5170_, v___x_5191_);
if (v___x_5192_ == 0)
{
lean_dec_ref(v_buckets_5189_);
v___y_5178_ = v___x_5190_;
goto v___jp_5177_;
}
else
{
size_t v___x_5193_; size_t v___x_5194_; lean_object* v___x_5195_; 
v___x_5193_ = ((size_t)0ULL);
v___x_5194_ = lean_usize_of_nat(v___x_5191_);
v___x_5195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5189_, v___x_5193_, v___x_5194_, v___x_5190_);
lean_dec_ref(v_buckets_5189_);
v___y_5178_ = v___x_5195_;
goto v___jp_5177_;
}
v___jp_5177_:
{
lean_object* v_r_5179_; size_t v_sz_5180_; size_t v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5185_; 
v_r_5179_ = lean_box(1);
v_sz_5180_ = lean_array_size(v___y_5178_);
v___x_5181_ = ((size_t)0ULL);
v___x_5182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5178_, v_sz_5180_, v___x_5181_, v_r_5179_);
lean_dec_ref(v___y_5178_);
v___x_5183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5183_, 0, v_a_5173_);
lean_ctor_set(v___x_5183_, 1, v___x_5182_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 0, v___x_5183_);
v___x_5185_ = v___x_5175_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5186_; 
v_reuseFailAlloc_5186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5186_, 0, v___x_5183_);
v___x_5185_ = v_reuseFailAlloc_5186_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
return v___x_5185_;
}
}
}
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
v_a_5197_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5172_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5172_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5205_, lean_object* v_a_5206_){
_start:
{
lean_object* v_res_5207_; 
v_res_5207_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5205_);
lean_dec_ref(v_infos_5205_);
return v_res_5207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5208_, lean_object* v_k_5209_, lean_object* v_v_5210_, lean_object* v_t_5211_, lean_object* v_hl_5212_){
_start:
{
lean_object* v___x_5213_; 
v___x_5213_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5209_, v_v_5210_, v_t_5211_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5214_, lean_object* v_key_5215_, lean_object* v_xs_5216_){
_start:
{
lean_object* v___x_5217_; 
v___x_5217_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5215_, v_xs_5216_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5218_, lean_object* v_key_5219_, lean_object* v_xs_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5218_, v_key_5219_, v_xs_5220_);
lean_dec_ref(v_xs_5220_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5222_, lean_object* v_a_5223_, lean_object* v_m_5224_, lean_object* v_a_5225_){
_start:
{
lean_object* v___x_5226_; 
v___x_5226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5223_, v_m_5224_, v_a_5225_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5227_, lean_object* v_key_5228_, lean_object* v_as_5229_, size_t v_sz_5230_, size_t v_i_5231_, lean_object* v_b_5232_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5228_, v_as_5229_, v_sz_5230_, v_i_5231_, v_b_5232_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5234_, lean_object* v_key_5235_, lean_object* v_as_5236_, lean_object* v_sz_5237_, lean_object* v_i_5238_, lean_object* v_b_5239_){
_start:
{
size_t v_sz_boxed_5240_; size_t v_i_boxed_5241_; lean_object* v_res_5242_; 
v_sz_boxed_5240_ = lean_unbox_usize(v_sz_5237_);
lean_dec(v_sz_5237_);
v_i_boxed_5241_ = lean_unbox_usize(v_i_5238_);
lean_dec(v_i_5238_);
v_res_5242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5234_, v_key_5235_, v_as_5236_, v_sz_boxed_5240_, v_i_boxed_5241_, v_b_5239_);
lean_dec_ref(v_as_5236_);
return v_res_5242_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5243_, lean_object* v_a_5244_, lean_object* v_x_5245_){
_start:
{
uint8_t v___x_5246_; 
v___x_5246_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5244_, v_x_5245_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5247_, lean_object* v_a_5248_, lean_object* v_x_5249_){
_start:
{
uint8_t v_res_5250_; lean_object* v_r_5251_; 
v_res_5250_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5247_, v_a_5248_, v_x_5249_);
lean_dec(v_x_5249_);
lean_dec(v_a_5248_);
v_r_5251_ = lean_box(v_res_5250_);
return v_r_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5252_, lean_object* v_data_5253_){
_start:
{
lean_object* v___x_5254_; 
v___x_5254_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5253_);
return v___x_5254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_x_5258_){
_start:
{
lean_object* v___x_5259_; 
v___x_5259_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5256_, v_a_5257_, v_x_5258_);
return v___x_5259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5260_, lean_object* v_i_5261_, lean_object* v_source_5262_, lean_object* v_target_5263_){
_start:
{
lean_object* v___x_5264_; 
v___x_5264_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5261_, v_source_5262_, v_target_5263_);
return v___x_5264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5265_, lean_object* v_x_5266_, lean_object* v_x_5267_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5266_, v_x_5267_);
return v___x_5268_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5269_){
_start:
{
lean_object* v_isSetupFailure_x3f_5270_; 
v_isSetupFailure_x3f_5270_ = lean_ctor_get(v_i_5269_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5270_) == 0)
{
uint8_t v___x_5271_; 
v___x_5271_ = 0;
return v___x_5271_;
}
else
{
lean_object* v_val_5272_; uint8_t v___x_5273_; 
v_val_5272_ = lean_ctor_get(v_isSetupFailure_x3f_5270_, 0);
v___x_5273_ = lean_unbox(v_val_5272_);
if (v___x_5273_ == 0)
{
uint8_t v___x_5274_; 
v___x_5274_ = 1;
return v___x_5274_;
}
else
{
uint8_t v___x_5275_; 
v___x_5275_ = 0;
return v___x_5275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5276_){
_start:
{
uint8_t v_res_5277_; lean_object* v_r_5278_; 
v_res_5277_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5276_);
lean_dec_ref(v_i_5276_);
v_r_5278_ = lean_box(v_res_5277_);
return v_r_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5284_, lean_object* v_path_5285_, lean_object* v_ilean_5286_){
_start:
{
lean_object* v_module_5288_; lean_object* v_directImports_5289_; lean_object* v_references_5290_; lean_object* v_decls_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5343_; 
v_module_5288_ = lean_ctor_get(v_ilean_5286_, 1);
v_directImports_5289_ = lean_ctor_get(v_ilean_5286_, 2);
v_references_5290_ = lean_ctor_get(v_ilean_5286_, 3);
v_decls_5291_ = lean_ctor_get(v_ilean_5286_, 4);
v_isSharedCheck_5343_ = !lean_is_exclusive(v_ilean_5286_);
if (v_isSharedCheck_5343_ == 0)
{
lean_object* v_unused_5344_; 
v_unused_5344_ = lean_ctor_get(v_ilean_5286_, 0);
lean_dec(v_unused_5344_);
v___x_5293_ = v_ilean_5286_;
v_isShared_5294_ = v_isSharedCheck_5343_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_decls_5291_);
lean_inc(v_references_5290_);
lean_inc(v_directImports_5289_);
lean_inc(v_module_5288_);
lean_dec(v_ilean_5286_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5343_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5295_; 
lean_inc(v_module_5288_);
v___x_5295_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5288_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5334_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5298_ = v___x_5295_;
v_isShared_5299_ = v_isSharedCheck_5334_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5295_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5334_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
if (lean_obj_tag(v_a_5296_) == 1)
{
lean_object* v_val_5300_; lean_object* v___x_5301_; 
lean_del_object(v___x_5298_);
v_val_5300_ = lean_ctor_get(v_a_5296_, 0);
lean_inc(v_val_5300_);
lean_dec_ref_known(v_a_5296_, 1);
v___x_5301_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5289_);
lean_dec_ref(v_directImports_5289_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5322_; 
v_a_5302_ = lean_ctor_get(v___x_5301_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5304_ = v___x_5301_;
v_isShared_5305_ = v_isSharedCheck_5322_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___x_5301_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5322_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v_ileans_5306_; lean_object* v_workers_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5321_; 
v_ileans_5306_ = lean_ctor_get(v_self_5284_, 0);
v_workers_5307_ = lean_ctor_get(v_self_5284_, 1);
v_isSharedCheck_5321_ = !lean_is_exclusive(v_self_5284_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5309_ = v_self_5284_;
v_isShared_5310_ = v_isSharedCheck_5321_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_workers_5307_);
lean_inc(v_ileans_5306_);
lean_dec(v_self_5284_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5321_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v___x_5312_; 
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 2, v_a_5302_);
lean_ctor_set(v___x_5293_, 1, v_path_5285_);
lean_ctor_set(v___x_5293_, 0, v_val_5300_);
v___x_5312_ = v___x_5293_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_val_5300_);
lean_ctor_set(v_reuseFailAlloc_5320_, 1, v_path_5285_);
lean_ctor_set(v_reuseFailAlloc_5320_, 2, v_a_5302_);
lean_ctor_set(v_reuseFailAlloc_5320_, 3, v_references_5290_);
lean_ctor_set(v_reuseFailAlloc_5320_, 4, v_decls_5291_);
v___x_5312_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
lean_object* v___x_5313_; lean_object* v___x_5315_; 
v___x_5313_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5288_, v___x_5312_, v_ileans_5306_);
if (v_isShared_5310_ == 0)
{
lean_ctor_set(v___x_5309_, 0, v___x_5313_);
v___x_5315_ = v___x_5309_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5313_);
lean_ctor_set(v_reuseFailAlloc_5319_, 1, v_workers_5307_);
v___x_5315_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
lean_object* v___x_5317_; 
if (v_isShared_5305_ == 0)
{
lean_ctor_set(v___x_5304_, 0, v___x_5315_);
v___x_5317_ = v___x_5304_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5315_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
}
}
}
else
{
lean_object* v_a_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5330_; 
lean_dec(v_val_5300_);
lean_del_object(v___x_5293_);
lean_dec(v_decls_5291_);
lean_dec(v_references_5290_);
lean_dec(v_module_5288_);
lean_dec_ref(v_path_5285_);
lean_dec_ref(v_self_5284_);
v_a_5323_ = lean_ctor_get(v___x_5301_, 0);
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5325_ = v___x_5301_;
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_a_5323_);
lean_dec(v___x_5301_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v___x_5328_; 
if (v_isShared_5326_ == 0)
{
v___x_5328_ = v___x_5325_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5323_);
v___x_5328_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
return v___x_5328_;
}
}
}
}
else
{
lean_object* v___x_5332_; 
lean_dec(v_a_5296_);
lean_del_object(v___x_5293_);
lean_dec(v_decls_5291_);
lean_dec(v_references_5290_);
lean_dec_ref(v_directImports_5289_);
lean_dec(v_module_5288_);
lean_dec_ref(v_path_5285_);
if (v_isShared_5299_ == 0)
{
lean_ctor_set(v___x_5298_, 0, v_self_5284_);
v___x_5332_ = v___x_5298_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_self_5284_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
}
else
{
lean_object* v_a_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5342_; 
lean_del_object(v___x_5293_);
lean_dec(v_decls_5291_);
lean_dec(v_references_5290_);
lean_dec_ref(v_directImports_5289_);
lean_dec(v_module_5288_);
lean_dec_ref(v_path_5285_);
lean_dec_ref(v_self_5284_);
v_a_5335_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5342_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5342_ == 0)
{
v___x_5337_ = v___x_5295_;
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_dec(v___x_5295_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5340_; 
if (v_isShared_5338_ == 0)
{
v___x_5340_ = v___x_5337_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_a_5335_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5345_, lean_object* v_path_5346_, lean_object* v_ilean_5347_, lean_object* v_a_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Lean_Server_References_addIlean(v_self_5345_, v_path_5346_, v_ilean_5347_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5350_, lean_object* v_t_5351_){
_start:
{
if (lean_obj_tag(v_t_5351_) == 0)
{
lean_object* v_v_5352_; lean_object* v_k_5353_; lean_object* v_l_5354_; lean_object* v_r_5355_; lean_object* v_ileanPath_5356_; uint8_t v___x_5357_; 
v_v_5352_ = lean_ctor_get(v_t_5351_, 2);
lean_inc(v_v_5352_);
v_k_5353_ = lean_ctor_get(v_t_5351_, 1);
lean_inc(v_k_5353_);
v_l_5354_ = lean_ctor_get(v_t_5351_, 3);
lean_inc(v_l_5354_);
v_r_5355_ = lean_ctor_get(v_t_5351_, 4);
lean_inc(v_r_5355_);
lean_dec_ref_known(v_t_5351_, 5);
v_ileanPath_5356_ = lean_ctor_get(v_v_5352_, 1);
v___x_5357_ = lean_string_dec_eq(v_ileanPath_5356_, v_path_5350_);
if (v___x_5357_ == 0)
{
lean_object* v_impl_5358_; lean_object* v_impl_5359_; lean_object* v___x_5360_; 
lean_dec(v_k_5353_);
lean_dec(v_v_5352_);
v_impl_5358_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5350_, v_l_5354_);
v_impl_5359_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5350_, v_r_5355_);
v___x_5360_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5358_, v_impl_5359_);
return v___x_5360_;
}
else
{
lean_object* v_impl_5361_; lean_object* v_impl_5362_; lean_object* v___x_5363_; 
v_impl_5361_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5350_, v_l_5354_);
v_impl_5362_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5350_, v_r_5355_);
v___x_5363_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5353_, v_v_5352_, v_impl_5361_, v_impl_5362_);
return v___x_5363_;
}
}
else
{
return v_t_5351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5364_, lean_object* v_t_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5364_, v_t_5365_);
lean_dec_ref(v_path_5364_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5367_, lean_object* v_t_5368_){
_start:
{
if (lean_obj_tag(v_t_5368_) == 0)
{
lean_object* v_k_5369_; lean_object* v_v_5370_; lean_object* v_l_5371_; lean_object* v_r_5372_; lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_6026_; 
v_k_5369_ = lean_ctor_get(v_t_5368_, 1);
v_v_5370_ = lean_ctor_get(v_t_5368_, 2);
v_l_5371_ = lean_ctor_get(v_t_5368_, 3);
v_r_5372_ = lean_ctor_get(v_t_5368_, 4);
v_isSharedCheck_6026_ = !lean_is_exclusive(v_t_5368_);
if (v_isSharedCheck_6026_ == 0)
{
lean_object* v_unused_6027_; 
v_unused_6027_ = lean_ctor_get(v_t_5368_, 0);
lean_dec(v_unused_6027_);
v___x_5374_ = v_t_5368_;
v_isShared_5375_ = v_isSharedCheck_6026_;
goto v_resetjp_5373_;
}
else
{
lean_inc(v_r_5372_);
lean_inc(v_l_5371_);
lean_inc(v_v_5370_);
lean_inc(v_k_5369_);
lean_dec(v_t_5368_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_6026_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
uint8_t v___x_5376_; 
v___x_5376_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5367_, v_k_5369_);
switch(v___x_5376_)
{
case 0:
{
lean_object* v_impl_5377_; lean_object* v___x_5378_; 
v_impl_5377_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5367_, v_l_5371_);
v___x_5378_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5377_) == 0)
{
if (lean_obj_tag(v_r_5372_) == 0)
{
lean_object* v_size_5379_; lean_object* v_size_5380_; lean_object* v_k_5381_; lean_object* v_v_5382_; lean_object* v_l_5383_; lean_object* v_r_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; uint8_t v___x_5387_; 
v_size_5379_ = lean_ctor_get(v_impl_5377_, 0);
v_size_5380_ = lean_ctor_get(v_r_5372_, 0);
v_k_5381_ = lean_ctor_get(v_r_5372_, 1);
v_v_5382_ = lean_ctor_get(v_r_5372_, 2);
v_l_5383_ = lean_ctor_get(v_r_5372_, 3);
lean_inc(v_l_5383_);
v_r_5384_ = lean_ctor_get(v_r_5372_, 4);
v___x_5385_ = lean_unsigned_to_nat(3u);
v___x_5386_ = lean_nat_mul(v___x_5385_, v_size_5379_);
v___x_5387_ = lean_nat_dec_lt(v___x_5386_, v_size_5380_);
lean_dec(v___x_5386_);
if (v___x_5387_ == 0)
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5391_; 
lean_dec(v_l_5383_);
v___x_5388_ = lean_nat_add(v___x_5378_, v_size_5379_);
v___x_5389_ = lean_nat_add(v___x_5388_, v_size_5380_);
lean_dec(v___x_5388_);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 3, v_impl_5377_);
lean_ctor_set(v___x_5374_, 0, v___x_5389_);
v___x_5391_ = v___x_5374_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v___x_5389_);
lean_ctor_set(v_reuseFailAlloc_5392_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5392_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5392_, 3, v_impl_5377_);
lean_ctor_set(v_reuseFailAlloc_5392_, 4, v_r_5372_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
else
{
lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5456_; 
lean_inc(v_r_5384_);
lean_inc(v_v_5382_);
lean_inc(v_k_5381_);
lean_inc(v_size_5380_);
v_isSharedCheck_5456_ = !lean_is_exclusive(v_r_5372_);
if (v_isSharedCheck_5456_ == 0)
{
lean_object* v_unused_5457_; lean_object* v_unused_5458_; lean_object* v_unused_5459_; lean_object* v_unused_5460_; lean_object* v_unused_5461_; 
v_unused_5457_ = lean_ctor_get(v_r_5372_, 4);
lean_dec(v_unused_5457_);
v_unused_5458_ = lean_ctor_get(v_r_5372_, 3);
lean_dec(v_unused_5458_);
v_unused_5459_ = lean_ctor_get(v_r_5372_, 2);
lean_dec(v_unused_5459_);
v_unused_5460_ = lean_ctor_get(v_r_5372_, 1);
lean_dec(v_unused_5460_);
v_unused_5461_ = lean_ctor_get(v_r_5372_, 0);
lean_dec(v_unused_5461_);
v___x_5394_ = v_r_5372_;
v_isShared_5395_ = v_isSharedCheck_5456_;
goto v_resetjp_5393_;
}
else
{
lean_dec(v_r_5372_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5456_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v_size_5396_; lean_object* v_k_5397_; lean_object* v_v_5398_; lean_object* v_l_5399_; lean_object* v_r_5400_; lean_object* v_size_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; uint8_t v___x_5404_; 
v_size_5396_ = lean_ctor_get(v_l_5383_, 0);
v_k_5397_ = lean_ctor_get(v_l_5383_, 1);
v_v_5398_ = lean_ctor_get(v_l_5383_, 2);
v_l_5399_ = lean_ctor_get(v_l_5383_, 3);
v_r_5400_ = lean_ctor_get(v_l_5383_, 4);
v_size_5401_ = lean_ctor_get(v_r_5384_, 0);
v___x_5402_ = lean_unsigned_to_nat(2u);
v___x_5403_ = lean_nat_mul(v___x_5402_, v_size_5401_);
v___x_5404_ = lean_nat_dec_lt(v_size_5396_, v___x_5403_);
lean_dec(v___x_5403_);
if (v___x_5404_ == 0)
{
lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5432_; 
lean_inc(v_r_5400_);
lean_inc(v_l_5399_);
lean_inc(v_v_5398_);
lean_inc(v_k_5397_);
v_isSharedCheck_5432_ = !lean_is_exclusive(v_l_5383_);
if (v_isSharedCheck_5432_ == 0)
{
lean_object* v_unused_5433_; lean_object* v_unused_5434_; lean_object* v_unused_5435_; lean_object* v_unused_5436_; lean_object* v_unused_5437_; 
v_unused_5433_ = lean_ctor_get(v_l_5383_, 4);
lean_dec(v_unused_5433_);
v_unused_5434_ = lean_ctor_get(v_l_5383_, 3);
lean_dec(v_unused_5434_);
v_unused_5435_ = lean_ctor_get(v_l_5383_, 2);
lean_dec(v_unused_5435_);
v_unused_5436_ = lean_ctor_get(v_l_5383_, 1);
lean_dec(v_unused_5436_);
v_unused_5437_ = lean_ctor_get(v_l_5383_, 0);
lean_dec(v_unused_5437_);
v___x_5406_ = v_l_5383_;
v_isShared_5407_ = v_isSharedCheck_5432_;
goto v_resetjp_5405_;
}
else
{
lean_dec(v_l_5383_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5432_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___y_5411_; lean_object* v___y_5412_; lean_object* v___y_5413_; lean_object* v___y_5422_; 
v___x_5408_ = lean_nat_add(v___x_5378_, v_size_5379_);
v___x_5409_ = lean_nat_add(v___x_5408_, v_size_5380_);
lean_dec(v_size_5380_);
if (lean_obj_tag(v_l_5399_) == 0)
{
lean_object* v_size_5430_; 
v_size_5430_ = lean_ctor_get(v_l_5399_, 0);
lean_inc(v_size_5430_);
v___y_5422_ = v_size_5430_;
goto v___jp_5421_;
}
else
{
lean_object* v___x_5431_; 
v___x_5431_ = lean_unsigned_to_nat(0u);
v___y_5422_ = v___x_5431_;
goto v___jp_5421_;
}
v___jp_5410_:
{
lean_object* v___x_5414_; lean_object* v___x_5416_; 
v___x_5414_ = lean_nat_add(v___y_5411_, v___y_5413_);
lean_dec(v___y_5413_);
lean_dec(v___y_5411_);
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 4, v_r_5384_);
lean_ctor_set(v___x_5406_, 3, v_r_5400_);
lean_ctor_set(v___x_5406_, 2, v_v_5382_);
lean_ctor_set(v___x_5406_, 1, v_k_5381_);
lean_ctor_set(v___x_5406_, 0, v___x_5414_);
v___x_5416_ = v___x_5406_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v___x_5414_);
lean_ctor_set(v_reuseFailAlloc_5420_, 1, v_k_5381_);
lean_ctor_set(v_reuseFailAlloc_5420_, 2, v_v_5382_);
lean_ctor_set(v_reuseFailAlloc_5420_, 3, v_r_5400_);
lean_ctor_set(v_reuseFailAlloc_5420_, 4, v_r_5384_);
v___x_5416_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
lean_object* v___x_5418_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 4, v___x_5416_);
lean_ctor_set(v___x_5394_, 3, v___y_5412_);
lean_ctor_set(v___x_5394_, 2, v_v_5398_);
lean_ctor_set(v___x_5394_, 1, v_k_5397_);
lean_ctor_set(v___x_5394_, 0, v___x_5409_);
v___x_5418_ = v___x_5394_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5409_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v_k_5397_);
lean_ctor_set(v_reuseFailAlloc_5419_, 2, v_v_5398_);
lean_ctor_set(v_reuseFailAlloc_5419_, 3, v___y_5412_);
lean_ctor_set(v_reuseFailAlloc_5419_, 4, v___x_5416_);
v___x_5418_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
return v___x_5418_;
}
}
}
v___jp_5421_:
{
lean_object* v___x_5423_; lean_object* v___x_5425_; 
v___x_5423_ = lean_nat_add(v___x_5408_, v___y_5422_);
lean_dec(v___y_5422_);
lean_dec(v___x_5408_);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v_l_5399_);
lean_ctor_set(v___x_5374_, 3, v_impl_5377_);
lean_ctor_set(v___x_5374_, 0, v___x_5423_);
v___x_5425_ = v___x_5374_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v___x_5423_);
lean_ctor_set(v_reuseFailAlloc_5429_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5429_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5429_, 3, v_impl_5377_);
lean_ctor_set(v_reuseFailAlloc_5429_, 4, v_l_5399_);
v___x_5425_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
lean_object* v___x_5426_; 
v___x_5426_ = lean_nat_add(v___x_5378_, v_size_5401_);
if (lean_obj_tag(v_r_5400_) == 0)
{
lean_object* v_size_5427_; 
v_size_5427_ = lean_ctor_get(v_r_5400_, 0);
lean_inc(v_size_5427_);
v___y_5411_ = v___x_5426_;
v___y_5412_ = v___x_5425_;
v___y_5413_ = v_size_5427_;
goto v___jp_5410_;
}
else
{
lean_object* v___x_5428_; 
v___x_5428_ = lean_unsigned_to_nat(0u);
v___y_5411_ = v___x_5426_;
v___y_5412_ = v___x_5425_;
v___y_5413_ = v___x_5428_;
goto v___jp_5410_;
}
}
}
}
}
else
{
lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5442_; 
lean_del_object(v___x_5374_);
v___x_5438_ = lean_nat_add(v___x_5378_, v_size_5379_);
v___x_5439_ = lean_nat_add(v___x_5438_, v_size_5380_);
lean_dec(v_size_5380_);
v___x_5440_ = lean_nat_add(v___x_5438_, v_size_5396_);
lean_dec(v___x_5438_);
lean_inc_ref(v_impl_5377_);
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 4, v_l_5383_);
lean_ctor_set(v___x_5394_, 3, v_impl_5377_);
lean_ctor_set(v___x_5394_, 2, v_v_5370_);
lean_ctor_set(v___x_5394_, 1, v_k_5369_);
lean_ctor_set(v___x_5394_, 0, v___x_5440_);
v___x_5442_ = v___x_5394_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v___x_5440_);
lean_ctor_set(v_reuseFailAlloc_5455_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5455_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5455_, 3, v_impl_5377_);
lean_ctor_set(v_reuseFailAlloc_5455_, 4, v_l_5383_);
v___x_5442_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5449_; 
v_isSharedCheck_5449_ = !lean_is_exclusive(v_impl_5377_);
if (v_isSharedCheck_5449_ == 0)
{
lean_object* v_unused_5450_; lean_object* v_unused_5451_; lean_object* v_unused_5452_; lean_object* v_unused_5453_; lean_object* v_unused_5454_; 
v_unused_5450_ = lean_ctor_get(v_impl_5377_, 4);
lean_dec(v_unused_5450_);
v_unused_5451_ = lean_ctor_get(v_impl_5377_, 3);
lean_dec(v_unused_5451_);
v_unused_5452_ = lean_ctor_get(v_impl_5377_, 2);
lean_dec(v_unused_5452_);
v_unused_5453_ = lean_ctor_get(v_impl_5377_, 1);
lean_dec(v_unused_5453_);
v_unused_5454_ = lean_ctor_get(v_impl_5377_, 0);
lean_dec(v_unused_5454_);
v___x_5444_ = v_impl_5377_;
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
else
{
lean_dec(v_impl_5377_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v___x_5447_; 
if (v_isShared_5445_ == 0)
{
lean_ctor_set(v___x_5444_, 4, v_r_5384_);
lean_ctor_set(v___x_5444_, 3, v___x_5442_);
lean_ctor_set(v___x_5444_, 2, v_v_5382_);
lean_ctor_set(v___x_5444_, 1, v_k_5381_);
lean_ctor_set(v___x_5444_, 0, v___x_5439_);
v___x_5447_ = v___x_5444_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5439_);
lean_ctor_set(v_reuseFailAlloc_5448_, 1, v_k_5381_);
lean_ctor_set(v_reuseFailAlloc_5448_, 2, v_v_5382_);
lean_ctor_set(v_reuseFailAlloc_5448_, 3, v___x_5442_);
lean_ctor_set(v_reuseFailAlloc_5448_, 4, v_r_5384_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5462_; lean_object* v___x_5463_; lean_object* v___x_5465_; 
v_size_5462_ = lean_ctor_get(v_impl_5377_, 0);
v___x_5463_ = lean_nat_add(v___x_5378_, v_size_5462_);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 3, v_impl_5377_);
lean_ctor_set(v___x_5374_, 0, v___x_5463_);
v___x_5465_ = v___x_5374_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5463_);
lean_ctor_set(v_reuseFailAlloc_5466_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5466_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5466_, 3, v_impl_5377_);
lean_ctor_set(v_reuseFailAlloc_5466_, 4, v_r_5372_);
v___x_5465_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
return v___x_5465_;
}
}
}
else
{
if (lean_obj_tag(v_r_5372_) == 0)
{
lean_object* v_l_5467_; 
v_l_5467_ = lean_ctor_get(v_r_5372_, 3);
lean_inc(v_l_5467_);
if (lean_obj_tag(v_l_5467_) == 0)
{
lean_object* v_r_5468_; 
v_r_5468_ = lean_ctor_get(v_r_5372_, 4);
lean_inc(v_r_5468_);
if (lean_obj_tag(v_r_5468_) == 0)
{
lean_object* v_size_5469_; lean_object* v_k_5470_; lean_object* v_v_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5484_; 
v_size_5469_ = lean_ctor_get(v_r_5372_, 0);
v_k_5470_ = lean_ctor_get(v_r_5372_, 1);
v_v_5471_ = lean_ctor_get(v_r_5372_, 2);
v_isSharedCheck_5484_ = !lean_is_exclusive(v_r_5372_);
if (v_isSharedCheck_5484_ == 0)
{
lean_object* v_unused_5485_; lean_object* v_unused_5486_; 
v_unused_5485_ = lean_ctor_get(v_r_5372_, 4);
lean_dec(v_unused_5485_);
v_unused_5486_ = lean_ctor_get(v_r_5372_, 3);
lean_dec(v_unused_5486_);
v___x_5473_ = v_r_5372_;
v_isShared_5474_ = v_isSharedCheck_5484_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_v_5471_);
lean_inc(v_k_5470_);
lean_inc(v_size_5469_);
lean_dec(v_r_5372_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5484_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v_size_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5479_; 
v_size_5475_ = lean_ctor_get(v_l_5467_, 0);
v___x_5476_ = lean_nat_add(v___x_5378_, v_size_5469_);
lean_dec(v_size_5469_);
v___x_5477_ = lean_nat_add(v___x_5378_, v_size_5475_);
if (v_isShared_5474_ == 0)
{
lean_ctor_set(v___x_5473_, 4, v_l_5467_);
lean_ctor_set(v___x_5473_, 3, v_impl_5377_);
lean_ctor_set(v___x_5473_, 2, v_v_5370_);
lean_ctor_set(v___x_5473_, 1, v_k_5369_);
lean_ctor_set(v___x_5473_, 0, v___x_5477_);
v___x_5479_ = v___x_5473_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5477_);
lean_ctor_set(v_reuseFailAlloc_5483_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5483_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5483_, 3, v_impl_5377_);
lean_ctor_set(v_reuseFailAlloc_5483_, 4, v_l_5467_);
v___x_5479_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
lean_object* v___x_5481_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v_r_5468_);
lean_ctor_set(v___x_5374_, 3, v___x_5479_);
lean_ctor_set(v___x_5374_, 2, v_v_5471_);
lean_ctor_set(v___x_5374_, 1, v_k_5470_);
lean_ctor_set(v___x_5374_, 0, v___x_5476_);
v___x_5481_ = v___x_5374_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5482_, 1, v_k_5470_);
lean_ctor_set(v_reuseFailAlloc_5482_, 2, v_v_5471_);
lean_ctor_set(v_reuseFailAlloc_5482_, 3, v___x_5479_);
lean_ctor_set(v_reuseFailAlloc_5482_, 4, v_r_5468_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
}
else
{
lean_object* v_k_5487_; lean_object* v_v_5488_; lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5511_; 
v_k_5487_ = lean_ctor_get(v_r_5372_, 1);
v_v_5488_ = lean_ctor_get(v_r_5372_, 2);
v_isSharedCheck_5511_ = !lean_is_exclusive(v_r_5372_);
if (v_isSharedCheck_5511_ == 0)
{
lean_object* v_unused_5512_; lean_object* v_unused_5513_; lean_object* v_unused_5514_; 
v_unused_5512_ = lean_ctor_get(v_r_5372_, 4);
lean_dec(v_unused_5512_);
v_unused_5513_ = lean_ctor_get(v_r_5372_, 3);
lean_dec(v_unused_5513_);
v_unused_5514_ = lean_ctor_get(v_r_5372_, 0);
lean_dec(v_unused_5514_);
v___x_5490_ = v_r_5372_;
v_isShared_5491_ = v_isSharedCheck_5511_;
goto v_resetjp_5489_;
}
else
{
lean_inc(v_v_5488_);
lean_inc(v_k_5487_);
lean_dec(v_r_5372_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5511_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v_k_5492_; lean_object* v_v_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5507_; 
v_k_5492_ = lean_ctor_get(v_l_5467_, 1);
v_v_5493_ = lean_ctor_get(v_l_5467_, 2);
v_isSharedCheck_5507_ = !lean_is_exclusive(v_l_5467_);
if (v_isSharedCheck_5507_ == 0)
{
lean_object* v_unused_5508_; lean_object* v_unused_5509_; lean_object* v_unused_5510_; 
v_unused_5508_ = lean_ctor_get(v_l_5467_, 4);
lean_dec(v_unused_5508_);
v_unused_5509_ = lean_ctor_get(v_l_5467_, 3);
lean_dec(v_unused_5509_);
v_unused_5510_ = lean_ctor_get(v_l_5467_, 0);
lean_dec(v_unused_5510_);
v___x_5495_ = v_l_5467_;
v_isShared_5496_ = v_isSharedCheck_5507_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_v_5493_);
lean_inc(v_k_5492_);
lean_dec(v_l_5467_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5507_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5497_; lean_object* v___x_5499_; 
v___x_5497_ = lean_unsigned_to_nat(3u);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 4, v_r_5468_);
lean_ctor_set(v___x_5495_, 3, v_r_5468_);
lean_ctor_set(v___x_5495_, 2, v_v_5370_);
lean_ctor_set(v___x_5495_, 1, v_k_5369_);
lean_ctor_set(v___x_5495_, 0, v___x_5378_);
v___x_5499_ = v___x_5495_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5378_);
lean_ctor_set(v_reuseFailAlloc_5506_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5506_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5506_, 3, v_r_5468_);
lean_ctor_set(v_reuseFailAlloc_5506_, 4, v_r_5468_);
v___x_5499_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
lean_object* v___x_5501_; 
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 3, v_r_5468_);
lean_ctor_set(v___x_5490_, 0, v___x_5378_);
v___x_5501_ = v___x_5490_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5378_);
lean_ctor_set(v_reuseFailAlloc_5505_, 1, v_k_5487_);
lean_ctor_set(v_reuseFailAlloc_5505_, 2, v_v_5488_);
lean_ctor_set(v_reuseFailAlloc_5505_, 3, v_r_5468_);
lean_ctor_set(v_reuseFailAlloc_5505_, 4, v_r_5468_);
v___x_5501_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
lean_object* v___x_5503_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v___x_5501_);
lean_ctor_set(v___x_5374_, 3, v___x_5499_);
lean_ctor_set(v___x_5374_, 2, v_v_5493_);
lean_ctor_set(v___x_5374_, 1, v_k_5492_);
lean_ctor_set(v___x_5374_, 0, v___x_5497_);
v___x_5503_ = v___x_5374_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5497_);
lean_ctor_set(v_reuseFailAlloc_5504_, 1, v_k_5492_);
lean_ctor_set(v_reuseFailAlloc_5504_, 2, v_v_5493_);
lean_ctor_set(v_reuseFailAlloc_5504_, 3, v___x_5499_);
lean_ctor_set(v_reuseFailAlloc_5504_, 4, v___x_5501_);
v___x_5503_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
return v___x_5503_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_5515_; 
v_r_5515_ = lean_ctor_get(v_r_5372_, 4);
lean_inc(v_r_5515_);
if (lean_obj_tag(v_r_5515_) == 0)
{
lean_object* v_k_5516_; lean_object* v_v_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5528_; 
v_k_5516_ = lean_ctor_get(v_r_5372_, 1);
v_v_5517_ = lean_ctor_get(v_r_5372_, 2);
v_isSharedCheck_5528_ = !lean_is_exclusive(v_r_5372_);
if (v_isSharedCheck_5528_ == 0)
{
lean_object* v_unused_5529_; lean_object* v_unused_5530_; lean_object* v_unused_5531_; 
v_unused_5529_ = lean_ctor_get(v_r_5372_, 4);
lean_dec(v_unused_5529_);
v_unused_5530_ = lean_ctor_get(v_r_5372_, 3);
lean_dec(v_unused_5530_);
v_unused_5531_ = lean_ctor_get(v_r_5372_, 0);
lean_dec(v_unused_5531_);
v___x_5519_ = v_r_5372_;
v_isShared_5520_ = v_isSharedCheck_5528_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_v_5517_);
lean_inc(v_k_5516_);
lean_dec(v_r_5372_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5528_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; lean_object* v___x_5523_; 
v___x_5521_ = lean_unsigned_to_nat(3u);
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 4, v_l_5467_);
lean_ctor_set(v___x_5519_, 2, v_v_5370_);
lean_ctor_set(v___x_5519_, 1, v_k_5369_);
lean_ctor_set(v___x_5519_, 0, v___x_5378_);
v___x_5523_ = v___x_5519_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v___x_5378_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5527_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5527_, 3, v_l_5467_);
lean_ctor_set(v_reuseFailAlloc_5527_, 4, v_l_5467_);
v___x_5523_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
lean_object* v___x_5525_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v_r_5515_);
lean_ctor_set(v___x_5374_, 3, v___x_5523_);
lean_ctor_set(v___x_5374_, 2, v_v_5517_);
lean_ctor_set(v___x_5374_, 1, v_k_5516_);
lean_ctor_set(v___x_5374_, 0, v___x_5521_);
v___x_5525_ = v___x_5374_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v___x_5521_);
lean_ctor_set(v_reuseFailAlloc_5526_, 1, v_k_5516_);
lean_ctor_set(v_reuseFailAlloc_5526_, 2, v_v_5517_);
lean_ctor_set(v_reuseFailAlloc_5526_, 3, v___x_5523_);
lean_ctor_set(v_reuseFailAlloc_5526_, 4, v_r_5515_);
v___x_5525_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
return v___x_5525_;
}
}
}
}
else
{
lean_object* v_size_5532_; lean_object* v_k_5533_; lean_object* v_v_5534_; lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5545_; 
v_size_5532_ = lean_ctor_get(v_r_5372_, 0);
v_k_5533_ = lean_ctor_get(v_r_5372_, 1);
v_v_5534_ = lean_ctor_get(v_r_5372_, 2);
v_isSharedCheck_5545_ = !lean_is_exclusive(v_r_5372_);
if (v_isSharedCheck_5545_ == 0)
{
lean_object* v_unused_5546_; lean_object* v_unused_5547_; 
v_unused_5546_ = lean_ctor_get(v_r_5372_, 4);
lean_dec(v_unused_5546_);
v_unused_5547_ = lean_ctor_get(v_r_5372_, 3);
lean_dec(v_unused_5547_);
v___x_5536_ = v_r_5372_;
v_isShared_5537_ = v_isSharedCheck_5545_;
goto v_resetjp_5535_;
}
else
{
lean_inc(v_v_5534_);
lean_inc(v_k_5533_);
lean_inc(v_size_5532_);
lean_dec(v_r_5372_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5545_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5539_; 
if (v_isShared_5537_ == 0)
{
lean_ctor_set(v___x_5536_, 3, v_r_5515_);
v___x_5539_ = v___x_5536_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_size_5532_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v_k_5533_);
lean_ctor_set(v_reuseFailAlloc_5544_, 2, v_v_5534_);
lean_ctor_set(v_reuseFailAlloc_5544_, 3, v_r_5515_);
lean_ctor_set(v_reuseFailAlloc_5544_, 4, v_r_5515_);
v___x_5539_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
lean_object* v___x_5540_; lean_object* v___x_5542_; 
v___x_5540_ = lean_unsigned_to_nat(2u);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v___x_5539_);
lean_ctor_set(v___x_5374_, 3, v_r_5515_);
lean_ctor_set(v___x_5374_, 0, v___x_5540_);
v___x_5542_ = v___x_5374_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5540_);
lean_ctor_set(v_reuseFailAlloc_5543_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5543_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5543_, 3, v_r_5515_);
lean_ctor_set(v_reuseFailAlloc_5543_, 4, v___x_5539_);
v___x_5542_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
return v___x_5542_;
}
}
}
}
}
}
else
{
lean_object* v___x_5549_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 3, v_r_5372_);
lean_ctor_set(v___x_5374_, 0, v___x_5378_);
v___x_5549_ = v___x_5374_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v___x_5378_);
lean_ctor_set(v_reuseFailAlloc_5550_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5550_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5550_, 3, v_r_5372_);
lean_ctor_set(v_reuseFailAlloc_5550_, 4, v_r_5372_);
v___x_5549_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
return v___x_5549_;
}
}
}
}
case 1:
{
lean_del_object(v___x_5374_);
lean_dec(v_v_5370_);
lean_dec(v_k_5369_);
if (lean_obj_tag(v_l_5371_) == 0)
{
if (lean_obj_tag(v_r_5372_) == 0)
{
lean_object* v_size_5551_; lean_object* v_k_5552_; lean_object* v_v_5553_; lean_object* v_l_5554_; lean_object* v_r_5555_; lean_object* v_size_5556_; lean_object* v_k_5557_; lean_object* v_v_5558_; lean_object* v_l_5559_; lean_object* v_r_5560_; lean_object* v___x_5561_; uint8_t v___x_5562_; 
v_size_5551_ = lean_ctor_get(v_l_5371_, 0);
v_k_5552_ = lean_ctor_get(v_l_5371_, 1);
v_v_5553_ = lean_ctor_get(v_l_5371_, 2);
v_l_5554_ = lean_ctor_get(v_l_5371_, 3);
v_r_5555_ = lean_ctor_get(v_l_5371_, 4);
lean_inc(v_r_5555_);
v_size_5556_ = lean_ctor_get(v_r_5372_, 0);
v_k_5557_ = lean_ctor_get(v_r_5372_, 1);
v_v_5558_ = lean_ctor_get(v_r_5372_, 2);
v_l_5559_ = lean_ctor_get(v_r_5372_, 3);
lean_inc(v_l_5559_);
v_r_5560_ = lean_ctor_get(v_r_5372_, 4);
v___x_5561_ = lean_unsigned_to_nat(1u);
v___x_5562_ = lean_nat_dec_lt(v_size_5551_, v_size_5556_);
if (v___x_5562_ == 0)
{
lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5698_; 
lean_inc(v_l_5554_);
lean_inc(v_v_5553_);
lean_inc(v_k_5552_);
v_isSharedCheck_5698_ = !lean_is_exclusive(v_l_5371_);
if (v_isSharedCheck_5698_ == 0)
{
lean_object* v_unused_5699_; lean_object* v_unused_5700_; lean_object* v_unused_5701_; lean_object* v_unused_5702_; lean_object* v_unused_5703_; 
v_unused_5699_ = lean_ctor_get(v_l_5371_, 4);
lean_dec(v_unused_5699_);
v_unused_5700_ = lean_ctor_get(v_l_5371_, 3);
lean_dec(v_unused_5700_);
v_unused_5701_ = lean_ctor_get(v_l_5371_, 2);
lean_dec(v_unused_5701_);
v_unused_5702_ = lean_ctor_get(v_l_5371_, 1);
lean_dec(v_unused_5702_);
v_unused_5703_ = lean_ctor_get(v_l_5371_, 0);
lean_dec(v_unused_5703_);
v___x_5564_ = v_l_5371_;
v_isShared_5565_ = v_isSharedCheck_5698_;
goto v_resetjp_5563_;
}
else
{
lean_dec(v_l_5371_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5698_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5566_; lean_object* v_tree_5567_; 
v___x_5566_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5552_, v_v_5553_, v_l_5554_, v_r_5555_);
v_tree_5567_ = lean_ctor_get(v___x_5566_, 2);
if (lean_obj_tag(v_tree_5567_) == 0)
{
lean_object* v_k_5568_; lean_object* v_v_5569_; lean_object* v_size_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; uint8_t v___x_5573_; 
lean_inc_ref(v_tree_5567_);
v_k_5568_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_k_5568_);
v_v_5569_ = lean_ctor_get(v___x_5566_, 1);
lean_inc(v_v_5569_);
lean_dec_ref(v___x_5566_);
v_size_5570_ = lean_ctor_get(v_tree_5567_, 0);
v___x_5571_ = lean_unsigned_to_nat(3u);
v___x_5572_ = lean_nat_mul(v___x_5571_, v_size_5570_);
v___x_5573_ = lean_nat_dec_lt(v___x_5572_, v_size_5556_);
lean_dec(v___x_5572_);
if (v___x_5573_ == 0)
{
lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5577_; 
lean_dec(v_l_5559_);
v___x_5574_ = lean_nat_add(v___x_5561_, v_size_5570_);
v___x_5575_ = lean_nat_add(v___x_5574_, v_size_5556_);
lean_dec(v___x_5574_);
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 4, v_r_5372_);
lean_ctor_set(v___x_5564_, 3, v_tree_5567_);
lean_ctor_set(v___x_5564_, 2, v_v_5569_);
lean_ctor_set(v___x_5564_, 1, v_k_5568_);
lean_ctor_set(v___x_5564_, 0, v___x_5575_);
v___x_5577_ = v___x_5564_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5575_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v_k_5568_);
lean_ctor_set(v_reuseFailAlloc_5578_, 2, v_v_5569_);
lean_ctor_set(v_reuseFailAlloc_5578_, 3, v_tree_5567_);
lean_ctor_set(v_reuseFailAlloc_5578_, 4, v_r_5372_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
else
{
lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5633_; 
lean_inc(v_r_5560_);
lean_inc(v_v_5558_);
lean_inc(v_k_5557_);
lean_inc(v_size_5556_);
v_isSharedCheck_5633_ = !lean_is_exclusive(v_r_5372_);
if (v_isSharedCheck_5633_ == 0)
{
lean_object* v_unused_5634_; lean_object* v_unused_5635_; lean_object* v_unused_5636_; lean_object* v_unused_5637_; lean_object* v_unused_5638_; 
v_unused_5634_ = lean_ctor_get(v_r_5372_, 4);
lean_dec(v_unused_5634_);
v_unused_5635_ = lean_ctor_get(v_r_5372_, 3);
lean_dec(v_unused_5635_);
v_unused_5636_ = lean_ctor_get(v_r_5372_, 2);
lean_dec(v_unused_5636_);
v_unused_5637_ = lean_ctor_get(v_r_5372_, 1);
lean_dec(v_unused_5637_);
v_unused_5638_ = lean_ctor_get(v_r_5372_, 0);
lean_dec(v_unused_5638_);
v___x_5580_ = v_r_5372_;
v_isShared_5581_ = v_isSharedCheck_5633_;
goto v_resetjp_5579_;
}
else
{
lean_dec(v_r_5372_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5633_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v_size_5582_; lean_object* v_k_5583_; lean_object* v_v_5584_; lean_object* v_l_5585_; lean_object* v_r_5586_; lean_object* v_size_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; uint8_t v___x_5590_; 
v_size_5582_ = lean_ctor_get(v_l_5559_, 0);
v_k_5583_ = lean_ctor_get(v_l_5559_, 1);
v_v_5584_ = lean_ctor_get(v_l_5559_, 2);
v_l_5585_ = lean_ctor_get(v_l_5559_, 3);
v_r_5586_ = lean_ctor_get(v_l_5559_, 4);
v_size_5587_ = lean_ctor_get(v_r_5560_, 0);
v___x_5588_ = lean_unsigned_to_nat(2u);
v___x_5589_ = lean_nat_mul(v___x_5588_, v_size_5587_);
v___x_5590_ = lean_nat_dec_lt(v_size_5582_, v___x_5589_);
lean_dec(v___x_5589_);
if (v___x_5590_ == 0)
{
lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5618_; 
lean_inc(v_r_5586_);
lean_inc(v_l_5585_);
lean_inc(v_v_5584_);
lean_inc(v_k_5583_);
v_isSharedCheck_5618_ = !lean_is_exclusive(v_l_5559_);
if (v_isSharedCheck_5618_ == 0)
{
lean_object* v_unused_5619_; lean_object* v_unused_5620_; lean_object* v_unused_5621_; lean_object* v_unused_5622_; lean_object* v_unused_5623_; 
v_unused_5619_ = lean_ctor_get(v_l_5559_, 4);
lean_dec(v_unused_5619_);
v_unused_5620_ = lean_ctor_get(v_l_5559_, 3);
lean_dec(v_unused_5620_);
v_unused_5621_ = lean_ctor_get(v_l_5559_, 2);
lean_dec(v_unused_5621_);
v_unused_5622_ = lean_ctor_get(v_l_5559_, 1);
lean_dec(v_unused_5622_);
v_unused_5623_ = lean_ctor_get(v_l_5559_, 0);
lean_dec(v_unused_5623_);
v___x_5592_ = v_l_5559_;
v_isShared_5593_ = v_isSharedCheck_5618_;
goto v_resetjp_5591_;
}
else
{
lean_dec(v_l_5559_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5618_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___y_5597_; lean_object* v___y_5598_; lean_object* v___y_5599_; lean_object* v___y_5608_; 
v___x_5594_ = lean_nat_add(v___x_5561_, v_size_5570_);
v___x_5595_ = lean_nat_add(v___x_5594_, v_size_5556_);
lean_dec(v_size_5556_);
if (lean_obj_tag(v_l_5585_) == 0)
{
lean_object* v_size_5616_; 
v_size_5616_ = lean_ctor_get(v_l_5585_, 0);
lean_inc(v_size_5616_);
v___y_5608_ = v_size_5616_;
goto v___jp_5607_;
}
else
{
lean_object* v___x_5617_; 
v___x_5617_ = lean_unsigned_to_nat(0u);
v___y_5608_ = v___x_5617_;
goto v___jp_5607_;
}
v___jp_5596_:
{
lean_object* v___x_5600_; lean_object* v___x_5602_; 
v___x_5600_ = lean_nat_add(v___y_5598_, v___y_5599_);
lean_dec(v___y_5599_);
lean_dec(v___y_5598_);
if (v_isShared_5593_ == 0)
{
lean_ctor_set(v___x_5592_, 4, v_r_5560_);
lean_ctor_set(v___x_5592_, 3, v_r_5586_);
lean_ctor_set(v___x_5592_, 2, v_v_5558_);
lean_ctor_set(v___x_5592_, 1, v_k_5557_);
lean_ctor_set(v___x_5592_, 0, v___x_5600_);
v___x_5602_ = v___x_5592_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v___x_5600_);
lean_ctor_set(v_reuseFailAlloc_5606_, 1, v_k_5557_);
lean_ctor_set(v_reuseFailAlloc_5606_, 2, v_v_5558_);
lean_ctor_set(v_reuseFailAlloc_5606_, 3, v_r_5586_);
lean_ctor_set(v_reuseFailAlloc_5606_, 4, v_r_5560_);
v___x_5602_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
lean_object* v___x_5604_; 
if (v_isShared_5581_ == 0)
{
lean_ctor_set(v___x_5580_, 4, v___x_5602_);
lean_ctor_set(v___x_5580_, 3, v___y_5597_);
lean_ctor_set(v___x_5580_, 2, v_v_5584_);
lean_ctor_set(v___x_5580_, 1, v_k_5583_);
lean_ctor_set(v___x_5580_, 0, v___x_5595_);
v___x_5604_ = v___x_5580_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5595_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v_k_5583_);
lean_ctor_set(v_reuseFailAlloc_5605_, 2, v_v_5584_);
lean_ctor_set(v_reuseFailAlloc_5605_, 3, v___y_5597_);
lean_ctor_set(v_reuseFailAlloc_5605_, 4, v___x_5602_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
v___jp_5607_:
{
lean_object* v___x_5609_; lean_object* v___x_5611_; 
v___x_5609_ = lean_nat_add(v___x_5594_, v___y_5608_);
lean_dec(v___y_5608_);
lean_dec(v___x_5594_);
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 4, v_l_5585_);
lean_ctor_set(v___x_5564_, 3, v_tree_5567_);
lean_ctor_set(v___x_5564_, 2, v_v_5569_);
lean_ctor_set(v___x_5564_, 1, v_k_5568_);
lean_ctor_set(v___x_5564_, 0, v___x_5609_);
v___x_5611_ = v___x_5564_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v___x_5609_);
lean_ctor_set(v_reuseFailAlloc_5615_, 1, v_k_5568_);
lean_ctor_set(v_reuseFailAlloc_5615_, 2, v_v_5569_);
lean_ctor_set(v_reuseFailAlloc_5615_, 3, v_tree_5567_);
lean_ctor_set(v_reuseFailAlloc_5615_, 4, v_l_5585_);
v___x_5611_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
lean_object* v___x_5612_; 
v___x_5612_ = lean_nat_add(v___x_5561_, v_size_5587_);
if (lean_obj_tag(v_r_5586_) == 0)
{
lean_object* v_size_5613_; 
v_size_5613_ = lean_ctor_get(v_r_5586_, 0);
lean_inc(v_size_5613_);
v___y_5597_ = v___x_5611_;
v___y_5598_ = v___x_5612_;
v___y_5599_ = v_size_5613_;
goto v___jp_5596_;
}
else
{
lean_object* v___x_5614_; 
v___x_5614_ = lean_unsigned_to_nat(0u);
v___y_5597_ = v___x_5611_;
v___y_5598_ = v___x_5612_;
v___y_5599_ = v___x_5614_;
goto v___jp_5596_;
}
}
}
}
}
else
{
lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5628_; 
v___x_5624_ = lean_nat_add(v___x_5561_, v_size_5570_);
v___x_5625_ = lean_nat_add(v___x_5624_, v_size_5556_);
lean_dec(v_size_5556_);
v___x_5626_ = lean_nat_add(v___x_5624_, v_size_5582_);
lean_dec(v___x_5624_);
if (v_isShared_5581_ == 0)
{
lean_ctor_set(v___x_5580_, 4, v_l_5559_);
lean_ctor_set(v___x_5580_, 3, v_tree_5567_);
lean_ctor_set(v___x_5580_, 2, v_v_5569_);
lean_ctor_set(v___x_5580_, 1, v_k_5568_);
lean_ctor_set(v___x_5580_, 0, v___x_5626_);
v___x_5628_ = v___x_5580_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v___x_5626_);
lean_ctor_set(v_reuseFailAlloc_5632_, 1, v_k_5568_);
lean_ctor_set(v_reuseFailAlloc_5632_, 2, v_v_5569_);
lean_ctor_set(v_reuseFailAlloc_5632_, 3, v_tree_5567_);
lean_ctor_set(v_reuseFailAlloc_5632_, 4, v_l_5559_);
v___x_5628_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
lean_object* v___x_5630_; 
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 4, v_r_5560_);
lean_ctor_set(v___x_5564_, 3, v___x_5628_);
lean_ctor_set(v___x_5564_, 2, v_v_5558_);
lean_ctor_set(v___x_5564_, 1, v_k_5557_);
lean_ctor_set(v___x_5564_, 0, v___x_5625_);
v___x_5630_ = v___x_5564_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v___x_5625_);
lean_ctor_set(v_reuseFailAlloc_5631_, 1, v_k_5557_);
lean_ctor_set(v_reuseFailAlloc_5631_, 2, v_v_5558_);
lean_ctor_set(v_reuseFailAlloc_5631_, 3, v___x_5628_);
lean_ctor_set(v_reuseFailAlloc_5631_, 4, v_r_5560_);
v___x_5630_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
return v___x_5630_;
}
}
}
}
}
}
else
{
lean_object* v___x_5640_; uint8_t v_isShared_5641_; uint8_t v_isSharedCheck_5692_; 
lean_inc(v_r_5560_);
lean_inc(v_v_5558_);
lean_inc(v_k_5557_);
lean_inc(v_size_5556_);
v_isSharedCheck_5692_ = !lean_is_exclusive(v_r_5372_);
if (v_isSharedCheck_5692_ == 0)
{
lean_object* v_unused_5693_; lean_object* v_unused_5694_; lean_object* v_unused_5695_; lean_object* v_unused_5696_; lean_object* v_unused_5697_; 
v_unused_5693_ = lean_ctor_get(v_r_5372_, 4);
lean_dec(v_unused_5693_);
v_unused_5694_ = lean_ctor_get(v_r_5372_, 3);
lean_dec(v_unused_5694_);
v_unused_5695_ = lean_ctor_get(v_r_5372_, 2);
lean_dec(v_unused_5695_);
v_unused_5696_ = lean_ctor_get(v_r_5372_, 1);
lean_dec(v_unused_5696_);
v_unused_5697_ = lean_ctor_get(v_r_5372_, 0);
lean_dec(v_unused_5697_);
v___x_5640_ = v_r_5372_;
v_isShared_5641_ = v_isSharedCheck_5692_;
goto v_resetjp_5639_;
}
else
{
lean_dec(v_r_5372_);
v___x_5640_ = lean_box(0);
v_isShared_5641_ = v_isSharedCheck_5692_;
goto v_resetjp_5639_;
}
v_resetjp_5639_:
{
if (lean_obj_tag(v_l_5559_) == 0)
{
if (lean_obj_tag(v_r_5560_) == 0)
{
lean_object* v_k_5642_; lean_object* v_v_5643_; lean_object* v_size_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5648_; 
lean_inc(v_tree_5567_);
v_k_5642_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_k_5642_);
v_v_5643_ = lean_ctor_get(v___x_5566_, 1);
lean_inc(v_v_5643_);
lean_dec_ref(v___x_5566_);
v_size_5644_ = lean_ctor_get(v_l_5559_, 0);
v___x_5645_ = lean_nat_add(v___x_5561_, v_size_5556_);
lean_dec(v_size_5556_);
v___x_5646_ = lean_nat_add(v___x_5561_, v_size_5644_);
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 4, v_l_5559_);
lean_ctor_set(v___x_5640_, 3, v_tree_5567_);
lean_ctor_set(v___x_5640_, 2, v_v_5643_);
lean_ctor_set(v___x_5640_, 1, v_k_5642_);
lean_ctor_set(v___x_5640_, 0, v___x_5646_);
v___x_5648_ = v___x_5640_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v___x_5646_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_k_5642_);
lean_ctor_set(v_reuseFailAlloc_5652_, 2, v_v_5643_);
lean_ctor_set(v_reuseFailAlloc_5652_, 3, v_tree_5567_);
lean_ctor_set(v_reuseFailAlloc_5652_, 4, v_l_5559_);
v___x_5648_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
lean_object* v___x_5650_; 
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 4, v_r_5560_);
lean_ctor_set(v___x_5564_, 3, v___x_5648_);
lean_ctor_set(v___x_5564_, 2, v_v_5558_);
lean_ctor_set(v___x_5564_, 1, v_k_5557_);
lean_ctor_set(v___x_5564_, 0, v___x_5645_);
v___x_5650_ = v___x_5564_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5645_);
lean_ctor_set(v_reuseFailAlloc_5651_, 1, v_k_5557_);
lean_ctor_set(v_reuseFailAlloc_5651_, 2, v_v_5558_);
lean_ctor_set(v_reuseFailAlloc_5651_, 3, v___x_5648_);
lean_ctor_set(v_reuseFailAlloc_5651_, 4, v_r_5560_);
v___x_5650_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
return v___x_5650_;
}
}
}
else
{
lean_object* v_k_5653_; lean_object* v_v_5654_; lean_object* v_k_5655_; lean_object* v_v_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5670_; 
lean_dec(v_size_5556_);
v_k_5653_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_k_5653_);
v_v_5654_ = lean_ctor_get(v___x_5566_, 1);
lean_inc(v_v_5654_);
lean_dec_ref(v___x_5566_);
v_k_5655_ = lean_ctor_get(v_l_5559_, 1);
v_v_5656_ = lean_ctor_get(v_l_5559_, 2);
v_isSharedCheck_5670_ = !lean_is_exclusive(v_l_5559_);
if (v_isSharedCheck_5670_ == 0)
{
lean_object* v_unused_5671_; lean_object* v_unused_5672_; lean_object* v_unused_5673_; 
v_unused_5671_ = lean_ctor_get(v_l_5559_, 4);
lean_dec(v_unused_5671_);
v_unused_5672_ = lean_ctor_get(v_l_5559_, 3);
lean_dec(v_unused_5672_);
v_unused_5673_ = lean_ctor_get(v_l_5559_, 0);
lean_dec(v_unused_5673_);
v___x_5658_ = v_l_5559_;
v_isShared_5659_ = v_isSharedCheck_5670_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_v_5656_);
lean_inc(v_k_5655_);
lean_dec(v_l_5559_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5670_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___x_5660_; lean_object* v___x_5662_; 
v___x_5660_ = lean_unsigned_to_nat(3u);
if (v_isShared_5659_ == 0)
{
lean_ctor_set(v___x_5658_, 4, v_r_5560_);
lean_ctor_set(v___x_5658_, 3, v_r_5560_);
lean_ctor_set(v___x_5658_, 2, v_v_5654_);
lean_ctor_set(v___x_5658_, 1, v_k_5653_);
lean_ctor_set(v___x_5658_, 0, v___x_5561_);
v___x_5662_ = v___x_5658_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5669_, 1, v_k_5653_);
lean_ctor_set(v_reuseFailAlloc_5669_, 2, v_v_5654_);
lean_ctor_set(v_reuseFailAlloc_5669_, 3, v_r_5560_);
lean_ctor_set(v_reuseFailAlloc_5669_, 4, v_r_5560_);
v___x_5662_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
lean_object* v___x_5664_; 
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 3, v_r_5560_);
lean_ctor_set(v___x_5640_, 0, v___x_5561_);
v___x_5664_ = v___x_5640_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5668_, 1, v_k_5557_);
lean_ctor_set(v_reuseFailAlloc_5668_, 2, v_v_5558_);
lean_ctor_set(v_reuseFailAlloc_5668_, 3, v_r_5560_);
lean_ctor_set(v_reuseFailAlloc_5668_, 4, v_r_5560_);
v___x_5664_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
lean_object* v___x_5666_; 
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 4, v___x_5664_);
lean_ctor_set(v___x_5564_, 3, v___x_5662_);
lean_ctor_set(v___x_5564_, 2, v_v_5656_);
lean_ctor_set(v___x_5564_, 1, v_k_5655_);
lean_ctor_set(v___x_5564_, 0, v___x_5660_);
v___x_5666_ = v___x_5564_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v___x_5660_);
lean_ctor_set(v_reuseFailAlloc_5667_, 1, v_k_5655_);
lean_ctor_set(v_reuseFailAlloc_5667_, 2, v_v_5656_);
lean_ctor_set(v_reuseFailAlloc_5667_, 3, v___x_5662_);
lean_ctor_set(v_reuseFailAlloc_5667_, 4, v___x_5664_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5560_) == 0)
{
lean_object* v_k_5674_; lean_object* v_v_5675_; lean_object* v___x_5676_; lean_object* v___x_5678_; 
lean_dec(v_size_5556_);
v_k_5674_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_k_5674_);
v_v_5675_ = lean_ctor_get(v___x_5566_, 1);
lean_inc(v_v_5675_);
lean_dec_ref(v___x_5566_);
v___x_5676_ = lean_unsigned_to_nat(3u);
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 4, v_l_5559_);
lean_ctor_set(v___x_5640_, 2, v_v_5675_);
lean_ctor_set(v___x_5640_, 1, v_k_5674_);
lean_ctor_set(v___x_5640_, 0, v___x_5561_);
v___x_5678_ = v___x_5640_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5682_, 1, v_k_5674_);
lean_ctor_set(v_reuseFailAlloc_5682_, 2, v_v_5675_);
lean_ctor_set(v_reuseFailAlloc_5682_, 3, v_l_5559_);
lean_ctor_set(v_reuseFailAlloc_5682_, 4, v_l_5559_);
v___x_5678_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
lean_object* v___x_5680_; 
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 4, v_r_5560_);
lean_ctor_set(v___x_5564_, 3, v___x_5678_);
lean_ctor_set(v___x_5564_, 2, v_v_5558_);
lean_ctor_set(v___x_5564_, 1, v_k_5557_);
lean_ctor_set(v___x_5564_, 0, v___x_5676_);
v___x_5680_ = v___x_5564_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v___x_5676_);
lean_ctor_set(v_reuseFailAlloc_5681_, 1, v_k_5557_);
lean_ctor_set(v_reuseFailAlloc_5681_, 2, v_v_5558_);
lean_ctor_set(v_reuseFailAlloc_5681_, 3, v___x_5678_);
lean_ctor_set(v_reuseFailAlloc_5681_, 4, v_r_5560_);
v___x_5680_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
return v___x_5680_;
}
}
}
else
{
lean_object* v_k_5683_; lean_object* v_v_5684_; lean_object* v___x_5686_; 
v_k_5683_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_k_5683_);
v_v_5684_ = lean_ctor_get(v___x_5566_, 1);
lean_inc(v_v_5684_);
lean_dec_ref(v___x_5566_);
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 3, v_r_5560_);
v___x_5686_ = v___x_5640_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_size_5556_);
lean_ctor_set(v_reuseFailAlloc_5691_, 1, v_k_5557_);
lean_ctor_set(v_reuseFailAlloc_5691_, 2, v_v_5558_);
lean_ctor_set(v_reuseFailAlloc_5691_, 3, v_r_5560_);
lean_ctor_set(v_reuseFailAlloc_5691_, 4, v_r_5560_);
v___x_5686_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
lean_object* v___x_5687_; lean_object* v___x_5689_; 
v___x_5687_ = lean_unsigned_to_nat(2u);
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 4, v___x_5686_);
lean_ctor_set(v___x_5564_, 3, v_r_5560_);
lean_ctor_set(v___x_5564_, 2, v_v_5684_);
lean_ctor_set(v___x_5564_, 1, v_k_5683_);
lean_ctor_set(v___x_5564_, 0, v___x_5687_);
v___x_5689_ = v___x_5564_;
goto v_reusejp_5688_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v___x_5687_);
lean_ctor_set(v_reuseFailAlloc_5690_, 1, v_k_5683_);
lean_ctor_set(v_reuseFailAlloc_5690_, 2, v_v_5684_);
lean_ctor_set(v_reuseFailAlloc_5690_, 3, v_r_5560_);
lean_ctor_set(v_reuseFailAlloc_5690_, 4, v___x_5686_);
v___x_5689_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5688_;
}
v_reusejp_5688_:
{
return v___x_5689_;
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
lean_object* v___x_5705_; uint8_t v_isShared_5706_; uint8_t v_isSharedCheck_5856_; 
lean_inc(v_r_5560_);
lean_inc(v_v_5558_);
lean_inc(v_k_5557_);
v_isSharedCheck_5856_ = !lean_is_exclusive(v_r_5372_);
if (v_isSharedCheck_5856_ == 0)
{
lean_object* v_unused_5857_; lean_object* v_unused_5858_; lean_object* v_unused_5859_; lean_object* v_unused_5860_; lean_object* v_unused_5861_; 
v_unused_5857_ = lean_ctor_get(v_r_5372_, 4);
lean_dec(v_unused_5857_);
v_unused_5858_ = lean_ctor_get(v_r_5372_, 3);
lean_dec(v_unused_5858_);
v_unused_5859_ = lean_ctor_get(v_r_5372_, 2);
lean_dec(v_unused_5859_);
v_unused_5860_ = lean_ctor_get(v_r_5372_, 1);
lean_dec(v_unused_5860_);
v_unused_5861_ = lean_ctor_get(v_r_5372_, 0);
lean_dec(v_unused_5861_);
v___x_5705_ = v_r_5372_;
v_isShared_5706_ = v_isSharedCheck_5856_;
goto v_resetjp_5704_;
}
else
{
lean_dec(v_r_5372_);
v___x_5705_ = lean_box(0);
v_isShared_5706_ = v_isSharedCheck_5856_;
goto v_resetjp_5704_;
}
v_resetjp_5704_:
{
lean_object* v___x_5707_; lean_object* v_tree_5708_; 
v___x_5707_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5557_, v_v_5558_, v_l_5559_, v_r_5560_);
v_tree_5708_ = lean_ctor_get(v___x_5707_, 2);
lean_inc(v_tree_5708_);
if (lean_obj_tag(v_tree_5708_) == 0)
{
lean_object* v_k_5709_; lean_object* v_v_5710_; lean_object* v_size_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; uint8_t v___x_5714_; 
v_k_5709_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_k_5709_);
v_v_5710_ = lean_ctor_get(v___x_5707_, 1);
lean_inc(v_v_5710_);
lean_dec_ref(v___x_5707_);
v_size_5711_ = lean_ctor_get(v_tree_5708_, 0);
v___x_5712_ = lean_unsigned_to_nat(3u);
v___x_5713_ = lean_nat_mul(v___x_5712_, v_size_5711_);
v___x_5714_ = lean_nat_dec_lt(v___x_5713_, v_size_5551_);
lean_dec(v___x_5713_);
if (v___x_5714_ == 0)
{
lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5718_; 
lean_dec(v_r_5555_);
v___x_5715_ = lean_nat_add(v___x_5561_, v_size_5551_);
v___x_5716_ = lean_nat_add(v___x_5715_, v_size_5711_);
lean_dec(v___x_5715_);
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 4, v_tree_5708_);
lean_ctor_set(v___x_5705_, 3, v_l_5371_);
lean_ctor_set(v___x_5705_, 2, v_v_5710_);
lean_ctor_set(v___x_5705_, 1, v_k_5709_);
lean_ctor_set(v___x_5705_, 0, v___x_5716_);
v___x_5718_ = v___x_5705_;
goto v_reusejp_5717_;
}
else
{
lean_object* v_reuseFailAlloc_5719_; 
v_reuseFailAlloc_5719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5719_, 0, v___x_5716_);
lean_ctor_set(v_reuseFailAlloc_5719_, 1, v_k_5709_);
lean_ctor_set(v_reuseFailAlloc_5719_, 2, v_v_5710_);
lean_ctor_set(v_reuseFailAlloc_5719_, 3, v_l_5371_);
lean_ctor_set(v_reuseFailAlloc_5719_, 4, v_tree_5708_);
v___x_5718_ = v_reuseFailAlloc_5719_;
goto v_reusejp_5717_;
}
v_reusejp_5717_:
{
return v___x_5718_;
}
}
else
{
lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5785_; 
lean_inc(v_l_5554_);
lean_inc(v_v_5553_);
lean_inc(v_k_5552_);
lean_inc(v_size_5551_);
v_isSharedCheck_5785_ = !lean_is_exclusive(v_l_5371_);
if (v_isSharedCheck_5785_ == 0)
{
lean_object* v_unused_5786_; lean_object* v_unused_5787_; lean_object* v_unused_5788_; lean_object* v_unused_5789_; lean_object* v_unused_5790_; 
v_unused_5786_ = lean_ctor_get(v_l_5371_, 4);
lean_dec(v_unused_5786_);
v_unused_5787_ = lean_ctor_get(v_l_5371_, 3);
lean_dec(v_unused_5787_);
v_unused_5788_ = lean_ctor_get(v_l_5371_, 2);
lean_dec(v_unused_5788_);
v_unused_5789_ = lean_ctor_get(v_l_5371_, 1);
lean_dec(v_unused_5789_);
v_unused_5790_ = lean_ctor_get(v_l_5371_, 0);
lean_dec(v_unused_5790_);
v___x_5721_ = v_l_5371_;
v_isShared_5722_ = v_isSharedCheck_5785_;
goto v_resetjp_5720_;
}
else
{
lean_dec(v_l_5371_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5785_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
lean_object* v_size_5723_; lean_object* v_size_5724_; lean_object* v_k_5725_; lean_object* v_v_5726_; lean_object* v_l_5727_; lean_object* v_r_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; uint8_t v___x_5731_; 
v_size_5723_ = lean_ctor_get(v_l_5554_, 0);
v_size_5724_ = lean_ctor_get(v_r_5555_, 0);
v_k_5725_ = lean_ctor_get(v_r_5555_, 1);
v_v_5726_ = lean_ctor_get(v_r_5555_, 2);
v_l_5727_ = lean_ctor_get(v_r_5555_, 3);
v_r_5728_ = lean_ctor_get(v_r_5555_, 4);
v___x_5729_ = lean_unsigned_to_nat(2u);
v___x_5730_ = lean_nat_mul(v___x_5729_, v_size_5723_);
v___x_5731_ = lean_nat_dec_lt(v_size_5724_, v___x_5730_);
lean_dec(v___x_5730_);
if (v___x_5731_ == 0)
{
lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5769_; 
lean_inc(v_r_5728_);
lean_inc(v_l_5727_);
lean_inc(v_v_5726_);
lean_inc(v_k_5725_);
lean_del_object(v___x_5721_);
v_isSharedCheck_5769_ = !lean_is_exclusive(v_r_5555_);
if (v_isSharedCheck_5769_ == 0)
{
lean_object* v_unused_5770_; lean_object* v_unused_5771_; lean_object* v_unused_5772_; lean_object* v_unused_5773_; lean_object* v_unused_5774_; 
v_unused_5770_ = lean_ctor_get(v_r_5555_, 4);
lean_dec(v_unused_5770_);
v_unused_5771_ = lean_ctor_get(v_r_5555_, 3);
lean_dec(v_unused_5771_);
v_unused_5772_ = lean_ctor_get(v_r_5555_, 2);
lean_dec(v_unused_5772_);
v_unused_5773_ = lean_ctor_get(v_r_5555_, 1);
lean_dec(v_unused_5773_);
v_unused_5774_ = lean_ctor_get(v_r_5555_, 0);
lean_dec(v_unused_5774_);
v___x_5733_ = v_r_5555_;
v_isShared_5734_ = v_isSharedCheck_5769_;
goto v_resetjp_5732_;
}
else
{
lean_dec(v_r_5555_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5769_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v___y_5740_; lean_object* v___x_5757_; lean_object* v___y_5759_; 
v___x_5735_ = lean_nat_add(v___x_5561_, v_size_5551_);
lean_dec(v_size_5551_);
v___x_5736_ = lean_nat_add(v___x_5735_, v_size_5711_);
lean_dec(v___x_5735_);
v___x_5757_ = lean_nat_add(v___x_5561_, v_size_5723_);
if (lean_obj_tag(v_l_5727_) == 0)
{
lean_object* v_size_5767_; 
v_size_5767_ = lean_ctor_get(v_l_5727_, 0);
lean_inc(v_size_5767_);
v___y_5759_ = v_size_5767_;
goto v___jp_5758_;
}
else
{
lean_object* v___x_5768_; 
v___x_5768_ = lean_unsigned_to_nat(0u);
v___y_5759_ = v___x_5768_;
goto v___jp_5758_;
}
v___jp_5737_:
{
lean_object* v___x_5741_; lean_object* v___x_5743_; 
v___x_5741_ = lean_nat_add(v___y_5739_, v___y_5740_);
lean_dec(v___y_5740_);
lean_dec(v___y_5739_);
lean_inc_ref(v_tree_5708_);
if (v_isShared_5734_ == 0)
{
lean_ctor_set(v___x_5733_, 4, v_tree_5708_);
lean_ctor_set(v___x_5733_, 3, v_r_5728_);
lean_ctor_set(v___x_5733_, 2, v_v_5710_);
lean_ctor_set(v___x_5733_, 1, v_k_5709_);
lean_ctor_set(v___x_5733_, 0, v___x_5741_);
v___x_5743_ = v___x_5733_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v___x_5741_);
lean_ctor_set(v_reuseFailAlloc_5756_, 1, v_k_5709_);
lean_ctor_set(v_reuseFailAlloc_5756_, 2, v_v_5710_);
lean_ctor_set(v_reuseFailAlloc_5756_, 3, v_r_5728_);
lean_ctor_set(v_reuseFailAlloc_5756_, 4, v_tree_5708_);
v___x_5743_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
lean_object* v___x_5745_; uint8_t v_isShared_5746_; uint8_t v_isSharedCheck_5750_; 
v_isSharedCheck_5750_ = !lean_is_exclusive(v_tree_5708_);
if (v_isSharedCheck_5750_ == 0)
{
lean_object* v_unused_5751_; lean_object* v_unused_5752_; lean_object* v_unused_5753_; lean_object* v_unused_5754_; lean_object* v_unused_5755_; 
v_unused_5751_ = lean_ctor_get(v_tree_5708_, 4);
lean_dec(v_unused_5751_);
v_unused_5752_ = lean_ctor_get(v_tree_5708_, 3);
lean_dec(v_unused_5752_);
v_unused_5753_ = lean_ctor_get(v_tree_5708_, 2);
lean_dec(v_unused_5753_);
v_unused_5754_ = lean_ctor_get(v_tree_5708_, 1);
lean_dec(v_unused_5754_);
v_unused_5755_ = lean_ctor_get(v_tree_5708_, 0);
lean_dec(v_unused_5755_);
v___x_5745_ = v_tree_5708_;
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
else
{
lean_dec(v_tree_5708_);
v___x_5745_ = lean_box(0);
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
v_resetjp_5744_:
{
lean_object* v___x_5748_; 
if (v_isShared_5746_ == 0)
{
lean_ctor_set(v___x_5745_, 4, v___x_5743_);
lean_ctor_set(v___x_5745_, 3, v___y_5738_);
lean_ctor_set(v___x_5745_, 2, v_v_5726_);
lean_ctor_set(v___x_5745_, 1, v_k_5725_);
lean_ctor_set(v___x_5745_, 0, v___x_5736_);
v___x_5748_ = v___x_5745_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v___x_5736_);
lean_ctor_set(v_reuseFailAlloc_5749_, 1, v_k_5725_);
lean_ctor_set(v_reuseFailAlloc_5749_, 2, v_v_5726_);
lean_ctor_set(v_reuseFailAlloc_5749_, 3, v___y_5738_);
lean_ctor_set(v_reuseFailAlloc_5749_, 4, v___x_5743_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
return v___x_5748_;
}
}
}
}
v___jp_5758_:
{
lean_object* v___x_5760_; lean_object* v___x_5762_; 
v___x_5760_ = lean_nat_add(v___x_5757_, v___y_5759_);
lean_dec(v___y_5759_);
lean_dec(v___x_5757_);
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 4, v_l_5727_);
lean_ctor_set(v___x_5705_, 3, v_l_5554_);
lean_ctor_set(v___x_5705_, 2, v_v_5553_);
lean_ctor_set(v___x_5705_, 1, v_k_5552_);
lean_ctor_set(v___x_5705_, 0, v___x_5760_);
v___x_5762_ = v___x_5705_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5766_; 
v_reuseFailAlloc_5766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5766_, 0, v___x_5760_);
lean_ctor_set(v_reuseFailAlloc_5766_, 1, v_k_5552_);
lean_ctor_set(v_reuseFailAlloc_5766_, 2, v_v_5553_);
lean_ctor_set(v_reuseFailAlloc_5766_, 3, v_l_5554_);
lean_ctor_set(v_reuseFailAlloc_5766_, 4, v_l_5727_);
v___x_5762_ = v_reuseFailAlloc_5766_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
lean_object* v___x_5763_; 
v___x_5763_ = lean_nat_add(v___x_5561_, v_size_5711_);
if (lean_obj_tag(v_r_5728_) == 0)
{
lean_object* v_size_5764_; 
v_size_5764_ = lean_ctor_get(v_r_5728_, 0);
lean_inc(v_size_5764_);
v___y_5738_ = v___x_5762_;
v___y_5739_ = v___x_5763_;
v___y_5740_ = v_size_5764_;
goto v___jp_5737_;
}
else
{
lean_object* v___x_5765_; 
v___x_5765_ = lean_unsigned_to_nat(0u);
v___y_5738_ = v___x_5762_;
v___y_5739_ = v___x_5763_;
v___y_5740_ = v___x_5765_;
goto v___jp_5737_;
}
}
}
}
}
else
{
lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5780_; 
v___x_5775_ = lean_nat_add(v___x_5561_, v_size_5551_);
lean_dec(v_size_5551_);
v___x_5776_ = lean_nat_add(v___x_5775_, v_size_5711_);
lean_dec(v___x_5775_);
v___x_5777_ = lean_nat_add(v___x_5561_, v_size_5711_);
v___x_5778_ = lean_nat_add(v___x_5777_, v_size_5724_);
lean_dec(v___x_5777_);
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 4, v_tree_5708_);
lean_ctor_set(v___x_5705_, 3, v_r_5555_);
lean_ctor_set(v___x_5705_, 2, v_v_5710_);
lean_ctor_set(v___x_5705_, 1, v_k_5709_);
lean_ctor_set(v___x_5705_, 0, v___x_5778_);
v___x_5780_ = v___x_5705_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5778_);
lean_ctor_set(v_reuseFailAlloc_5784_, 1, v_k_5709_);
lean_ctor_set(v_reuseFailAlloc_5784_, 2, v_v_5710_);
lean_ctor_set(v_reuseFailAlloc_5784_, 3, v_r_5555_);
lean_ctor_set(v_reuseFailAlloc_5784_, 4, v_tree_5708_);
v___x_5780_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
lean_object* v___x_5782_; 
if (v_isShared_5722_ == 0)
{
lean_ctor_set(v___x_5721_, 4, v___x_5780_);
lean_ctor_set(v___x_5721_, 0, v___x_5776_);
v___x_5782_ = v___x_5721_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v___x_5776_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v_k_5552_);
lean_ctor_set(v_reuseFailAlloc_5783_, 2, v_v_5553_);
lean_ctor_set(v_reuseFailAlloc_5783_, 3, v_l_5554_);
lean_ctor_set(v_reuseFailAlloc_5783_, 4, v___x_5780_);
v___x_5782_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
return v___x_5782_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_5554_) == 0)
{
lean_object* v___x_5792_; uint8_t v_isShared_5793_; uint8_t v_isSharedCheck_5814_; 
lean_inc_ref(v_l_5554_);
lean_inc(v_v_5553_);
lean_inc(v_k_5552_);
lean_inc(v_size_5551_);
v_isSharedCheck_5814_ = !lean_is_exclusive(v_l_5371_);
if (v_isSharedCheck_5814_ == 0)
{
lean_object* v_unused_5815_; lean_object* v_unused_5816_; lean_object* v_unused_5817_; lean_object* v_unused_5818_; lean_object* v_unused_5819_; 
v_unused_5815_ = lean_ctor_get(v_l_5371_, 4);
lean_dec(v_unused_5815_);
v_unused_5816_ = lean_ctor_get(v_l_5371_, 3);
lean_dec(v_unused_5816_);
v_unused_5817_ = lean_ctor_get(v_l_5371_, 2);
lean_dec(v_unused_5817_);
v_unused_5818_ = lean_ctor_get(v_l_5371_, 1);
lean_dec(v_unused_5818_);
v_unused_5819_ = lean_ctor_get(v_l_5371_, 0);
lean_dec(v_unused_5819_);
v___x_5792_ = v_l_5371_;
v_isShared_5793_ = v_isSharedCheck_5814_;
goto v_resetjp_5791_;
}
else
{
lean_dec(v_l_5371_);
v___x_5792_ = lean_box(0);
v_isShared_5793_ = v_isSharedCheck_5814_;
goto v_resetjp_5791_;
}
v_resetjp_5791_:
{
if (lean_obj_tag(v_r_5555_) == 0)
{
lean_object* v_k_5794_; lean_object* v_v_5795_; lean_object* v_size_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5800_; 
v_k_5794_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_k_5794_);
v_v_5795_ = lean_ctor_get(v___x_5707_, 1);
lean_inc(v_v_5795_);
lean_dec_ref(v___x_5707_);
v_size_5796_ = lean_ctor_get(v_r_5555_, 0);
v___x_5797_ = lean_nat_add(v___x_5561_, v_size_5551_);
lean_dec(v_size_5551_);
v___x_5798_ = lean_nat_add(v___x_5561_, v_size_5796_);
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 4, v_tree_5708_);
lean_ctor_set(v___x_5705_, 3, v_r_5555_);
lean_ctor_set(v___x_5705_, 2, v_v_5795_);
lean_ctor_set(v___x_5705_, 1, v_k_5794_);
lean_ctor_set(v___x_5705_, 0, v___x_5798_);
v___x_5800_ = v___x_5705_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5804_; 
v_reuseFailAlloc_5804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5804_, 0, v___x_5798_);
lean_ctor_set(v_reuseFailAlloc_5804_, 1, v_k_5794_);
lean_ctor_set(v_reuseFailAlloc_5804_, 2, v_v_5795_);
lean_ctor_set(v_reuseFailAlloc_5804_, 3, v_r_5555_);
lean_ctor_set(v_reuseFailAlloc_5804_, 4, v_tree_5708_);
v___x_5800_ = v_reuseFailAlloc_5804_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
lean_object* v___x_5802_; 
if (v_isShared_5793_ == 0)
{
lean_ctor_set(v___x_5792_, 4, v___x_5800_);
lean_ctor_set(v___x_5792_, 0, v___x_5797_);
v___x_5802_ = v___x_5792_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5797_);
lean_ctor_set(v_reuseFailAlloc_5803_, 1, v_k_5552_);
lean_ctor_set(v_reuseFailAlloc_5803_, 2, v_v_5553_);
lean_ctor_set(v_reuseFailAlloc_5803_, 3, v_l_5554_);
lean_ctor_set(v_reuseFailAlloc_5803_, 4, v___x_5800_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
else
{
lean_object* v_k_5805_; lean_object* v_v_5806_; lean_object* v___x_5807_; lean_object* v___x_5809_; 
lean_dec(v_size_5551_);
v_k_5805_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_k_5805_);
v_v_5806_ = lean_ctor_get(v___x_5707_, 1);
lean_inc(v_v_5806_);
lean_dec_ref(v___x_5707_);
v___x_5807_ = lean_unsigned_to_nat(3u);
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 4, v_r_5555_);
lean_ctor_set(v___x_5705_, 3, v_r_5555_);
lean_ctor_set(v___x_5705_, 2, v_v_5806_);
lean_ctor_set(v___x_5705_, 1, v_k_5805_);
lean_ctor_set(v___x_5705_, 0, v___x_5561_);
v___x_5809_ = v___x_5705_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5813_, 1, v_k_5805_);
lean_ctor_set(v_reuseFailAlloc_5813_, 2, v_v_5806_);
lean_ctor_set(v_reuseFailAlloc_5813_, 3, v_r_5555_);
lean_ctor_set(v_reuseFailAlloc_5813_, 4, v_r_5555_);
v___x_5809_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
lean_object* v___x_5811_; 
if (v_isShared_5793_ == 0)
{
lean_ctor_set(v___x_5792_, 4, v___x_5809_);
lean_ctor_set(v___x_5792_, 0, v___x_5807_);
v___x_5811_ = v___x_5792_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v___x_5807_);
lean_ctor_set(v_reuseFailAlloc_5812_, 1, v_k_5552_);
lean_ctor_set(v_reuseFailAlloc_5812_, 2, v_v_5553_);
lean_ctor_set(v_reuseFailAlloc_5812_, 3, v_l_5554_);
lean_ctor_set(v_reuseFailAlloc_5812_, 4, v___x_5809_);
v___x_5811_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
return v___x_5811_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5555_) == 0)
{
lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5844_; 
lean_inc(v_l_5554_);
lean_inc(v_v_5553_);
lean_inc(v_k_5552_);
v_isSharedCheck_5844_ = !lean_is_exclusive(v_l_5371_);
if (v_isSharedCheck_5844_ == 0)
{
lean_object* v_unused_5845_; lean_object* v_unused_5846_; lean_object* v_unused_5847_; lean_object* v_unused_5848_; lean_object* v_unused_5849_; 
v_unused_5845_ = lean_ctor_get(v_l_5371_, 4);
lean_dec(v_unused_5845_);
v_unused_5846_ = lean_ctor_get(v_l_5371_, 3);
lean_dec(v_unused_5846_);
v_unused_5847_ = lean_ctor_get(v_l_5371_, 2);
lean_dec(v_unused_5847_);
v_unused_5848_ = lean_ctor_get(v_l_5371_, 1);
lean_dec(v_unused_5848_);
v_unused_5849_ = lean_ctor_get(v_l_5371_, 0);
lean_dec(v_unused_5849_);
v___x_5821_ = v_l_5371_;
v_isShared_5822_ = v_isSharedCheck_5844_;
goto v_resetjp_5820_;
}
else
{
lean_dec(v_l_5371_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5844_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v_k_5823_; lean_object* v_v_5824_; lean_object* v_k_5825_; lean_object* v_v_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5840_; 
v_k_5823_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_k_5823_);
v_v_5824_ = lean_ctor_get(v___x_5707_, 1);
lean_inc(v_v_5824_);
lean_dec_ref(v___x_5707_);
v_k_5825_ = lean_ctor_get(v_r_5555_, 1);
v_v_5826_ = lean_ctor_get(v_r_5555_, 2);
v_isSharedCheck_5840_ = !lean_is_exclusive(v_r_5555_);
if (v_isSharedCheck_5840_ == 0)
{
lean_object* v_unused_5841_; lean_object* v_unused_5842_; lean_object* v_unused_5843_; 
v_unused_5841_ = lean_ctor_get(v_r_5555_, 4);
lean_dec(v_unused_5841_);
v_unused_5842_ = lean_ctor_get(v_r_5555_, 3);
lean_dec(v_unused_5842_);
v_unused_5843_ = lean_ctor_get(v_r_5555_, 0);
lean_dec(v_unused_5843_);
v___x_5828_ = v_r_5555_;
v_isShared_5829_ = v_isSharedCheck_5840_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_v_5826_);
lean_inc(v_k_5825_);
lean_dec(v_r_5555_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5840_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v___x_5830_; lean_object* v___x_5832_; 
v___x_5830_ = lean_unsigned_to_nat(3u);
if (v_isShared_5829_ == 0)
{
lean_ctor_set(v___x_5828_, 4, v_l_5554_);
lean_ctor_set(v___x_5828_, 3, v_l_5554_);
lean_ctor_set(v___x_5828_, 2, v_v_5553_);
lean_ctor_set(v___x_5828_, 1, v_k_5552_);
lean_ctor_set(v___x_5828_, 0, v___x_5561_);
v___x_5832_ = v___x_5828_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5839_; 
v_reuseFailAlloc_5839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5839_, 0, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5839_, 1, v_k_5552_);
lean_ctor_set(v_reuseFailAlloc_5839_, 2, v_v_5553_);
lean_ctor_set(v_reuseFailAlloc_5839_, 3, v_l_5554_);
lean_ctor_set(v_reuseFailAlloc_5839_, 4, v_l_5554_);
v___x_5832_ = v_reuseFailAlloc_5839_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
lean_object* v___x_5834_; 
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 4, v_l_5554_);
lean_ctor_set(v___x_5705_, 3, v_l_5554_);
lean_ctor_set(v___x_5705_, 2, v_v_5824_);
lean_ctor_set(v___x_5705_, 1, v_k_5823_);
lean_ctor_set(v___x_5705_, 0, v___x_5561_);
v___x_5834_ = v___x_5705_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5838_; 
v_reuseFailAlloc_5838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5838_, 0, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5838_, 1, v_k_5823_);
lean_ctor_set(v_reuseFailAlloc_5838_, 2, v_v_5824_);
lean_ctor_set(v_reuseFailAlloc_5838_, 3, v_l_5554_);
lean_ctor_set(v_reuseFailAlloc_5838_, 4, v_l_5554_);
v___x_5834_ = v_reuseFailAlloc_5838_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
lean_object* v___x_5836_; 
if (v_isShared_5822_ == 0)
{
lean_ctor_set(v___x_5821_, 4, v___x_5834_);
lean_ctor_set(v___x_5821_, 3, v___x_5832_);
lean_ctor_set(v___x_5821_, 2, v_v_5826_);
lean_ctor_set(v___x_5821_, 1, v_k_5825_);
lean_ctor_set(v___x_5821_, 0, v___x_5830_);
v___x_5836_ = v___x_5821_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5830_);
lean_ctor_set(v_reuseFailAlloc_5837_, 1, v_k_5825_);
lean_ctor_set(v_reuseFailAlloc_5837_, 2, v_v_5826_);
lean_ctor_set(v_reuseFailAlloc_5837_, 3, v___x_5832_);
lean_ctor_set(v_reuseFailAlloc_5837_, 4, v___x_5834_);
v___x_5836_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
return v___x_5836_;
}
}
}
}
}
}
else
{
lean_object* v_k_5850_; lean_object* v_v_5851_; lean_object* v___x_5852_; lean_object* v___x_5854_; 
v_k_5850_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_k_5850_);
v_v_5851_ = lean_ctor_get(v___x_5707_, 1);
lean_inc(v_v_5851_);
lean_dec_ref(v___x_5707_);
v___x_5852_ = lean_unsigned_to_nat(2u);
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 4, v_r_5555_);
lean_ctor_set(v___x_5705_, 3, v_l_5371_);
lean_ctor_set(v___x_5705_, 2, v_v_5851_);
lean_ctor_set(v___x_5705_, 1, v_k_5850_);
lean_ctor_set(v___x_5705_, 0, v___x_5852_);
v___x_5854_ = v___x_5705_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v___x_5852_);
lean_ctor_set(v_reuseFailAlloc_5855_, 1, v_k_5850_);
lean_ctor_set(v_reuseFailAlloc_5855_, 2, v_v_5851_);
lean_ctor_set(v_reuseFailAlloc_5855_, 3, v_l_5371_);
lean_ctor_set(v_reuseFailAlloc_5855_, 4, v_r_5555_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
}
}
}
}
}
}
}
else
{
return v_l_5371_;
}
}
else
{
return v_r_5372_;
}
}
default: 
{
lean_object* v_impl_5862_; lean_object* v___x_5863_; 
v_impl_5862_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5367_, v_r_5372_);
v___x_5863_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5862_) == 0)
{
if (lean_obj_tag(v_l_5371_) == 0)
{
lean_object* v_size_5864_; lean_object* v_size_5865_; lean_object* v_k_5866_; lean_object* v_v_5867_; lean_object* v_l_5868_; lean_object* v_r_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; uint8_t v___x_5872_; 
v_size_5864_ = lean_ctor_get(v_impl_5862_, 0);
v_size_5865_ = lean_ctor_get(v_l_5371_, 0);
v_k_5866_ = lean_ctor_get(v_l_5371_, 1);
v_v_5867_ = lean_ctor_get(v_l_5371_, 2);
v_l_5868_ = lean_ctor_get(v_l_5371_, 3);
v_r_5869_ = lean_ctor_get(v_l_5371_, 4);
lean_inc(v_r_5869_);
v___x_5870_ = lean_unsigned_to_nat(3u);
v___x_5871_ = lean_nat_mul(v___x_5870_, v_size_5864_);
v___x_5872_ = lean_nat_dec_lt(v___x_5871_, v_size_5865_);
lean_dec(v___x_5871_);
if (v___x_5872_ == 0)
{
lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5876_; 
lean_dec(v_r_5869_);
v___x_5873_ = lean_nat_add(v___x_5863_, v_size_5865_);
v___x_5874_ = lean_nat_add(v___x_5873_, v_size_5864_);
lean_dec(v___x_5873_);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v_impl_5862_);
lean_ctor_set(v___x_5374_, 0, v___x_5874_);
v___x_5876_ = v___x_5374_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v___x_5874_);
lean_ctor_set(v_reuseFailAlloc_5877_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5877_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5877_, 3, v_l_5371_);
lean_ctor_set(v_reuseFailAlloc_5877_, 4, v_impl_5862_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
else
{
lean_object* v___x_5879_; uint8_t v_isShared_5880_; uint8_t v_isSharedCheck_5943_; 
lean_inc(v_l_5868_);
lean_inc(v_v_5867_);
lean_inc(v_k_5866_);
lean_inc(v_size_5865_);
v_isSharedCheck_5943_ = !lean_is_exclusive(v_l_5371_);
if (v_isSharedCheck_5943_ == 0)
{
lean_object* v_unused_5944_; lean_object* v_unused_5945_; lean_object* v_unused_5946_; lean_object* v_unused_5947_; lean_object* v_unused_5948_; 
v_unused_5944_ = lean_ctor_get(v_l_5371_, 4);
lean_dec(v_unused_5944_);
v_unused_5945_ = lean_ctor_get(v_l_5371_, 3);
lean_dec(v_unused_5945_);
v_unused_5946_ = lean_ctor_get(v_l_5371_, 2);
lean_dec(v_unused_5946_);
v_unused_5947_ = lean_ctor_get(v_l_5371_, 1);
lean_dec(v_unused_5947_);
v_unused_5948_ = lean_ctor_get(v_l_5371_, 0);
lean_dec(v_unused_5948_);
v___x_5879_ = v_l_5371_;
v_isShared_5880_ = v_isSharedCheck_5943_;
goto v_resetjp_5878_;
}
else
{
lean_dec(v_l_5371_);
v___x_5879_ = lean_box(0);
v_isShared_5880_ = v_isSharedCheck_5943_;
goto v_resetjp_5878_;
}
v_resetjp_5878_:
{
lean_object* v_size_5881_; lean_object* v_size_5882_; lean_object* v_k_5883_; lean_object* v_v_5884_; lean_object* v_l_5885_; lean_object* v_r_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; uint8_t v___x_5889_; 
v_size_5881_ = lean_ctor_get(v_l_5868_, 0);
v_size_5882_ = lean_ctor_get(v_r_5869_, 0);
v_k_5883_ = lean_ctor_get(v_r_5869_, 1);
v_v_5884_ = lean_ctor_get(v_r_5869_, 2);
v_l_5885_ = lean_ctor_get(v_r_5869_, 3);
v_r_5886_ = lean_ctor_get(v_r_5869_, 4);
v___x_5887_ = lean_unsigned_to_nat(2u);
v___x_5888_ = lean_nat_mul(v___x_5887_, v_size_5881_);
v___x_5889_ = lean_nat_dec_lt(v_size_5882_, v___x_5888_);
lean_dec(v___x_5888_);
if (v___x_5889_ == 0)
{
lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5918_; 
lean_inc(v_r_5886_);
lean_inc(v_l_5885_);
lean_inc(v_v_5884_);
lean_inc(v_k_5883_);
v_isSharedCheck_5918_ = !lean_is_exclusive(v_r_5869_);
if (v_isSharedCheck_5918_ == 0)
{
lean_object* v_unused_5919_; lean_object* v_unused_5920_; lean_object* v_unused_5921_; lean_object* v_unused_5922_; lean_object* v_unused_5923_; 
v_unused_5919_ = lean_ctor_get(v_r_5869_, 4);
lean_dec(v_unused_5919_);
v_unused_5920_ = lean_ctor_get(v_r_5869_, 3);
lean_dec(v_unused_5920_);
v_unused_5921_ = lean_ctor_get(v_r_5869_, 2);
lean_dec(v_unused_5921_);
v_unused_5922_ = lean_ctor_get(v_r_5869_, 1);
lean_dec(v_unused_5922_);
v_unused_5923_ = lean_ctor_get(v_r_5869_, 0);
lean_dec(v_unused_5923_);
v___x_5891_ = v_r_5869_;
v_isShared_5892_ = v_isSharedCheck_5918_;
goto v_resetjp_5890_;
}
else
{
lean_dec(v_r_5869_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5918_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___y_5896_; lean_object* v___y_5897_; lean_object* v___y_5898_; lean_object* v___x_5906_; lean_object* v___y_5908_; 
v___x_5893_ = lean_nat_add(v___x_5863_, v_size_5865_);
lean_dec(v_size_5865_);
v___x_5894_ = lean_nat_add(v___x_5893_, v_size_5864_);
lean_dec(v___x_5893_);
v___x_5906_ = lean_nat_add(v___x_5863_, v_size_5881_);
if (lean_obj_tag(v_l_5885_) == 0)
{
lean_object* v_size_5916_; 
v_size_5916_ = lean_ctor_get(v_l_5885_, 0);
lean_inc(v_size_5916_);
v___y_5908_ = v_size_5916_;
goto v___jp_5907_;
}
else
{
lean_object* v___x_5917_; 
v___x_5917_ = lean_unsigned_to_nat(0u);
v___y_5908_ = v___x_5917_;
goto v___jp_5907_;
}
v___jp_5895_:
{
lean_object* v___x_5899_; lean_object* v___x_5901_; 
v___x_5899_ = lean_nat_add(v___y_5896_, v___y_5898_);
lean_dec(v___y_5898_);
lean_dec(v___y_5896_);
if (v_isShared_5892_ == 0)
{
lean_ctor_set(v___x_5891_, 4, v_impl_5862_);
lean_ctor_set(v___x_5891_, 3, v_r_5886_);
lean_ctor_set(v___x_5891_, 2, v_v_5370_);
lean_ctor_set(v___x_5891_, 1, v_k_5369_);
lean_ctor_set(v___x_5891_, 0, v___x_5899_);
v___x_5901_ = v___x_5891_;
goto v_reusejp_5900_;
}
else
{
lean_object* v_reuseFailAlloc_5905_; 
v_reuseFailAlloc_5905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5905_, 0, v___x_5899_);
lean_ctor_set(v_reuseFailAlloc_5905_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5905_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5905_, 3, v_r_5886_);
lean_ctor_set(v_reuseFailAlloc_5905_, 4, v_impl_5862_);
v___x_5901_ = v_reuseFailAlloc_5905_;
goto v_reusejp_5900_;
}
v_reusejp_5900_:
{
lean_object* v___x_5903_; 
if (v_isShared_5880_ == 0)
{
lean_ctor_set(v___x_5879_, 4, v___x_5901_);
lean_ctor_set(v___x_5879_, 3, v___y_5897_);
lean_ctor_set(v___x_5879_, 2, v_v_5884_);
lean_ctor_set(v___x_5879_, 1, v_k_5883_);
lean_ctor_set(v___x_5879_, 0, v___x_5894_);
v___x_5903_ = v___x_5879_;
goto v_reusejp_5902_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v___x_5894_);
lean_ctor_set(v_reuseFailAlloc_5904_, 1, v_k_5883_);
lean_ctor_set(v_reuseFailAlloc_5904_, 2, v_v_5884_);
lean_ctor_set(v_reuseFailAlloc_5904_, 3, v___y_5897_);
lean_ctor_set(v_reuseFailAlloc_5904_, 4, v___x_5901_);
v___x_5903_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5902_;
}
v_reusejp_5902_:
{
return v___x_5903_;
}
}
}
v___jp_5907_:
{
lean_object* v___x_5909_; lean_object* v___x_5911_; 
v___x_5909_ = lean_nat_add(v___x_5906_, v___y_5908_);
lean_dec(v___y_5908_);
lean_dec(v___x_5906_);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v_l_5885_);
lean_ctor_set(v___x_5374_, 3, v_l_5868_);
lean_ctor_set(v___x_5374_, 2, v_v_5867_);
lean_ctor_set(v___x_5374_, 1, v_k_5866_);
lean_ctor_set(v___x_5374_, 0, v___x_5909_);
v___x_5911_ = v___x_5374_;
goto v_reusejp_5910_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v___x_5909_);
lean_ctor_set(v_reuseFailAlloc_5915_, 1, v_k_5866_);
lean_ctor_set(v_reuseFailAlloc_5915_, 2, v_v_5867_);
lean_ctor_set(v_reuseFailAlloc_5915_, 3, v_l_5868_);
lean_ctor_set(v_reuseFailAlloc_5915_, 4, v_l_5885_);
v___x_5911_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5910_;
}
v_reusejp_5910_:
{
lean_object* v___x_5912_; 
v___x_5912_ = lean_nat_add(v___x_5863_, v_size_5864_);
if (lean_obj_tag(v_r_5886_) == 0)
{
lean_object* v_size_5913_; 
v_size_5913_ = lean_ctor_get(v_r_5886_, 0);
lean_inc(v_size_5913_);
v___y_5896_ = v___x_5912_;
v___y_5897_ = v___x_5911_;
v___y_5898_ = v_size_5913_;
goto v___jp_5895_;
}
else
{
lean_object* v___x_5914_; 
v___x_5914_ = lean_unsigned_to_nat(0u);
v___y_5896_ = v___x_5912_;
v___y_5897_ = v___x_5911_;
v___y_5898_ = v___x_5914_;
goto v___jp_5895_;
}
}
}
}
}
else
{
lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5929_; 
lean_del_object(v___x_5374_);
v___x_5924_ = lean_nat_add(v___x_5863_, v_size_5865_);
lean_dec(v_size_5865_);
v___x_5925_ = lean_nat_add(v___x_5924_, v_size_5864_);
lean_dec(v___x_5924_);
v___x_5926_ = lean_nat_add(v___x_5863_, v_size_5864_);
v___x_5927_ = lean_nat_add(v___x_5926_, v_size_5882_);
lean_dec(v___x_5926_);
lean_inc_ref(v_impl_5862_);
if (v_isShared_5880_ == 0)
{
lean_ctor_set(v___x_5879_, 4, v_impl_5862_);
lean_ctor_set(v___x_5879_, 3, v_r_5869_);
lean_ctor_set(v___x_5879_, 2, v_v_5370_);
lean_ctor_set(v___x_5879_, 1, v_k_5369_);
lean_ctor_set(v___x_5879_, 0, v___x_5927_);
v___x_5929_ = v___x_5879_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v___x_5927_);
lean_ctor_set(v_reuseFailAlloc_5942_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5942_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5942_, 3, v_r_5869_);
lean_ctor_set(v_reuseFailAlloc_5942_, 4, v_impl_5862_);
v___x_5929_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
lean_object* v___x_5931_; uint8_t v_isShared_5932_; uint8_t v_isSharedCheck_5936_; 
v_isSharedCheck_5936_ = !lean_is_exclusive(v_impl_5862_);
if (v_isSharedCheck_5936_ == 0)
{
lean_object* v_unused_5937_; lean_object* v_unused_5938_; lean_object* v_unused_5939_; lean_object* v_unused_5940_; lean_object* v_unused_5941_; 
v_unused_5937_ = lean_ctor_get(v_impl_5862_, 4);
lean_dec(v_unused_5937_);
v_unused_5938_ = lean_ctor_get(v_impl_5862_, 3);
lean_dec(v_unused_5938_);
v_unused_5939_ = lean_ctor_get(v_impl_5862_, 2);
lean_dec(v_unused_5939_);
v_unused_5940_ = lean_ctor_get(v_impl_5862_, 1);
lean_dec(v_unused_5940_);
v_unused_5941_ = lean_ctor_get(v_impl_5862_, 0);
lean_dec(v_unused_5941_);
v___x_5931_ = v_impl_5862_;
v_isShared_5932_ = v_isSharedCheck_5936_;
goto v_resetjp_5930_;
}
else
{
lean_dec(v_impl_5862_);
v___x_5931_ = lean_box(0);
v_isShared_5932_ = v_isSharedCheck_5936_;
goto v_resetjp_5930_;
}
v_resetjp_5930_:
{
lean_object* v___x_5934_; 
if (v_isShared_5932_ == 0)
{
lean_ctor_set(v___x_5931_, 4, v___x_5929_);
lean_ctor_set(v___x_5931_, 3, v_l_5868_);
lean_ctor_set(v___x_5931_, 2, v_v_5867_);
lean_ctor_set(v___x_5931_, 1, v_k_5866_);
lean_ctor_set(v___x_5931_, 0, v___x_5925_);
v___x_5934_ = v___x_5931_;
goto v_reusejp_5933_;
}
else
{
lean_object* v_reuseFailAlloc_5935_; 
v_reuseFailAlloc_5935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5935_, 0, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5935_, 1, v_k_5866_);
lean_ctor_set(v_reuseFailAlloc_5935_, 2, v_v_5867_);
lean_ctor_set(v_reuseFailAlloc_5935_, 3, v_l_5868_);
lean_ctor_set(v_reuseFailAlloc_5935_, 4, v___x_5929_);
v___x_5934_ = v_reuseFailAlloc_5935_;
goto v_reusejp_5933_;
}
v_reusejp_5933_:
{
return v___x_5934_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5949_; lean_object* v___x_5950_; lean_object* v___x_5952_; 
v_size_5949_ = lean_ctor_get(v_impl_5862_, 0);
v___x_5950_ = lean_nat_add(v___x_5863_, v_size_5949_);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v_impl_5862_);
lean_ctor_set(v___x_5374_, 0, v___x_5950_);
v___x_5952_ = v___x_5374_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v___x_5950_);
lean_ctor_set(v_reuseFailAlloc_5953_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5953_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5953_, 3, v_l_5371_);
lean_ctor_set(v_reuseFailAlloc_5953_, 4, v_impl_5862_);
v___x_5952_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
return v___x_5952_;
}
}
}
else
{
if (lean_obj_tag(v_l_5371_) == 0)
{
lean_object* v_l_5954_; 
v_l_5954_ = lean_ctor_get(v_l_5371_, 3);
if (lean_obj_tag(v_l_5954_) == 0)
{
lean_object* v_r_5955_; 
lean_inc_ref(v_l_5954_);
v_r_5955_ = lean_ctor_get(v_l_5371_, 4);
lean_inc(v_r_5955_);
if (lean_obj_tag(v_r_5955_) == 0)
{
lean_object* v_size_5956_; lean_object* v_k_5957_; lean_object* v_v_5958_; lean_object* v___x_5960_; uint8_t v_isShared_5961_; uint8_t v_isSharedCheck_5971_; 
v_size_5956_ = lean_ctor_get(v_l_5371_, 0);
v_k_5957_ = lean_ctor_get(v_l_5371_, 1);
v_v_5958_ = lean_ctor_get(v_l_5371_, 2);
v_isSharedCheck_5971_ = !lean_is_exclusive(v_l_5371_);
if (v_isSharedCheck_5971_ == 0)
{
lean_object* v_unused_5972_; lean_object* v_unused_5973_; 
v_unused_5972_ = lean_ctor_get(v_l_5371_, 4);
lean_dec(v_unused_5972_);
v_unused_5973_ = lean_ctor_get(v_l_5371_, 3);
lean_dec(v_unused_5973_);
v___x_5960_ = v_l_5371_;
v_isShared_5961_ = v_isSharedCheck_5971_;
goto v_resetjp_5959_;
}
else
{
lean_inc(v_v_5958_);
lean_inc(v_k_5957_);
lean_inc(v_size_5956_);
lean_dec(v_l_5371_);
v___x_5960_ = lean_box(0);
v_isShared_5961_ = v_isSharedCheck_5971_;
goto v_resetjp_5959_;
}
v_resetjp_5959_:
{
lean_object* v_size_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5966_; 
v_size_5962_ = lean_ctor_get(v_r_5955_, 0);
v___x_5963_ = lean_nat_add(v___x_5863_, v_size_5956_);
lean_dec(v_size_5956_);
v___x_5964_ = lean_nat_add(v___x_5863_, v_size_5962_);
if (v_isShared_5961_ == 0)
{
lean_ctor_set(v___x_5960_, 4, v_impl_5862_);
lean_ctor_set(v___x_5960_, 3, v_r_5955_);
lean_ctor_set(v___x_5960_, 2, v_v_5370_);
lean_ctor_set(v___x_5960_, 1, v_k_5369_);
lean_ctor_set(v___x_5960_, 0, v___x_5964_);
v___x_5966_ = v___x_5960_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v___x_5964_);
lean_ctor_set(v_reuseFailAlloc_5970_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5970_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5970_, 3, v_r_5955_);
lean_ctor_set(v_reuseFailAlloc_5970_, 4, v_impl_5862_);
v___x_5966_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
lean_object* v___x_5968_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v___x_5966_);
lean_ctor_set(v___x_5374_, 3, v_l_5954_);
lean_ctor_set(v___x_5374_, 2, v_v_5958_);
lean_ctor_set(v___x_5374_, 1, v_k_5957_);
lean_ctor_set(v___x_5374_, 0, v___x_5963_);
v___x_5968_ = v___x_5374_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5969_; 
v_reuseFailAlloc_5969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5969_, 0, v___x_5963_);
lean_ctor_set(v_reuseFailAlloc_5969_, 1, v_k_5957_);
lean_ctor_set(v_reuseFailAlloc_5969_, 2, v_v_5958_);
lean_ctor_set(v_reuseFailAlloc_5969_, 3, v_l_5954_);
lean_ctor_set(v_reuseFailAlloc_5969_, 4, v___x_5966_);
v___x_5968_ = v_reuseFailAlloc_5969_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
return v___x_5968_;
}
}
}
}
else
{
lean_object* v_k_5974_; lean_object* v_v_5975_; lean_object* v___x_5977_; uint8_t v_isShared_5978_; uint8_t v_isSharedCheck_5986_; 
v_k_5974_ = lean_ctor_get(v_l_5371_, 1);
v_v_5975_ = lean_ctor_get(v_l_5371_, 2);
v_isSharedCheck_5986_ = !lean_is_exclusive(v_l_5371_);
if (v_isSharedCheck_5986_ == 0)
{
lean_object* v_unused_5987_; lean_object* v_unused_5988_; lean_object* v_unused_5989_; 
v_unused_5987_ = lean_ctor_get(v_l_5371_, 4);
lean_dec(v_unused_5987_);
v_unused_5988_ = lean_ctor_get(v_l_5371_, 3);
lean_dec(v_unused_5988_);
v_unused_5989_ = lean_ctor_get(v_l_5371_, 0);
lean_dec(v_unused_5989_);
v___x_5977_ = v_l_5371_;
v_isShared_5978_ = v_isSharedCheck_5986_;
goto v_resetjp_5976_;
}
else
{
lean_inc(v_v_5975_);
lean_inc(v_k_5974_);
lean_dec(v_l_5371_);
v___x_5977_ = lean_box(0);
v_isShared_5978_ = v_isSharedCheck_5986_;
goto v_resetjp_5976_;
}
v_resetjp_5976_:
{
lean_object* v___x_5979_; lean_object* v___x_5981_; 
v___x_5979_ = lean_unsigned_to_nat(3u);
if (v_isShared_5978_ == 0)
{
lean_ctor_set(v___x_5977_, 3, v_r_5955_);
lean_ctor_set(v___x_5977_, 2, v_v_5370_);
lean_ctor_set(v___x_5977_, 1, v_k_5369_);
lean_ctor_set(v___x_5977_, 0, v___x_5863_);
v___x_5981_ = v___x_5977_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v___x_5863_);
lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_5985_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_5985_, 3, v_r_5955_);
lean_ctor_set(v_reuseFailAlloc_5985_, 4, v_r_5955_);
v___x_5981_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
lean_object* v___x_5983_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v___x_5981_);
lean_ctor_set(v___x_5374_, 3, v_l_5954_);
lean_ctor_set(v___x_5374_, 2, v_v_5975_);
lean_ctor_set(v___x_5374_, 1, v_k_5974_);
lean_ctor_set(v___x_5374_, 0, v___x_5979_);
v___x_5983_ = v___x_5374_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v___x_5979_);
lean_ctor_set(v_reuseFailAlloc_5984_, 1, v_k_5974_);
lean_ctor_set(v_reuseFailAlloc_5984_, 2, v_v_5975_);
lean_ctor_set(v_reuseFailAlloc_5984_, 3, v_l_5954_);
lean_ctor_set(v_reuseFailAlloc_5984_, 4, v___x_5981_);
v___x_5983_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
return v___x_5983_;
}
}
}
}
}
else
{
lean_object* v_r_5990_; 
v_r_5990_ = lean_ctor_get(v_l_5371_, 4);
lean_inc(v_r_5990_);
if (lean_obj_tag(v_r_5990_) == 0)
{
lean_object* v_k_5991_; lean_object* v_v_5992_; lean_object* v___x_5994_; uint8_t v_isShared_5995_; uint8_t v_isSharedCheck_6015_; 
lean_inc(v_l_5954_);
v_k_5991_ = lean_ctor_get(v_l_5371_, 1);
v_v_5992_ = lean_ctor_get(v_l_5371_, 2);
v_isSharedCheck_6015_ = !lean_is_exclusive(v_l_5371_);
if (v_isSharedCheck_6015_ == 0)
{
lean_object* v_unused_6016_; lean_object* v_unused_6017_; lean_object* v_unused_6018_; 
v_unused_6016_ = lean_ctor_get(v_l_5371_, 4);
lean_dec(v_unused_6016_);
v_unused_6017_ = lean_ctor_get(v_l_5371_, 3);
lean_dec(v_unused_6017_);
v_unused_6018_ = lean_ctor_get(v_l_5371_, 0);
lean_dec(v_unused_6018_);
v___x_5994_ = v_l_5371_;
v_isShared_5995_ = v_isSharedCheck_6015_;
goto v_resetjp_5993_;
}
else
{
lean_inc(v_v_5992_);
lean_inc(v_k_5991_);
lean_dec(v_l_5371_);
v___x_5994_ = lean_box(0);
v_isShared_5995_ = v_isSharedCheck_6015_;
goto v_resetjp_5993_;
}
v_resetjp_5993_:
{
lean_object* v_k_5996_; lean_object* v_v_5997_; lean_object* v___x_5999_; uint8_t v_isShared_6000_; uint8_t v_isSharedCheck_6011_; 
v_k_5996_ = lean_ctor_get(v_r_5990_, 1);
v_v_5997_ = lean_ctor_get(v_r_5990_, 2);
v_isSharedCheck_6011_ = !lean_is_exclusive(v_r_5990_);
if (v_isSharedCheck_6011_ == 0)
{
lean_object* v_unused_6012_; lean_object* v_unused_6013_; lean_object* v_unused_6014_; 
v_unused_6012_ = lean_ctor_get(v_r_5990_, 4);
lean_dec(v_unused_6012_);
v_unused_6013_ = lean_ctor_get(v_r_5990_, 3);
lean_dec(v_unused_6013_);
v_unused_6014_ = lean_ctor_get(v_r_5990_, 0);
lean_dec(v_unused_6014_);
v___x_5999_ = v_r_5990_;
v_isShared_6000_ = v_isSharedCheck_6011_;
goto v_resetjp_5998_;
}
else
{
lean_inc(v_v_5997_);
lean_inc(v_k_5996_);
lean_dec(v_r_5990_);
v___x_5999_ = lean_box(0);
v_isShared_6000_ = v_isSharedCheck_6011_;
goto v_resetjp_5998_;
}
v_resetjp_5998_:
{
lean_object* v___x_6001_; lean_object* v___x_6003_; 
v___x_6001_ = lean_unsigned_to_nat(3u);
if (v_isShared_6000_ == 0)
{
lean_ctor_set(v___x_5999_, 4, v_l_5954_);
lean_ctor_set(v___x_5999_, 3, v_l_5954_);
lean_ctor_set(v___x_5999_, 2, v_v_5992_);
lean_ctor_set(v___x_5999_, 1, v_k_5991_);
lean_ctor_set(v___x_5999_, 0, v___x_5863_);
v___x_6003_ = v___x_5999_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v___x_5863_);
lean_ctor_set(v_reuseFailAlloc_6010_, 1, v_k_5991_);
lean_ctor_set(v_reuseFailAlloc_6010_, 2, v_v_5992_);
lean_ctor_set(v_reuseFailAlloc_6010_, 3, v_l_5954_);
lean_ctor_set(v_reuseFailAlloc_6010_, 4, v_l_5954_);
v___x_6003_ = v_reuseFailAlloc_6010_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
lean_object* v___x_6005_; 
if (v_isShared_5995_ == 0)
{
lean_ctor_set(v___x_5994_, 4, v_l_5954_);
lean_ctor_set(v___x_5994_, 2, v_v_5370_);
lean_ctor_set(v___x_5994_, 1, v_k_5369_);
lean_ctor_set(v___x_5994_, 0, v___x_5863_);
v___x_6005_ = v___x_5994_;
goto v_reusejp_6004_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v___x_5863_);
lean_ctor_set(v_reuseFailAlloc_6009_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_6009_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_6009_, 3, v_l_5954_);
lean_ctor_set(v_reuseFailAlloc_6009_, 4, v_l_5954_);
v___x_6005_ = v_reuseFailAlloc_6009_;
goto v_reusejp_6004_;
}
v_reusejp_6004_:
{
lean_object* v___x_6007_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v___x_6005_);
lean_ctor_set(v___x_5374_, 3, v___x_6003_);
lean_ctor_set(v___x_5374_, 2, v_v_5997_);
lean_ctor_set(v___x_5374_, 1, v_k_5996_);
lean_ctor_set(v___x_5374_, 0, v___x_6001_);
v___x_6007_ = v___x_5374_;
goto v_reusejp_6006_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v___x_6001_);
lean_ctor_set(v_reuseFailAlloc_6008_, 1, v_k_5996_);
lean_ctor_set(v_reuseFailAlloc_6008_, 2, v_v_5997_);
lean_ctor_set(v_reuseFailAlloc_6008_, 3, v___x_6003_);
lean_ctor_set(v_reuseFailAlloc_6008_, 4, v___x_6005_);
v___x_6007_ = v_reuseFailAlloc_6008_;
goto v_reusejp_6006_;
}
v_reusejp_6006_:
{
return v___x_6007_;
}
}
}
}
}
}
else
{
lean_object* v___x_6019_; lean_object* v___x_6021_; 
v___x_6019_ = lean_unsigned_to_nat(2u);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v_r_5990_);
lean_ctor_set(v___x_5374_, 0, v___x_6019_);
v___x_6021_ = v___x_5374_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v___x_6019_);
lean_ctor_set(v_reuseFailAlloc_6022_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_6022_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_6022_, 3, v_l_5371_);
lean_ctor_set(v_reuseFailAlloc_6022_, 4, v_r_5990_);
v___x_6021_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
return v___x_6021_;
}
}
}
}
else
{
lean_object* v___x_6024_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v_l_5371_);
lean_ctor_set(v___x_5374_, 0, v___x_5863_);
v___x_6024_ = v___x_5374_;
goto v_reusejp_6023_;
}
else
{
lean_object* v_reuseFailAlloc_6025_; 
v_reuseFailAlloc_6025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6025_, 0, v___x_5863_);
lean_ctor_set(v_reuseFailAlloc_6025_, 1, v_k_5369_);
lean_ctor_set(v_reuseFailAlloc_6025_, 2, v_v_5370_);
lean_ctor_set(v_reuseFailAlloc_6025_, 3, v_l_5371_);
lean_ctor_set(v_reuseFailAlloc_6025_, 4, v_l_5371_);
v___x_6024_ = v_reuseFailAlloc_6025_;
goto v_reusejp_6023_;
}
v_reusejp_6023_:
{
return v___x_6024_;
}
}
}
}
}
}
}
else
{
return v_t_5368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_6028_, lean_object* v_t_6029_){
_start:
{
lean_object* v_res_6030_; 
v_res_6030_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6028_, v_t_6029_);
lean_dec(v_k_6028_);
return v_res_6030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_6031_, lean_object* v_x_6032_){
_start:
{
if (lean_obj_tag(v_x_6032_) == 0)
{
lean_object* v_k_6033_; lean_object* v_l_6034_; lean_object* v_r_6035_; lean_object* v___x_6036_; lean_object* v_ileans_6037_; lean_object* v_workers_6038_; lean_object* v___x_6040_; uint8_t v_isShared_6041_; uint8_t v_isSharedCheck_6047_; 
v_k_6033_ = lean_ctor_get(v_x_6032_, 1);
v_l_6034_ = lean_ctor_get(v_x_6032_, 3);
v_r_6035_ = lean_ctor_get(v_x_6032_, 4);
v___x_6036_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6031_, v_l_6034_);
v_ileans_6037_ = lean_ctor_get(v___x_6036_, 0);
v_workers_6038_ = lean_ctor_get(v___x_6036_, 1);
v_isSharedCheck_6047_ = !lean_is_exclusive(v___x_6036_);
if (v_isSharedCheck_6047_ == 0)
{
v___x_6040_ = v___x_6036_;
v_isShared_6041_ = v_isSharedCheck_6047_;
goto v_resetjp_6039_;
}
else
{
lean_inc(v_workers_6038_);
lean_inc(v_ileans_6037_);
lean_dec(v___x_6036_);
v___x_6040_ = lean_box(0);
v_isShared_6041_ = v_isSharedCheck_6047_;
goto v_resetjp_6039_;
}
v_resetjp_6039_:
{
lean_object* v___x_6042_; lean_object* v___x_6044_; 
v___x_6042_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6033_, v_ileans_6037_);
if (v_isShared_6041_ == 0)
{
lean_ctor_set(v___x_6040_, 0, v___x_6042_);
v___x_6044_ = v___x_6040_;
goto v_reusejp_6043_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v___x_6042_);
lean_ctor_set(v_reuseFailAlloc_6046_, 1, v_workers_6038_);
v___x_6044_ = v_reuseFailAlloc_6046_;
goto v_reusejp_6043_;
}
v_reusejp_6043_:
{
v_init_6031_ = v___x_6044_;
v_x_6032_ = v_r_6035_;
goto _start;
}
}
}
else
{
return v_init_6031_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_6048_, lean_object* v_x_6049_){
_start:
{
lean_object* v_res_6050_; 
v_res_6050_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6048_, v_x_6049_);
lean_dec(v_x_6049_);
return v_res_6050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_6051_, lean_object* v_path_6052_){
_start:
{
lean_object* v_ileans_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; 
v_ileans_6053_ = lean_ctor_get(v_self_6051_, 0);
lean_inc(v_ileans_6053_);
v___x_6054_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6052_, v_ileans_6053_);
v___x_6055_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_6051_, v___x_6054_);
lean_dec(v___x_6054_);
return v___x_6055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_6056_, lean_object* v_path_6057_){
_start:
{
lean_object* v_res_6058_; 
v_res_6058_ = l_Lean_Server_References_removeIlean(v_self_6056_, v_path_6057_);
lean_dec_ref(v_path_6057_);
return v_res_6058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_6059_, lean_object* v_k_6060_, lean_object* v_t_6061_, lean_object* v_h_6062_){
_start:
{
lean_object* v___x_6063_; 
v___x_6063_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6060_, v_t_6061_);
return v___x_6063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_6064_, lean_object* v_k_6065_, lean_object* v_t_6066_, lean_object* v_h_6067_){
_start:
{
lean_object* v_res_6068_; 
v_res_6068_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_6064_, v_k_6065_, v_t_6066_, v_h_6067_);
lean_dec(v_k_6065_);
return v_res_6068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_6069_, lean_object* v_t_6070_, lean_object* v_hl_6071_){
_start:
{
lean_object* v___x_6072_; 
v___x_6072_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6069_, v_t_6070_);
return v___x_6072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_6073_, lean_object* v_t_6074_, lean_object* v_hl_6075_){
_start:
{
lean_object* v_res_6076_; 
v_res_6076_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_6073_, v_t_6074_, v_hl_6075_);
lean_dec_ref(v_path_6073_);
return v_res_6076_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_6077_, lean_object* v_t_6078_){
_start:
{
lean_object* v___x_6079_; 
v___x_6079_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6077_, v_t_6078_);
return v___x_6079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_6080_, lean_object* v_t_6081_){
_start:
{
lean_object* v_res_6082_; 
v_res_6082_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_6080_, v_t_6081_);
lean_dec(v_t_6081_);
return v_res_6082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_6083_, lean_object* v_k_6084_){
_start:
{
if (lean_obj_tag(v_t_6083_) == 0)
{
lean_object* v_k_6085_; lean_object* v_v_6086_; lean_object* v_l_6087_; lean_object* v_r_6088_; uint8_t v___x_6089_; 
v_k_6085_ = lean_ctor_get(v_t_6083_, 1);
v_v_6086_ = lean_ctor_get(v_t_6083_, 2);
v_l_6087_ = lean_ctor_get(v_t_6083_, 3);
v_r_6088_ = lean_ctor_get(v_t_6083_, 4);
v___x_6089_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6084_, v_k_6085_);
switch(v___x_6089_)
{
case 0:
{
v_t_6083_ = v_l_6087_;
goto _start;
}
case 1:
{
lean_object* v___x_6091_; 
lean_inc(v_v_6086_);
v___x_6091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6091_, 0, v_v_6086_);
return v___x_6091_;
}
default: 
{
v_t_6083_ = v_r_6088_;
goto _start;
}
}
}
else
{
lean_object* v___x_6093_; 
v___x_6093_ = lean_box(0);
return v___x_6093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_6094_, lean_object* v_k_6095_){
_start:
{
lean_object* v_res_6096_; 
v_res_6096_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6094_, v_k_6095_);
lean_dec(v_k_6095_);
lean_dec(v_t_6094_);
return v_res_6096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_6097_, lean_object* v_name_6098_, lean_object* v_moduleUri_6099_, lean_object* v_version_6100_, lean_object* v_directImports_6101_, uint8_t v_isSetupFailure_6102_){
_start:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6104_ = lean_box(1);
v___x_6105_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_6101_);
if (lean_obj_tag(v___x_6105_) == 0)
{
lean_object* v_a_6106_; lean_object* v___x_6108_; uint8_t v_isShared_6109_; uint8_t v_isSharedCheck_6171_; 
v_a_6106_ = lean_ctor_get(v___x_6105_, 0);
v_isSharedCheck_6171_ = !lean_is_exclusive(v___x_6105_);
if (v_isSharedCheck_6171_ == 0)
{
v___x_6108_ = v___x_6105_;
v_isShared_6109_ = v_isSharedCheck_6171_;
goto v_resetjp_6107_;
}
else
{
lean_inc(v_a_6106_);
lean_dec(v___x_6105_);
v___x_6108_ = lean_box(0);
v_isShared_6109_ = v_isSharedCheck_6171_;
goto v_resetjp_6107_;
}
v_resetjp_6107_:
{
lean_object* v_ileans_6110_; lean_object* v_workers_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; 
v_ileans_6110_ = lean_ctor_get(v_self_6097_, 0);
v_workers_6111_ = lean_ctor_get(v_self_6097_, 1);
v___x_6112_ = lean_box(v_isSetupFailure_6102_);
v___x_6113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
v___x_6114_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6111_, v_name_6098_);
if (lean_obj_tag(v___x_6114_) == 1)
{
lean_object* v_val_6115_; lean_object* v_version_6116_; lean_object* v_refs_6117_; lean_object* v_decls_6118_; lean_object* v___x_6120_; uint8_t v_isShared_6121_; uint8_t v_isSharedCheck_6153_; 
v_val_6115_ = lean_ctor_get(v___x_6114_, 0);
lean_inc(v_val_6115_);
lean_dec_ref_known(v___x_6114_, 1);
v_version_6116_ = lean_ctor_get(v_val_6115_, 1);
v_refs_6117_ = lean_ctor_get(v_val_6115_, 4);
v_decls_6118_ = lean_ctor_get(v_val_6115_, 5);
v_isSharedCheck_6153_ = !lean_is_exclusive(v_val_6115_);
if (v_isSharedCheck_6153_ == 0)
{
lean_object* v_unused_6154_; lean_object* v_unused_6155_; lean_object* v_unused_6156_; 
v_unused_6154_ = lean_ctor_get(v_val_6115_, 3);
lean_dec(v_unused_6154_);
v_unused_6155_ = lean_ctor_get(v_val_6115_, 2);
lean_dec(v_unused_6155_);
v_unused_6156_ = lean_ctor_get(v_val_6115_, 0);
lean_dec(v_unused_6156_);
v___x_6120_ = v_val_6115_;
v_isShared_6121_ = v_isSharedCheck_6153_;
goto v_resetjp_6119_;
}
else
{
lean_inc(v_decls_6118_);
lean_inc(v_refs_6117_);
lean_inc(v_version_6116_);
lean_dec(v_val_6115_);
v___x_6120_ = lean_box(0);
v_isShared_6121_ = v_isSharedCheck_6153_;
goto v_resetjp_6119_;
}
v_resetjp_6119_:
{
uint8_t v___x_6122_; 
v___x_6122_ = lean_nat_dec_lt(v_version_6100_, v_version_6116_);
if (v___x_6122_ == 0)
{
lean_object* v___x_6124_; uint8_t v_isShared_6125_; uint8_t v_isSharedCheck_6147_; 
lean_inc(v_workers_6111_);
lean_inc(v_ileans_6110_);
v_isSharedCheck_6147_ = !lean_is_exclusive(v_self_6097_);
if (v_isSharedCheck_6147_ == 0)
{
lean_object* v_unused_6148_; lean_object* v_unused_6149_; 
v_unused_6148_ = lean_ctor_get(v_self_6097_, 1);
lean_dec(v_unused_6148_);
v_unused_6149_ = lean_ctor_get(v_self_6097_, 0);
lean_dec(v_unused_6149_);
v___x_6124_ = v_self_6097_;
v_isShared_6125_ = v_isSharedCheck_6147_;
goto v_resetjp_6123_;
}
else
{
lean_dec(v_self_6097_);
v___x_6124_ = lean_box(0);
v_isShared_6125_ = v_isSharedCheck_6147_;
goto v_resetjp_6123_;
}
v_resetjp_6123_:
{
uint8_t v___x_6126_; 
v___x_6126_ = lean_nat_dec_eq(v_version_6100_, v_version_6116_);
lean_dec(v_version_6116_);
if (v___x_6126_ == 0)
{
lean_object* v___x_6128_; 
lean_dec(v_decls_6118_);
lean_dec(v_refs_6117_);
if (v_isShared_6121_ == 0)
{
lean_ctor_set(v___x_6120_, 5, v___x_6104_);
lean_ctor_set(v___x_6120_, 4, v___x_6104_);
lean_ctor_set(v___x_6120_, 3, v___x_6113_);
lean_ctor_set(v___x_6120_, 2, v_a_6106_);
lean_ctor_set(v___x_6120_, 1, v_version_6100_);
lean_ctor_set(v___x_6120_, 0, v_moduleUri_6099_);
v___x_6128_ = v___x_6120_;
goto v_reusejp_6127_;
}
else
{
lean_object* v_reuseFailAlloc_6136_; 
v_reuseFailAlloc_6136_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6136_, 0, v_moduleUri_6099_);
lean_ctor_set(v_reuseFailAlloc_6136_, 1, v_version_6100_);
lean_ctor_set(v_reuseFailAlloc_6136_, 2, v_a_6106_);
lean_ctor_set(v_reuseFailAlloc_6136_, 3, v___x_6113_);
lean_ctor_set(v_reuseFailAlloc_6136_, 4, v___x_6104_);
lean_ctor_set(v_reuseFailAlloc_6136_, 5, v___x_6104_);
v___x_6128_ = v_reuseFailAlloc_6136_;
goto v_reusejp_6127_;
}
v_reusejp_6127_:
{
lean_object* v___x_6129_; lean_object* v___x_6131_; 
v___x_6129_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6098_, v___x_6128_, v_workers_6111_);
if (v_isShared_6125_ == 0)
{
lean_ctor_set(v___x_6124_, 1, v___x_6129_);
v___x_6131_ = v___x_6124_;
goto v_reusejp_6130_;
}
else
{
lean_object* v_reuseFailAlloc_6135_; 
v_reuseFailAlloc_6135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_ileans_6110_);
lean_ctor_set(v_reuseFailAlloc_6135_, 1, v___x_6129_);
v___x_6131_ = v_reuseFailAlloc_6135_;
goto v_reusejp_6130_;
}
v_reusejp_6130_:
{
lean_object* v___x_6133_; 
if (v_isShared_6109_ == 0)
{
lean_ctor_set(v___x_6108_, 0, v___x_6131_);
v___x_6133_ = v___x_6108_;
goto v_reusejp_6132_;
}
else
{
lean_object* v_reuseFailAlloc_6134_; 
v_reuseFailAlloc_6134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6134_, 0, v___x_6131_);
v___x_6133_ = v_reuseFailAlloc_6134_;
goto v_reusejp_6132_;
}
v_reusejp_6132_:
{
return v___x_6133_;
}
}
}
}
else
{
lean_object* v___x_6138_; 
if (v_isShared_6121_ == 0)
{
lean_ctor_set(v___x_6120_, 3, v___x_6113_);
lean_ctor_set(v___x_6120_, 2, v_a_6106_);
lean_ctor_set(v___x_6120_, 1, v_version_6100_);
lean_ctor_set(v___x_6120_, 0, v_moduleUri_6099_);
v___x_6138_ = v___x_6120_;
goto v_reusejp_6137_;
}
else
{
lean_object* v_reuseFailAlloc_6146_; 
v_reuseFailAlloc_6146_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6146_, 0, v_moduleUri_6099_);
lean_ctor_set(v_reuseFailAlloc_6146_, 1, v_version_6100_);
lean_ctor_set(v_reuseFailAlloc_6146_, 2, v_a_6106_);
lean_ctor_set(v_reuseFailAlloc_6146_, 3, v___x_6113_);
lean_ctor_set(v_reuseFailAlloc_6146_, 4, v_refs_6117_);
lean_ctor_set(v_reuseFailAlloc_6146_, 5, v_decls_6118_);
v___x_6138_ = v_reuseFailAlloc_6146_;
goto v_reusejp_6137_;
}
v_reusejp_6137_:
{
lean_object* v___x_6139_; lean_object* v___x_6141_; 
v___x_6139_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6098_, v___x_6138_, v_workers_6111_);
if (v_isShared_6125_ == 0)
{
lean_ctor_set(v___x_6124_, 1, v___x_6139_);
v___x_6141_ = v___x_6124_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_ileans_6110_);
lean_ctor_set(v_reuseFailAlloc_6145_, 1, v___x_6139_);
v___x_6141_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
lean_object* v___x_6143_; 
if (v_isShared_6109_ == 0)
{
lean_ctor_set(v___x_6108_, 0, v___x_6141_);
v___x_6143_ = v___x_6108_;
goto v_reusejp_6142_;
}
else
{
lean_object* v_reuseFailAlloc_6144_; 
v_reuseFailAlloc_6144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6144_, 0, v___x_6141_);
v___x_6143_ = v_reuseFailAlloc_6144_;
goto v_reusejp_6142_;
}
v_reusejp_6142_:
{
return v___x_6143_;
}
}
}
}
}
}
else
{
lean_object* v___x_6151_; 
lean_del_object(v___x_6120_);
lean_dec(v_decls_6118_);
lean_dec(v_refs_6117_);
lean_dec(v_version_6116_);
lean_dec_ref_known(v___x_6113_, 1);
lean_dec(v_a_6106_);
lean_dec(v_version_6100_);
lean_dec_ref(v_moduleUri_6099_);
lean_dec(v_name_6098_);
if (v_isShared_6109_ == 0)
{
lean_ctor_set(v___x_6108_, 0, v_self_6097_);
v___x_6151_ = v___x_6108_;
goto v_reusejp_6150_;
}
else
{
lean_object* v_reuseFailAlloc_6152_; 
v_reuseFailAlloc_6152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6152_, 0, v_self_6097_);
v___x_6151_ = v_reuseFailAlloc_6152_;
goto v_reusejp_6150_;
}
v_reusejp_6150_:
{
return v___x_6151_;
}
}
}
}
else
{
lean_object* v___x_6158_; uint8_t v_isShared_6159_; uint8_t v_isSharedCheck_6168_; 
lean_inc(v_workers_6111_);
lean_inc(v_ileans_6110_);
lean_dec(v___x_6114_);
v_isSharedCheck_6168_ = !lean_is_exclusive(v_self_6097_);
if (v_isSharedCheck_6168_ == 0)
{
lean_object* v_unused_6169_; lean_object* v_unused_6170_; 
v_unused_6169_ = lean_ctor_get(v_self_6097_, 1);
lean_dec(v_unused_6169_);
v_unused_6170_ = lean_ctor_get(v_self_6097_, 0);
lean_dec(v_unused_6170_);
v___x_6158_ = v_self_6097_;
v_isShared_6159_ = v_isSharedCheck_6168_;
goto v_resetjp_6157_;
}
else
{
lean_dec(v_self_6097_);
v___x_6158_ = lean_box(0);
v_isShared_6159_ = v_isSharedCheck_6168_;
goto v_resetjp_6157_;
}
v_resetjp_6157_:
{
lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6163_; 
v___x_6160_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6160_, 0, v_moduleUri_6099_);
lean_ctor_set(v___x_6160_, 1, v_version_6100_);
lean_ctor_set(v___x_6160_, 2, v_a_6106_);
lean_ctor_set(v___x_6160_, 3, v___x_6113_);
lean_ctor_set(v___x_6160_, 4, v___x_6104_);
lean_ctor_set(v___x_6160_, 5, v___x_6104_);
v___x_6161_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6098_, v___x_6160_, v_workers_6111_);
if (v_isShared_6159_ == 0)
{
lean_ctor_set(v___x_6158_, 1, v___x_6161_);
v___x_6163_ = v___x_6158_;
goto v_reusejp_6162_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v_ileans_6110_);
lean_ctor_set(v_reuseFailAlloc_6167_, 1, v___x_6161_);
v___x_6163_ = v_reuseFailAlloc_6167_;
goto v_reusejp_6162_;
}
v_reusejp_6162_:
{
lean_object* v___x_6165_; 
if (v_isShared_6109_ == 0)
{
lean_ctor_set(v___x_6108_, 0, v___x_6163_);
v___x_6165_ = v___x_6108_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v___x_6163_);
v___x_6165_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
return v___x_6165_;
}
}
}
}
}
}
else
{
lean_object* v_a_6172_; lean_object* v___x_6174_; uint8_t v_isShared_6175_; uint8_t v_isSharedCheck_6179_; 
lean_dec(v_version_6100_);
lean_dec_ref(v_moduleUri_6099_);
lean_dec(v_name_6098_);
lean_dec_ref(v_self_6097_);
v_a_6172_ = lean_ctor_get(v___x_6105_, 0);
v_isSharedCheck_6179_ = !lean_is_exclusive(v___x_6105_);
if (v_isSharedCheck_6179_ == 0)
{
v___x_6174_ = v___x_6105_;
v_isShared_6175_ = v_isSharedCheck_6179_;
goto v_resetjp_6173_;
}
else
{
lean_inc(v_a_6172_);
lean_dec(v___x_6105_);
v___x_6174_ = lean_box(0);
v_isShared_6175_ = v_isSharedCheck_6179_;
goto v_resetjp_6173_;
}
v_resetjp_6173_:
{
lean_object* v___x_6177_; 
if (v_isShared_6175_ == 0)
{
v___x_6177_ = v___x_6174_;
goto v_reusejp_6176_;
}
else
{
lean_object* v_reuseFailAlloc_6178_; 
v_reuseFailAlloc_6178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6178_, 0, v_a_6172_);
v___x_6177_ = v_reuseFailAlloc_6178_;
goto v_reusejp_6176_;
}
v_reusejp_6176_:
{
return v___x_6177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6180_, lean_object* v_name_6181_, lean_object* v_moduleUri_6182_, lean_object* v_version_6183_, lean_object* v_directImports_6184_, lean_object* v_isSetupFailure_6185_, lean_object* v_a_6186_){
_start:
{
uint8_t v_isSetupFailure_boxed_6187_; lean_object* v_res_6188_; 
v_isSetupFailure_boxed_6187_ = lean_unbox(v_isSetupFailure_6185_);
v_res_6188_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6180_, v_name_6181_, v_moduleUri_6182_, v_version_6183_, v_directImports_6184_, v_isSetupFailure_boxed_6187_);
lean_dec_ref(v_directImports_6184_);
return v_res_6188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6189_, lean_object* v_t_6190_, lean_object* v_k_6191_){
_start:
{
lean_object* v___x_6192_; 
v___x_6192_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6190_, v_k_6191_);
return v___x_6192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6193_, lean_object* v_t_6194_, lean_object* v_k_6195_){
_start:
{
lean_object* v_res_6196_; 
v_res_6196_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6193_, v_t_6194_, v_k_6195_);
lean_dec(v_k_6195_);
lean_dec(v_t_6194_);
return v_res_6196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6197_, lean_object* v_____s_6198_){
_start:
{
lean_object* v_fst_6199_; lean_object* v_snd_6200_; lean_object* v_r_6201_; lean_object* v___x_6202_; 
v_fst_6199_ = lean_ctor_get(v_x_6197_, 0);
lean_inc(v_fst_6199_);
v_snd_6200_ = lean_ctor_get(v_x_6197_, 1);
lean_inc(v_snd_6200_);
lean_dec_ref(v_x_6197_);
v_r_6201_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6199_, v_snd_6200_, v_____s_6198_);
v___x_6202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6202_, 0, v_r_6201_);
return v___x_6202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6203_, lean_object* v_k_6204_, lean_object* v_fallback_6205_){
_start:
{
if (lean_obj_tag(v_t_6203_) == 0)
{
lean_object* v_k_6206_; lean_object* v_v_6207_; lean_object* v_l_6208_; lean_object* v_r_6209_; uint8_t v___x_6210_; 
v_k_6206_ = lean_ctor_get(v_t_6203_, 1);
v_v_6207_ = lean_ctor_get(v_t_6203_, 2);
v_l_6208_ = lean_ctor_get(v_t_6203_, 3);
v_r_6209_ = lean_ctor_get(v_t_6203_, 4);
v___x_6210_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6204_, v_k_6206_);
switch(v___x_6210_)
{
case 0:
{
v_t_6203_ = v_l_6208_;
goto _start;
}
case 1:
{
lean_inc(v_v_6207_);
return v_v_6207_;
}
default: 
{
v_t_6203_ = v_r_6209_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6205_);
return v_fallback_6205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6213_, lean_object* v_k_6214_, lean_object* v_fallback_6215_){
_start:
{
lean_object* v_res_6216_; 
v_res_6216_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6213_, v_k_6214_, v_fallback_6215_);
lean_dec(v_fallback_6215_);
lean_dec_ref(v_k_6214_);
lean_dec(v_t_6213_);
return v_res_6216_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6217_, lean_object* v_x_6218_){
_start:
{
if (lean_obj_tag(v_x_6218_) == 0)
{
lean_object* v_k_6219_; lean_object* v_v_6220_; lean_object* v_l_6221_; lean_object* v_r_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; 
v_k_6219_ = lean_ctor_get(v_x_6218_, 1);
lean_inc(v_k_6219_);
v_v_6220_ = lean_ctor_get(v_x_6218_, 2);
lean_inc(v_v_6220_);
v_l_6221_ = lean_ctor_get(v_x_6218_, 3);
lean_inc(v_l_6221_);
v_r_6222_ = lean_ctor_get(v_x_6218_, 4);
lean_inc(v_r_6222_);
lean_dec_ref_known(v_x_6218_, 5);
v___x_6223_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6217_, v_l_6221_);
v___x_6224_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6225_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6223_, v_k_6219_, v___x_6224_);
v___x_6226_ = l_Lean_Lsp_RefInfo_merge(v___x_6225_, v_v_6220_);
v___x_6227_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6219_, v___x_6226_, v___x_6223_);
v_init_6217_ = v___x_6227_;
v_x_6218_ = v_r_6222_;
goto _start;
}
else
{
return v_init_6217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6230_, lean_object* v_name_6231_, lean_object* v_moduleUri_6232_, lean_object* v_version_6233_, lean_object* v_refs_6234_, lean_object* v_decls_6235_){
_start:
{
lean_object* v_ileans_6237_; lean_object* v_workers_6238_; lean_object* v___x_6239_; 
v_ileans_6237_ = lean_ctor_get(v_self_6230_, 0);
v_workers_6238_ = lean_ctor_get(v_self_6230_, 1);
v___x_6239_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6238_, v_name_6231_);
if (lean_obj_tag(v___x_6239_) == 1)
{
lean_object* v_val_6240_; lean_object* v___x_6242_; uint8_t v_isShared_6243_; uint8_t v_isSharedCheck_6288_; 
v_val_6240_ = lean_ctor_get(v___x_6239_, 0);
v_isSharedCheck_6288_ = !lean_is_exclusive(v___x_6239_);
if (v_isSharedCheck_6288_ == 0)
{
v___x_6242_ = v___x_6239_;
v_isShared_6243_ = v_isSharedCheck_6288_;
goto v_resetjp_6241_;
}
else
{
lean_inc(v_val_6240_);
lean_dec(v___x_6239_);
v___x_6242_ = lean_box(0);
v_isShared_6243_ = v_isSharedCheck_6288_;
goto v_resetjp_6241_;
}
v_resetjp_6241_:
{
lean_object* v_version_6244_; lean_object* v_directImports_6245_; lean_object* v_isSetupFailure_x3f_6246_; lean_object* v_refs_6247_; lean_object* v_decls_6248_; lean_object* v___x_6250_; uint8_t v_isShared_6251_; uint8_t v_isSharedCheck_6286_; 
v_version_6244_ = lean_ctor_get(v_val_6240_, 1);
v_directImports_6245_ = lean_ctor_get(v_val_6240_, 2);
v_isSetupFailure_x3f_6246_ = lean_ctor_get(v_val_6240_, 3);
v_refs_6247_ = lean_ctor_get(v_val_6240_, 4);
v_decls_6248_ = lean_ctor_get(v_val_6240_, 5);
v_isSharedCheck_6286_ = !lean_is_exclusive(v_val_6240_);
if (v_isSharedCheck_6286_ == 0)
{
lean_object* v_unused_6287_; 
v_unused_6287_ = lean_ctor_get(v_val_6240_, 0);
lean_dec(v_unused_6287_);
v___x_6250_ = v_val_6240_;
v_isShared_6251_ = v_isSharedCheck_6286_;
goto v_resetjp_6249_;
}
else
{
lean_inc(v_decls_6248_);
lean_inc(v_refs_6247_);
lean_inc(v_isSetupFailure_x3f_6246_);
lean_inc(v_directImports_6245_);
lean_inc(v_version_6244_);
lean_dec(v_val_6240_);
v___x_6250_ = lean_box(0);
v_isShared_6251_ = v_isSharedCheck_6286_;
goto v_resetjp_6249_;
}
v_resetjp_6249_:
{
uint8_t v___x_6252_; 
v___x_6252_ = lean_nat_dec_lt(v_version_6233_, v_version_6244_);
if (v___x_6252_ == 0)
{
lean_object* v___x_6254_; uint8_t v_isShared_6255_; uint8_t v_isSharedCheck_6280_; 
lean_inc(v_workers_6238_);
lean_inc(v_ileans_6237_);
v_isSharedCheck_6280_ = !lean_is_exclusive(v_self_6230_);
if (v_isSharedCheck_6280_ == 0)
{
lean_object* v_unused_6281_; lean_object* v_unused_6282_; 
v_unused_6281_ = lean_ctor_get(v_self_6230_, 1);
lean_dec(v_unused_6281_);
v_unused_6282_ = lean_ctor_get(v_self_6230_, 0);
lean_dec(v_unused_6282_);
v___x_6254_ = v_self_6230_;
v_isShared_6255_ = v_isSharedCheck_6280_;
goto v_resetjp_6253_;
}
else
{
lean_dec(v_self_6230_);
v___x_6254_ = lean_box(0);
v_isShared_6255_ = v_isSharedCheck_6280_;
goto v_resetjp_6253_;
}
v_resetjp_6253_:
{
uint8_t v___x_6256_; 
v___x_6256_ = lean_nat_dec_eq(v_version_6233_, v_version_6244_);
lean_dec(v_version_6244_);
if (v___x_6256_ == 0)
{
lean_object* v___x_6258_; 
lean_dec(v_decls_6248_);
lean_dec(v_refs_6247_);
if (v_isShared_6251_ == 0)
{
lean_ctor_set(v___x_6250_, 5, v_decls_6235_);
lean_ctor_set(v___x_6250_, 4, v_refs_6234_);
lean_ctor_set(v___x_6250_, 1, v_version_6233_);
lean_ctor_set(v___x_6250_, 0, v_moduleUri_6232_);
v___x_6258_ = v___x_6250_;
goto v_reusejp_6257_;
}
else
{
lean_object* v_reuseFailAlloc_6266_; 
v_reuseFailAlloc_6266_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6266_, 0, v_moduleUri_6232_);
lean_ctor_set(v_reuseFailAlloc_6266_, 1, v_version_6233_);
lean_ctor_set(v_reuseFailAlloc_6266_, 2, v_directImports_6245_);
lean_ctor_set(v_reuseFailAlloc_6266_, 3, v_isSetupFailure_x3f_6246_);
lean_ctor_set(v_reuseFailAlloc_6266_, 4, v_refs_6234_);
lean_ctor_set(v_reuseFailAlloc_6266_, 5, v_decls_6235_);
v___x_6258_ = v_reuseFailAlloc_6266_;
goto v_reusejp_6257_;
}
v_reusejp_6257_:
{
lean_object* v___x_6259_; lean_object* v___x_6261_; 
v___x_6259_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6231_, v___x_6258_, v_workers_6238_);
if (v_isShared_6255_ == 0)
{
lean_ctor_set(v___x_6254_, 1, v___x_6259_);
v___x_6261_ = v___x_6254_;
goto v_reusejp_6260_;
}
else
{
lean_object* v_reuseFailAlloc_6265_; 
v_reuseFailAlloc_6265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_ileans_6237_);
lean_ctor_set(v_reuseFailAlloc_6265_, 1, v___x_6259_);
v___x_6261_ = v_reuseFailAlloc_6265_;
goto v_reusejp_6260_;
}
v_reusejp_6260_:
{
lean_object* v___x_6263_; 
if (v_isShared_6243_ == 0)
{
lean_ctor_set_tag(v___x_6242_, 0);
lean_ctor_set(v___x_6242_, 0, v___x_6261_);
v___x_6263_ = v___x_6242_;
goto v_reusejp_6262_;
}
else
{
lean_object* v_reuseFailAlloc_6264_; 
v_reuseFailAlloc_6264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6264_, 0, v___x_6261_);
v___x_6263_ = v_reuseFailAlloc_6264_;
goto v_reusejp_6262_;
}
v_reusejp_6262_:
{
return v___x_6263_;
}
}
}
}
else
{
lean_object* v___f_6267_; lean_object* v_mergedRefs_6268_; lean_object* v_mergedDecls_6269_; lean_object* v___x_6271_; 
v___f_6267_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6268_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6247_, v_refs_6234_);
v_mergedDecls_6269_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6235_, v_decls_6248_, v___f_6267_);
lean_dec(v_decls_6235_);
if (v_isShared_6251_ == 0)
{
lean_ctor_set(v___x_6250_, 5, v_mergedDecls_6269_);
lean_ctor_set(v___x_6250_, 4, v_mergedRefs_6268_);
lean_ctor_set(v___x_6250_, 1, v_version_6233_);
lean_ctor_set(v___x_6250_, 0, v_moduleUri_6232_);
v___x_6271_ = v___x_6250_;
goto v_reusejp_6270_;
}
else
{
lean_object* v_reuseFailAlloc_6279_; 
v_reuseFailAlloc_6279_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6279_, 0, v_moduleUri_6232_);
lean_ctor_set(v_reuseFailAlloc_6279_, 1, v_version_6233_);
lean_ctor_set(v_reuseFailAlloc_6279_, 2, v_directImports_6245_);
lean_ctor_set(v_reuseFailAlloc_6279_, 3, v_isSetupFailure_x3f_6246_);
lean_ctor_set(v_reuseFailAlloc_6279_, 4, v_mergedRefs_6268_);
lean_ctor_set(v_reuseFailAlloc_6279_, 5, v_mergedDecls_6269_);
v___x_6271_ = v_reuseFailAlloc_6279_;
goto v_reusejp_6270_;
}
v_reusejp_6270_:
{
lean_object* v___x_6272_; lean_object* v___x_6274_; 
v___x_6272_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6231_, v___x_6271_, v_workers_6238_);
if (v_isShared_6255_ == 0)
{
lean_ctor_set(v___x_6254_, 1, v___x_6272_);
v___x_6274_ = v___x_6254_;
goto v_reusejp_6273_;
}
else
{
lean_object* v_reuseFailAlloc_6278_; 
v_reuseFailAlloc_6278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6278_, 0, v_ileans_6237_);
lean_ctor_set(v_reuseFailAlloc_6278_, 1, v___x_6272_);
v___x_6274_ = v_reuseFailAlloc_6278_;
goto v_reusejp_6273_;
}
v_reusejp_6273_:
{
lean_object* v___x_6276_; 
if (v_isShared_6243_ == 0)
{
lean_ctor_set_tag(v___x_6242_, 0);
lean_ctor_set(v___x_6242_, 0, v___x_6274_);
v___x_6276_ = v___x_6242_;
goto v_reusejp_6275_;
}
else
{
lean_object* v_reuseFailAlloc_6277_; 
v_reuseFailAlloc_6277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6277_, 0, v___x_6274_);
v___x_6276_ = v_reuseFailAlloc_6277_;
goto v_reusejp_6275_;
}
v_reusejp_6275_:
{
return v___x_6276_;
}
}
}
}
}
}
else
{
lean_object* v___x_6284_; 
lean_del_object(v___x_6250_);
lean_dec(v_decls_6248_);
lean_dec(v_refs_6247_);
lean_dec(v_isSetupFailure_x3f_6246_);
lean_dec_ref(v_directImports_6245_);
lean_dec(v_version_6244_);
lean_dec(v_decls_6235_);
lean_dec(v_refs_6234_);
lean_dec(v_version_6233_);
lean_dec_ref(v_moduleUri_6232_);
lean_dec(v_name_6231_);
if (v_isShared_6243_ == 0)
{
lean_ctor_set_tag(v___x_6242_, 0);
lean_ctor_set(v___x_6242_, 0, v_self_6230_);
v___x_6284_ = v___x_6242_;
goto v_reusejp_6283_;
}
else
{
lean_object* v_reuseFailAlloc_6285_; 
v_reuseFailAlloc_6285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6285_, 0, v_self_6230_);
v___x_6284_ = v_reuseFailAlloc_6285_;
goto v_reusejp_6283_;
}
v_reusejp_6283_:
{
return v___x_6284_;
}
}
}
}
}
else
{
lean_object* v___x_6290_; uint8_t v_isShared_6291_; uint8_t v_isSharedCheck_6300_; 
lean_inc(v_workers_6238_);
lean_inc(v_ileans_6237_);
lean_dec(v___x_6239_);
v_isSharedCheck_6300_ = !lean_is_exclusive(v_self_6230_);
if (v_isSharedCheck_6300_ == 0)
{
lean_object* v_unused_6301_; lean_object* v_unused_6302_; 
v_unused_6301_ = lean_ctor_get(v_self_6230_, 1);
lean_dec(v_unused_6301_);
v_unused_6302_ = lean_ctor_get(v_self_6230_, 0);
lean_dec(v_unused_6302_);
v___x_6290_ = v_self_6230_;
v_isShared_6291_ = v_isSharedCheck_6300_;
goto v_resetjp_6289_;
}
else
{
lean_dec(v_self_6230_);
v___x_6290_ = lean_box(0);
v_isShared_6291_ = v_isSharedCheck_6300_;
goto v_resetjp_6289_;
}
v_resetjp_6289_:
{
lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6297_; 
v___x_6292_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6293_ = lean_box(0);
v___x_6294_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6294_, 0, v_moduleUri_6232_);
lean_ctor_set(v___x_6294_, 1, v_version_6233_);
lean_ctor_set(v___x_6294_, 2, v___x_6292_);
lean_ctor_set(v___x_6294_, 3, v___x_6293_);
lean_ctor_set(v___x_6294_, 4, v_refs_6234_);
lean_ctor_set(v___x_6294_, 5, v_decls_6235_);
v___x_6295_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6231_, v___x_6294_, v_workers_6238_);
if (v_isShared_6291_ == 0)
{
lean_ctor_set(v___x_6290_, 1, v___x_6295_);
v___x_6297_ = v___x_6290_;
goto v_reusejp_6296_;
}
else
{
lean_object* v_reuseFailAlloc_6299_; 
v_reuseFailAlloc_6299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6299_, 0, v_ileans_6237_);
lean_ctor_set(v_reuseFailAlloc_6299_, 1, v___x_6295_);
v___x_6297_ = v_reuseFailAlloc_6299_;
goto v_reusejp_6296_;
}
v_reusejp_6296_:
{
lean_object* v___x_6298_; 
v___x_6298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6298_, 0, v___x_6297_);
return v___x_6298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6303_, lean_object* v_name_6304_, lean_object* v_moduleUri_6305_, lean_object* v_version_6306_, lean_object* v_refs_6307_, lean_object* v_decls_6308_, lean_object* v_a_6309_){
_start:
{
lean_object* v_res_6310_; 
v_res_6310_ = l_Lean_Server_References_updateWorkerRefs(v_self_6303_, v_name_6304_, v_moduleUri_6305_, v_version_6306_, v_refs_6307_, v_decls_6308_);
return v_res_6310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6311_, lean_object* v_t_6312_, lean_object* v_k_6313_, lean_object* v_fallback_6314_){
_start:
{
lean_object* v___x_6315_; 
v___x_6315_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6312_, v_k_6313_, v_fallback_6314_);
return v___x_6315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6316_, lean_object* v_t_6317_, lean_object* v_k_6318_, lean_object* v_fallback_6319_){
_start:
{
lean_object* v_res_6320_; 
v_res_6320_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6316_, v_t_6317_, v_k_6318_, v_fallback_6319_);
lean_dec(v_fallback_6319_);
lean_dec_ref(v_k_6318_);
lean_dec(v_t_6317_);
return v_res_6320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6321_, lean_object* v_t_6322_){
_start:
{
lean_object* v___x_6323_; 
v___x_6323_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6321_, v_t_6322_);
return v___x_6323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6324_, lean_object* v_name_6325_, lean_object* v_moduleUri_6326_, lean_object* v_version_6327_, lean_object* v_refs_6328_, lean_object* v_decls_6329_){
_start:
{
lean_object* v_ileans_6331_; lean_object* v_workers_6332_; lean_object* v___x_6333_; 
v_ileans_6331_ = lean_ctor_get(v_self_6324_, 0);
v_workers_6332_ = lean_ctor_get(v_self_6324_, 1);
v___x_6333_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6332_, v_name_6325_);
if (lean_obj_tag(v___x_6333_) == 1)
{
lean_object* v_val_6334_; lean_object* v___x_6336_; uint8_t v_isShared_6337_; uint8_t v_isSharedCheck_6368_; 
v_val_6334_ = lean_ctor_get(v___x_6333_, 0);
v_isSharedCheck_6368_ = !lean_is_exclusive(v___x_6333_);
if (v_isSharedCheck_6368_ == 0)
{
v___x_6336_ = v___x_6333_;
v_isShared_6337_ = v_isSharedCheck_6368_;
goto v_resetjp_6335_;
}
else
{
lean_inc(v_val_6334_);
lean_dec(v___x_6333_);
v___x_6336_ = lean_box(0);
v_isShared_6337_ = v_isSharedCheck_6368_;
goto v_resetjp_6335_;
}
v_resetjp_6335_:
{
lean_object* v_version_6338_; lean_object* v_directImports_6339_; lean_object* v_isSetupFailure_x3f_6340_; lean_object* v___x_6342_; uint8_t v_isShared_6343_; uint8_t v_isSharedCheck_6364_; 
v_version_6338_ = lean_ctor_get(v_val_6334_, 1);
v_directImports_6339_ = lean_ctor_get(v_val_6334_, 2);
v_isSetupFailure_x3f_6340_ = lean_ctor_get(v_val_6334_, 3);
v_isSharedCheck_6364_ = !lean_is_exclusive(v_val_6334_);
if (v_isSharedCheck_6364_ == 0)
{
lean_object* v_unused_6365_; lean_object* v_unused_6366_; lean_object* v_unused_6367_; 
v_unused_6365_ = lean_ctor_get(v_val_6334_, 5);
lean_dec(v_unused_6365_);
v_unused_6366_ = lean_ctor_get(v_val_6334_, 4);
lean_dec(v_unused_6366_);
v_unused_6367_ = lean_ctor_get(v_val_6334_, 0);
lean_dec(v_unused_6367_);
v___x_6342_ = v_val_6334_;
v_isShared_6343_ = v_isSharedCheck_6364_;
goto v_resetjp_6341_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6340_);
lean_inc(v_directImports_6339_);
lean_inc(v_version_6338_);
lean_dec(v_val_6334_);
v___x_6342_ = lean_box(0);
v_isShared_6343_ = v_isSharedCheck_6364_;
goto v_resetjp_6341_;
}
v_resetjp_6341_:
{
uint8_t v___x_6344_; 
v___x_6344_ = lean_nat_dec_lt(v_version_6327_, v_version_6338_);
lean_dec(v_version_6338_);
if (v___x_6344_ == 0)
{
lean_object* v___x_6346_; uint8_t v_isShared_6347_; uint8_t v_isSharedCheck_6358_; 
lean_inc(v_workers_6332_);
lean_inc(v_ileans_6331_);
v_isSharedCheck_6358_ = !lean_is_exclusive(v_self_6324_);
if (v_isSharedCheck_6358_ == 0)
{
lean_object* v_unused_6359_; lean_object* v_unused_6360_; 
v_unused_6359_ = lean_ctor_get(v_self_6324_, 1);
lean_dec(v_unused_6359_);
v_unused_6360_ = lean_ctor_get(v_self_6324_, 0);
lean_dec(v_unused_6360_);
v___x_6346_ = v_self_6324_;
v_isShared_6347_ = v_isSharedCheck_6358_;
goto v_resetjp_6345_;
}
else
{
lean_dec(v_self_6324_);
v___x_6346_ = lean_box(0);
v_isShared_6347_ = v_isSharedCheck_6358_;
goto v_resetjp_6345_;
}
v_resetjp_6345_:
{
lean_object* v___x_6349_; 
if (v_isShared_6343_ == 0)
{
lean_ctor_set(v___x_6342_, 5, v_decls_6329_);
lean_ctor_set(v___x_6342_, 4, v_refs_6328_);
lean_ctor_set(v___x_6342_, 1, v_version_6327_);
lean_ctor_set(v___x_6342_, 0, v_moduleUri_6326_);
v___x_6349_ = v___x_6342_;
goto v_reusejp_6348_;
}
else
{
lean_object* v_reuseFailAlloc_6357_; 
v_reuseFailAlloc_6357_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_moduleUri_6326_);
lean_ctor_set(v_reuseFailAlloc_6357_, 1, v_version_6327_);
lean_ctor_set(v_reuseFailAlloc_6357_, 2, v_directImports_6339_);
lean_ctor_set(v_reuseFailAlloc_6357_, 3, v_isSetupFailure_x3f_6340_);
lean_ctor_set(v_reuseFailAlloc_6357_, 4, v_refs_6328_);
lean_ctor_set(v_reuseFailAlloc_6357_, 5, v_decls_6329_);
v___x_6349_ = v_reuseFailAlloc_6357_;
goto v_reusejp_6348_;
}
v_reusejp_6348_:
{
lean_object* v___x_6350_; lean_object* v___x_6352_; 
v___x_6350_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6325_, v___x_6349_, v_workers_6332_);
if (v_isShared_6347_ == 0)
{
lean_ctor_set(v___x_6346_, 1, v___x_6350_);
v___x_6352_ = v___x_6346_;
goto v_reusejp_6351_;
}
else
{
lean_object* v_reuseFailAlloc_6356_; 
v_reuseFailAlloc_6356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6356_, 0, v_ileans_6331_);
lean_ctor_set(v_reuseFailAlloc_6356_, 1, v___x_6350_);
v___x_6352_ = v_reuseFailAlloc_6356_;
goto v_reusejp_6351_;
}
v_reusejp_6351_:
{
lean_object* v___x_6354_; 
if (v_isShared_6337_ == 0)
{
lean_ctor_set_tag(v___x_6336_, 0);
lean_ctor_set(v___x_6336_, 0, v___x_6352_);
v___x_6354_ = v___x_6336_;
goto v_reusejp_6353_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v___x_6352_);
v___x_6354_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6353_;
}
v_reusejp_6353_:
{
return v___x_6354_;
}
}
}
}
}
else
{
lean_object* v___x_6362_; 
lean_del_object(v___x_6342_);
lean_dec(v_isSetupFailure_x3f_6340_);
lean_dec_ref(v_directImports_6339_);
lean_dec(v_decls_6329_);
lean_dec(v_refs_6328_);
lean_dec(v_version_6327_);
lean_dec_ref(v_moduleUri_6326_);
lean_dec(v_name_6325_);
if (v_isShared_6337_ == 0)
{
lean_ctor_set_tag(v___x_6336_, 0);
lean_ctor_set(v___x_6336_, 0, v_self_6324_);
v___x_6362_ = v___x_6336_;
goto v_reusejp_6361_;
}
else
{
lean_object* v_reuseFailAlloc_6363_; 
v_reuseFailAlloc_6363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6363_, 0, v_self_6324_);
v___x_6362_ = v_reuseFailAlloc_6363_;
goto v_reusejp_6361_;
}
v_reusejp_6361_:
{
return v___x_6362_;
}
}
}
}
}
else
{
lean_object* v___x_6370_; uint8_t v_isShared_6371_; uint8_t v_isSharedCheck_6380_; 
lean_inc(v_workers_6332_);
lean_inc(v_ileans_6331_);
lean_dec(v___x_6333_);
v_isSharedCheck_6380_ = !lean_is_exclusive(v_self_6324_);
if (v_isSharedCheck_6380_ == 0)
{
lean_object* v_unused_6381_; lean_object* v_unused_6382_; 
v_unused_6381_ = lean_ctor_get(v_self_6324_, 1);
lean_dec(v_unused_6381_);
v_unused_6382_ = lean_ctor_get(v_self_6324_, 0);
lean_dec(v_unused_6382_);
v___x_6370_ = v_self_6324_;
v_isShared_6371_ = v_isSharedCheck_6380_;
goto v_resetjp_6369_;
}
else
{
lean_dec(v_self_6324_);
v___x_6370_ = lean_box(0);
v_isShared_6371_ = v_isSharedCheck_6380_;
goto v_resetjp_6369_;
}
v_resetjp_6369_:
{
lean_object* v___x_6372_; lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; lean_object* v___x_6377_; 
v___x_6372_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6373_ = lean_box(0);
v___x_6374_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6374_, 0, v_moduleUri_6326_);
lean_ctor_set(v___x_6374_, 1, v_version_6327_);
lean_ctor_set(v___x_6374_, 2, v___x_6372_);
lean_ctor_set(v___x_6374_, 3, v___x_6373_);
lean_ctor_set(v___x_6374_, 4, v_refs_6328_);
lean_ctor_set(v___x_6374_, 5, v_decls_6329_);
v___x_6375_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6325_, v___x_6374_, v_workers_6332_);
if (v_isShared_6371_ == 0)
{
lean_ctor_set(v___x_6370_, 1, v___x_6375_);
v___x_6377_ = v___x_6370_;
goto v_reusejp_6376_;
}
else
{
lean_object* v_reuseFailAlloc_6379_; 
v_reuseFailAlloc_6379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6379_, 0, v_ileans_6331_);
lean_ctor_set(v_reuseFailAlloc_6379_, 1, v___x_6375_);
v___x_6377_ = v_reuseFailAlloc_6379_;
goto v_reusejp_6376_;
}
v_reusejp_6376_:
{
lean_object* v___x_6378_; 
v___x_6378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6378_, 0, v___x_6377_);
return v___x_6378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6383_, lean_object* v_name_6384_, lean_object* v_moduleUri_6385_, lean_object* v_version_6386_, lean_object* v_refs_6387_, lean_object* v_decls_6388_, lean_object* v_a_6389_){
_start:
{
lean_object* v_res_6390_; 
v_res_6390_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6383_, v_name_6384_, v_moduleUri_6385_, v_version_6386_, v_refs_6387_, v_decls_6388_);
return v_res_6390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6391_, lean_object* v_name_6392_){
_start:
{
lean_object* v_ileans_6393_; lean_object* v_workers_6394_; lean_object* v___x_6396_; uint8_t v_isShared_6397_; uint8_t v_isSharedCheck_6402_; 
v_ileans_6393_ = lean_ctor_get(v_self_6391_, 0);
v_workers_6394_ = lean_ctor_get(v_self_6391_, 1);
v_isSharedCheck_6402_ = !lean_is_exclusive(v_self_6391_);
if (v_isSharedCheck_6402_ == 0)
{
v___x_6396_ = v_self_6391_;
v_isShared_6397_ = v_isSharedCheck_6402_;
goto v_resetjp_6395_;
}
else
{
lean_inc(v_workers_6394_);
lean_inc(v_ileans_6393_);
lean_dec(v_self_6391_);
v___x_6396_ = lean_box(0);
v_isShared_6397_ = v_isSharedCheck_6402_;
goto v_resetjp_6395_;
}
v_resetjp_6395_:
{
lean_object* v___x_6398_; lean_object* v___x_6400_; 
v___x_6398_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6392_, v_workers_6394_);
if (v_isShared_6397_ == 0)
{
lean_ctor_set(v___x_6396_, 1, v___x_6398_);
v___x_6400_ = v___x_6396_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6401_; 
v_reuseFailAlloc_6401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6401_, 0, v_ileans_6393_);
lean_ctor_set(v_reuseFailAlloc_6401_, 1, v___x_6398_);
v___x_6400_ = v_reuseFailAlloc_6401_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
return v___x_6400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6403_, lean_object* v_name_6404_){
_start:
{
lean_object* v_res_6405_; 
v_res_6405_ = l_Lean_Server_References_removeWorkerRefs(v_self_6403_, v_name_6404_);
lean_dec(v_name_6404_);
return v_res_6405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6406_, lean_object* v_x_6407_){
_start:
{
if (lean_obj_tag(v_x_6407_) == 0)
{
lean_object* v_v_6408_; lean_object* v_k_6409_; lean_object* v_l_6410_; lean_object* v_r_6411_; lean_object* v_moduleUri_6412_; lean_object* v_refs_6413_; lean_object* v_decls_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; 
v_v_6408_ = lean_ctor_get(v_x_6407_, 2);
lean_inc(v_v_6408_);
v_k_6409_ = lean_ctor_get(v_x_6407_, 1);
lean_inc(v_k_6409_);
v_l_6410_ = lean_ctor_get(v_x_6407_, 3);
lean_inc(v_l_6410_);
v_r_6411_ = lean_ctor_get(v_x_6407_, 4);
lean_inc(v_r_6411_);
lean_dec_ref_known(v_x_6407_, 5);
v_moduleUri_6412_ = lean_ctor_get(v_v_6408_, 0);
lean_inc_ref(v_moduleUri_6412_);
v_refs_6413_ = lean_ctor_get(v_v_6408_, 3);
lean_inc(v_refs_6413_);
v_decls_6414_ = lean_ctor_get(v_v_6408_, 4);
lean_inc(v_decls_6414_);
lean_dec(v_v_6408_);
v___x_6415_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6406_, v_l_6410_);
v___x_6416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6416_, 0, v_refs_6413_);
lean_ctor_set(v___x_6416_, 1, v_decls_6414_);
v___x_6417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6417_, 0, v_moduleUri_6412_);
lean_ctor_set(v___x_6417_, 1, v___x_6416_);
v___x_6418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6409_, v___x_6417_, v___x_6415_);
v_init_6406_ = v___x_6418_;
v_x_6407_ = v_r_6411_;
goto _start;
}
else
{
return v_init_6406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6420_, lean_object* v_x_6421_){
_start:
{
if (lean_obj_tag(v_x_6421_) == 0)
{
lean_object* v_v_6422_; lean_object* v_k_6423_; lean_object* v_l_6424_; lean_object* v_r_6425_; lean_object* v_moduleUri_6426_; lean_object* v_refs_6427_; lean_object* v_decls_6428_; lean_object* v___x_6429_; uint8_t v___x_6430_; 
v_v_6422_ = lean_ctor_get(v_x_6421_, 2);
lean_inc(v_v_6422_);
v_k_6423_ = lean_ctor_get(v_x_6421_, 1);
lean_inc(v_k_6423_);
v_l_6424_ = lean_ctor_get(v_x_6421_, 3);
lean_inc(v_l_6424_);
v_r_6425_ = lean_ctor_get(v_x_6421_, 4);
lean_inc(v_r_6425_);
lean_dec_ref_known(v_x_6421_, 5);
v_moduleUri_6426_ = lean_ctor_get(v_v_6422_, 0);
lean_inc_ref(v_moduleUri_6426_);
v_refs_6427_ = lean_ctor_get(v_v_6422_, 4);
lean_inc(v_refs_6427_);
v_decls_6428_ = lean_ctor_get(v_v_6422_, 5);
lean_inc(v_decls_6428_);
v___x_6429_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6420_, v_l_6424_);
v___x_6430_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6422_);
lean_dec(v_v_6422_);
if (v___x_6430_ == 0)
{
lean_dec(v_decls_6428_);
lean_dec(v_refs_6427_);
lean_dec_ref(v_moduleUri_6426_);
lean_dec(v_k_6423_);
v_init_6420_ = v___x_6429_;
v_x_6421_ = v_r_6425_;
goto _start;
}
else
{
lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; 
v___x_6432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6432_, 0, v_refs_6427_);
lean_ctor_set(v___x_6432_, 1, v_decls_6428_);
v___x_6433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6433_, 0, v_moduleUri_6426_);
lean_ctor_set(v___x_6433_, 1, v___x_6432_);
v___x_6434_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6423_, v___x_6433_, v___x_6429_);
v_init_6420_ = v___x_6434_;
v_x_6421_ = v_r_6425_;
goto _start;
}
}
else
{
return v_init_6420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6436_){
_start:
{
lean_object* v_ileans_6437_; lean_object* v_workers_6438_; lean_object* v___x_6439_; lean_object* v_ileanRefs_6440_; lean_object* v___x_6441_; 
v_ileans_6437_ = lean_ctor_get(v_self_6436_, 0);
lean_inc(v_ileans_6437_);
v_workers_6438_ = lean_ctor_get(v_self_6436_, 1);
lean_inc(v_workers_6438_);
lean_dec_ref(v_self_6436_);
v___x_6439_ = lean_box(1);
v_ileanRefs_6440_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6439_, v_ileans_6437_);
v___x_6441_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6440_, v_workers_6438_);
return v___x_6441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6442_, lean_object* v_t_6443_){
_start:
{
lean_object* v___x_6444_; 
v___x_6444_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6442_, v_t_6443_);
return v___x_6444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6445_, lean_object* v_t_6446_){
_start:
{
lean_object* v___x_6447_; 
v___x_6447_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6445_, v_t_6446_);
return v___x_6447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6448_, lean_object* v_x_6449_){
_start:
{
if (lean_obj_tag(v_x_6449_) == 0)
{
lean_object* v_k_6450_; lean_object* v_v_6451_; lean_object* v_l_6452_; lean_object* v_r_6453_; lean_object* v___x_6454_; lean_object* v_a_6455_; uint8_t v___x_6456_; 
v_k_6450_ = lean_ctor_get(v_x_6449_, 1);
lean_inc(v_k_6450_);
v_v_6451_ = lean_ctor_get(v_x_6449_, 2);
lean_inc(v_v_6451_);
v_l_6452_ = lean_ctor_get(v_x_6449_, 3);
lean_inc(v_l_6452_);
v_r_6453_ = lean_ctor_get(v_x_6449_, 4);
lean_inc(v_r_6453_);
lean_dec_ref_known(v_x_6449_, 5);
v___x_6454_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6448_, v_l_6452_);
v_a_6455_ = lean_ctor_get(v___x_6454_, 0);
lean_inc(v_a_6455_);
lean_dec_ref(v___x_6454_);
v___x_6456_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6451_);
if (v___x_6456_ == 0)
{
lean_dec(v_v_6451_);
lean_dec(v_k_6450_);
v_init_6448_ = v_a_6455_;
v_x_6449_ = v_r_6453_;
goto _start;
}
else
{
lean_object* v_moduleUri_6458_; lean_object* v_directImports_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; 
v_moduleUri_6458_ = lean_ctor_get(v_v_6451_, 0);
lean_inc_ref(v_moduleUri_6458_);
v_directImports_6459_ = lean_ctor_get(v_v_6451_, 2);
lean_inc_ref(v_directImports_6459_);
lean_dec(v_v_6451_);
v___x_6460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6460_, 0, v_moduleUri_6458_);
lean_ctor_set(v___x_6460_, 1, v_directImports_6459_);
v___x_6461_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6450_, v___x_6460_, v_a_6455_);
v_init_6448_ = v___x_6461_;
v_x_6449_ = v_r_6453_;
goto _start;
}
}
else
{
lean_object* v___x_6463_; 
v___x_6463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6463_, 0, v_init_6448_);
return v___x_6463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6464_, lean_object* v_x_6465_){
_start:
{
if (lean_obj_tag(v_x_6465_) == 0)
{
lean_object* v_k_6466_; lean_object* v_v_6467_; lean_object* v_l_6468_; lean_object* v_r_6469_; lean_object* v___x_6470_; lean_object* v_a_6471_; lean_object* v_moduleUri_6472_; lean_object* v_directImports_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; 
v_k_6466_ = lean_ctor_get(v_x_6465_, 1);
lean_inc(v_k_6466_);
v_v_6467_ = lean_ctor_get(v_x_6465_, 2);
lean_inc(v_v_6467_);
v_l_6468_ = lean_ctor_get(v_x_6465_, 3);
lean_inc(v_l_6468_);
v_r_6469_ = lean_ctor_get(v_x_6465_, 4);
lean_inc(v_r_6469_);
lean_dec_ref_known(v_x_6465_, 5);
v___x_6470_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6464_, v_l_6468_);
v_a_6471_ = lean_ctor_get(v___x_6470_, 0);
lean_inc(v_a_6471_);
lean_dec_ref(v___x_6470_);
v_moduleUri_6472_ = lean_ctor_get(v_v_6467_, 0);
lean_inc_ref(v_moduleUri_6472_);
v_directImports_6473_ = lean_ctor_get(v_v_6467_, 2);
lean_inc_ref(v_directImports_6473_);
lean_dec(v_v_6467_);
v___x_6474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6474_, 0, v_moduleUri_6472_);
lean_ctor_set(v___x_6474_, 1, v_directImports_6473_);
v___x_6475_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6466_, v___x_6474_, v_a_6471_);
v_init_6464_ = v___x_6475_;
v_x_6465_ = v_r_6469_;
goto _start;
}
else
{
lean_object* v___x_6477_; 
v___x_6477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6477_, 0, v_init_6464_);
return v___x_6477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6478_){
_start:
{
lean_object* v_ileans_6479_; lean_object* v_workers_6480_; lean_object* v___y_6482_; lean_object* v_allDirectImports_6485_; lean_object* v___x_6486_; lean_object* v_a_6487_; 
v_ileans_6479_ = lean_ctor_get(v_self_6478_, 0);
lean_inc(v_ileans_6479_);
v_workers_6480_ = lean_ctor_get(v_self_6478_, 1);
lean_inc(v_workers_6480_);
lean_dec_ref(v_self_6478_);
v_allDirectImports_6485_ = lean_box(1);
v___x_6486_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6485_, v_ileans_6479_);
v_a_6487_ = lean_ctor_get(v___x_6486_, 0);
lean_inc(v_a_6487_);
lean_dec_ref(v___x_6486_);
v___y_6482_ = v_a_6487_;
goto v___jp_6481_;
v___jp_6481_:
{
lean_object* v___x_6483_; lean_object* v_a_6484_; 
v___x_6483_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6482_, v_workers_6480_);
v_a_6484_ = lean_ctor_get(v___x_6483_, 0);
lean_inc(v_a_6484_);
lean_dec_ref(v___x_6483_);
return v_a_6484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6488_, lean_object* v_mod_6489_){
_start:
{
lean_object* v_ileans_6490_; lean_object* v_workers_6491_; lean_object* v___x_6493_; uint8_t v_isShared_6494_; uint8_t v_isSharedCheck_6528_; 
v_ileans_6490_ = lean_ctor_get(v_self_6488_, 0);
v_workers_6491_ = lean_ctor_get(v_self_6488_, 1);
v_isSharedCheck_6528_ = !lean_is_exclusive(v_self_6488_);
if (v_isSharedCheck_6528_ == 0)
{
v___x_6493_ = v_self_6488_;
v_isShared_6494_ = v_isSharedCheck_6528_;
goto v_resetjp_6492_;
}
else
{
lean_inc(v_workers_6491_);
lean_inc(v_ileans_6490_);
lean_dec(v_self_6488_);
v___x_6493_ = lean_box(0);
v_isShared_6494_ = v_isSharedCheck_6528_;
goto v_resetjp_6492_;
}
v_resetjp_6492_:
{
lean_object* v___x_6513_; 
v___x_6513_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6491_, v_mod_6489_);
lean_dec(v_workers_6491_);
if (lean_obj_tag(v___x_6513_) == 1)
{
lean_object* v_val_6514_; lean_object* v___x_6516_; uint8_t v_isShared_6517_; uint8_t v_isSharedCheck_6527_; 
v_val_6514_ = lean_ctor_get(v___x_6513_, 0);
v_isSharedCheck_6527_ = !lean_is_exclusive(v___x_6513_);
if (v_isSharedCheck_6527_ == 0)
{
v___x_6516_ = v___x_6513_;
v_isShared_6517_ = v_isSharedCheck_6527_;
goto v_resetjp_6515_;
}
else
{
lean_inc(v_val_6514_);
lean_dec(v___x_6513_);
v___x_6516_ = lean_box(0);
v_isShared_6517_ = v_isSharedCheck_6527_;
goto v_resetjp_6515_;
}
v_resetjp_6515_:
{
uint8_t v___x_6518_; 
v___x_6518_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6514_);
if (v___x_6518_ == 0)
{
lean_del_object(v___x_6516_);
lean_dec(v_val_6514_);
goto v___jp_6495_;
}
else
{
lean_object* v_moduleUri_6519_; lean_object* v_refs_6520_; lean_object* v_decls_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v___x_6525_; 
lean_del_object(v___x_6493_);
lean_dec(v_ileans_6490_);
v_moduleUri_6519_ = lean_ctor_get(v_val_6514_, 0);
lean_inc_ref(v_moduleUri_6519_);
v_refs_6520_ = lean_ctor_get(v_val_6514_, 4);
lean_inc(v_refs_6520_);
v_decls_6521_ = lean_ctor_get(v_val_6514_, 5);
lean_inc(v_decls_6521_);
lean_dec(v_val_6514_);
v___x_6522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6522_, 0, v_refs_6520_);
lean_ctor_set(v___x_6522_, 1, v_decls_6521_);
v___x_6523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6523_, 0, v_moduleUri_6519_);
lean_ctor_set(v___x_6523_, 1, v___x_6522_);
if (v_isShared_6517_ == 0)
{
lean_ctor_set(v___x_6516_, 0, v___x_6523_);
v___x_6525_ = v___x_6516_;
goto v_reusejp_6524_;
}
else
{
lean_object* v_reuseFailAlloc_6526_; 
v_reuseFailAlloc_6526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6526_, 0, v___x_6523_);
v___x_6525_ = v_reuseFailAlloc_6526_;
goto v_reusejp_6524_;
}
v_reusejp_6524_:
{
return v___x_6525_;
}
}
}
}
else
{
lean_dec(v___x_6513_);
goto v___jp_6495_;
}
v___jp_6495_:
{
lean_object* v___x_6496_; 
v___x_6496_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6490_, v_mod_6489_);
lean_dec(v_ileans_6490_);
if (lean_obj_tag(v___x_6496_) == 1)
{
lean_object* v_val_6497_; lean_object* v___x_6499_; uint8_t v_isShared_6500_; uint8_t v_isSharedCheck_6511_; 
v_val_6497_ = lean_ctor_get(v___x_6496_, 0);
v_isSharedCheck_6511_ = !lean_is_exclusive(v___x_6496_);
if (v_isSharedCheck_6511_ == 0)
{
v___x_6499_ = v___x_6496_;
v_isShared_6500_ = v_isSharedCheck_6511_;
goto v_resetjp_6498_;
}
else
{
lean_inc(v_val_6497_);
lean_dec(v___x_6496_);
v___x_6499_ = lean_box(0);
v_isShared_6500_ = v_isSharedCheck_6511_;
goto v_resetjp_6498_;
}
v_resetjp_6498_:
{
lean_object* v_moduleUri_6501_; lean_object* v_refs_6502_; lean_object* v_decls_6503_; lean_object* v___x_6505_; 
v_moduleUri_6501_ = lean_ctor_get(v_val_6497_, 0);
lean_inc_ref(v_moduleUri_6501_);
v_refs_6502_ = lean_ctor_get(v_val_6497_, 3);
lean_inc(v_refs_6502_);
v_decls_6503_ = lean_ctor_get(v_val_6497_, 4);
lean_inc(v_decls_6503_);
lean_dec(v_val_6497_);
if (v_isShared_6494_ == 0)
{
lean_ctor_set(v___x_6493_, 1, v_decls_6503_);
lean_ctor_set(v___x_6493_, 0, v_refs_6502_);
v___x_6505_ = v___x_6493_;
goto v_reusejp_6504_;
}
else
{
lean_object* v_reuseFailAlloc_6510_; 
v_reuseFailAlloc_6510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6510_, 0, v_refs_6502_);
lean_ctor_set(v_reuseFailAlloc_6510_, 1, v_decls_6503_);
v___x_6505_ = v_reuseFailAlloc_6510_;
goto v_reusejp_6504_;
}
v_reusejp_6504_:
{
lean_object* v___x_6506_; lean_object* v___x_6508_; 
v___x_6506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6506_, 0, v_moduleUri_6501_);
lean_ctor_set(v___x_6506_, 1, v___x_6505_);
if (v_isShared_6500_ == 0)
{
lean_ctor_set(v___x_6499_, 0, v___x_6506_);
v___x_6508_ = v___x_6499_;
goto v_reusejp_6507_;
}
else
{
lean_object* v_reuseFailAlloc_6509_; 
v_reuseFailAlloc_6509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6509_, 0, v___x_6506_);
v___x_6508_ = v_reuseFailAlloc_6509_;
goto v_reusejp_6507_;
}
v_reusejp_6507_:
{
return v___x_6508_;
}
}
}
}
else
{
lean_object* v___x_6512_; 
lean_dec(v___x_6496_);
lean_del_object(v___x_6493_);
v___x_6512_ = lean_box(0);
return v___x_6512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6529_, lean_object* v_mod_6530_){
_start:
{
lean_object* v_res_6531_; 
v_res_6531_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6529_, v_mod_6530_);
lean_dec(v_mod_6530_);
return v_res_6531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6532_, lean_object* v_mod_6533_){
_start:
{
lean_object* v_ileans_6534_; lean_object* v_workers_6535_; lean_object* v___x_6548_; 
v_ileans_6534_ = lean_ctor_get(v_self_6532_, 0);
v_workers_6535_ = lean_ctor_get(v_self_6532_, 1);
v___x_6548_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6535_, v_mod_6533_);
if (lean_obj_tag(v___x_6548_) == 1)
{
lean_object* v_val_6549_; lean_object* v___x_6551_; uint8_t v_isShared_6552_; uint8_t v_isSharedCheck_6558_; 
v_val_6549_ = lean_ctor_get(v___x_6548_, 0);
v_isSharedCheck_6558_ = !lean_is_exclusive(v___x_6548_);
if (v_isSharedCheck_6558_ == 0)
{
v___x_6551_ = v___x_6548_;
v_isShared_6552_ = v_isSharedCheck_6558_;
goto v_resetjp_6550_;
}
else
{
lean_inc(v_val_6549_);
lean_dec(v___x_6548_);
v___x_6551_ = lean_box(0);
v_isShared_6552_ = v_isSharedCheck_6558_;
goto v_resetjp_6550_;
}
v_resetjp_6550_:
{
uint8_t v___x_6553_; 
v___x_6553_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6549_);
if (v___x_6553_ == 0)
{
lean_del_object(v___x_6551_);
lean_dec(v_val_6549_);
goto v___jp_6536_;
}
else
{
lean_object* v_directImports_6554_; lean_object* v___x_6556_; 
v_directImports_6554_ = lean_ctor_get(v_val_6549_, 2);
lean_inc_ref(v_directImports_6554_);
lean_dec(v_val_6549_);
if (v_isShared_6552_ == 0)
{
lean_ctor_set(v___x_6551_, 0, v_directImports_6554_);
v___x_6556_ = v___x_6551_;
goto v_reusejp_6555_;
}
else
{
lean_object* v_reuseFailAlloc_6557_; 
v_reuseFailAlloc_6557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6557_, 0, v_directImports_6554_);
v___x_6556_ = v_reuseFailAlloc_6557_;
goto v_reusejp_6555_;
}
v_reusejp_6555_:
{
return v___x_6556_;
}
}
}
}
else
{
lean_dec(v___x_6548_);
goto v___jp_6536_;
}
v___jp_6536_:
{
lean_object* v___x_6537_; 
v___x_6537_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6534_, v_mod_6533_);
if (lean_obj_tag(v___x_6537_) == 1)
{
lean_object* v_val_6538_; lean_object* v___x_6540_; uint8_t v_isShared_6541_; uint8_t v_isSharedCheck_6546_; 
v_val_6538_ = lean_ctor_get(v___x_6537_, 0);
v_isSharedCheck_6546_ = !lean_is_exclusive(v___x_6537_);
if (v_isSharedCheck_6546_ == 0)
{
v___x_6540_ = v___x_6537_;
v_isShared_6541_ = v_isSharedCheck_6546_;
goto v_resetjp_6539_;
}
else
{
lean_inc(v_val_6538_);
lean_dec(v___x_6537_);
v___x_6540_ = lean_box(0);
v_isShared_6541_ = v_isSharedCheck_6546_;
goto v_resetjp_6539_;
}
v_resetjp_6539_:
{
lean_object* v_directImports_6542_; lean_object* v___x_6544_; 
v_directImports_6542_ = lean_ctor_get(v_val_6538_, 2);
lean_inc_ref(v_directImports_6542_);
lean_dec(v_val_6538_);
if (v_isShared_6541_ == 0)
{
lean_ctor_set(v___x_6540_, 0, v_directImports_6542_);
v___x_6544_ = v___x_6540_;
goto v_reusejp_6543_;
}
else
{
lean_object* v_reuseFailAlloc_6545_; 
v_reuseFailAlloc_6545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6545_, 0, v_directImports_6542_);
v___x_6544_ = v_reuseFailAlloc_6545_;
goto v_reusejp_6543_;
}
v_reusejp_6543_:
{
return v___x_6544_;
}
}
}
else
{
lean_object* v___x_6547_; 
lean_dec(v___x_6537_);
v___x_6547_ = lean_box(0);
return v___x_6547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6559_, lean_object* v_mod_6560_){
_start:
{
lean_object* v_res_6561_; 
v_res_6561_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6559_, v_mod_6560_);
lean_dec(v_mod_6560_);
lean_dec_ref(v_self_6559_);
return v_res_6561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6562_, lean_object* v_mod_6563_){
_start:
{
lean_object* v_ileans_6564_; lean_object* v_workers_6565_; lean_object* v___x_6578_; 
v_ileans_6564_ = lean_ctor_get(v_self_6562_, 0);
v_workers_6565_ = lean_ctor_get(v_self_6562_, 1);
v___x_6578_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6565_, v_mod_6563_);
if (lean_obj_tag(v___x_6578_) == 1)
{
lean_object* v_val_6579_; lean_object* v___x_6581_; uint8_t v_isShared_6582_; uint8_t v_isSharedCheck_6588_; 
v_val_6579_ = lean_ctor_get(v___x_6578_, 0);
v_isSharedCheck_6588_ = !lean_is_exclusive(v___x_6578_);
if (v_isSharedCheck_6588_ == 0)
{
v___x_6581_ = v___x_6578_;
v_isShared_6582_ = v_isSharedCheck_6588_;
goto v_resetjp_6580_;
}
else
{
lean_inc(v_val_6579_);
lean_dec(v___x_6578_);
v___x_6581_ = lean_box(0);
v_isShared_6582_ = v_isSharedCheck_6588_;
goto v_resetjp_6580_;
}
v_resetjp_6580_:
{
uint8_t v___x_6583_; 
v___x_6583_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6579_);
if (v___x_6583_ == 0)
{
lean_del_object(v___x_6581_);
lean_dec(v_val_6579_);
goto v___jp_6566_;
}
else
{
lean_object* v_decls_6584_; lean_object* v___x_6586_; 
v_decls_6584_ = lean_ctor_get(v_val_6579_, 5);
lean_inc(v_decls_6584_);
lean_dec(v_val_6579_);
if (v_isShared_6582_ == 0)
{
lean_ctor_set(v___x_6581_, 0, v_decls_6584_);
v___x_6586_ = v___x_6581_;
goto v_reusejp_6585_;
}
else
{
lean_object* v_reuseFailAlloc_6587_; 
v_reuseFailAlloc_6587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6587_, 0, v_decls_6584_);
v___x_6586_ = v_reuseFailAlloc_6587_;
goto v_reusejp_6585_;
}
v_reusejp_6585_:
{
return v___x_6586_;
}
}
}
}
else
{
lean_dec(v___x_6578_);
goto v___jp_6566_;
}
v___jp_6566_:
{
lean_object* v___x_6567_; 
v___x_6567_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6564_, v_mod_6563_);
if (lean_obj_tag(v___x_6567_) == 1)
{
lean_object* v_val_6568_; lean_object* v___x_6570_; uint8_t v_isShared_6571_; uint8_t v_isSharedCheck_6576_; 
v_val_6568_ = lean_ctor_get(v___x_6567_, 0);
v_isSharedCheck_6576_ = !lean_is_exclusive(v___x_6567_);
if (v_isSharedCheck_6576_ == 0)
{
v___x_6570_ = v___x_6567_;
v_isShared_6571_ = v_isSharedCheck_6576_;
goto v_resetjp_6569_;
}
else
{
lean_inc(v_val_6568_);
lean_dec(v___x_6567_);
v___x_6570_ = lean_box(0);
v_isShared_6571_ = v_isSharedCheck_6576_;
goto v_resetjp_6569_;
}
v_resetjp_6569_:
{
lean_object* v_decls_6572_; lean_object* v___x_6574_; 
v_decls_6572_ = lean_ctor_get(v_val_6568_, 4);
lean_inc(v_decls_6572_);
lean_dec(v_val_6568_);
if (v_isShared_6571_ == 0)
{
lean_ctor_set(v___x_6570_, 0, v_decls_6572_);
v___x_6574_ = v___x_6570_;
goto v_reusejp_6573_;
}
else
{
lean_object* v_reuseFailAlloc_6575_; 
v_reuseFailAlloc_6575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_decls_6572_);
v___x_6574_ = v_reuseFailAlloc_6575_;
goto v_reusejp_6573_;
}
v_reusejp_6573_:
{
return v___x_6574_;
}
}
}
else
{
lean_object* v___x_6577_; 
lean_dec(v___x_6567_);
v___x_6577_ = lean_box(0);
return v___x_6577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6589_, lean_object* v_mod_6590_){
_start:
{
lean_object* v_res_6591_; 
v_res_6591_ = l_Lean_Server_References_getDecls_x3f(v_self_6589_, v_mod_6590_);
lean_dec(v_mod_6590_);
lean_dec_ref(v_self_6589_);
return v_res_6591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6592_, lean_object* v_x_6593_){
_start:
{
if (lean_obj_tag(v_x_6593_) == 0)
{
lean_object* v_k_6594_; lean_object* v_v_6595_; lean_object* v_l_6596_; lean_object* v_r_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; lean_object* v___x_6600_; 
v_k_6594_ = lean_ctor_get(v_x_6593_, 1);
v_v_6595_ = lean_ctor_get(v_x_6593_, 2);
v_l_6596_ = lean_ctor_get(v_x_6593_, 3);
v_r_6597_ = lean_ctor_get(v_x_6593_, 4);
v___x_6598_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6592_, v_l_6596_);
lean_inc(v_v_6595_);
lean_inc(v_k_6594_);
v___x_6599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6599_, 0, v_k_6594_);
lean_ctor_set(v___x_6599_, 1, v_v_6595_);
v___x_6600_ = lean_array_push(v___x_6598_, v___x_6599_);
v_init_6592_ = v___x_6600_;
v_x_6593_ = v_r_6597_;
goto _start;
}
else
{
return v_init_6592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6602_, lean_object* v_x_6603_){
_start:
{
lean_object* v_res_6604_; 
v_res_6604_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6602_, v_x_6603_);
lean_dec(v_x_6603_);
return v_res_6604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6605_, lean_object* v_k_6606_){
_start:
{
if (lean_obj_tag(v_t_6605_) == 0)
{
lean_object* v_k_6607_; lean_object* v_v_6608_; lean_object* v_l_6609_; lean_object* v_r_6610_; uint8_t v___x_6611_; 
v_k_6607_ = lean_ctor_get(v_t_6605_, 1);
v_v_6608_ = lean_ctor_get(v_t_6605_, 2);
v_l_6609_ = lean_ctor_get(v_t_6605_, 3);
v_r_6610_ = lean_ctor_get(v_t_6605_, 4);
v___x_6611_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6606_, v_k_6607_);
switch(v___x_6611_)
{
case 0:
{
v_t_6605_ = v_l_6609_;
goto _start;
}
case 1:
{
lean_object* v___x_6613_; 
lean_inc(v_v_6608_);
v___x_6613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6613_, 0, v_v_6608_);
return v___x_6613_;
}
default: 
{
v_t_6605_ = v_r_6610_;
goto _start;
}
}
}
else
{
lean_object* v___x_6615_; 
v___x_6615_ = lean_box(0);
return v___x_6615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6616_, lean_object* v_k_6617_){
_start:
{
lean_object* v_res_6618_; 
v_res_6618_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6616_, v_k_6617_);
lean_dec_ref(v_k_6617_);
lean_dec(v_t_6616_);
return v_res_6618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6619_, lean_object* v_as_6620_, size_t v_sz_6621_, size_t v_i_6622_, lean_object* v_b_6623_){
_start:
{
lean_object* v_a_6625_; uint8_t v___x_6629_; 
v___x_6629_ = lean_usize_dec_lt(v_i_6622_, v_sz_6621_);
if (v___x_6629_ == 0)
{
return v_b_6623_;
}
else
{
lean_object* v_a_6630_; lean_object* v_snd_6631_; lean_object* v_snd_6632_; lean_object* v_fst_6633_; lean_object* v___x_6635_; uint8_t v_isShared_6636_; uint8_t v_isSharedCheck_6661_; 
v_a_6630_ = lean_array_uget(v_as_6620_, v_i_6622_);
v_snd_6631_ = lean_ctor_get(v_a_6630_, 1);
lean_inc(v_snd_6631_);
v_snd_6632_ = lean_ctor_get(v_snd_6631_, 1);
lean_inc(v_snd_6632_);
v_fst_6633_ = lean_ctor_get(v_a_6630_, 0);
v_isSharedCheck_6661_ = !lean_is_exclusive(v_a_6630_);
if (v_isSharedCheck_6661_ == 0)
{
lean_object* v_unused_6662_; 
v_unused_6662_ = lean_ctor_get(v_a_6630_, 1);
lean_dec(v_unused_6662_);
v___x_6635_ = v_a_6630_;
v_isShared_6636_ = v_isSharedCheck_6661_;
goto v_resetjp_6634_;
}
else
{
lean_inc(v_fst_6633_);
lean_dec(v_a_6630_);
v___x_6635_ = lean_box(0);
v_isShared_6636_ = v_isSharedCheck_6661_;
goto v_resetjp_6634_;
}
v_resetjp_6634_:
{
lean_object* v_fst_6637_; lean_object* v___x_6639_; uint8_t v_isShared_6640_; uint8_t v_isSharedCheck_6659_; 
v_fst_6637_ = lean_ctor_get(v_snd_6631_, 0);
v_isSharedCheck_6659_ = !lean_is_exclusive(v_snd_6631_);
if (v_isSharedCheck_6659_ == 0)
{
lean_object* v_unused_6660_; 
v_unused_6660_ = lean_ctor_get(v_snd_6631_, 1);
lean_dec(v_unused_6660_);
v___x_6639_ = v_snd_6631_;
v_isShared_6640_ = v_isSharedCheck_6659_;
goto v_resetjp_6638_;
}
else
{
lean_inc(v_fst_6637_);
lean_dec(v_snd_6631_);
v___x_6639_ = lean_box(0);
v_isShared_6640_ = v_isSharedCheck_6659_;
goto v_resetjp_6638_;
}
v_resetjp_6638_:
{
lean_object* v_fst_6641_; lean_object* v_snd_6642_; lean_object* v___x_6644_; uint8_t v_isShared_6645_; uint8_t v_isSharedCheck_6658_; 
v_fst_6641_ = lean_ctor_get(v_snd_6632_, 0);
v_snd_6642_ = lean_ctor_get(v_snd_6632_, 1);
v_isSharedCheck_6658_ = !lean_is_exclusive(v_snd_6632_);
if (v_isSharedCheck_6658_ == 0)
{
v___x_6644_ = v_snd_6632_;
v_isShared_6645_ = v_isSharedCheck_6658_;
goto v_resetjp_6643_;
}
else
{
lean_inc(v_snd_6642_);
lean_inc(v_fst_6641_);
lean_dec(v_snd_6632_);
v___x_6644_ = lean_box(0);
v_isShared_6645_ = v_isSharedCheck_6658_;
goto v_resetjp_6643_;
}
v_resetjp_6643_:
{
lean_object* v___x_6646_; 
v___x_6646_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6641_, v_ident_6619_);
lean_dec(v_fst_6641_);
if (lean_obj_tag(v___x_6646_) == 1)
{
lean_object* v_val_6647_; lean_object* v___x_6649_; 
v_val_6647_ = lean_ctor_get(v___x_6646_, 0);
lean_inc(v_val_6647_);
lean_dec_ref_known(v___x_6646_, 1);
if (v_isShared_6645_ == 0)
{
lean_ctor_set(v___x_6644_, 0, v_val_6647_);
v___x_6649_ = v___x_6644_;
goto v_reusejp_6648_;
}
else
{
lean_object* v_reuseFailAlloc_6657_; 
v_reuseFailAlloc_6657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6657_, 0, v_val_6647_);
lean_ctor_set(v_reuseFailAlloc_6657_, 1, v_snd_6642_);
v___x_6649_ = v_reuseFailAlloc_6657_;
goto v_reusejp_6648_;
}
v_reusejp_6648_:
{
lean_object* v___x_6651_; 
if (v_isShared_6640_ == 0)
{
lean_ctor_set(v___x_6639_, 1, v___x_6649_);
lean_ctor_set(v___x_6639_, 0, v_fst_6633_);
v___x_6651_ = v___x_6639_;
goto v_reusejp_6650_;
}
else
{
lean_object* v_reuseFailAlloc_6656_; 
v_reuseFailAlloc_6656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6656_, 0, v_fst_6633_);
lean_ctor_set(v_reuseFailAlloc_6656_, 1, v___x_6649_);
v___x_6651_ = v_reuseFailAlloc_6656_;
goto v_reusejp_6650_;
}
v_reusejp_6650_:
{
lean_object* v___x_6653_; 
if (v_isShared_6636_ == 0)
{
lean_ctor_set(v___x_6635_, 1, v___x_6651_);
lean_ctor_set(v___x_6635_, 0, v_fst_6637_);
v___x_6653_ = v___x_6635_;
goto v_reusejp_6652_;
}
else
{
lean_object* v_reuseFailAlloc_6655_; 
v_reuseFailAlloc_6655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6655_, 0, v_fst_6637_);
lean_ctor_set(v_reuseFailAlloc_6655_, 1, v___x_6651_);
v___x_6653_ = v_reuseFailAlloc_6655_;
goto v_reusejp_6652_;
}
v_reusejp_6652_:
{
lean_object* v___x_6654_; 
v___x_6654_ = lean_array_push(v_b_6623_, v___x_6653_);
v_a_6625_ = v___x_6654_;
goto v___jp_6624_;
}
}
}
}
else
{
lean_dec(v___x_6646_);
lean_del_object(v___x_6644_);
lean_dec(v_snd_6642_);
lean_del_object(v___x_6639_);
lean_dec(v_fst_6637_);
lean_del_object(v___x_6635_);
lean_dec(v_fst_6633_);
v_a_6625_ = v_b_6623_;
goto v___jp_6624_;
}
}
}
}
}
v___jp_6624_:
{
size_t v___x_6626_; size_t v___x_6627_; 
v___x_6626_ = ((size_t)1ULL);
v___x_6627_ = lean_usize_add(v_i_6622_, v___x_6626_);
v_i_6622_ = v___x_6627_;
v_b_6623_ = v_a_6625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6663_, lean_object* v_as_6664_, lean_object* v_sz_6665_, lean_object* v_i_6666_, lean_object* v_b_6667_){
_start:
{
size_t v_sz_boxed_6668_; size_t v_i_boxed_6669_; lean_object* v_res_6670_; 
v_sz_boxed_6668_ = lean_unbox_usize(v_sz_6665_);
lean_dec(v_sz_6665_);
v_i_boxed_6669_ = lean_unbox_usize(v_i_6666_);
lean_dec(v_i_6666_);
v_res_6670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6663_, v_as_6664_, v_sz_boxed_6668_, v_i_boxed_6669_, v_b_6667_);
lean_dec_ref(v_as_6664_);
lean_dec_ref(v_ident_6663_);
return v_res_6670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6677_, lean_object* v_ident_6678_){
_start:
{
lean_object* v___y_6680_; 
if (lean_obj_tag(v_ident_6678_) == 0)
{
lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; 
v___x_6685_ = l_Lean_Server_References_allRefs(v_self_6677_);
v___x_6686_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6687_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6686_, v___x_6685_);
lean_dec(v___x_6685_);
v___y_6680_ = v___x_6687_;
goto v___jp_6679_;
}
else
{
lean_object* v_moduleName_6688_; lean_object* v_identModuleName_6689_; lean_object* v___x_6690_; 
v_moduleName_6688_ = lean_ctor_get(v_ident_6678_, 0);
lean_inc_ref(v_moduleName_6688_);
v_identModuleName_6689_ = l_String_toName(v_moduleName_6688_);
v___x_6690_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6677_, v_identModuleName_6689_);
if (lean_obj_tag(v___x_6690_) == 0)
{
lean_object* v___x_6691_; 
lean_dec(v_identModuleName_6689_);
v___x_6691_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6680_ = v___x_6691_;
goto v___jp_6679_;
}
else
{
lean_object* v_val_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; 
v_val_6692_ = lean_ctor_get(v___x_6690_, 0);
lean_inc(v_val_6692_);
lean_dec_ref_known(v___x_6690_, 1);
v___x_6693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6693_, 0, v_identModuleName_6689_);
lean_ctor_set(v___x_6693_, 1, v_val_6692_);
v___x_6694_ = lean_unsigned_to_nat(1u);
v___x_6695_ = lean_mk_empty_array_with_capacity(v___x_6694_);
v___x_6696_ = lean_array_push(v___x_6695_, v___x_6693_);
v___y_6680_ = v___x_6696_;
goto v___jp_6679_;
}
}
v___jp_6679_:
{
lean_object* v_result_6681_; size_t v_sz_6682_; size_t v___x_6683_; lean_object* v___x_6684_; 
v_result_6681_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6682_ = lean_array_size(v___y_6680_);
v___x_6683_ = ((size_t)0ULL);
v___x_6684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6678_, v___y_6680_, v_sz_6682_, v___x_6683_, v_result_6681_);
lean_dec_ref(v___y_6680_);
lean_dec_ref(v_ident_6678_);
return v___x_6684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6697_, lean_object* v_t_6698_, lean_object* v_k_6699_){
_start:
{
lean_object* v___x_6700_; 
v___x_6700_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6698_, v_k_6699_);
return v___x_6700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6701_, lean_object* v_t_6702_, lean_object* v_k_6703_){
_start:
{
lean_object* v_res_6704_; 
v_res_6704_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6701_, v_t_6702_, v_k_6703_);
lean_dec_ref(v_k_6703_);
lean_dec(v_t_6702_);
return v_res_6704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6705_, lean_object* v_t_6706_){
_start:
{
lean_object* v___x_6707_; 
v___x_6707_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6705_, v_t_6706_);
return v___x_6707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6708_, lean_object* v_t_6709_){
_start:
{
lean_object* v_res_6710_; 
v_res_6710_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6708_, v_t_6709_);
lean_dec(v_t_6709_);
return v_res_6710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6711_, lean_object* v_module_6712_, lean_object* v_pos_6713_, uint8_t v_includeStop_6714_){
_start:
{
lean_object* v___x_6715_; 
v___x_6715_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6711_, v_module_6712_);
if (lean_obj_tag(v___x_6715_) == 1)
{
lean_object* v_val_6716_; lean_object* v_snd_6717_; lean_object* v_fst_6718_; lean_object* v___x_6719_; 
v_val_6716_ = lean_ctor_get(v___x_6715_, 0);
lean_inc(v_val_6716_);
lean_dec_ref_known(v___x_6715_, 1);
v_snd_6717_ = lean_ctor_get(v_val_6716_, 1);
lean_inc(v_snd_6717_);
lean_dec(v_val_6716_);
v_fst_6718_ = lean_ctor_get(v_snd_6717_, 0);
lean_inc(v_fst_6718_);
lean_dec(v_snd_6717_);
v___x_6719_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6718_, v_pos_6713_, v_includeStop_6714_);
return v___x_6719_;
}
else
{
lean_object* v___x_6720_; 
lean_dec(v___x_6715_);
v___x_6720_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6721_, lean_object* v_module_6722_, lean_object* v_pos_6723_, lean_object* v_includeStop_6724_){
_start:
{
uint8_t v_includeStop_boxed_6725_; lean_object* v_res_6726_; 
v_includeStop_boxed_6725_ = lean_unbox(v_includeStop_6724_);
v_res_6726_ = l_Lean_Server_References_findAt(v_self_6721_, v_module_6722_, v_pos_6723_, v_includeStop_boxed_6725_);
lean_dec_ref(v_pos_6723_);
lean_dec(v_module_6722_);
return v_res_6726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6727_, lean_object* v_module_6728_, lean_object* v_pos_6729_, uint8_t v_includeStop_6730_){
_start:
{
lean_object* v___x_6731_; 
v___x_6731_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6727_, v_module_6728_);
if (lean_obj_tag(v___x_6731_) == 0)
{
lean_object* v___x_6732_; 
v___x_6732_ = lean_box(0);
return v___x_6732_;
}
else
{
lean_object* v_val_6733_; lean_object* v_snd_6734_; lean_object* v_fst_6735_; lean_object* v___x_6736_; 
v_val_6733_ = lean_ctor_get(v___x_6731_, 0);
lean_inc(v_val_6733_);
lean_dec_ref_known(v___x_6731_, 1);
v_snd_6734_ = lean_ctor_get(v_val_6733_, 1);
lean_inc(v_snd_6734_);
lean_dec(v_val_6733_);
v_fst_6735_ = lean_ctor_get(v_snd_6734_, 0);
lean_inc(v_fst_6735_);
lean_dec(v_snd_6734_);
v___x_6736_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6735_, v_pos_6729_, v_includeStop_6730_);
lean_dec(v_fst_6735_);
return v___x_6736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6737_, lean_object* v_module_6738_, lean_object* v_pos_6739_, lean_object* v_includeStop_6740_){
_start:
{
uint8_t v_includeStop_boxed_6741_; lean_object* v_res_6742_; 
v_includeStop_boxed_6741_ = lean_unbox(v_includeStop_6740_);
v_res_6742_ = l_Lean_Server_References_findRange_x3f(v_self_6737_, v_module_6738_, v_pos_6739_, v_includeStop_boxed_6741_);
lean_dec_ref(v_pos_6739_);
lean_dec(v_module_6738_);
return v_res_6742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6743_, lean_object* v_k_6744_){
_start:
{
if (lean_obj_tag(v_t_6743_) == 0)
{
lean_object* v_k_6745_; lean_object* v_v_6746_; lean_object* v_l_6747_; lean_object* v_r_6748_; uint8_t v___x_6749_; 
v_k_6745_ = lean_ctor_get(v_t_6743_, 1);
v_v_6746_ = lean_ctor_get(v_t_6743_, 2);
v_l_6747_ = lean_ctor_get(v_t_6743_, 3);
v_r_6748_ = lean_ctor_get(v_t_6743_, 4);
v___x_6749_ = lean_string_compare(v_k_6744_, v_k_6745_);
switch(v___x_6749_)
{
case 0:
{
v_t_6743_ = v_l_6747_;
goto _start;
}
case 1:
{
lean_object* v___x_6751_; 
lean_inc(v_v_6746_);
v___x_6751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6751_, 0, v_v_6746_);
return v___x_6751_;
}
default: 
{
v_t_6743_ = v_r_6748_;
goto _start;
}
}
}
else
{
lean_object* v___x_6753_; 
v___x_6753_ = lean_box(0);
return v___x_6753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6754_, lean_object* v_k_6755_){
_start:
{
lean_object* v_res_6756_; 
v_res_6756_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6754_, v_k_6755_);
lean_dec_ref(v_k_6755_);
lean_dec(v_t_6754_);
return v_res_6756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6757_, lean_object* v_name_6758_){
_start:
{
lean_object* v___x_6759_; 
v___x_6759_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6757_, v_name_6758_);
if (lean_obj_tag(v___x_6759_) == 0)
{
lean_object* v___x_6760_; 
lean_dec_ref(v_name_6758_);
v___x_6760_ = lean_box(0);
return v___x_6760_;
}
else
{
lean_object* v_val_6761_; lean_object* v___x_6763_; uint8_t v_isShared_6764_; uint8_t v_isSharedCheck_6771_; 
v_val_6761_ = lean_ctor_get(v___x_6759_, 0);
v_isSharedCheck_6771_ = !lean_is_exclusive(v___x_6759_);
if (v_isSharedCheck_6771_ == 0)
{
v___x_6763_ = v___x_6759_;
v_isShared_6764_ = v_isSharedCheck_6771_;
goto v_resetjp_6762_;
}
else
{
lean_inc(v_val_6761_);
lean_dec(v___x_6759_);
v___x_6763_ = lean_box(0);
v_isShared_6764_ = v_isSharedCheck_6771_;
goto v_resetjp_6762_;
}
v_resetjp_6762_:
{
lean_object* v___x_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6769_; 
v___x_6765_ = l_Lean_Lsp_DeclInfo_range(v_val_6761_);
v___x_6766_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6761_);
lean_dec(v_val_6761_);
v___x_6767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6767_, 0, v_name_6758_);
lean_ctor_set(v___x_6767_, 1, v___x_6765_);
lean_ctor_set(v___x_6767_, 2, v___x_6766_);
if (v_isShared_6764_ == 0)
{
lean_ctor_set(v___x_6763_, 0, v___x_6767_);
v___x_6769_ = v___x_6763_;
goto v_reusejp_6768_;
}
else
{
lean_object* v_reuseFailAlloc_6770_; 
v_reuseFailAlloc_6770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6770_, 0, v___x_6767_);
v___x_6769_ = v_reuseFailAlloc_6770_;
goto v_reusejp_6768_;
}
v_reusejp_6768_:
{
return v___x_6769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6772_, lean_object* v_name_6773_){
_start:
{
lean_object* v_res_6774_; 
v_res_6774_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6772_, v_name_6773_);
lean_dec(v_ds_6772_);
return v_res_6774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6775_, lean_object* v_t_6776_, lean_object* v_k_6777_){
_start:
{
lean_object* v___x_6778_; 
v___x_6778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6776_, v_k_6777_);
return v___x_6778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6779_, lean_object* v_t_6780_, lean_object* v_k_6781_){
_start:
{
lean_object* v_res_6782_; 
v_res_6782_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6779_, v_t_6780_, v_k_6781_);
lean_dec_ref(v_k_6781_);
lean_dec(v_t_6780_);
return v_res_6782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6783_, lean_object* v_fst_6784_, lean_object* v_snd_6785_, lean_object* v_as_6786_, size_t v_sz_6787_, size_t v_i_6788_, lean_object* v_b_6789_){
_start:
{
uint8_t v___x_6790_; 
v___x_6790_ = lean_usize_dec_lt(v_i_6788_, v_sz_6787_);
if (v___x_6790_ == 0)
{
lean_dec(v_fst_6784_);
lean_dec_ref(v_fst_6783_);
return v_b_6789_;
}
else
{
lean_object* v_a_6791_; lean_object* v___y_6793_; lean_object* v___x_6801_; 
v_a_6791_ = lean_array_uget_borrowed(v_as_6786_, v_i_6788_);
v___x_6801_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6791_);
if (lean_obj_tag(v___x_6801_) == 0)
{
lean_object* v___x_6802_; 
v___x_6802_ = lean_box(0);
v___y_6793_ = v___x_6802_;
goto v___jp_6792_;
}
else
{
lean_object* v_val_6803_; lean_object* v___x_6804_; 
v_val_6803_ = lean_ctor_get(v___x_6801_, 0);
lean_inc(v_val_6803_);
lean_dec_ref_known(v___x_6801_, 1);
v___x_6804_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6785_, v_val_6803_);
v___y_6793_ = v___x_6804_;
goto v___jp_6792_;
}
v___jp_6792_:
{
lean_object* v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; size_t v___x_6798_; size_t v___x_6799_; 
v___x_6794_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6791_);
lean_inc_ref(v_fst_6783_);
v___x_6795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6795_, 0, v_fst_6783_);
lean_ctor_set(v___x_6795_, 1, v___x_6794_);
lean_inc(v_fst_6784_);
v___x_6796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6796_, 0, v___x_6795_);
lean_ctor_set(v___x_6796_, 1, v_fst_6784_);
lean_ctor_set(v___x_6796_, 2, v___y_6793_);
v___x_6797_ = lean_array_push(v_b_6789_, v___x_6796_);
v___x_6798_ = ((size_t)1ULL);
v___x_6799_ = lean_usize_add(v_i_6788_, v___x_6798_);
v_i_6788_ = v___x_6799_;
v_b_6789_ = v___x_6797_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6805_, lean_object* v_fst_6806_, lean_object* v_snd_6807_, lean_object* v_as_6808_, lean_object* v_sz_6809_, lean_object* v_i_6810_, lean_object* v_b_6811_){
_start:
{
size_t v_sz_boxed_6812_; size_t v_i_boxed_6813_; lean_object* v_res_6814_; 
v_sz_boxed_6812_ = lean_unbox_usize(v_sz_6809_);
lean_dec(v_sz_6809_);
v_i_boxed_6813_ = lean_unbox_usize(v_i_6810_);
lean_dec(v_i_6810_);
v_res_6814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6805_, v_fst_6806_, v_snd_6807_, v_as_6808_, v_sz_boxed_6812_, v_i_boxed_6813_, v_b_6811_);
lean_dec_ref(v_as_6808_);
lean_dec(v_snd_6807_);
return v_res_6814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6815_, lean_object* v_as_6816_, size_t v_sz_6817_, size_t v_i_6818_, lean_object* v_b_6819_){
_start:
{
uint8_t v___x_6820_; 
v___x_6820_ = lean_usize_dec_lt(v_i_6818_, v_sz_6817_);
if (v___x_6820_ == 0)
{
return v_b_6819_;
}
else
{
lean_object* v_a_6821_; lean_object* v_snd_6822_; lean_object* v_snd_6823_; lean_object* v_fst_6824_; lean_object* v_fst_6825_; lean_object* v_fst_6826_; lean_object* v_snd_6827_; lean_object* v___x_6829_; uint8_t v_isShared_6830_; uint8_t v_isSharedCheck_6854_; 
v_a_6821_ = lean_array_uget_borrowed(v_as_6816_, v_i_6818_);
v_snd_6822_ = lean_ctor_get(v_a_6821_, 1);
v_snd_6823_ = lean_ctor_get(v_snd_6822_, 1);
lean_inc(v_snd_6823_);
v_fst_6824_ = lean_ctor_get(v_a_6821_, 0);
v_fst_6825_ = lean_ctor_get(v_snd_6822_, 0);
v_fst_6826_ = lean_ctor_get(v_snd_6823_, 0);
v_snd_6827_ = lean_ctor_get(v_snd_6823_, 1);
v_isSharedCheck_6854_ = !lean_is_exclusive(v_snd_6823_);
if (v_isSharedCheck_6854_ == 0)
{
v___x_6829_ = v_snd_6823_;
v_isShared_6830_ = v_isSharedCheck_6854_;
goto v_resetjp_6828_;
}
else
{
lean_inc(v_snd_6827_);
lean_inc(v_fst_6826_);
lean_dec(v_snd_6823_);
v___x_6829_ = lean_box(0);
v_isShared_6830_ = v_isSharedCheck_6854_;
goto v_resetjp_6828_;
}
v_resetjp_6828_:
{
lean_object* v_result_6832_; 
if (v_includeDefinition_6815_ == 0)
{
lean_del_object(v___x_6829_);
v_result_6832_ = v_b_6819_;
goto v___jp_6831_;
}
else
{
lean_object* v_definition_x3f_6840_; 
v_definition_x3f_6840_ = lean_ctor_get(v_fst_6826_, 0);
if (lean_obj_tag(v_definition_x3f_6840_) == 1)
{
lean_object* v_val_6841_; lean_object* v___y_6843_; lean_object* v___x_6850_; 
v_val_6841_ = lean_ctor_get(v_definition_x3f_6840_, 0);
v___x_6850_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6841_);
if (lean_obj_tag(v___x_6850_) == 0)
{
lean_object* v___x_6851_; 
v___x_6851_ = lean_box(0);
v___y_6843_ = v___x_6851_;
goto v___jp_6842_;
}
else
{
lean_object* v_val_6852_; lean_object* v___x_6853_; 
v_val_6852_ = lean_ctor_get(v___x_6850_, 0);
lean_inc(v_val_6852_);
lean_dec_ref_known(v___x_6850_, 1);
v___x_6853_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6827_, v_val_6852_);
v___y_6843_ = v___x_6853_;
goto v___jp_6842_;
}
v___jp_6842_:
{
lean_object* v___x_6844_; lean_object* v___x_6846_; 
v___x_6844_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6841_);
lean_inc(v_fst_6824_);
if (v_isShared_6830_ == 0)
{
lean_ctor_set(v___x_6829_, 1, v___x_6844_);
lean_ctor_set(v___x_6829_, 0, v_fst_6824_);
v___x_6846_ = v___x_6829_;
goto v_reusejp_6845_;
}
else
{
lean_object* v_reuseFailAlloc_6849_; 
v_reuseFailAlloc_6849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6849_, 0, v_fst_6824_);
lean_ctor_set(v_reuseFailAlloc_6849_, 1, v___x_6844_);
v___x_6846_ = v_reuseFailAlloc_6849_;
goto v_reusejp_6845_;
}
v_reusejp_6845_:
{
lean_object* v___x_6847_; lean_object* v___x_6848_; 
lean_inc(v_fst_6825_);
v___x_6847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6847_, 0, v___x_6846_);
lean_ctor_set(v___x_6847_, 1, v_fst_6825_);
lean_ctor_set(v___x_6847_, 2, v___y_6843_);
v___x_6848_ = lean_array_push(v_b_6819_, v___x_6847_);
v_result_6832_ = v___x_6848_;
goto v___jp_6831_;
}
}
}
else
{
lean_del_object(v___x_6829_);
v_result_6832_ = v_b_6819_;
goto v___jp_6831_;
}
}
v___jp_6831_:
{
lean_object* v_usages_6833_; size_t v_sz_6834_; size_t v___x_6835_; lean_object* v___x_6836_; size_t v___x_6837_; size_t v___x_6838_; 
v_usages_6833_ = lean_ctor_get(v_fst_6826_, 1);
lean_inc_ref(v_usages_6833_);
lean_dec(v_fst_6826_);
v_sz_6834_ = lean_array_size(v_usages_6833_);
v___x_6835_ = ((size_t)0ULL);
lean_inc(v_fst_6825_);
lean_inc(v_fst_6824_);
v___x_6836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6824_, v_fst_6825_, v_snd_6827_, v_usages_6833_, v_sz_6834_, v___x_6835_, v_result_6832_);
lean_dec_ref(v_usages_6833_);
lean_dec(v_snd_6827_);
v___x_6837_ = ((size_t)1ULL);
v___x_6838_ = lean_usize_add(v_i_6818_, v___x_6837_);
v_i_6818_ = v___x_6838_;
v_b_6819_ = v___x_6836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6855_, lean_object* v_as_6856_, lean_object* v_sz_6857_, lean_object* v_i_6858_, lean_object* v_b_6859_){
_start:
{
uint8_t v_includeDefinition_boxed_6860_; size_t v_sz_boxed_6861_; size_t v_i_boxed_6862_; lean_object* v_res_6863_; 
v_includeDefinition_boxed_6860_ = lean_unbox(v_includeDefinition_6855_);
v_sz_boxed_6861_ = lean_unbox_usize(v_sz_6857_);
lean_dec(v_sz_6857_);
v_i_boxed_6862_ = lean_unbox_usize(v_i_6858_);
lean_dec(v_i_6858_);
v_res_6863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6860_, v_as_6856_, v_sz_boxed_6861_, v_i_boxed_6862_, v_b_6859_);
lean_dec_ref(v_as_6856_);
return v_res_6863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6866_, lean_object* v_ident_6867_, uint8_t v_includeDefinition_6868_){
_start:
{
lean_object* v_result_6869_; lean_object* v___x_6870_; size_t v_sz_6871_; size_t v___x_6872_; lean_object* v___x_6873_; 
v_result_6869_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6870_ = l_Lean_Server_References_allRefsFor(v_self_6866_, v_ident_6867_);
v_sz_6871_ = lean_array_size(v___x_6870_);
v___x_6872_ = ((size_t)0ULL);
v___x_6873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6868_, v___x_6870_, v_sz_6871_, v___x_6872_, v_result_6869_);
lean_dec_ref(v___x_6870_);
return v___x_6873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6874_, lean_object* v_ident_6875_, lean_object* v_includeDefinition_6876_){
_start:
{
uint8_t v_includeDefinition_boxed_6877_; lean_object* v_res_6878_; 
v_includeDefinition_boxed_6877_ = lean_unbox(v_includeDefinition_6876_);
v_res_6878_ = l_Lean_Server_References_referringTo(v_self_6874_, v_ident_6875_, v_includeDefinition_boxed_6877_);
return v_res_6878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6882_, size_t v_sz_6883_, size_t v_i_6884_, lean_object* v_b_6885_){
_start:
{
uint8_t v___x_6886_; 
v___x_6886_ = lean_usize_dec_lt(v_i_6884_, v_sz_6883_);
if (v___x_6886_ == 0)
{
lean_inc_ref(v_b_6885_);
return v_b_6885_;
}
else
{
lean_object* v_a_6887_; lean_object* v_snd_6888_; lean_object* v_snd_6889_; lean_object* v_fst_6890_; lean_object* v_fst_6891_; lean_object* v_fst_6892_; lean_object* v_snd_6893_; lean_object* v___x_6895_; uint8_t v_isShared_6896_; uint8_t v_isSharedCheck_6931_; 
v_a_6887_ = lean_array_uget_borrowed(v_as_6882_, v_i_6884_);
v_snd_6888_ = lean_ctor_get(v_a_6887_, 1);
v_snd_6889_ = lean_ctor_get(v_snd_6888_, 1);
lean_inc(v_snd_6889_);
v_fst_6890_ = lean_ctor_get(v_snd_6889_, 0);
lean_inc(v_fst_6890_);
v_fst_6891_ = lean_ctor_get(v_a_6887_, 0);
v_fst_6892_ = lean_ctor_get(v_snd_6888_, 0);
v_snd_6893_ = lean_ctor_get(v_snd_6889_, 1);
v_isSharedCheck_6931_ = !lean_is_exclusive(v_snd_6889_);
if (v_isSharedCheck_6931_ == 0)
{
lean_object* v_unused_6932_; 
v_unused_6932_ = lean_ctor_get(v_snd_6889_, 0);
lean_dec(v_unused_6932_);
v___x_6895_ = v_snd_6889_;
v_isShared_6896_ = v_isSharedCheck_6931_;
goto v_resetjp_6894_;
}
else
{
lean_inc(v_snd_6893_);
lean_dec(v_snd_6889_);
v___x_6895_ = lean_box(0);
v_isShared_6896_ = v_isSharedCheck_6931_;
goto v_resetjp_6894_;
}
v_resetjp_6894_:
{
lean_object* v_definition_x3f_6897_; lean_object* v___x_6899_; uint8_t v_isShared_6900_; uint8_t v_isSharedCheck_6929_; 
v_definition_x3f_6897_ = lean_ctor_get(v_fst_6890_, 0);
v_isSharedCheck_6929_ = !lean_is_exclusive(v_fst_6890_);
if (v_isSharedCheck_6929_ == 0)
{
lean_object* v_unused_6930_; 
v_unused_6930_ = lean_ctor_get(v_fst_6890_, 1);
lean_dec(v_unused_6930_);
v___x_6899_ = v_fst_6890_;
v_isShared_6900_ = v_isSharedCheck_6929_;
goto v_resetjp_6898_;
}
else
{
lean_inc(v_definition_x3f_6897_);
lean_dec(v_fst_6890_);
v___x_6899_ = lean_box(0);
v_isShared_6900_ = v_isSharedCheck_6929_;
goto v_resetjp_6898_;
}
v_resetjp_6898_:
{
lean_object* v___x_6901_; 
v___x_6901_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6897_) == 1)
{
lean_object* v_val_6902_; lean_object* v___x_6904_; uint8_t v_isShared_6905_; uint8_t v_isSharedCheck_6924_; 
v_val_6902_ = lean_ctor_get(v_definition_x3f_6897_, 0);
v_isSharedCheck_6924_ = !lean_is_exclusive(v_definition_x3f_6897_);
if (v_isSharedCheck_6924_ == 0)
{
v___x_6904_ = v_definition_x3f_6897_;
v_isShared_6905_ = v_isSharedCheck_6924_;
goto v_resetjp_6903_;
}
else
{
lean_inc(v_val_6902_);
lean_dec(v_definition_x3f_6897_);
v___x_6904_ = lean_box(0);
v_isShared_6905_ = v_isSharedCheck_6924_;
goto v_resetjp_6903_;
}
v_resetjp_6903_:
{
lean_object* v___y_6907_; lean_object* v___x_6920_; 
v___x_6920_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6902_);
if (lean_obj_tag(v___x_6920_) == 0)
{
lean_object* v___x_6921_; 
lean_dec(v_snd_6893_);
v___x_6921_ = lean_box(0);
v___y_6907_ = v___x_6921_;
goto v___jp_6906_;
}
else
{
lean_object* v_val_6922_; lean_object* v___x_6923_; 
v_val_6922_ = lean_ctor_get(v___x_6920_, 0);
lean_inc(v_val_6922_);
lean_dec_ref_known(v___x_6920_, 1);
v___x_6923_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6893_, v_val_6922_);
lean_dec(v_snd_6893_);
v___y_6907_ = v___x_6923_;
goto v___jp_6906_;
}
v___jp_6906_:
{
lean_object* v___x_6908_; lean_object* v___x_6910_; 
v___x_6908_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6902_);
lean_dec(v_val_6902_);
lean_inc(v_fst_6891_);
if (v_isShared_6900_ == 0)
{
lean_ctor_set(v___x_6899_, 1, v___x_6908_);
lean_ctor_set(v___x_6899_, 0, v_fst_6891_);
v___x_6910_ = v___x_6899_;
goto v_reusejp_6909_;
}
else
{
lean_object* v_reuseFailAlloc_6919_; 
v_reuseFailAlloc_6919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6919_, 0, v_fst_6891_);
lean_ctor_set(v_reuseFailAlloc_6919_, 1, v___x_6908_);
v___x_6910_ = v_reuseFailAlloc_6919_;
goto v_reusejp_6909_;
}
v_reusejp_6909_:
{
lean_object* v___x_6911_; lean_object* v___x_6913_; 
lean_inc(v_fst_6892_);
v___x_6911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6911_, 0, v___x_6910_);
lean_ctor_set(v___x_6911_, 1, v_fst_6892_);
lean_ctor_set(v___x_6911_, 2, v___y_6907_);
if (v_isShared_6905_ == 0)
{
lean_ctor_set(v___x_6904_, 0, v___x_6911_);
v___x_6913_ = v___x_6904_;
goto v_reusejp_6912_;
}
else
{
lean_object* v_reuseFailAlloc_6918_; 
v_reuseFailAlloc_6918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6918_, 0, v___x_6911_);
v___x_6913_ = v_reuseFailAlloc_6918_;
goto v_reusejp_6912_;
}
v_reusejp_6912_:
{
lean_object* v___x_6914_; lean_object* v___x_6916_; 
v___x_6914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6914_, 0, v___x_6913_);
if (v_isShared_6896_ == 0)
{
lean_ctor_set(v___x_6895_, 1, v___x_6901_);
lean_ctor_set(v___x_6895_, 0, v___x_6914_);
v___x_6916_ = v___x_6895_;
goto v_reusejp_6915_;
}
else
{
lean_object* v_reuseFailAlloc_6917_; 
v_reuseFailAlloc_6917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6917_, 0, v___x_6914_);
lean_ctor_set(v_reuseFailAlloc_6917_, 1, v___x_6901_);
v___x_6916_ = v_reuseFailAlloc_6917_;
goto v_reusejp_6915_;
}
v_reusejp_6915_:
{
return v___x_6916_;
}
}
}
}
}
}
else
{
lean_object* v___x_6925_; size_t v___x_6926_; size_t v___x_6927_; 
lean_del_object(v___x_6899_);
lean_dec(v_definition_x3f_6897_);
lean_del_object(v___x_6895_);
lean_dec(v_snd_6893_);
v___x_6925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6926_ = ((size_t)1ULL);
v___x_6927_ = lean_usize_add(v_i_6884_, v___x_6926_);
v_i_6884_ = v___x_6927_;
v_b_6885_ = v___x_6925_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6933_, lean_object* v_sz_6934_, lean_object* v_i_6935_, lean_object* v_b_6936_){
_start:
{
size_t v_sz_boxed_6937_; size_t v_i_boxed_6938_; lean_object* v_res_6939_; 
v_sz_boxed_6937_ = lean_unbox_usize(v_sz_6934_);
lean_dec(v_sz_6934_);
v_i_boxed_6938_ = lean_unbox_usize(v_i_6935_);
lean_dec(v_i_6935_);
v_res_6939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6933_, v_sz_boxed_6937_, v_i_boxed_6938_, v_b_6936_);
lean_dec_ref(v_b_6936_);
lean_dec_ref(v_as_6933_);
return v_res_6939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6940_, lean_object* v_ident_6941_){
_start:
{
lean_object* v___x_6942_; lean_object* v___x_6943_; lean_object* v___x_6944_; size_t v_sz_6945_; size_t v___x_6946_; lean_object* v___x_6947_; lean_object* v_fst_6948_; 
v___x_6942_ = l_Lean_Server_References_allRefsFor(v_self_6940_, v_ident_6941_);
v___x_6943_ = lean_box(0);
v___x_6944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6945_ = lean_array_size(v___x_6942_);
v___x_6946_ = ((size_t)0ULL);
v___x_6947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6942_, v_sz_6945_, v___x_6946_, v___x_6944_);
lean_dec_ref(v___x_6942_);
v_fst_6948_ = lean_ctor_get(v___x_6947_, 0);
lean_inc(v_fst_6948_);
lean_dec_ref(v___x_6947_);
if (lean_obj_tag(v_fst_6948_) == 0)
{
return v___x_6943_;
}
else
{
lean_object* v_val_6949_; 
v_val_6949_ = lean_ctor_get(v_fst_6948_, 0);
lean_inc(v_val_6949_);
lean_dec_ref_known(v_fst_6948_, 1);
return v_val_6949_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6950_, lean_object* v_a_6951_, lean_object* v_fst_6952_, lean_object* v_init_6953_, lean_object* v_x_6954_){
_start:
{
if (lean_obj_tag(v_x_6954_) == 0)
{
lean_object* v_k_6956_; lean_object* v_v_6957_; lean_object* v_l_6958_; lean_object* v_r_6959_; lean_object* v___x_6960_; 
v_k_6956_ = lean_ctor_get(v_x_6954_, 1);
lean_inc(v_k_6956_);
v_v_6957_ = lean_ctor_get(v_x_6954_, 2);
lean_inc(v_v_6957_);
v_l_6958_ = lean_ctor_get(v_x_6954_, 3);
lean_inc(v_l_6958_);
v_r_6959_ = lean_ctor_get(v_x_6954_, 4);
lean_inc(v_r_6959_);
lean_dec_ref_known(v_x_6954_, 5);
lean_inc_ref(v_fst_6952_);
lean_inc(v_a_6951_);
lean_inc_ref(v_filterMapIdent_6950_);
v___x_6960_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6950_, v_a_6951_, v_fst_6952_, v_init_6953_, v_l_6958_);
if (lean_obj_tag(v_k_6956_) == 0)
{
lean_object* v_definition_x3f_6961_; 
v_definition_x3f_6961_ = lean_ctor_get(v_v_6957_, 0);
lean_inc(v_definition_x3f_6961_);
lean_dec(v_v_6957_);
if (lean_obj_tag(v_definition_x3f_6961_) == 1)
{
lean_object* v_a_6962_; lean_object* v_identName_6963_; lean_object* v_val_6964_; lean_object* v___x_6965_; lean_object* v___x_6966_; 
v_a_6962_ = lean_ctor_get(v___x_6960_, 0);
lean_inc(v_a_6962_);
lean_dec_ref(v___x_6960_);
v_identName_6963_ = lean_ctor_get(v_k_6956_, 1);
lean_inc_ref(v_identName_6963_);
lean_dec_ref_known(v_k_6956_, 2);
v_val_6964_ = lean_ctor_get(v_definition_x3f_6961_, 0);
lean_inc(v_val_6964_);
lean_dec_ref_known(v_definition_x3f_6961_, 1);
v___x_6965_ = l_String_toName(v_identName_6963_);
lean_inc_ref(v_filterMapIdent_6950_);
v___x_6966_ = lean_apply_1(v_filterMapIdent_6950_, v___x_6965_);
if (lean_obj_tag(v___x_6966_) == 1)
{
lean_object* v_val_6967_; lean_object* v___x_6968_; lean_object* v___x_6969_; lean_object* v___x_6970_; 
v_val_6967_ = lean_ctor_get(v___x_6966_, 0);
lean_inc(v_val_6967_);
lean_dec_ref_known(v___x_6966_, 1);
v___x_6968_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6964_);
lean_dec(v_val_6964_);
lean_inc_ref(v_fst_6952_);
lean_inc(v_a_6951_);
v___x_6969_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6969_, 0, v_a_6951_);
lean_ctor_set(v___x_6969_, 1, v_fst_6952_);
lean_ctor_set(v___x_6969_, 2, v_val_6967_);
lean_ctor_set(v___x_6969_, 3, v___x_6968_);
v___x_6970_ = lean_array_push(v_a_6962_, v___x_6969_);
v_init_6953_ = v___x_6970_;
v_x_6954_ = v_r_6959_;
goto _start;
}
else
{
lean_dec(v___x_6966_);
lean_dec(v_val_6964_);
v_init_6953_ = v_a_6962_;
v_x_6954_ = v_r_6959_;
goto _start;
}
}
else
{
lean_object* v_a_6973_; 
lean_dec_ref_known(v_k_6956_, 2);
lean_dec(v_definition_x3f_6961_);
v_a_6973_ = lean_ctor_get(v___x_6960_, 0);
lean_inc(v_a_6973_);
lean_dec_ref(v___x_6960_);
v_init_6953_ = v_a_6973_;
v_x_6954_ = v_r_6959_;
goto _start;
}
}
else
{
lean_object* v_a_6975_; 
lean_dec(v_v_6957_);
lean_dec(v_k_6956_);
v_a_6975_ = lean_ctor_get(v___x_6960_, 0);
lean_inc(v_a_6975_);
lean_dec_ref(v___x_6960_);
v_init_6953_ = v_a_6975_;
v_x_6954_ = v_r_6959_;
goto _start;
}
}
else
{
lean_object* v___x_6977_; 
lean_dec_ref(v_fst_6952_);
lean_dec(v_a_6951_);
lean_dec_ref(v_filterMapIdent_6950_);
v___x_6977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6977_, 0, v_init_6953_);
return v___x_6977_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6978_, lean_object* v_a_6979_, lean_object* v_fst_6980_, lean_object* v_init_6981_, lean_object* v_x_6982_, lean_object* v___y_6983_){
_start:
{
lean_object* v_res_6984_; 
v_res_6984_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6978_, v_a_6979_, v_fst_6980_, v_init_6981_, v_x_6982_);
return v_res_6984_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6985_, lean_object* v_cancelTk_x3f_6986_, lean_object* v_init_6987_, lean_object* v_x_6988_){
_start:
{
lean_object* v_d_6991_; 
if (lean_obj_tag(v_x_6988_) == 0)
{
lean_object* v_k_6993_; lean_object* v_v_6994_; lean_object* v_l_6995_; lean_object* v_r_6996_; lean_object* v___x_6997_; lean_object* v_val_6999_; lean_object* v___x_7002_; 
v_k_6993_ = lean_ctor_get(v_x_6988_, 1);
lean_inc(v_k_6993_);
v_v_6994_ = lean_ctor_get(v_x_6988_, 2);
lean_inc(v_v_6994_);
v_l_6995_ = lean_ctor_get(v_x_6988_, 3);
lean_inc(v_l_6995_);
v_r_6996_ = lean_ctor_get(v_x_6988_, 4);
lean_inc(v_r_6996_);
lean_dec_ref_known(v_x_6988_, 5);
v___x_6997_ = lean_box(0);
lean_inc(v_cancelTk_x3f_6986_);
lean_inc_ref(v_filterMapIdent_6985_);
v___x_7002_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6985_, v_cancelTk_x3f_6986_, v_init_6987_, v_l_6995_);
if (lean_obj_tag(v___x_7002_) == 0)
{
lean_object* v_a_7003_; 
lean_dec(v_r_6996_);
lean_dec(v_v_6994_);
lean_dec(v_k_6993_);
lean_dec(v_cancelTk_x3f_6986_);
lean_dec_ref(v_filterMapIdent_6985_);
v_a_7003_ = lean_ctor_get(v___x_7002_, 0);
lean_inc(v_a_7003_);
lean_dec_ref_known(v___x_7002_, 1);
v_d_6991_ = v_a_7003_;
goto v___jp_6990_;
}
else
{
lean_object* v_snd_7004_; lean_object* v_a_7005_; lean_object* v_fst_7006_; lean_object* v_fst_7007_; lean_object* v_snd_7008_; lean_object* v___x_7010_; uint8_t v_isShared_7011_; uint8_t v_isSharedCheck_7028_; 
v_snd_7004_ = lean_ctor_get(v_v_6994_, 1);
lean_inc(v_snd_7004_);
v_a_7005_ = lean_ctor_get(v___x_7002_, 0);
lean_inc(v_a_7005_);
lean_dec_ref_known(v___x_7002_, 1);
v_fst_7006_ = lean_ctor_get(v_v_6994_, 0);
lean_inc(v_fst_7006_);
lean_dec(v_v_6994_);
v_fst_7007_ = lean_ctor_get(v_snd_7004_, 0);
lean_inc(v_fst_7007_);
lean_dec(v_snd_7004_);
v_snd_7008_ = lean_ctor_get(v_a_7005_, 1);
v_isSharedCheck_7028_ = !lean_is_exclusive(v_a_7005_);
if (v_isSharedCheck_7028_ == 0)
{
lean_object* v_unused_7029_; 
v_unused_7029_ = lean_ctor_get(v_a_7005_, 0);
lean_dec(v_unused_7029_);
v___x_7010_ = v_a_7005_;
v_isShared_7011_ = v_isSharedCheck_7028_;
goto v_resetjp_7009_;
}
else
{
lean_inc(v_snd_7008_);
lean_dec(v_a_7005_);
v___x_7010_ = lean_box(0);
v_isShared_7011_ = v_isSharedCheck_7028_;
goto v_resetjp_7009_;
}
v_resetjp_7009_:
{
if (lean_obj_tag(v_cancelTk_x3f_6986_) == 1)
{
lean_object* v_val_7015_; uint8_t v___x_7016_; 
v_val_7015_ = lean_ctor_get(v_cancelTk_x3f_6986_, 0);
v___x_7016_ = l_IO_CancelToken_isSet(v_val_7015_);
if (v___x_7016_ == 0)
{
lean_del_object(v___x_7010_);
goto v___jp_7012_;
}
else
{
lean_object* v___x_7018_; uint8_t v_isShared_7019_; uint8_t v_isSharedCheck_7026_; 
lean_dec(v_fst_7007_);
lean_dec(v_fst_7006_);
lean_dec(v_r_6996_);
lean_dec(v_k_6993_);
lean_dec_ref(v_filterMapIdent_6985_);
v_isSharedCheck_7026_ = !lean_is_exclusive(v_cancelTk_x3f_6986_);
if (v_isSharedCheck_7026_ == 0)
{
lean_object* v_unused_7027_; 
v_unused_7027_ = lean_ctor_get(v_cancelTk_x3f_6986_, 0);
lean_dec(v_unused_7027_);
v___x_7018_ = v_cancelTk_x3f_6986_;
v_isShared_7019_ = v_isSharedCheck_7026_;
goto v_resetjp_7017_;
}
else
{
lean_dec(v_cancelTk_x3f_6986_);
v___x_7018_ = lean_box(0);
v_isShared_7019_ = v_isSharedCheck_7026_;
goto v_resetjp_7017_;
}
v_resetjp_7017_:
{
lean_object* v___x_7021_; 
lean_inc(v_snd_7008_);
if (v_isShared_7019_ == 0)
{
lean_ctor_set(v___x_7018_, 0, v_snd_7008_);
v___x_7021_ = v___x_7018_;
goto v_reusejp_7020_;
}
else
{
lean_object* v_reuseFailAlloc_7025_; 
v_reuseFailAlloc_7025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7025_, 0, v_snd_7008_);
v___x_7021_ = v_reuseFailAlloc_7025_;
goto v_reusejp_7020_;
}
v_reusejp_7020_:
{
lean_object* v___x_7023_; 
if (v_isShared_7011_ == 0)
{
lean_ctor_set(v___x_7010_, 0, v___x_7021_);
v___x_7023_ = v___x_7010_;
goto v_reusejp_7022_;
}
else
{
lean_object* v_reuseFailAlloc_7024_; 
v_reuseFailAlloc_7024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7024_, 0, v___x_7021_);
lean_ctor_set(v_reuseFailAlloc_7024_, 1, v_snd_7008_);
v___x_7023_ = v_reuseFailAlloc_7024_;
goto v_reusejp_7022_;
}
v_reusejp_7022_:
{
v_d_6991_ = v___x_7023_;
goto v___jp_6990_;
}
}
}
}
}
else
{
lean_del_object(v___x_7010_);
goto v___jp_7012_;
}
v___jp_7012_:
{
lean_object* v___x_7013_; lean_object* v_a_7014_; 
lean_inc_ref(v_filterMapIdent_6985_);
v___x_7013_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6985_, v_k_6993_, v_fst_7006_, v_snd_7008_, v_fst_7007_);
v_a_7014_ = lean_ctor_get(v___x_7013_, 0);
lean_inc(v_a_7014_);
lean_dec_ref(v___x_7013_);
v_val_6999_ = v_a_7014_;
goto v___jp_6998_;
}
}
}
v___jp_6998_:
{
lean_object* v___x_7000_; 
v___x_7000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7000_, 0, v___x_6997_);
lean_ctor_set(v___x_7000_, 1, v_val_6999_);
v_init_6987_ = v___x_7000_;
v_x_6988_ = v_r_6996_;
goto _start;
}
}
else
{
lean_object* v___x_7030_; 
lean_dec(v_cancelTk_x3f_6986_);
lean_dec_ref(v_filterMapIdent_6985_);
v___x_7030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7030_, 0, v_init_6987_);
return v___x_7030_;
}
v___jp_6990_:
{
lean_object* v___x_6992_; 
v___x_6992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6992_, 0, v_d_6991_);
return v___x_6992_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_7031_, lean_object* v_cancelTk_x3f_7032_, lean_object* v_init_7033_, lean_object* v_x_7034_, lean_object* v___y_7035_){
_start:
{
lean_object* v_res_7036_; 
v_res_7036_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7031_, v_cancelTk_x3f_7032_, v_init_7033_, v_x_7034_);
return v_res_7036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_7042_, lean_object* v_filterMapIdent_7043_, lean_object* v_cancelTk_x3f_7044_){
_start:
{
lean_object* v_val_7047_; lean_object* v___x_7051_; lean_object* v___x_7052_; lean_object* v___x_7053_; lean_object* v_a_7054_; 
v___x_7051_ = l_Lean_Server_References_allRefs(v_self_7042_);
v___x_7052_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_7053_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7043_, v_cancelTk_x3f_7044_, v___x_7052_, v___x_7051_);
v_a_7054_ = lean_ctor_get(v___x_7053_, 0);
lean_inc(v_a_7054_);
lean_dec_ref(v___x_7053_);
v_val_7047_ = v_a_7054_;
goto v___jp_7046_;
v___jp_7046_:
{
lean_object* v_fst_7048_; 
v_fst_7048_ = lean_ctor_get(v_val_7047_, 0);
if (lean_obj_tag(v_fst_7048_) == 0)
{
lean_object* v_snd_7049_; 
v_snd_7049_ = lean_ctor_get(v_val_7047_, 1);
lean_inc(v_snd_7049_);
lean_dec_ref(v_val_7047_);
return v_snd_7049_;
}
else
{
lean_object* v_val_7050_; 
lean_inc_ref(v_fst_7048_);
lean_dec_ref(v_val_7047_);
v_val_7050_ = lean_ctor_get(v_fst_7048_, 0);
lean_inc(v_val_7050_);
lean_dec_ref_known(v_fst_7048_, 1);
return v_val_7050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_7055_, lean_object* v_filterMapIdent_7056_, lean_object* v_cancelTk_x3f_7057_, lean_object* v_a_7058_){
_start:
{
lean_object* v_res_7059_; 
v_res_7059_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7055_, v_filterMapIdent_7056_, v_cancelTk_x3f_7057_);
return v_res_7059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_7060_, lean_object* v_self_7061_, lean_object* v_filterMapIdent_7062_, lean_object* v_cancelTk_x3f_7063_){
_start:
{
lean_object* v___x_7065_; 
v___x_7065_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7061_, v_filterMapIdent_7062_, v_cancelTk_x3f_7063_);
return v___x_7065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_7066_, lean_object* v_self_7067_, lean_object* v_filterMapIdent_7068_, lean_object* v_cancelTk_x3f_7069_, lean_object* v_a_7070_){
_start:
{
lean_object* v_res_7071_; 
v_res_7071_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_7066_, v_self_7067_, v_filterMapIdent_7068_, v_cancelTk_x3f_7069_);
return v_res_7071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_7072_, lean_object* v_filterMapIdent_7073_, lean_object* v_a_7074_, lean_object* v_fst_7075_, lean_object* v_init_7076_, lean_object* v_x_7077_){
_start:
{
lean_object* v___x_7079_; 
v___x_7079_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_7073_, v_a_7074_, v_fst_7075_, v_init_7076_, v_x_7077_);
return v___x_7079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_7080_, lean_object* v_filterMapIdent_7081_, lean_object* v_a_7082_, lean_object* v_fst_7083_, lean_object* v_init_7084_, lean_object* v_x_7085_, lean_object* v___y_7086_){
_start:
{
lean_object* v_res_7087_; 
v_res_7087_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_7080_, v_filterMapIdent_7081_, v_a_7082_, v_fst_7083_, v_init_7084_, v_x_7085_);
return v_res_7087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_7088_, lean_object* v_filterMapIdent_7089_, lean_object* v_cancelTk_x3f_7090_, lean_object* v_init_7091_, lean_object* v_x_7092_){
_start:
{
lean_object* v___x_7094_; 
v___x_7094_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7089_, v_cancelTk_x3f_7090_, v_init_7091_, v_x_7092_);
return v___x_7094_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7095_, lean_object* v_filterMapIdent_7096_, lean_object* v_cancelTk_x3f_7097_, lean_object* v_init_7098_, lean_object* v_x_7099_, lean_object* v___y_7100_){
_start:
{
lean_object* v_res_7101_; 
v_res_7101_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7095_, v_filterMapIdent_7096_, v_cancelTk_x3f_7097_, v_init_7098_, v_x_7099_);
return v_res_7101_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7102_){
_start:
{
lean_object* v___x_7103_; lean_object* v___x_7104_; 
v___x_7103_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7104_ = lean_panic_fn_borrowed(v___x_7103_, v_msg_7102_);
return v___x_7104_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7108_; lean_object* v___x_7109_; lean_object* v___x_7110_; lean_object* v___x_7111_; lean_object* v___x_7112_; lean_object* v___x_7113_; 
v___x_7108_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7109_ = lean_unsigned_to_nat(14u);
v___x_7110_ = lean_unsigned_to_nat(22u);
v___x_7111_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7112_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7113_ = l_mkPanicMessageWithDecl(v___x_7112_, v___x_7111_, v___x_7110_, v___x_7109_, v___x_7108_);
return v___x_7113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7114_, lean_object* v_init_7115_, lean_object* v_x_7116_){
_start:
{
if (lean_obj_tag(v_x_7116_) == 0)
{
lean_object* v_k_7117_; lean_object* v_v_7118_; lean_object* v_l_7119_; lean_object* v_r_7120_; lean_object* v___x_7121_; lean_object* v_a_7122_; lean_object* v_fst_7123_; lean_object* v_snd_7124_; lean_object* v___y_7126_; lean_object* v_index_7141_; lean_object* v___x_7142_; 
v_k_7117_ = lean_ctor_get(v_x_7116_, 1);
v_v_7118_ = lean_ctor_get(v_x_7116_, 2);
v_l_7119_ = lean_ctor_get(v_x_7116_, 3);
v_r_7120_ = lean_ctor_get(v_x_7116_, 4);
v___x_7121_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7114_, v_init_7115_, v_l_7119_);
v_a_7122_ = lean_ctor_get(v___x_7121_, 0);
lean_inc(v_a_7122_);
lean_dec_ref(v___x_7121_);
v_fst_7123_ = lean_ctor_get(v_v_7118_, 0);
v_snd_7124_ = lean_ctor_get(v_v_7118_, 1);
v_index_7141_ = lean_ctor_get(v_snd_7124_, 1);
v___x_7142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7141_, v_requestedMod_7114_);
if (lean_obj_tag(v___x_7142_) == 1)
{
lean_object* v_val_7143_; lean_object* v___x_7144_; 
v_val_7143_ = lean_ctor_get(v___x_7142_, 0);
lean_inc(v_val_7143_);
lean_dec_ref_known(v___x_7142_, 1);
v___x_7144_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7143_);
lean_dec(v_val_7143_);
if (lean_obj_tag(v___x_7144_) == 0)
{
lean_object* v___x_7145_; lean_object* v___x_7146_; 
v___x_7145_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7146_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7145_);
v___y_7126_ = v___x_7146_;
goto v___jp_7125_;
}
else
{
lean_object* v_val_7147_; 
v_val_7147_ = lean_ctor_get(v___x_7144_, 0);
lean_inc(v_val_7147_);
lean_dec_ref_known(v___x_7144_, 1);
v___y_7126_ = v_val_7147_;
goto v___jp_7125_;
}
}
else
{
lean_dec(v___x_7142_);
v_init_7115_ = v_a_7122_;
v_x_7116_ = v_r_7120_;
goto _start;
}
v___jp_7125_:
{
uint8_t v_isAll_7127_; uint8_t v_isPrivate_7128_; uint8_t v_metaKind_7129_; lean_object* v___x_7131_; uint8_t v_isShared_7132_; uint8_t v_isSharedCheck_7138_; 
v_isAll_7127_ = lean_ctor_get_uint8(v___y_7126_, sizeof(void*)*2);
v_isPrivate_7128_ = lean_ctor_get_uint8(v___y_7126_, sizeof(void*)*2 + 1);
v_metaKind_7129_ = lean_ctor_get_uint8(v___y_7126_, sizeof(void*)*2 + 2);
v_isSharedCheck_7138_ = !lean_is_exclusive(v___y_7126_);
if (v_isSharedCheck_7138_ == 0)
{
lean_object* v_unused_7139_; lean_object* v_unused_7140_; 
v_unused_7139_ = lean_ctor_get(v___y_7126_, 1);
lean_dec(v_unused_7139_);
v_unused_7140_ = lean_ctor_get(v___y_7126_, 0);
lean_dec(v_unused_7140_);
v___x_7131_ = v___y_7126_;
v_isShared_7132_ = v_isSharedCheck_7138_;
goto v_resetjp_7130_;
}
else
{
lean_dec(v___y_7126_);
v___x_7131_ = lean_box(0);
v_isShared_7132_ = v_isSharedCheck_7138_;
goto v_resetjp_7130_;
}
v_resetjp_7130_:
{
lean_object* v___x_7134_; 
lean_inc(v_fst_7123_);
lean_inc(v_k_7117_);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 1, v_fst_7123_);
lean_ctor_set(v___x_7131_, 0, v_k_7117_);
v___x_7134_ = v___x_7131_;
goto v_reusejp_7133_;
}
else
{
lean_object* v_reuseFailAlloc_7137_; 
v_reuseFailAlloc_7137_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7137_, 0, v_k_7117_);
lean_ctor_set(v_reuseFailAlloc_7137_, 1, v_fst_7123_);
lean_ctor_set_uint8(v_reuseFailAlloc_7137_, sizeof(void*)*2, v_isAll_7127_);
lean_ctor_set_uint8(v_reuseFailAlloc_7137_, sizeof(void*)*2 + 1, v_isPrivate_7128_);
lean_ctor_set_uint8(v_reuseFailAlloc_7137_, sizeof(void*)*2 + 2, v_metaKind_7129_);
v___x_7134_ = v_reuseFailAlloc_7137_;
goto v_reusejp_7133_;
}
v_reusejp_7133_:
{
lean_object* v___x_7135_; 
v___x_7135_ = lean_array_push(v_a_7122_, v___x_7134_);
v_init_7115_ = v___x_7135_;
v_x_7116_ = v_r_7120_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7149_; 
v___x_7149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7149_, 0, v_init_7115_);
return v___x_7149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object* v_requestedMod_7150_, lean_object* v_init_7151_, lean_object* v_x_7152_){
_start:
{
lean_object* v_res_7153_; 
v_res_7153_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7150_, v_init_7151_, v_x_7152_);
lean_dec(v_x_7152_);
lean_dec(v_requestedMod_7150_);
return v_res_7153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object* v_self_7154_, lean_object* v_requestedMod_7155_){
_start:
{
lean_object* v_result_7156_; lean_object* v___x_7157_; lean_object* v___x_7158_; lean_object* v_a_7159_; 
v_result_7156_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_7157_ = l_Lean_Server_References_allDirectImports(v_self_7154_);
v___x_7158_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7155_, v_result_7156_, v___x_7157_);
lean_dec(v___x_7157_);
v_a_7159_ = lean_ctor_get(v___x_7158_, 0);
lean_inc(v_a_7159_);
lean_dec_ref(v___x_7158_);
return v_a_7159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object* v_self_7160_, lean_object* v_requestedMod_7161_){
_start:
{
lean_object* v_res_7162_; 
v_res_7162_ = l_Lean_Server_References_importedBy(v_self_7160_, v_requestedMod_7161_);
lean_dec(v_requestedMod_7161_);
return v_res_7162_;
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

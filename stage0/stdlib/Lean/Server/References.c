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
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_findReferences(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_findReferences___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
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
lean_inc(v_size_83_);
v_k_84_ = lean_ctor_get(v_impl_80_, 1);
lean_inc(v_k_84_);
v_v_85_ = lean_ctor_get(v_impl_80_, 2);
lean_inc(v_v_85_);
v_l_86_ = lean_ctor_get(v_impl_80_, 3);
lean_inc(v_l_86_);
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
lean_dec(v_l_86_);
lean_dec(v_v_85_);
lean_dec(v_k_84_);
v___x_91_ = lean_nat_add(v___x_81_, v_size_83_);
lean_dec(v_size_83_);
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
lean_inc(v_l_167_);
if (lean_obj_tag(v_l_167_) == 0)
{
lean_object* v_r_168_; lean_object* v_k_169_; lean_object* v_v_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_181_; 
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
lean_inc(v_size_223_);
v_k_224_ = lean_ctor_get(v_impl_220_, 1);
lean_inc(v_k_224_);
v_v_225_ = lean_ctor_get(v_impl_220_, 2);
lean_inc(v_v_225_);
v_l_226_ = lean_ctor_get(v_impl_220_, 3);
lean_inc(v_l_226_);
v_r_227_ = lean_ctor_get(v_impl_220_, 4);
lean_inc(v_r_227_);
v___x_228_ = lean_unsigned_to_nat(3u);
v___x_229_ = lean_nat_mul(v___x_228_, v_size_222_);
v___x_230_ = lean_nat_dec_lt(v___x_229_, v_size_223_);
lean_dec(v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
lean_dec(v_r_227_);
lean_dec(v_l_226_);
lean_dec(v_v_225_);
lean_dec(v_k_224_);
v___x_231_ = lean_nat_add(v___x_221_, v_size_222_);
v___x_232_ = lean_nat_add(v___x_231_, v_size_223_);
lean_dec(v_size_223_);
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
lean_inc(v_size_573_);
v_k_574_ = lean_ctor_get(v_impl_570_, 1);
lean_inc(v_k_574_);
v_v_575_ = lean_ctor_get(v_impl_570_, 2);
lean_inc(v_v_575_);
v_l_576_ = lean_ctor_get(v_impl_570_, 3);
lean_inc(v_l_576_);
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
lean_dec(v_l_576_);
lean_dec(v_v_575_);
lean_dec(v_k_574_);
v___x_581_ = lean_nat_add(v___x_571_, v_size_573_);
lean_dec(v_size_573_);
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
lean_inc(v_l_657_);
if (lean_obj_tag(v_l_657_) == 0)
{
lean_object* v_r_658_; lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_671_; 
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
lean_inc(v_size_713_);
v_k_714_ = lean_ctor_get(v_impl_710_, 1);
lean_inc(v_k_714_);
v_v_715_ = lean_ctor_get(v_impl_710_, 2);
lean_inc(v_v_715_);
v_l_716_ = lean_ctor_get(v_impl_710_, 3);
lean_inc(v_l_716_);
v_r_717_ = lean_ctor_get(v_impl_710_, 4);
lean_inc(v_r_717_);
v___x_718_ = lean_unsigned_to_nat(3u);
v___x_719_ = lean_nat_mul(v___x_718_, v_size_712_);
v___x_720_ = lean_nat_dec_lt(v___x_719_, v_size_713_);
lean_dec(v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
lean_dec(v_r_717_);
lean_dec(v_l_716_);
lean_dec(v_v_715_);
lean_dec(v_k_714_);
v___x_721_ = lean_nat_add(v___x_711_, v_size_712_);
v___x_722_ = lean_nat_add(v___x_721_, v_size_713_);
lean_dec(v_size_713_);
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
v___x_747_ = lean_nat_add(v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec(v___y_745_);
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
lean_ctor_set(v___x_727_, 3, v___y_744_);
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
lean_ctor_set(v_reuseFailAlloc_752_, 3, v___y_744_);
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
v___y_744_ = v___x_758_;
v___y_745_ = v___x_759_;
v___y_746_ = v_size_760_;
goto v___jp_743_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = lean_unsigned_to_nat(0u);
v___y_744_ = v___x_758_;
v___y_745_ = v___x_759_;
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
v___x_1012_ = l_Lean_Lsp_RefInfo_contains(v_v_1007_, v_pos_1002_, v_includeStop_1003_);
lean_dec(v_v_1007_);
if (v___x_1012_ == 0)
{
lean_object* v_a_1013_; 
lean_dec(v_a_1011_);
lean_dec(v_k_1006_);
v_a_1013_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1010_);
v_init_1004_ = v_a_1013_;
v_x_1005_ = v_r_1009_;
goto _start;
}
else
{
lean_object* v___x_1015_; 
lean_dec_ref(v___x_1010_);
v___x_1015_ = lean_array_push(v_a_1011_, v_k_1006_);
v_init_1004_ = v___x_1015_;
v_x_1005_ = v_r_1009_;
goto _start;
}
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_init_1004_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0___boxed(lean_object* v_pos_1018_, lean_object* v_includeStop_1019_, lean_object* v_init_1020_, lean_object* v_x_1021_){
_start:
{
uint8_t v_includeStop_boxed_1022_; lean_object* v_res_1023_; 
v_includeStop_boxed_1022_ = lean_unbox(v_includeStop_1019_);
v_res_1023_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1018_, v_includeStop_boxed_1022_, v_init_1020_, v_x_1021_);
lean_dec_ref(v_pos_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt(lean_object* v_self_1026_, lean_object* v_pos_1027_, uint8_t v_includeStop_1028_){
_start:
{
lean_object* v_result_1029_; lean_object* v___x_1030_; lean_object* v_a_1031_; 
v_result_1029_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_1030_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1027_, v_includeStop_1028_, v_result_1029_, v_self_1026_);
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref(v___x_1030_);
return v_a_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt___boxed(lean_object* v_self_1032_, lean_object* v_pos_1033_, lean_object* v_includeStop_1034_){
_start:
{
uint8_t v_includeStop_boxed_1035_; lean_object* v_res_1036_; 
v_includeStop_boxed_1035_ = lean_unbox(v_includeStop_1034_);
v_res_1036_ = l_Lean_Lsp_ModuleRefs_findAt(v_self_1032_, v_pos_1033_, v_includeStop_boxed_1035_);
lean_dec_ref(v_pos_1033_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(lean_object* v_pos_1040_, uint8_t v_includeStop_1041_, lean_object* v_init_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v_d_1045_; 
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_object* v_v_1048_; lean_object* v_l_1049_; lean_object* v_r_1050_; lean_object* v___x_1051_; lean_object* v_val_1052_; 
v_v_1048_ = lean_ctor_get(v_x_1043_, 2);
v_l_1049_ = lean_ctor_get(v_x_1043_, 3);
v_r_1050_ = lean_ctor_get(v_x_1043_, 4);
v___x_1051_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1040_, v_includeStop_1041_, v_init_1042_, v_l_1049_);
v_val_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_val_1052_);
lean_dec(v___x_1051_);
if (lean_obj_tag(v_val_1052_) == 0)
{
lean_object* v_a_1053_; 
v_a_1053_ = lean_ctor_get(v_val_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v_val_1052_, 1);
v_d_1045_ = v_a_1053_;
goto v___jp_1044_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref_known(v_val_1052_, 1);
v___x_1054_ = lean_box(0);
v___x_1055_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_v_1048_, v_pos_1040_, v_includeStop_1041_);
if (lean_obj_tag(v___x_1055_) == 1)
{
lean_object* v_val_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1065_; 
v_val_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_val_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = l_Lean_Lsp_RefInfo_Location_range(v_val_1056_);
lean_dec(v_val_1056_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___x_1054_);
v_d_1045_ = v___x_1063_;
goto v___jp_1044_;
}
}
}
else
{
lean_object* v___x_1066_; 
lean_dec(v___x_1055_);
v___x_1066_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0));
v_init_1042_ = v___x_1066_;
v_x_1043_ = v_r_1050_;
goto _start;
}
}
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_init_1042_);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
v___jp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v_d_1045_);
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___boxed(lean_object* v_pos_1070_, lean_object* v_includeStop_1071_, lean_object* v_init_1072_, lean_object* v_x_1073_){
_start:
{
uint8_t v_includeStop_boxed_1074_; lean_object* v_res_1075_; 
v_includeStop_boxed_1074_ = lean_unbox(v_includeStop_1071_);
v_res_1075_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1070_, v_includeStop_boxed_1074_, v_init_1072_, v_x_1073_);
lean_dec(v_x_1073_);
lean_dec_ref(v_pos_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f(lean_object* v_self_1076_, lean_object* v_pos_1077_, uint8_t v_includeStop_1078_){
_start:
{
lean_object* v___x_1079_; lean_object* v_val_1081_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_val_1085_; lean_object* v_a_1086_; 
v___x_1079_ = lean_box(0);
v___x_1083_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0));
v___x_1084_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1077_, v_includeStop_1078_, v___x_1083_, v_self_1076_);
v_val_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_val_1085_);
lean_dec(v___x_1084_);
v_a_1086_ = lean_ctor_get(v_val_1085_, 0);
lean_inc(v_a_1086_);
lean_dec(v_val_1085_);
v_val_1081_ = v_a_1086_;
goto v___jp_1080_;
v___jp_1080_:
{
lean_object* v_fst_1082_; 
v_fst_1082_ = lean_ctor_get(v_val_1081_, 0);
lean_inc(v_fst_1082_);
lean_dec_ref(v_val_1081_);
if (lean_obj_tag(v_fst_1082_) == 0)
{
return v___x_1079_;
}
else
{
return v_fst_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f___boxed(lean_object* v_self_1087_, lean_object* v_pos_1088_, lean_object* v_includeStop_1089_){
_start:
{
uint8_t v_includeStop_boxed_1090_; lean_object* v_res_1091_; 
v_includeStop_boxed_1090_ = lean_unbox(v_includeStop_1089_);
v_res_1091_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_self_1087_, v_pos_1088_, v_includeStop_boxed_1090_);
lean_dec_ref(v_pos_1088_);
lean_dec(v_self_1087_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(lean_object* v_j_1092_, lean_object* v_k_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = l_Lean_Json_getObjValD(v_j_1092_, v_k_1093_);
v___x_1095_ = l_Lean_Json_getNat_x3f(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0___boxed(lean_object* v_j_1096_, lean_object* v_k_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(v_j_1096_, v_k_1097_);
lean_dec_ref(v_k_1097_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(lean_object* v_j_1099_, lean_object* v_k_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = l_Lean_Json_getObjValD(v_j_1099_, v_k_1100_);
v___x_1102_ = l_Lean_Name_fromJson_x3f(v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1___boxed(lean_object* v_j_1103_, lean_object* v_k_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(v_j_1103_, v_k_1104_);
lean_dec_ref(v_k_1104_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(lean_object* v_init_1110_, lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
lean_object* v_k_1112_; lean_object* v_v_1113_; lean_object* v_l_1114_; lean_object* v_r_1115_; lean_object* v___x_1116_; 
v_k_1112_ = lean_ctor_get(v_x_1111_, 1);
lean_inc(v_k_1112_);
v_v_1113_ = lean_ctor_get(v_x_1111_, 2);
lean_inc(v_v_1113_);
v_l_1114_ = lean_ctor_get(v_x_1111_, 3);
lean_inc(v_l_1114_);
v_r_1115_ = lean_ctor_get(v_x_1111_, 4);
lean_inc(v_r_1115_);
lean_dec_ref_known(v_x_1111_, 5);
v___x_1116_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(v_init_1110_, v_l_1114_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_dec(v_r_1115_);
lean_dec(v_v_1113_);
lean_dec(v_k_1112_);
return v___x_1116_;
}
else
{
if (lean_obj_tag(v_v_1113_) == 4)
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1231_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1231_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1231_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v_elems_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_elems_1121_ = lean_ctor_get(v_v_1113_, 0);
lean_inc_ref(v_elems_1121_);
lean_dec_ref_known(v_v_1113_, 1);
v___x_1122_ = lean_array_get_size(v_elems_1121_);
v___x_1123_ = lean_unsigned_to_nat(8u);
v___x_1124_ = lean_nat_dec_eq(v___x_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_dec_ref(v_elems_1121_);
lean_dec(v_a_1117_);
lean_dec(v_r_1115_);
lean_dec(v_k_1112_);
v___x_1125_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__0));
v___x_1126_ = l_Nat_reprFast(v___x_1122_);
v___x_1127_ = lean_string_append(v___x_1125_, v___x_1126_);
lean_dec_ref(v___x_1126_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1127_);
v___x_1129_ = v___x_1119_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_del_object(v___x_1119_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_array_get_borrowed(v___x_1131_, v_elems_1121_, v___x_1132_);
lean_inc(v___x_1133_);
v___x_1134_ = l_Lean_Json_getNat_x3f(v___x_1133_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v_elems_1121_);
lean_dec(v_a_1117_);
lean_dec(v_r_1115_);
lean_dec(v_k_1112_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_a_1143_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_array_get_borrowed(v___x_1131_, v_elems_1121_, v___x_1144_);
lean_inc(v___x_1145_);
v___x_1146_ = l_Lean_Json_getNat_x3f(v___x_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_a_1143_);
lean_dec_ref(v_elems_1121_);
lean_dec(v_a_1117_);
lean_dec(v_r_1115_);
lean_dec(v_k_1112_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_a_1155_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1156_ = lean_unsigned_to_nat(2u);
v___x_1157_ = lean_array_get_borrowed(v___x_1131_, v_elems_1121_, v___x_1156_);
lean_inc(v___x_1157_);
v___x_1158_ = l_Lean_Json_getNat_x3f(v___x_1157_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_a_1155_);
lean_dec(v_a_1143_);
lean_dec_ref(v_elems_1121_);
lean_dec(v_a_1117_);
lean_dec(v_r_1115_);
lean_dec(v_k_1112_);
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_a_1167_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1168_ = lean_unsigned_to_nat(3u);
v___x_1169_ = lean_array_get_borrowed(v___x_1131_, v_elems_1121_, v___x_1168_);
lean_inc(v___x_1169_);
v___x_1170_ = l_Lean_Json_getNat_x3f(v___x_1169_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec(v_a_1167_);
lean_dec(v_a_1155_);
lean_dec(v_a_1143_);
lean_dec_ref(v_elems_1121_);
lean_dec(v_a_1117_);
lean_dec(v_r_1115_);
lean_dec(v_k_1112_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1179_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1180_ = lean_unsigned_to_nat(4u);
v___x_1181_ = lean_array_get_borrowed(v___x_1131_, v_elems_1121_, v___x_1180_);
lean_inc(v___x_1181_);
v___x_1182_ = l_Lean_Json_getNat_x3f(v___x_1181_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec(v_a_1179_);
lean_dec(v_a_1167_);
lean_dec(v_a_1155_);
lean_dec(v_a_1143_);
lean_dec_ref(v_elems_1121_);
lean_dec(v_a_1117_);
lean_dec(v_r_1115_);
lean_dec(v_k_1112_);
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_a_1191_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1182_, 1);
v___x_1192_ = lean_unsigned_to_nat(5u);
v___x_1193_ = lean_array_get_borrowed(v___x_1131_, v_elems_1121_, v___x_1192_);
lean_inc(v___x_1193_);
v___x_1194_ = l_Lean_Json_getNat_x3f(v___x_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec(v_a_1191_);
lean_dec(v_a_1179_);
lean_dec(v_a_1167_);
lean_dec(v_a_1155_);
lean_dec(v_a_1143_);
lean_dec_ref(v_elems_1121_);
lean_dec(v_a_1117_);
lean_dec(v_r_1115_);
lean_dec(v_k_1112_);
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_a_1203_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1204_ = lean_unsigned_to_nat(6u);
v___x_1205_ = lean_array_get_borrowed(v___x_1131_, v_elems_1121_, v___x_1204_);
lean_inc(v___x_1205_);
v___x_1206_ = l_Lean_Json_getNat_x3f(v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_a_1203_);
lean_dec(v_a_1191_);
lean_dec(v_a_1179_);
lean_dec(v_a_1167_);
lean_dec(v_a_1155_);
lean_dec(v_a_1143_);
lean_dec_ref(v_elems_1121_);
lean_dec(v_a_1117_);
lean_dec(v_r_1115_);
lean_dec(v_k_1112_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_a_1215_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1216_ = lean_unsigned_to_nat(7u);
v___x_1217_ = lean_array_get(v___x_1131_, v_elems_1121_, v___x_1216_);
lean_dec_ref(v_elems_1121_);
v___x_1218_ = l_Lean_Json_getNat_x3f(v___x_1217_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_a_1215_);
lean_dec(v_a_1203_);
lean_dec(v_a_1191_);
lean_dec(v_a_1179_);
lean_dec(v_a_1167_);
lean_dec(v_a_1155_);
lean_dec(v_a_1143_);
lean_dec(v_a_1117_);
lean_dec(v_r_1115_);
lean_dec(v_k_1112_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_a_1227_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1218_, 1);
v___x_1228_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1228_, 0, v_a_1143_);
lean_ctor_set(v___x_1228_, 1, v_a_1155_);
lean_ctor_set(v___x_1228_, 2, v_a_1167_);
lean_ctor_set(v___x_1228_, 3, v_a_1179_);
lean_ctor_set(v___x_1228_, 4, v_a_1191_);
lean_ctor_set(v___x_1228_, 5, v_a_1203_);
lean_ctor_set(v___x_1228_, 6, v_a_1215_);
lean_ctor_set(v___x_1228_, 7, v_a_1227_);
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_1112_, v___x_1228_, v_a_1117_);
v_init_1110_ = v___x_1229_;
v_x_1111_ = v_r_1115_;
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
lean_object* v___x_1232_; 
lean_dec_ref_known(v___x_1116_, 1);
lean_dec(v_r_1115_);
lean_dec(v_v_1113_);
lean_dec(v_k_1112_);
v___x_1232_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__2));
return v___x_1232_;
}
}
}
else
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_init_1110_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(lean_object* v_j_1234_, lean_object* v_k_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = l_Lean_Json_getObjValD(v_j_1234_, v_k_1235_);
v___x_1237_ = l_Lean_Json_getObj_x3f(v___x_1236_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_a_1246_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1247_ = lean_box(1);
v___x_1248_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(v___x_1247_, v_a_1246_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4___boxed(lean_object* v_j_1249_, lean_object* v_k_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(v_j_1249_, v_k_1250_);
lean_dec_ref(v_k_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(size_t v_sz_1252_, size_t v_i_1253_, lean_object* v_bs_1254_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_usize_dec_lt(v_i_1253_, v_sz_1252_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_bs_1254_);
return v___x_1256_;
}
else
{
lean_object* v_v_1257_; lean_object* v___x_1258_; lean_object* v_bs_x27_1259_; size_t v___x_1260_; size_t v___x_1261_; lean_object* v___x_1262_; 
v_v_1257_ = lean_array_uget(v_bs_1254_, v_i_1253_);
v___x_1258_ = lean_unsigned_to_nat(0u);
v_bs_x27_1259_ = lean_array_uset(v_bs_1254_, v_i_1253_, v___x_1258_);
v___x_1260_ = ((size_t)1ULL);
v___x_1261_ = lean_usize_add(v_i_1253_, v___x_1260_);
v___x_1262_ = lean_array_uset(v_bs_x27_1259_, v_i_1253_, v_v_1257_);
v_i_1253_ = v___x_1261_;
v_bs_1254_ = v___x_1262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13___boxed(lean_object* v_sz_1264_, lean_object* v_i_1265_, lean_object* v_bs_1266_){
_start:
{
size_t v_sz_boxed_1267_; size_t v_i_boxed_1268_; lean_object* v_res_1269_; 
v_sz_boxed_1267_ = lean_unbox_usize(v_sz_1264_);
lean_dec(v_sz_1264_);
v_i_boxed_1268_ = lean_unbox_usize(v_i_1265_);
lean_dec(v_i_1265_);
v_res_1269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(v_sz_boxed_1267_, v_i_boxed_1268_, v_bs_1266_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(lean_object* v_x_1272_){
_start:
{
if (lean_obj_tag(v_x_1272_) == 4)
{
lean_object* v_elems_1273_; size_t v_sz_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v_elems_1273_ = lean_ctor_get(v_x_1272_, 0);
lean_inc_ref(v_elems_1273_);
lean_dec_ref_known(v_x_1272_, 1);
v_sz_1274_ = lean_array_size(v_elems_1273_);
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(v_sz_1274_, v___x_1275_, v_elems_1273_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1277_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1278_ = lean_unsigned_to_nat(80u);
v___x_1279_ = l_Lean_Json_pretty(v_x_1272_, v___x_1278_);
v___x_1280_ = lean_string_append(v___x_1277_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1282_ = lean_string_append(v___x_1280_, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(size_t v_sz_1284_, size_t v_i_1285_, lean_object* v_bs_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_usize_dec_lt(v_i_1285_, v_sz_1284_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_bs_1286_);
return v___x_1288_;
}
else
{
lean_object* v_v_1289_; lean_object* v___x_1290_; 
v_v_1289_ = lean_array_uget_borrowed(v_bs_1286_, v_i_1285_);
lean_inc(v_v_1289_);
v___x_1290_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(v_v_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_bs_1286_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v_bs_x27_1301_; size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v_a_1299_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1300_ = lean_unsigned_to_nat(0u);
v_bs_x27_1301_ = lean_array_uset(v_bs_1286_, v_i_1285_, v___x_1300_);
v___x_1302_ = ((size_t)1ULL);
v___x_1303_ = lean_usize_add(v_i_1285_, v___x_1302_);
v___x_1304_ = lean_array_uset(v_bs_x27_1301_, v_i_1285_, v_a_1299_);
v_i_1285_ = v___x_1303_;
v_bs_1286_ = v___x_1304_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9___boxed(lean_object* v_sz_1306_, lean_object* v_i_1307_, lean_object* v_bs_1308_){
_start:
{
size_t v_sz_boxed_1309_; size_t v_i_boxed_1310_; lean_object* v_res_1311_; 
v_sz_boxed_1309_ = lean_unbox_usize(v_sz_1306_);
lean_dec(v_sz_1306_);
v_i_boxed_1310_ = lean_unbox_usize(v_i_1307_);
lean_dec(v_i_1307_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(v_sz_boxed_1309_, v_i_boxed_1310_, v_bs_1308_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(lean_object* v_x_1312_){
_start:
{
if (lean_obj_tag(v_x_1312_) == 4)
{
lean_object* v_elems_1313_; size_t v_sz_1314_; size_t v___x_1315_; lean_object* v___x_1316_; 
v_elems_1313_ = lean_ctor_get(v_x_1312_, 0);
lean_inc_ref(v_elems_1313_);
lean_dec_ref_known(v_x_1312_, 1);
v_sz_1314_ = lean_array_size(v_elems_1313_);
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(v_sz_1314_, v___x_1315_, v_elems_1313_);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1317_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1318_ = lean_unsigned_to_nat(80u);
v___x_1319_ = l_Lean_Json_pretty(v_x_1312_, v___x_1318_);
v___x_1320_ = lean_string_append(v___x_1317_, v___x_1319_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1322_ = lean_string_append(v___x_1320_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(lean_object* v_j_1324_, lean_object* v_k_1325_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = l_Lean_Json_getObjValD(v_j_1324_, v_k_1325_);
v___x_1327_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4___boxed(lean_object* v_j_1328_, lean_object* v_k_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(v_j_1328_, v_k_1329_);
lean_dec_ref(v_k_1329_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_bs_1335_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_bs_1335_);
return v___x_1337_;
}
else
{
lean_object* v_v_1338_; lean_object* v___x_1339_; lean_object* v_bs_x27_1340_; lean_object* v_a_1342_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___y_1350_; uint8_t v___y_1414_; uint8_t v___y_1415_; uint8_t v___y_1416_; uint8_t v___y_1422_; uint8_t v___x_1426_; 
v_v_1338_ = lean_array_uget(v_bs_1335_, v_i_1334_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v_bs_x27_1340_ = lean_array_uset(v_bs_1335_, v_i_1334_, v___x_1339_);
v___x_1347_ = lean_array_get_size(v_v_1338_);
v___x_1348_ = lean_unsigned_to_nat(4u);
v___x_1426_ = lean_nat_dec_eq(v___x_1347_, v___x_1348_);
if (v___x_1426_ == 0)
{
v___y_1422_ = v___x_1336_;
goto v___jp_1421_;
}
else
{
uint8_t v___x_1427_; 
v___x_1427_ = 0;
v___y_1422_ = v___x_1427_;
goto v___jp_1421_;
}
v___jp_1341_:
{
size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = ((size_t)1ULL);
v___x_1344_ = lean_usize_add(v_i_1334_, v___x_1343_);
v___x_1345_ = lean_array_uset(v_bs_x27_1340_, v_i_1334_, v_a_1342_);
v_i_1334_ = v___x_1344_;
v_bs_1335_ = v___x_1345_;
goto _start;
}
v___jp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_array_fget_borrowed(v_v_1338_, v___x_1339_);
lean_inc(v___x_1351_);
v___x_1352_ = l_Lean_Json_getNat_x3f(v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_a_1361_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_array_fget_borrowed(v_v_1338_, v___x_1362_);
lean_inc(v___x_1363_);
v___x_1364_ = l_Lean_Json_getNat_x3f(v___x_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_a_1361_);
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_a_1373_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1374_ = lean_unsigned_to_nat(2u);
v___x_1375_ = lean_array_fget_borrowed(v_v_1338_, v___x_1374_);
lean_inc(v___x_1375_);
v___x_1376_ = l_Lean_Json_getNat_x3f(v___x_1375_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_a_1373_);
lean_dec(v_a_1361_);
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_a_1385_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1386_ = lean_unsigned_to_nat(3u);
v___x_1387_ = lean_array_fget_borrowed(v_v_1338_, v___x_1386_);
lean_inc(v___x_1387_);
v___x_1388_ = l_Lean_Json_getNat_x3f(v___x_1387_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec(v_a_1385_);
lean_dec(v_a_1373_);
lean_dec(v_a_1361_);
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
if (v___y_1350_ == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec(v_v_1338_);
v_a_1397_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
v___x_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1399_, 0, v_a_1361_);
lean_ctor_set(v___x_1399_, 1, v_a_1373_);
lean_ctor_set(v___x_1399_, 2, v_a_1385_);
lean_ctor_set(v___x_1399_, 3, v_a_1397_);
lean_ctor_set(v___x_1399_, 4, v___x_1398_);
v_a_1342_ = v___x_1399_;
goto v___jp_1341_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_a_1400_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1401_ = lean_array_fget(v_v_1338_, v___x_1348_);
lean_dec(v_v_1338_);
v___x_1402_ = l_Lean_Json_getStr_x3f(v___x_1401_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_a_1400_);
lean_dec(v_a_1385_);
lean_dec(v_a_1373_);
lean_dec(v_a_1361_);
lean_dec_ref(v_bs_x27_1340_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1412_; 
v_a_1411_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1412_, 0, v_a_1361_);
lean_ctor_set(v___x_1412_, 1, v_a_1373_);
lean_ctor_set(v___x_1412_, 2, v_a_1385_);
lean_ctor_set(v___x_1412_, 3, v_a_1400_);
lean_ctor_set(v___x_1412_, 4, v_a_1411_);
v_a_1342_ = v___x_1412_;
goto v___jp_1341_;
}
}
}
}
}
}
}
v___jp_1413_:
{
if (v___y_1414_ == 0)
{
v___y_1350_ = v___y_1415_;
goto v___jp_1349_;
}
else
{
if (v___y_1416_ == 0)
{
v___y_1350_ = v___y_1415_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v___x_1417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1418_ = l_Nat_reprFast(v___x_1347_);
v___x_1419_ = lean_string_append(v___x_1417_, v___x_1418_);
lean_dec_ref(v___x_1418_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
}
v___jp_1421_:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = lean_unsigned_to_nat(5u);
v___x_1424_ = lean_nat_dec_eq(v___x_1347_, v___x_1423_);
if (v___x_1424_ == 0)
{
v___y_1414_ = v___y_1422_;
v___y_1415_ = v___x_1424_;
v___y_1416_ = v___x_1336_;
goto v___jp_1413_;
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = 0;
v___y_1414_ = v___y_1422_;
v___y_1415_ = v___x_1424_;
v___y_1416_ = v___x_1425_;
goto v___jp_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___boxed(lean_object* v_sz_1428_, lean_object* v_i_1429_, lean_object* v_bs_1430_){
_start:
{
size_t v_sz_boxed_1431_; size_t v_i_boxed_1432_; lean_object* v_res_1433_; 
v_sz_boxed_1431_ = lean_unbox_usize(v_sz_1428_);
lean_dec(v_sz_1428_);
v_i_boxed_1432_ = lean_unbox_usize(v_i_1429_);
lean_dec(v_i_1429_);
v_res_1433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_boxed_1431_, v_i_boxed_1432_, v_bs_1430_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0));
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(v_x_1436_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
v_a_1447_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1449_ = v___x_1438_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1438_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_a_1447_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(lean_object* v_j_1456_, lean_object* v_k_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = l_Lean_Json_getObjValD(v_j_1456_, v_k_1457_);
v___x_1459_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6___boxed(lean_object* v_j_1460_, lean_object* v_k_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_j_1460_, v_k_1461_);
lean_dec_ref(v_k_1461_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(lean_object* v_init_1465_, lean_object* v_x_1466_){
_start:
{
if (lean_obj_tag(v_x_1466_) == 0)
{
lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v_l_1469_; lean_object* v_r_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1640_; 
v_k_1467_ = lean_ctor_get(v_x_1466_, 1);
v_v_1468_ = lean_ctor_get(v_x_1466_, 2);
v_l_1469_ = lean_ctor_get(v_x_1466_, 3);
v_r_1470_ = lean_ctor_get(v_x_1466_, 4);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_x_1466_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; 
v_unused_1641_ = lean_ctor_get(v_x_1466_, 0);
lean_dec(v_unused_1641_);
v___x_1472_ = v_x_1466_;
v_isShared_1473_ = v_isSharedCheck_1640_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_r_1470_);
lean_inc(v_l_1469_);
lean_inc(v_v_1468_);
lean_inc(v_k_1467_);
lean_dec(v_x_1466_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1640_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v_init_1465_, v_l_1469_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
lean_dec(v_k_1467_);
return v___x_1474_;
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1639_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1639_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1639_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Json_parse(v_k_1467_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_del_object(v___x_1477_);
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1489_; 
v_a_1488_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1489_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1488_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_del_object(v___x_1477_);
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v_definition_x3f_1500_; lean_object* v_a_1528_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_a_1498_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1489_, 1);
v___x_1532_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
lean_inc(v_v_1468_);
v___x_1533_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_v_1468_, v___x_1532_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_a_1498_);
lean_del_object(v___x_1477_);
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1638_; 
v_a_1542_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1544_ = v___x_1533_;
v_isShared_1545_ = v_isSharedCheck_1638_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1533_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1638_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
if (lean_obj_tag(v_a_1542_) == 0)
{
lean_object* v___x_1546_; 
lean_del_object(v___x_1544_);
lean_del_object(v___x_1477_);
lean_del_object(v___x_1472_);
v___x_1546_ = lean_box(0);
v_definition_x3f_1500_ = v___x_1546_;
goto v___jp_1499_;
}
else
{
lean_object* v_val_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___y_1551_; uint8_t v___y_1620_; uint8_t v___y_1621_; uint8_t v___y_1622_; uint8_t v___y_1630_; uint8_t v___x_1635_; 
v_val_1547_ = lean_ctor_get(v_a_1542_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v_a_1542_, 1);
v___x_1548_ = lean_array_get_size(v_val_1547_);
v___x_1549_ = lean_unsigned_to_nat(4u);
v___x_1635_ = lean_nat_dec_eq(v___x_1548_, v___x_1549_);
if (v___x_1635_ == 0)
{
uint8_t v___x_1636_; 
v___x_1636_ = 1;
v___y_1630_ = v___x_1636_;
goto v___jp_1629_;
}
else
{
uint8_t v___x_1637_; 
v___x_1637_ = 0;
v___y_1630_ = v___x_1637_;
goto v___jp_1629_;
}
v___jp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_array_fget_borrowed(v_val_1547_, v___x_1552_);
lean_inc(v___x_1553_);
v___x_1554_ = l_Lean_Json_getNat_x3f(v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_val_1547_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1477_);
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
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
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_array_fget_borrowed(v_val_1547_, v___x_1564_);
lean_inc(v___x_1565_);
v___x_1566_ = l_Lean_Json_getNat_x3f(v___x_1565_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1563_);
lean_dec(v_val_1547_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1477_);
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
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
v___x_1576_ = lean_unsigned_to_nat(2u);
v___x_1577_ = lean_array_fget_borrowed(v_val_1547_, v___x_1576_);
lean_inc(v___x_1577_);
v___x_1578_ = l_Lean_Json_getNat_x3f(v___x_1577_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1575_);
lean_dec(v_a_1563_);
lean_dec(v_val_1547_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1477_);
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
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
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1587_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1588_ = lean_unsigned_to_nat(3u);
v___x_1589_ = lean_array_fget_borrowed(v_val_1547_, v___x_1588_);
lean_inc(v___x_1589_);
v___x_1590_ = l_Lean_Json_getNat_x3f(v___x_1589_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_a_1587_);
lean_dec(v_a_1575_);
lean_dec(v_a_1563_);
lean_dec(v_val_1547_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1477_);
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
else
{
if (v___y_1551_ == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
lean_dec(v_val_1547_);
v_a_1599_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 4, v___x_1600_);
lean_ctor_set(v___x_1472_, 3, v_a_1599_);
lean_ctor_set(v___x_1472_, 2, v_a_1587_);
lean_ctor_set(v___x_1472_, 1, v_a_1575_);
lean_ctor_set(v___x_1472_, 0, v_a_1563_);
v___x_1602_ = v___x_1472_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1563_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_a_1575_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_a_1587_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_a_1599_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
v_a_1528_ = v___x_1602_;
goto v___jp_1527_;
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_a_1604_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1605_ = lean_array_fget(v_val_1547_, v___x_1549_);
lean_dec(v_val_1547_);
v___x_1606_ = l_Lean_Json_getStr_x3f(v___x_1605_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_a_1604_);
lean_dec(v_a_1587_);
lean_dec(v_a_1575_);
lean_dec(v_a_1563_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1477_);
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; 
v_a_1615_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1606_, 1);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 4, v_a_1615_);
lean_ctor_set(v___x_1472_, 3, v_a_1604_);
lean_ctor_set(v___x_1472_, 2, v_a_1587_);
lean_ctor_set(v___x_1472_, 1, v_a_1575_);
lean_ctor_set(v___x_1472_, 0, v_a_1563_);
v___x_1617_ = v___x_1472_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1563_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_a_1575_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_a_1587_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v_a_1604_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v_a_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
v_a_1528_ = v___x_1617_;
goto v___jp_1527_;
}
}
}
}
}
}
}
}
v___jp_1619_:
{
if (v___y_1621_ == 0)
{
lean_del_object(v___x_1544_);
v___y_1551_ = v___y_1620_;
goto v___jp_1550_;
}
else
{
if (v___y_1622_ == 0)
{
lean_del_object(v___x_1544_);
v___y_1551_ = v___y_1620_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_dec(v_val_1547_);
lean_dec(v_a_1498_);
lean_del_object(v___x_1477_);
lean_dec(v_a_1475_);
lean_del_object(v___x_1472_);
lean_dec(v_r_1470_);
lean_dec(v_v_1468_);
v___x_1623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1624_ = l_Nat_reprFast(v___x_1548_);
v___x_1625_ = lean_string_append(v___x_1623_, v___x_1624_);
lean_dec_ref(v___x_1624_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1625_);
v___x_1627_ = v___x_1544_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
v___jp_1629_:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = lean_unsigned_to_nat(5u);
v___x_1632_ = lean_nat_dec_eq(v___x_1548_, v___x_1631_);
if (v___x_1632_ == 0)
{
uint8_t v___x_1633_; 
v___x_1633_ = 1;
v___y_1620_ = v___x_1632_;
v___y_1621_ = v___y_1630_;
v___y_1622_ = v___x_1633_;
goto v___jp_1619_;
}
else
{
uint8_t v___x_1634_; 
v___x_1634_ = 0;
v___y_1620_ = v___x_1632_;
v___y_1621_ = v___y_1630_;
v___y_1622_ = v___x_1634_;
goto v___jp_1619_;
}
}
}
}
}
v___jp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v___x_1502_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(v_v_1468_, v___x_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_definition_x3f_1500_);
lean_dec(v_a_1498_);
lean_dec(v_a_1475_);
lean_dec(v_r_1470_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
else
{
lean_object* v_a_1511_; size_t v_sz_1512_; size_t v___x_1513_; lean_object* v___x_1514_; 
v_a_1511_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1502_, 1);
v_sz_1512_ = lean_array_size(v_a_1511_);
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_1512_, v___x_1513_, v_a_1511_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec(v_definition_x3f_1500_);
lean_dec(v_a_1498_);
lean_dec(v_a_1475_);
lean_dec(v_r_1470_);
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_a_1523_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_definition_x3f_1500_);
lean_ctor_set(v___x_1524_, 1, v_a_1523_);
v___x_1525_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_a_1498_, v___x_1524_, v_a_1475_);
v_init_1465_ = v___x_1525_;
v_x_1466_ = v_r_1470_;
goto _start;
}
}
}
v___jp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v_a_1528_);
v___x_1530_ = v___x_1477_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
v_definition_x3f_1500_ = v___x_1530_;
goto v___jp_1499_;
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
lean_object* v___x_1642_; 
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v_init_1465_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(lean_object* v_j_1643_, lean_object* v_k_1644_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = l_Lean_Json_getObjValD(v_j_1643_, v_k_1644_);
v___x_1646_ = l_Lean_Json_getObj_x3f(v___x_1645_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_a_1655_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1656_ = lean_box(1);
v___x_1657_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v___x_1656_, v_a_1655_);
return v___x_1657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3___boxed(lean_object* v_j_1658_, lean_object* v_k_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_j_1658_, v_k_1659_);
lean_dec_ref(v_k_1659_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1664_, size_t v_i_1665_, lean_object* v_bs_1666_){
_start:
{
uint8_t v___x_1669_; 
v___x_1669_ = lean_usize_dec_lt(v_i_1665_, v_sz_1664_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_bs_1666_);
return v___x_1670_;
}
else
{
lean_object* v_v_1671_; 
v_v_1671_ = lean_array_uget_borrowed(v_bs_1666_, v_i_1665_);
if (lean_obj_tag(v_v_1671_) == 4)
{
lean_object* v_elems_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v_elems_1672_ = lean_ctor_get(v_v_1671_, 0);
v___x_1673_ = lean_array_get_size(v_elems_1672_);
v___x_1674_ = lean_unsigned_to_nat(4u);
v___x_1675_ = lean_nat_dec_eq(v___x_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_dec_ref(v_bs_1666_);
goto v___jp_1667_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_array_fget_borrowed(v_elems_1672_, v___x_1676_);
lean_inc(v___x_1677_);
v___x_1678_ = l_Lean_Json_getStr_x3f(v___x_1677_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_bs_1666_);
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_a_1687_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1678_, 1);
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_array_fget_borrowed(v_elems_1672_, v___x_1688_);
v___x_1690_ = l_Lean_Json_getBool_x3f(v___x_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_a_1687_);
lean_dec_ref(v_bs_1666_);
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_a_1699_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1700_ = lean_unsigned_to_nat(2u);
v___x_1701_ = lean_array_fget_borrowed(v_elems_1672_, v___x_1700_);
v___x_1702_ = l_Lean_Json_getBool_x3f(v___x_1701_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_a_1699_);
lean_dec(v_a_1687_);
lean_dec_ref(v_bs_1666_);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_a_1711_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1712_ = lean_unsigned_to_nat(3u);
v___x_1713_ = lean_array_fget_borrowed(v_elems_1672_, v___x_1712_);
v___x_1714_ = l_Lean_Json_getBool_x3f(v___x_1713_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_a_1711_);
lean_dec(v_a_1699_);
lean_dec(v_a_1687_);
lean_dec_ref(v_bs_1666_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v_bs_x27_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; uint8_t v___x_1727_; uint8_t v___x_1728_; size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v_a_1723_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1714_, 1);
v_bs_x27_1724_ = lean_array_uset(v_bs_1666_, v_i_1665_, v___x_1676_);
v___x_1725_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1725_, 0, v_a_1687_);
v___x_1726_ = lean_unbox(v_a_1699_);
lean_dec(v_a_1699_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*1, v___x_1726_);
v___x_1727_ = lean_unbox(v_a_1711_);
lean_dec(v_a_1711_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*1 + 1, v___x_1727_);
v___x_1728_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*1 + 2, v___x_1728_);
v___x_1729_ = ((size_t)1ULL);
v___x_1730_ = lean_usize_add(v_i_1665_, v___x_1729_);
v___x_1731_ = lean_array_uset(v_bs_x27_1724_, v_i_1665_, v___x_1725_);
v_i_1665_ = v___x_1730_;
v_bs_1666_ = v___x_1731_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1666_);
goto v___jp_1667_;
}
}
v___jp_1667_:
{
lean_object* v___x_1668_; 
v___x_1668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1));
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1733_, lean_object* v_i_1734_, lean_object* v_bs_1735_){
_start:
{
size_t v_sz_boxed_1736_; size_t v_i_boxed_1737_; lean_object* v_res_1738_; 
v_sz_boxed_1736_ = lean_unbox_usize(v_sz_1733_);
lean_dec(v_sz_1733_);
v_i_boxed_1737_ = lean_unbox_usize(v_i_1734_);
lean_dec(v_i_1734_);
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1736_, v_i_boxed_1737_, v_bs_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(lean_object* v_x_1739_){
_start:
{
if (lean_obj_tag(v_x_1739_) == 4)
{
lean_object* v_elems_1740_; size_t v_sz_1741_; size_t v___x_1742_; lean_object* v___x_1743_; 
v_elems_1740_ = lean_ctor_get(v_x_1739_, 0);
lean_inc_ref(v_elems_1740_);
lean_dec_ref_known(v_x_1739_, 1);
v_sz_1741_ = lean_array_size(v_elems_1740_);
v___x_1742_ = ((size_t)0ULL);
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_1741_, v___x_1742_, v_elems_1740_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1744_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1745_ = lean_unsigned_to_nat(80u);
v___x_1746_ = l_Lean_Json_pretty(v_x_1739_, v___x_1745_);
v___x_1747_ = lean_string_append(v___x_1744_, v___x_1746_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1749_ = lean_string_append(v___x_1747_, v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(lean_object* v_j_1751_, lean_object* v_k_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = l_Lean_Json_getObjValD(v_j_1751_, v_k_1752_);
v___x_1754_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2___boxed(lean_object* v_j_1755_, lean_object* v_k_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_j_1755_, v_k_1756_);
lean_dec_ref(v_k_1756_);
return v_res_1757_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = 1;
v___x_1767_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__4));
v___x_1768_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1767_, v___x_1766_);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__6));
v___x_1771_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__5, &l_Lean_Server_instFromJsonIlean_fromJson___closed__5_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5);
v___x_1772_ = lean_string_append(v___x_1771_, v___x_1770_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = 1;
v___x_1776_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__8));
v___x_1777_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1776_, v___x_1775_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__9, &l_Lean_Server_instFromJsonIlean_fromJson___closed__9_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9);
v___x_1779_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1780_ = lean_string_append(v___x_1779_, v___x_1778_);
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1783_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__10, &l_Lean_Server_instFromJsonIlean_fromJson___closed__10_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10);
v___x_1784_ = lean_string_append(v___x_1783_, v___x_1782_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = 1;
v___x_1789_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__14));
v___x_1790_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1789_, v___x_1788_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__15, &l_Lean_Server_instFromJsonIlean_fromJson___closed__15_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15);
v___x_1792_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1793_ = lean_string_append(v___x_1792_, v___x_1791_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1795_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__16, &l_Lean_Server_instFromJsonIlean_fromJson___closed__16_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16);
v___x_1796_ = lean_string_append(v___x_1795_, v___x_1794_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = 1;
v___x_1801_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__19));
v___x_1802_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__20, &l_Lean_Server_instFromJsonIlean_fromJson___closed__20_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20);
v___x_1804_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1805_ = lean_string_append(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1807_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__21, &l_Lean_Server_instFromJsonIlean_fromJson___closed__21_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21);
v___x_1808_ = lean_string_append(v___x_1807_, v___x_1806_);
return v___x_1808_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = 1;
v___x_1813_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__24));
v___x_1814_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1813_, v___x_1812_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__25, &l_Lean_Server_instFromJsonIlean_fromJson___closed__25_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25);
v___x_1816_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1817_ = lean_string_append(v___x_1816_, v___x_1815_);
return v___x_1817_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1819_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__26, &l_Lean_Server_instFromJsonIlean_fromJson___closed__26_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26);
v___x_1820_ = lean_string_append(v___x_1819_, v___x_1818_);
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30(void){
_start:
{
uint8_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = 1;
v___x_1825_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__29));
v___x_1826_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1825_, v___x_1824_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__30, &l_Lean_Server_instFromJsonIlean_fromJson___closed__30_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30);
v___x_1828_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1829_ = lean_string_append(v___x_1828_, v___x_1827_);
return v___x_1829_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1831_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__31, &l_Lean_Server_instFromJsonIlean_fromJson___closed__31_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31);
v___x_1832_ = lean_string_append(v___x_1831_, v___x_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonIlean_fromJson(lean_object* v_json_1833_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
lean_inc(v_json_1833_);
v___x_1835_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(v_json_1833_, v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_json_1833_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__12, &l_Lean_Server_instFromJsonIlean_fromJson___closed__12_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12);
v___x_1841_ = lean_string_append(v___x_1840_, v_a_1836_);
lean_dec(v_a_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
else
{
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_json_1833_);
v_a_1846_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1835_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1835_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_a_1854_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1855_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
lean_inc(v_json_1833_);
v___x_1856_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(v_json_1833_, v___x_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1854_);
lean_dec(v_json_1833_);
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1861_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__17, &l_Lean_Server_instFromJsonIlean_fromJson___closed__17_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17);
v___x_1862_ = lean_string_append(v___x_1861_, v_a_1857_);
lean_dec(v_a_1857_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1862_);
v___x_1864_ = v___x_1859_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_a_1854_);
lean_dec(v_json_1833_);
v_a_1867_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1856_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1856_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 0);
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_a_1875_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1876_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
lean_inc(v_json_1833_);
v___x_1877_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_json_1833_, v___x_1876_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_a_1875_);
lean_dec(v_a_1854_);
lean_dec(v_json_1833_);
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1882_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__22, &l_Lean_Server_instFromJsonIlean_fromJson___closed__22_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22);
v___x_1883_ = lean_string_append(v___x_1882_, v_a_1878_);
lean_dec(v_a_1878_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1883_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_a_1875_);
lean_dec(v_a_1854_);
lean_dec(v_json_1833_);
v_a_1888_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1877_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1877_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 0);
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_a_1896_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1897_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
lean_inc(v_json_1833_);
v___x_1898_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_json_1833_, v___x_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_a_1896_);
lean_dec(v_a_1875_);
lean_dec(v_a_1854_);
lean_dec(v_json_1833_);
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1903_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__27, &l_Lean_Server_instFromJsonIlean_fromJson___closed__27_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27);
v___x_1904_ = lean_string_append(v___x_1903_, v_a_1899_);
lean_dec(v_a_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1904_);
v___x_1906_ = v___x_1901_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_a_1896_);
lean_dec(v_a_1875_);
lean_dec(v_a_1854_);
lean_dec(v_json_1833_);
v_a_1909_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1898_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1898_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 0);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_a_1917_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1918_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_1919_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(v_json_1833_, v___x_1918_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_a_1917_);
lean_dec(v_a_1896_);
lean_dec(v_a_1875_);
lean_dec(v_a_1854_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1929_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1929_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1924_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__32, &l_Lean_Server_instFromJsonIlean_fromJson___closed__32_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32);
v___x_1925_ = lean_string_append(v___x_1924_, v_a_1920_);
lean_dec(v_a_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1925_);
v___x_1927_ = v___x_1922_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_a_1917_);
lean_dec(v_a_1896_);
lean_dec(v_a_1875_);
lean_dec(v_a_1854_);
v_a_1930_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1919_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1919_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set_tag(v___x_1932_, 0);
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1946_; 
v_a_1938_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1940_ = v___x_1919_;
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1919_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1942_, 0, v_a_1854_);
lean_ctor_set(v___x_1942_, 1, v_a_1875_);
lean_ctor_set(v___x_1942_, 2, v_a_1896_);
lean_ctor_set(v___x_1942_, 3, v_a_1917_);
lean_ctor_set(v___x_1942_, 4, v_a_1938_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1942_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(size_t v_sz_1949_, size_t v_i_1950_, lean_object* v_bs_1951_){
_start:
{
uint8_t v___x_1952_; 
v___x_1952_ = lean_usize_dec_lt(v_i_1950_, v_sz_1949_);
if (v___x_1952_ == 0)
{
return v_bs_1951_;
}
else
{
lean_object* v_v_1953_; lean_object* v_module_1954_; uint8_t v_isPrivate_1955_; uint8_t v_isAll_1956_; uint8_t v_isMeta_1957_; lean_object* v___x_1958_; lean_object* v_bs_x27_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v_v_1953_ = lean_array_uget_borrowed(v_bs_1951_, v_i_1950_);
v_module_1954_ = lean_ctor_get(v_v_1953_, 0);
lean_inc_ref(v_module_1954_);
v_isPrivate_1955_ = lean_ctor_get_uint8(v_v_1953_, sizeof(void*)*1);
v_isAll_1956_ = lean_ctor_get_uint8(v_v_1953_, sizeof(void*)*1 + 1);
v_isMeta_1957_ = lean_ctor_get_uint8(v_v_1953_, sizeof(void*)*1 + 2);
v___x_1958_ = lean_unsigned_to_nat(0u);
v_bs_x27_1959_ = lean_array_uset(v_bs_1951_, v_i_1950_, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1960_, 0, v_module_1954_);
v___x_1961_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1961_, 0, v_isPrivate_1955_);
v___x_1962_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1962_, 0, v_isAll_1956_);
v___x_1963_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1963_, 0, v_isMeta_1957_);
v___x_1964_ = lean_unsigned_to_nat(4u);
v___x_1965_ = lean_mk_empty_array_with_capacity(v___x_1964_);
v___x_1966_ = lean_array_push(v___x_1965_, v___x_1960_);
v___x_1967_ = lean_array_push(v___x_1966_, v___x_1961_);
v___x_1968_ = lean_array_push(v___x_1967_, v___x_1962_);
v___x_1969_ = lean_array_push(v___x_1968_, v___x_1963_);
v___x_1970_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
v___x_1971_ = ((size_t)1ULL);
v___x_1972_ = lean_usize_add(v_i_1950_, v___x_1971_);
v___x_1973_ = lean_array_uset(v_bs_x27_1959_, v_i_1950_, v___x_1970_);
v_i_1950_ = v___x_1972_;
v_bs_1951_ = v___x_1973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6___boxed(lean_object* v_sz_1975_, lean_object* v_i_1976_, lean_object* v_bs_1977_){
_start:
{
size_t v_sz_boxed_1978_; size_t v_i_boxed_1979_; lean_object* v_res_1980_; 
v_sz_boxed_1978_ = lean_unbox_usize(v_sz_1975_);
lean_dec(v_sz_1975_);
v_i_boxed_1979_ = lean_unbox_usize(v_i_1976_);
lean_dec(v_i_1976_);
v_res_1980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_boxed_1978_, v_i_boxed_1979_, v_bs_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(lean_object* v_a_1981_){
_start:
{
size_t v_sz_1982_; size_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_sz_1982_ = lean_array_size(v_a_1981_);
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_1982_, v___x_1983_, v_a_1981_);
v___x_1985_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
if (lean_obj_tag(v_a_1986_) == 0)
{
lean_object* v___x_1988_; 
v___x_1988_ = l_List_reverse___redArg(v_a_1987_);
return v___x_1988_;
}
else
{
lean_object* v_head_1989_; lean_object* v_tail_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2000_; 
v_head_1989_ = lean_ctor_get(v_a_1986_, 0);
v_tail_1990_ = lean_ctor_get(v_a_1986_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_a_1986_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1992_ = v_a_1986_;
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_tail_1990_);
lean_inc(v_head_1989_);
lean_dec(v_a_1986_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1994_ = l_Lean_JsonNumber_fromNat(v_head_1989_);
v___x_1995_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v_a_1987_);
lean_ctor_set(v___x_1992_, 0, v___x_1995_);
v___x_1997_ = v___x_1992_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_a_1987_);
v___x_1997_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
v_a_1986_ = v_tail_1990_;
v_a_1987_ = v___x_1997_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(size_t v_sz_2001_, size_t v_i_2002_, lean_object* v_bs_2003_){
_start:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_usize_dec_lt(v_i_2002_, v_sz_2001_);
if (v___x_2004_ == 0)
{
return v_bs_2003_;
}
else
{
lean_object* v_v_2005_; lean_object* v___x_2006_; lean_object* v_bs_x27_2007_; size_t v___x_2008_; size_t v___x_2009_; lean_object* v___x_2010_; 
v_v_2005_ = lean_array_uget(v_bs_2003_, v_i_2002_);
v___x_2006_ = lean_unsigned_to_nat(0u);
v_bs_x27_2007_ = lean_array_uset(v_bs_2003_, v_i_2002_, v___x_2006_);
v___x_2008_ = ((size_t)1ULL);
v___x_2009_ = lean_usize_add(v_i_2002_, v___x_2008_);
v___x_2010_ = lean_array_uset(v_bs_x27_2007_, v_i_2002_, v_v_2005_);
v_i_2002_ = v___x_2009_;
v_bs_2003_ = v___x_2010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11___boxed(lean_object* v_sz_2012_, lean_object* v_i_2013_, lean_object* v_bs_2014_){
_start:
{
size_t v_sz_boxed_2015_; size_t v_i_boxed_2016_; lean_object* v_res_2017_; 
v_sz_boxed_2015_ = lean_unbox_usize(v_sz_2012_);
lean_dec(v_sz_2012_);
v_i_boxed_2016_ = lean_unbox_usize(v_i_2013_);
lean_dec(v_i_2013_);
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_boxed_2015_, v_i_boxed_2016_, v_bs_2014_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(lean_object* v_a_2018_){
_start:
{
size_t v_sz_2019_; size_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_sz_2019_ = lean_array_size(v_a_2018_);
v___x_2020_ = ((size_t)0ULL);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_2019_, v___x_2020_, v_a_2018_);
v___x_2022_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(lean_object* v_a_2023_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_array_mk(v_a_2023_);
v___x_2025_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(lean_object* v_x_2026_){
_start:
{
if (lean_obj_tag(v_x_2026_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_box(0);
return v___x_2027_;
}
else
{
lean_object* v_val_2028_; lean_object* v___x_2029_; 
v_val_2028_ = lean_ctor_get(v_x_2026_, 0);
lean_inc(v_val_2028_);
lean_dec_ref_known(v_x_2026_, 1);
v___x_2029_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_val_2028_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(size_t v_sz_2030_, size_t v_i_2031_, lean_object* v_bs_2032_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = lean_usize_dec_lt(v_i_2031_, v_sz_2030_);
if (v___x_2033_ == 0)
{
return v_bs_2032_;
}
else
{
lean_object* v_v_2034_; lean_object* v_startPosLine_2035_; lean_object* v_startPosCharacter_2036_; lean_object* v_endPosLine_2037_; lean_object* v_endPosCharacter_2038_; lean_object* v___x_2039_; lean_object* v_bs_x27_2040_; lean_object* v___y_2042_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v_range_2052_; lean_object* v___x_2053_; 
v_v_2034_ = lean_array_uget(v_bs_2032_, v_i_2031_);
v_startPosLine_2035_ = lean_ctor_get(v_v_2034_, 0);
v_startPosCharacter_2036_ = lean_ctor_get(v_v_2034_, 1);
v_endPosLine_2037_ = lean_ctor_get(v_v_2034_, 2);
v_endPosCharacter_2038_ = lean_ctor_get(v_v_2034_, 3);
v___x_2039_ = lean_unsigned_to_nat(0u);
v_bs_x27_2040_ = lean_array_uset(v_bs_2032_, v_i_2031_, v___x_2039_);
v___x_2047_ = lean_box(0);
lean_inc(v_endPosCharacter_2038_);
v___x_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2048_, 0, v_endPosCharacter_2038_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_inc(v_endPosLine_2037_);
v___x_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2049_, 0, v_endPosLine_2037_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
lean_inc(v_startPosCharacter_2036_);
v___x_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_startPosCharacter_2036_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
lean_inc(v_startPosLine_2035_);
v___x_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2051_, 0, v_startPosLine_2035_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v_range_2052_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_2051_, v___x_2047_);
v___x_2053_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_2034_);
lean_dec(v_v_2034_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2054_; 
v___x_2054_ = l_List_appendTR___redArg(v_range_2052_, v___x_2047_);
v___y_2042_ = v___x_2054_;
goto v___jp_2041_;
}
else
{
lean_object* v_val_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2064_; 
v_val_2055_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2057_ = v___x_2053_;
v_isShared_2058_ = v_isSharedCheck_2064_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_val_2055_);
lean_dec(v___x_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2064_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 3);
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_val_2055_);
v___x_2060_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___x_2047_);
v___x_2062_ = l_List_appendTR___redArg(v_range_2052_, v___x_2061_);
v___y_2042_ = v___x_2062_;
goto v___jp_2041_;
}
}
}
v___jp_2041_:
{
size_t v___x_2043_; size_t v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = ((size_t)1ULL);
v___x_2044_ = lean_usize_add(v_i_2031_, v___x_2043_);
v___x_2045_ = lean_array_uset(v_bs_x27_2040_, v_i_2031_, v___y_2042_);
v_i_2031_ = v___x_2044_;
v_bs_2032_ = v___x_2045_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2___boxed(lean_object* v_sz_2065_, lean_object* v_i_2066_, lean_object* v_bs_2067_){
_start:
{
size_t v_sz_boxed_2068_; size_t v_i_boxed_2069_; lean_object* v_res_2070_; 
v_sz_boxed_2068_ = lean_unbox_usize(v_sz_2065_);
lean_dec(v_sz_2065_);
v_i_boxed_2069_ = lean_unbox_usize(v_i_2066_);
lean_dec(v_i_2066_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_boxed_2068_, v_i_boxed_2069_, v_bs_2067_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(size_t v_sz_2071_, size_t v_i_2072_, lean_object* v_bs_2073_){
_start:
{
uint8_t v___x_2074_; 
v___x_2074_ = lean_usize_dec_lt(v_i_2072_, v_sz_2071_);
if (v___x_2074_ == 0)
{
return v_bs_2073_;
}
else
{
lean_object* v_v_2075_; lean_object* v___x_2076_; lean_object* v_bs_x27_2077_; lean_object* v___x_2078_; size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v_v_2075_ = lean_array_uget(v_bs_2073_, v_i_2072_);
v___x_2076_ = lean_unsigned_to_nat(0u);
v_bs_x27_2077_ = lean_array_uset(v_bs_2073_, v_i_2072_, v___x_2076_);
v___x_2078_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_v_2075_);
v___x_2079_ = ((size_t)1ULL);
v___x_2080_ = lean_usize_add(v_i_2072_, v___x_2079_);
v___x_2081_ = lean_array_uset(v_bs_x27_2077_, v_i_2072_, v___x_2078_);
v_i_2072_ = v___x_2080_;
v_bs_2073_ = v___x_2081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4___boxed(lean_object* v_sz_2083_, lean_object* v_i_2084_, lean_object* v_bs_2085_){
_start:
{
size_t v_sz_boxed_2086_; size_t v_i_boxed_2087_; lean_object* v_res_2088_; 
v_sz_boxed_2086_ = lean_unbox_usize(v_sz_2083_);
lean_dec(v_sz_2083_);
v_i_boxed_2087_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_res_2088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_boxed_2086_, v_i_boxed_2087_, v_bs_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(lean_object* v_a_2089_){
_start:
{
size_t v_sz_2090_; size_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v_sz_2090_ = lean_array_size(v_a_2089_);
v___x_2091_ = ((size_t)0ULL);
v___x_2092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_2090_, v___x_2091_, v_a_2089_);
v___x_2093_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
if (lean_obj_tag(v_a_2094_) == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = l_List_reverse___redArg(v_a_2095_);
return v___x_2096_;
}
else
{
lean_object* v_head_2097_; lean_object* v_snd_2098_; lean_object* v_tail_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2168_; 
v_head_2097_ = lean_ctor_get(v_a_2094_, 0);
lean_inc(v_head_2097_);
v_snd_2098_ = lean_ctor_get(v_head_2097_, 1);
lean_inc(v_snd_2098_);
v_tail_2099_ = lean_ctor_get(v_a_2094_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_a_2094_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v_a_2094_, 0);
lean_dec(v_unused_2169_);
v___x_2101_ = v_a_2094_;
v_isShared_2102_ = v_isSharedCheck_2168_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_tail_2099_);
lean_dec(v_a_2094_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2168_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_fst_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2166_; 
v_fst_2103_ = lean_ctor_get(v_head_2097_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_head_2097_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; 
v_unused_2167_ = lean_ctor_get(v_head_2097_, 1);
lean_dec(v_unused_2167_);
v___x_2105_ = v_head_2097_;
v_isShared_2106_ = v_isSharedCheck_2166_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_fst_2103_);
lean_dec(v_head_2097_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2166_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_definition_x3f_2107_; lean_object* v_usages_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2165_; 
v_definition_x3f_2107_ = lean_ctor_get(v_snd_2098_, 0);
v_usages_2108_ = lean_ctor_get(v_snd_2098_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_snd_2098_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2110_ = v_snd_2098_;
v_isShared_2111_ = v_isSharedCheck_2165_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_usages_2108_);
lean_inc(v_definition_x3f_2107_);
lean_dec(v_snd_2098_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2165_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___y_2116_; lean_object* v___y_2139_; 
v___x_2112_ = l_Lean_Lsp_RefIdent_toJson(v_fst_2103_);
v___x_2113_ = l_Lean_Json_compress(v___x_2112_);
v___x_2114_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
if (lean_obj_tag(v_definition_x3f_2107_) == 0)
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_box(0);
v___y_2116_ = v___x_2141_;
goto v___jp_2115_;
}
else
{
lean_object* v_val_2142_; lean_object* v_startPosLine_2143_; lean_object* v_startPosCharacter_2144_; lean_object* v_endPosLine_2145_; lean_object* v_endPosCharacter_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_range_2152_; lean_object* v___x_2153_; 
v_val_2142_ = lean_ctor_get(v_definition_x3f_2107_, 0);
lean_inc(v_val_2142_);
lean_dec_ref_known(v_definition_x3f_2107_, 1);
v_startPosLine_2143_ = lean_ctor_get(v_val_2142_, 0);
v_startPosCharacter_2144_ = lean_ctor_get(v_val_2142_, 1);
v_endPosLine_2145_ = lean_ctor_get(v_val_2142_, 2);
v_endPosCharacter_2146_ = lean_ctor_get(v_val_2142_, 3);
v___x_2147_ = lean_box(0);
lean_inc(v_endPosCharacter_2146_);
v___x_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2148_, 0, v_endPosCharacter_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
lean_inc(v_endPosLine_2145_);
v___x_2149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2149_, 0, v_endPosLine_2145_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
lean_inc(v_startPosCharacter_2144_);
v___x_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2150_, 0, v_startPosCharacter_2144_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
lean_inc(v_startPosLine_2143_);
v___x_2151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2151_, 0, v_startPosLine_2143_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v_range_2152_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_2151_, v___x_2147_);
v___x_2153_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_2142_);
lean_dec(v_val_2142_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = l_List_appendTR___redArg(v_range_2152_, v___x_2147_);
v___y_2139_ = v___x_2154_;
goto v___jp_2138_;
}
else
{
lean_object* v_val_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2164_; 
v_val_2155_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2157_ = v___x_2153_;
v_isShared_2158_ = v_isSharedCheck_2164_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_val_2155_);
lean_dec(v___x_2153_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2164_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 3);
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_val_2155_);
v___x_2160_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v___x_2147_);
v___x_2162_ = l_List_appendTR___redArg(v_range_2152_, v___x_2161_);
v___y_2139_ = v___x_2162_;
goto v___jp_2138_;
}
}
}
}
v___jp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = l_Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(v___y_2116_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v___x_2117_);
lean_ctor_set(v___x_2105_, 0, v___x_2114_);
v___x_2119_ = v___x_2105_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; size_t v_sz_2121_; size_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2120_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v_sz_2121_ = lean_array_size(v_usages_2108_);
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_2121_, v___x_2122_, v_usages_2108_);
v___x_2124_ = l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(v___x_2123_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 1, v___x_2124_);
lean_ctor_set(v___x_2110_, 0, v___x_2120_);
v___x_2126_ = v___x_2110_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_box(0);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v___x_2127_);
lean_ctor_set(v___x_2101_, 0, v___x_2126_);
v___x_2129_ = v___x_2101_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2119_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_Json_mkObj(v___x_2130_);
lean_dec_ref_known(v___x_2130_, 2);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2113_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v_a_2095_);
v_a_2094_ = v_tail_2099_;
v_a_2095_ = v___x_2133_;
goto _start;
}
}
}
}
v___jp_2138_:
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___y_2139_);
v___y_2116_ = v___x_2140_;
goto v___jp_2115_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(lean_object* v_init_2170_, lean_object* v_x_2171_){
_start:
{
if (lean_obj_tag(v_x_2171_) == 0)
{
lean_object* v_k_2172_; lean_object* v_v_2173_; lean_object* v_l_2174_; lean_object* v_r_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_k_2172_ = lean_ctor_get(v_x_2171_, 1);
v_v_2173_ = lean_ctor_get(v_x_2171_, 2);
v_l_2174_ = lean_ctor_get(v_x_2171_, 3);
v_r_2175_ = lean_ctor_get(v_x_2171_, 4);
v___x_2176_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2170_, v_r_2175_);
lean_inc(v_v_2173_);
lean_inc(v_k_2172_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v_k_2172_);
lean_ctor_set(v___x_2177_, 1, v_v_2173_);
v___x_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2176_);
v_init_2170_ = v___x_2178_;
v_x_2171_ = v_l_2174_;
goto _start;
}
else
{
return v_init_2170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5___boxed(lean_object* v_init_2180_, lean_object* v_x_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2180_, v_x_2181_);
lean_dec(v_x_2181_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
if (lean_obj_tag(v_a_2183_) == 0)
{
lean_object* v___x_2185_; 
v___x_2185_ = l_List_reverse___redArg(v_a_2184_);
return v___x_2185_;
}
else
{
lean_object* v_head_2186_; lean_object* v_snd_2187_; lean_object* v_tail_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2240_; 
v_head_2186_ = lean_ctor_get(v_a_2183_, 0);
lean_inc(v_head_2186_);
v_snd_2187_ = lean_ctor_get(v_head_2186_, 1);
lean_inc(v_snd_2187_);
v_tail_2188_ = lean_ctor_get(v_a_2183_, 1);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v_a_2183_, 0);
lean_dec(v_unused_2241_);
v___x_2190_ = v_a_2183_;
v_isShared_2191_ = v_isSharedCheck_2240_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_tail_2188_);
lean_dec(v_a_2183_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2240_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v_fst_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2238_; 
v_fst_2192_ = lean_ctor_get(v_head_2186_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_head_2186_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; 
v_unused_2239_ = lean_ctor_get(v_head_2186_, 1);
lean_dec(v_unused_2239_);
v___x_2194_ = v_head_2186_;
v_isShared_2195_ = v_isSharedCheck_2238_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_fst_2192_);
lean_dec(v_head_2186_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2238_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_rangeStartPosLine_2196_; lean_object* v_rangeStartPosCharacter_2197_; lean_object* v_rangeEndPosLine_2198_; lean_object* v_rangeEndPosCharacter_2199_; lean_object* v_selectionRangeStartPosLine_2200_; lean_object* v_selectionRangeStartPosCharacter_2201_; lean_object* v_selectionRangeEndPosLine_2202_; lean_object* v_selectionRangeEndPosCharacter_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v_rangeStartPosLine_2196_ = lean_ctor_get(v_snd_2187_, 0);
lean_inc(v_rangeStartPosLine_2196_);
v_rangeStartPosCharacter_2197_ = lean_ctor_get(v_snd_2187_, 1);
lean_inc(v_rangeStartPosCharacter_2197_);
v_rangeEndPosLine_2198_ = lean_ctor_get(v_snd_2187_, 2);
lean_inc(v_rangeEndPosLine_2198_);
v_rangeEndPosCharacter_2199_ = lean_ctor_get(v_snd_2187_, 3);
lean_inc(v_rangeEndPosCharacter_2199_);
v_selectionRangeStartPosLine_2200_ = lean_ctor_get(v_snd_2187_, 4);
lean_inc(v_selectionRangeStartPosLine_2200_);
v_selectionRangeStartPosCharacter_2201_ = lean_ctor_get(v_snd_2187_, 5);
lean_inc(v_selectionRangeStartPosCharacter_2201_);
v_selectionRangeEndPosLine_2202_ = lean_ctor_get(v_snd_2187_, 6);
lean_inc(v_selectionRangeEndPosLine_2202_);
v_selectionRangeEndPosCharacter_2203_ = lean_ctor_get(v_snd_2187_, 7);
lean_inc(v_selectionRangeEndPosCharacter_2203_);
lean_dec(v_snd_2187_);
v___x_2204_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_2196_);
v___x_2205_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
v___x_2206_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_2197_);
v___x_2207_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
v___x_2208_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_2198_);
v___x_2209_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_2199_);
v___x_2211_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
v___x_2212_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_2200_);
v___x_2213_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
v___x_2214_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_2201_);
v___x_2215_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
v___x_2216_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_2202_);
v___x_2217_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
v___x_2218_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_2203_);
v___x_2219_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
v___x_2220_ = lean_unsigned_to_nat(8u);
v___x_2221_ = lean_mk_empty_array_with_capacity(v___x_2220_);
v___x_2222_ = lean_array_push(v___x_2221_, v___x_2205_);
v___x_2223_ = lean_array_push(v___x_2222_, v___x_2207_);
v___x_2224_ = lean_array_push(v___x_2223_, v___x_2209_);
v___x_2225_ = lean_array_push(v___x_2224_, v___x_2211_);
v___x_2226_ = lean_array_push(v___x_2225_, v___x_2213_);
v___x_2227_ = lean_array_push(v___x_2226_, v___x_2215_);
v___x_2228_ = lean_array_push(v___x_2227_, v___x_2217_);
v___x_2229_ = lean_array_push(v___x_2228_, v___x_2219_);
v___x_2230_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v___x_2230_);
v___x_2232_ = v___x_2194_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_fst_2192_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 1, v_a_2184_);
lean_ctor_set(v___x_2190_, 0, v___x_2232_);
v___x_2234_ = v___x_2190_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_a_2184_);
v___x_2234_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
v_a_2183_ = v_tail_2188_;
v_a_2184_ = v___x_2234_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
if (lean_obj_tag(v_a_2242_) == 0)
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_array_to_list(v_a_2243_);
return v___x_2244_;
}
else
{
lean_object* v_head_2245_; lean_object* v_tail_2246_; lean_object* v___x_2247_; 
v_head_2245_ = lean_ctor_get(v_a_2242_, 0);
lean_inc(v_head_2245_);
v_tail_2246_ = lean_ctor_get(v_a_2242_, 1);
lean_inc(v_tail_2246_);
lean_dec_ref_known(v_a_2242_, 2);
v___x_2247_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2243_, v_head_2245_);
v_a_2242_ = v_tail_2246_;
v_a_2243_ = v___x_2247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(lean_object* v_init_2249_, lean_object* v_x_2250_){
_start:
{
if (lean_obj_tag(v_x_2250_) == 0)
{
lean_object* v_k_2251_; lean_object* v_v_2252_; lean_object* v_l_2253_; lean_object* v_r_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v_k_2251_ = lean_ctor_get(v_x_2250_, 1);
v_v_2252_ = lean_ctor_get(v_x_2250_, 2);
v_l_2253_ = lean_ctor_get(v_x_2250_, 3);
v_r_2254_ = lean_ctor_get(v_x_2250_, 4);
v___x_2255_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2249_, v_r_2254_);
lean_inc(v_v_2252_);
lean_inc(v_k_2251_);
v___x_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2256_, 0, v_k_2251_);
lean_ctor_set(v___x_2256_, 1, v_v_2252_);
v___x_2257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2255_);
v_init_2249_ = v___x_2257_;
v_x_2250_ = v_l_2253_;
goto _start;
}
else
{
return v_init_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7___boxed(lean_object* v_init_2259_, lean_object* v_x_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2259_, v_x_2260_);
lean_dec(v_x_2260_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonIlean_toJson(lean_object* v_x_2264_){
_start:
{
lean_object* v_version_2265_; lean_object* v_module_2266_; lean_object* v_directImports_2267_; lean_object* v_references_2268_; lean_object* v_decls_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_version_2265_ = lean_ctor_get(v_x_2264_, 0);
lean_inc(v_version_2265_);
v_module_2266_ = lean_ctor_get(v_x_2264_, 1);
lean_inc(v_module_2266_);
v_directImports_2267_ = lean_ctor_get(v_x_2264_, 2);
lean_inc_ref(v_directImports_2267_);
v_references_2268_ = lean_ctor_get(v_x_2264_, 3);
lean_inc(v_references_2268_);
v_decls_2269_ = lean_ctor_get(v_x_2264_, 4);
lean_inc(v_decls_2269_);
lean_dec_ref(v_x_2264_);
v___x_2270_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
v___x_2271_ = l_Lean_JsonNumber_fromNat(v_version_2265_);
v___x_2272_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2270_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = lean_box(0);
v___x_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
v___x_2277_ = 1;
v___x_2278_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_2266_, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2276_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v___x_2274_);
v___x_2282_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
v___x_2283_ = l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(v_directImports_2267_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v___x_2274_);
v___x_2286_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
v___x_2287_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v___x_2274_, v_references_2268_);
lean_dec(v_references_2268_);
v___x_2288_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(v___x_2287_, v___x_2274_);
v___x_2289_ = l_Lean_Json_mkObj(v___x_2288_);
lean_dec(v___x_2288_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2286_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___x_2274_);
v___x_2292_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_2293_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v___x_2274_, v_decls_2269_);
lean_dec(v_decls_2269_);
v___x_2294_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(v___x_2293_, v___x_2274_);
v___x_2295_ = l_Lean_Json_mkObj(v___x_2294_);
lean_dec(v___x_2294_);
v___x_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2292_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v___x_2274_);
v___x_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2274_);
v___x_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2291_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2285_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2281_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2275_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = ((lean_object*)(l_Lean_Server_instToJsonIlean_toJson___closed__0));
v___x_2304_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(v___x_2302_, v___x_2303_);
v___x_2305_ = l_Lean_Json_mkObj(v___x_2304_);
lean_dec(v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load(lean_object* v_path_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_IO_FS_readFile(v_path_2309_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2333_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2333_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2333_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v_a_2317_; lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Json_parse(v_a_2312_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; 
lean_del_object(v___x_2314_);
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v_a_2317_ = v_a_2325_;
goto v___jp_2316_;
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2327_ = l_Lean_Server_instFromJsonIlean_fromJson(v_a_2326_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; 
lean_del_object(v___x_2314_);
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v_a_2317_ = v_a_2328_;
goto v___jp_2316_;
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; 
v_a_2329_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2327_, 1);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v_a_2329_);
v___x_2331_ = v___x_2314_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
v___jp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2318_ = ((lean_object*)(l_Lean_Server_Ilean_load___closed__0));
v___x_2319_ = lean_string_append(v___x_2318_, v_path_2309_);
v___x_2320_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_2321_ = lean_string_append(v___x_2319_, v___x_2320_);
v___x_2322_ = lean_string_append(v___x_2321_, v_a_2317_);
lean_dec_ref(v_a_2317_);
v___x_2323_ = l_Lean_IO_throwServerError___redArg(v___x_2322_);
return v___x_2323_;
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2311_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2311_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load___boxed(lean_object* v_path_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_Server_Ilean_load(v_path_2342_);
lean_dec_ref(v_path_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f(lean_object* v_env_2345_, lean_object* v_declName_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2345_, v_declName_2346_);
if (lean_obj_tag(v___x_2347_) == 1)
{
lean_object* v_val_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2360_; 
v_val_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2360_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_val_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2360_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2352_ = l_Lean_Environment_allImportedModuleNames(v_env_2345_);
v___x_2353_ = lean_array_get_size(v___x_2352_);
v___x_2354_ = lean_nat_dec_lt(v_val_2348_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
lean_dec_ref(v___x_2352_);
lean_del_object(v___x_2350_);
lean_dec(v_val_2348_);
v___x_2355_ = lean_box(0);
return v___x_2355_;
}
else
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_array_fget(v___x_2352_, v_val_2348_);
lean_dec(v_val_2348_);
lean_dec_ref(v___x_2352_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2356_);
v___x_2358_ = v___x_2350_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v___x_2361_; lean_object* v_mainModule_2362_; lean_object* v___x_2363_; 
lean_dec(v___x_2347_);
v___x_2361_ = l_Lean_Environment_header(v_env_2345_);
v_mainModule_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_mainModule_2362_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v_mainModule_2362_);
return v___x_2363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f___boxed(lean_object* v_env_2364_, lean_object* v_declName_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2364_, v_declName_2365_);
lean_dec(v_declName_2365_);
lean_dec_ref(v_env_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf(lean_object* v_ci_2367_, lean_object* v_i_2368_){
_start:
{
switch(lean_obj_tag(v_i_2368_))
{
case 1:
{
lean_object* v_i_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2410_; 
v_i_2369_ = lean_ctor_get(v_i_2368_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_i_2368_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2371_ = v_i_2368_;
v_isShared_2372_ = v_isSharedCheck_2410_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_i_2369_);
lean_dec(v_i_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2410_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v_expr_2373_; 
v_expr_2373_ = lean_ctor_get(v_i_2369_, 3);
lean_inc_ref(v_expr_2373_);
switch(lean_obj_tag(v_expr_2373_))
{
case 4:
{
lean_object* v_toCommandContextInfo_2374_; uint8_t v_isBinder_2375_; lean_object* v_declName_2376_; lean_object* v_env_2377_; lean_object* v___x_2378_; 
lean_del_object(v___x_2371_);
v_toCommandContextInfo_2374_ = lean_ctor_get(v_ci_2367_, 0);
v_isBinder_2375_ = lean_ctor_get_uint8(v_i_2369_, sizeof(void*)*4);
lean_dec_ref(v_i_2369_);
v_declName_2376_ = lean_ctor_get(v_expr_2373_, 0);
lean_inc(v_declName_2376_);
lean_dec_ref_known(v_expr_2373_, 2);
v_env_2377_ = lean_ctor_get(v_toCommandContextInfo_2374_, 0);
v___x_2378_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2377_, v_declName_2376_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v___x_2379_; 
lean_dec(v_declName_2376_);
v___x_2379_ = lean_box(0);
return v___x_2379_;
}
else
{
lean_object* v_val_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2393_; 
v_val_2380_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2382_ = v___x_2378_;
v_isShared_2383_ = v_isSharedCheck_2393_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_val_2380_);
lean_dec(v___x_2378_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2393_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2384_ = 1;
v___x_2385_ = l_Lean_Name_toString(v_val_2380_, v___x_2384_);
v___x_2386_ = l_Lean_Name_toString(v_declName_2376_, v___x_2384_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = lean_box(v_isBinder_2375_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2389_);
v___x_2391_ = v___x_2382_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
case 1:
{
lean_object* v_toCommandContextInfo_2394_; uint8_t v_isBinder_2395_; lean_object* v_fvarId_2396_; lean_object* v_env_2397_; lean_object* v___x_2398_; lean_object* v_mainModule_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v_toCommandContextInfo_2394_ = lean_ctor_get(v_ci_2367_, 0);
v_isBinder_2395_ = lean_ctor_get_uint8(v_i_2369_, sizeof(void*)*4);
lean_dec_ref(v_i_2369_);
v_fvarId_2396_ = lean_ctor_get(v_expr_2373_, 0);
lean_inc(v_fvarId_2396_);
lean_dec_ref_known(v_expr_2373_, 1);
v_env_2397_ = lean_ctor_get(v_toCommandContextInfo_2394_, 0);
v___x_2398_ = l_Lean_Environment_header(v_env_2397_);
v_mainModule_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_mainModule_2399_);
lean_dec_ref(v___x_2398_);
v___x_2400_ = 1;
v___x_2401_ = l_Lean_Name_toString(v_mainModule_2399_, v___x_2400_);
v___x_2402_ = l_Lean_Name_toString(v_fvarId_2396_, v___x_2400_);
v___x_2403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = lean_box(v_isBinder_2395_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2405_);
v___x_2407_ = v___x_2371_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
default: 
{
lean_object* v___x_2409_; 
lean_dec_ref(v_expr_2373_);
lean_del_object(v___x_2371_);
lean_dec_ref(v_i_2369_);
v___x_2409_ = lean_box(0);
return v___x_2409_;
}
}
}
}
case 7:
{
lean_object* v_toCommandContextInfo_2411_; lean_object* v_i_2412_; lean_object* v_env_2413_; lean_object* v_projName_2414_; lean_object* v___x_2415_; 
v_toCommandContextInfo_2411_ = lean_ctor_get(v_ci_2367_, 0);
v_i_2412_ = lean_ctor_get(v_i_2368_, 0);
lean_inc_ref(v_i_2412_);
lean_dec_ref_known(v_i_2368_, 1);
v_env_2413_ = lean_ctor_get(v_toCommandContextInfo_2411_, 0);
v_projName_2414_ = lean_ctor_get(v_i_2412_, 0);
lean_inc(v_projName_2414_);
lean_dec_ref(v_i_2412_);
v___x_2415_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2413_, v_projName_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v___x_2416_; 
lean_dec(v_projName_2414_);
v___x_2416_ = lean_box(0);
return v___x_2416_;
}
else
{
lean_object* v_val_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2431_; 
v_val_2417_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2419_ = v___x_2415_;
v_isShared_2420_ = v_isSharedCheck_2431_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_val_2417_);
lean_dec(v___x_2415_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2431_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2421_ = 1;
v___x_2422_ = l_Lean_Name_toString(v_val_2417_, v___x_2421_);
v___x_2423_ = l_Lean_Name_toString(v_projName_2414_, v___x_2421_);
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = 0;
v___x_2426_ = lean_box(v___x_2425_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2424_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2427_);
v___x_2429_ = v___x_2419_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
case 5:
{
lean_object* v_toCommandContextInfo_2432_; lean_object* v_i_2433_; lean_object* v_env_2434_; lean_object* v_declName_2435_; lean_object* v___x_2436_; 
v_toCommandContextInfo_2432_ = lean_ctor_get(v_ci_2367_, 0);
v_i_2433_ = lean_ctor_get(v_i_2368_, 0);
lean_inc_ref(v_i_2433_);
lean_dec_ref_known(v_i_2368_, 1);
v_env_2434_ = lean_ctor_get(v_toCommandContextInfo_2432_, 0);
v_declName_2435_ = lean_ctor_get(v_i_2433_, 2);
lean_inc(v_declName_2435_);
lean_dec_ref(v_i_2433_);
v___x_2436_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2434_, v_declName_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2437_; 
lean_dec(v_declName_2435_);
v___x_2437_ = lean_box(0);
return v___x_2437_;
}
else
{
lean_object* v_val_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2452_; 
v_val_2438_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2440_ = v___x_2436_;
v_isShared_2441_ = v_isSharedCheck_2452_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_val_2438_);
lean_dec(v___x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2452_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
uint8_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2442_ = 1;
v___x_2443_ = l_Lean_Name_toString(v_val_2438_, v___x_2442_);
v___x_2444_ = l_Lean_Name_toString(v_declName_2435_, v___x_2442_);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = 0;
v___x_2447_ = lean_box(v___x_2446_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2445_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2448_);
v___x_2450_ = v___x_2440_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
case 16:
{
lean_object* v_toCommandContextInfo_2453_; lean_object* v_i_2454_; lean_object* v_env_2455_; lean_object* v_name_2456_; lean_object* v___x_2457_; 
v_toCommandContextInfo_2453_ = lean_ctor_get(v_ci_2367_, 0);
v_i_2454_ = lean_ctor_get(v_i_2368_, 0);
lean_inc_ref(v_i_2454_);
lean_dec_ref_known(v_i_2368_, 1);
v_env_2455_ = lean_ctor_get(v_toCommandContextInfo_2453_, 0);
v_name_2456_ = lean_ctor_get(v_i_2454_, 1);
lean_inc(v_name_2456_);
lean_dec_ref(v_i_2454_);
v___x_2457_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2455_, v_name_2456_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v___x_2458_; 
lean_dec(v_name_2456_);
v___x_2458_ = lean_box(0);
return v___x_2458_;
}
else
{
lean_object* v_val_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2473_; 
v_val_2459_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2461_ = v___x_2457_;
v_isShared_2462_ = v_isSharedCheck_2473_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_val_2459_);
lean_dec(v___x_2457_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2473_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
uint8_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2463_ = 1;
v___x_2464_ = l_Lean_Name_toString(v_val_2459_, v___x_2463_);
v___x_2465_ = l_Lean_Name_toString(v_name_2456_, v___x_2463_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = 0;
v___x_2468_ = lean_box(v___x_2467_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2466_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2469_);
v___x_2471_ = v___x_2461_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
default: 
{
lean_object* v___x_2474_; 
lean_dec_ref(v_i_2368_);
v___x_2474_ = lean_box(0);
return v___x_2474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf___boxed(lean_object* v_ci_2475_, lean_object* v_i_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Server_identOf(v_ci_2475_, v_i_2476_);
lean_dec_ref(v_ci_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(uint8_t v___x_2478_, lean_object* v_x_2479_, lean_object* v_x_2480_, lean_object* v_x_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_box(v___x_2478_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
lean_ctor_set(v___x_2484_, 1, v___y_2482_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed(lean_object* v___x_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_, lean_object* v_x_2488_, lean_object* v___y_2489_){
_start:
{
uint8_t v___x_3522__boxed_2490_; lean_object* v_res_2491_; 
v___x_3522__boxed_2490_ = lean_unbox(v___x_2485_);
v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(v___x_3522__boxed_2490_, v_x_2486_, v_x_2487_, v_x_2488_, v___y_2489_);
lean_dec_ref(v_x_2488_);
lean_dec_ref(v_x_2487_);
lean_dec_ref(v_x_2486_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(lean_object* v_text_2492_, lean_object* v_ci_2493_, lean_object* v_info_2494_, lean_object* v_x_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2497_; 
lean_inc_ref(v_info_2494_);
v___x_2497_ = l_Lean_Server_identOf(v_ci_2493_, v_info_2494_);
if (lean_obj_tag(v___x_2497_) == 1)
{
lean_object* v_val_2498_; lean_object* v_fst_2499_; lean_object* v_snd_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2525_; 
v_val_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_val_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v_fst_2499_ = lean_ctor_get(v_val_2498_, 0);
v_snd_2500_ = lean_ctor_get(v_val_2498_, 1);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_val_2498_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2502_ = v_val_2498_;
v_isShared_2503_ = v_isSharedCheck_2525_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_snd_2500_);
lean_inc(v_fst_2499_);
lean_dec(v_val_2498_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2525_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_Elab_Info_range_x3f(v_info_2494_);
if (lean_obj_tag(v___x_2504_) == 1)
{
lean_object* v_val_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_val_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_val_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2506_ = l_Lean_Elab_Info_stx(v_info_2494_);
v___x_2507_ = l_Lean_Syntax_getHeadInfo(v___x_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_dec_ref_known(v___x_2507_, 4);
v___x_2508_ = lean_box(0);
v___x_2509_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_2510_ = l_Lean_Syntax_Range_toLspRange(v_text_2492_, v_val_2505_);
v___x_2511_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2511_, 0, v_fst_2499_);
lean_ctor_set(v___x_2511_, 1, v___x_2509_);
lean_ctor_set(v___x_2511_, 2, v___x_2510_);
lean_ctor_set(v___x_2511_, 3, v___x_2506_);
lean_ctor_set(v___x_2511_, 4, v_ci_2493_);
lean_ctor_set(v___x_2511_, 5, v_info_2494_);
v___x_2512_ = lean_unbox(v_snd_2500_);
lean_dec(v_snd_2500_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*6, v___x_2512_);
v___x_2513_ = lean_array_push(v___y_2496_, v___x_2511_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v___x_2513_);
lean_ctor_set(v___x_2502_, 0, v___x_2508_);
v___x_2515_ = v___x_2502_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_dec(v___x_2507_);
lean_dec(v___x_2506_);
lean_dec(v_val_2505_);
lean_dec(v_snd_2500_);
lean_dec(v_fst_2499_);
lean_dec_ref(v_info_2494_);
lean_dec_ref(v_ci_2493_);
lean_dec_ref(v_text_2492_);
v___x_2517_ = lean_box(0);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v___y_2496_);
lean_ctor_set(v___x_2502_, 0, v___x_2517_);
v___x_2519_ = v___x_2502_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v___y_2496_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_dec(v___x_2504_);
lean_dec(v_snd_2500_);
lean_dec(v_fst_2499_);
lean_dec_ref(v_info_2494_);
lean_dec_ref(v_ci_2493_);
lean_dec_ref(v_text_2492_);
v___x_2521_ = lean_box(0);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v___y_2496_);
lean_ctor_set(v___x_2502_, 0, v___x_2521_);
v___x_2523_ = v___x_2502_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v___y_2496_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec(v___x_2497_);
lean_dec_ref(v_info_2494_);
lean_dec_ref(v_ci_2493_);
lean_dec_ref(v_text_2492_);
v___x_2526_ = lean_box(0);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v___y_2496_);
return v___x_2527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed(lean_object* v_text_2528_, lean_object* v_ci_2529_, lean_object* v_info_2530_, lean_object* v_x_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(v_text_2528_, v_ci_2529_, v_info_2530_, v_x_2531_, v___y_2532_);
lean_dec_ref(v_x_2531_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object* v_postNode_2534_, lean_object* v_ci_2535_, lean_object* v_i_2536_, lean_object* v_cs_2537_, lean_object* v_x_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_apply_4(v_postNode_2534_, v_ci_2535_, v_i_2536_, v_cs_2537_, v___y_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object* v_postNode_2541_, lean_object* v_ci_2542_, lean_object* v_i_2543_, lean_object* v_cs_2544_, lean_object* v_x_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(v_postNode_2541_, v_ci_2542_, v_i_2543_, v_cs_2544_, v_x_2545_, v___y_2546_);
lean_dec(v_x_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___f_2557_; lean_object* v___f_2558_; lean_object* v___f_2559_; lean_object* v___f_2560_; lean_object* v___f_2561_; lean_object* v___f_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_3116__overap_2579_; lean_object* v___x_2580_; 
v___f_2557_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_2558_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_2559_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_2560_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_2561_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_2562_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_2563_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___f_2557_);
lean_ctor_set(v___x_2564_, 1, v___f_2558_);
v___x_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v___f_2559_);
lean_ctor_set(v___x_2565_, 2, v___f_2560_);
lean_ctor_set(v___x_2565_, 3, v___f_2561_);
lean_ctor_set(v___x_2565_, 4, v___f_2562_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v___f_2563_);
lean_inc_ref_n(v___x_2566_, 6);
v___f_2567_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2567_, 0, v___x_2566_);
v___f_2568_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2568_, 0, v___x_2566_);
v___f_2569_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2569_, 0, v___x_2566_);
v___f_2570_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2570_, 0, v___x_2566_);
v___x_2571_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2571_, 0, lean_box(0));
lean_closure_set(v___x_2571_, 1, lean_box(0));
lean_closure_set(v___x_2571_, 2, v___x_2566_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___f_2567_);
v___x_2573_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2573_, 0, lean_box(0));
lean_closure_set(v___x_2573_, 1, lean_box(0));
lean_closure_set(v___x_2573_, 2, v___x_2566_);
v___x_2574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
lean_ctor_set(v___x_2574_, 2, v___f_2568_);
lean_ctor_set(v___x_2574_, 3, v___f_2569_);
lean_ctor_set(v___x_2574_, 4, v___f_2570_);
v___x_2575_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2575_, 0, lean_box(0));
lean_closure_set(v___x_2575_, 1, lean_box(0));
lean_closure_set(v___x_2575_, 2, v___x_2566_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_box(0);
v___x_2578_ = l_instInhabitedOfMonad___redArg(v___x_2576_, v___x_2577_);
v___x_3116__overap_2579_ = lean_panic_fn_borrowed(v___x_2578_, v_msg_2555_);
lean_dec(v___x_2578_);
v___x_2580_ = lean_apply_1(v___x_3116__overap_2579_, v___y_2556_);
return v___x_2580_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2584_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2));
v___x_2585_ = lean_unsigned_to_nat(21u);
v___x_2586_ = lean_unsigned_to_nat(65u);
v___x_2587_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1));
v___x_2588_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0));
v___x_2589_ = l_mkPanicMessageWithDecl(v___x_2588_, v___x_2587_, v___x_2586_, v___x_2585_, v___x_2584_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object* v_preNode_2590_, lean_object* v_postNode_2591_, lean_object* v_x_2592_, lean_object* v_x_2593_, lean_object* v___y_2594_){
_start:
{
switch(lean_obj_tag(v_x_2593_))
{
case 0:
{
lean_object* v_i_2595_; lean_object* v_t_2596_; lean_object* v___x_2597_; 
v_i_2595_ = lean_ctor_get(v_x_2593_, 0);
lean_inc_ref(v_i_2595_);
v_t_2596_ = lean_ctor_get(v_x_2593_, 1);
lean_inc_ref(v_t_2596_);
lean_dec_ref_known(v_x_2593_, 2);
v___x_2597_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2595_, v_x_2592_);
v_x_2592_ = v___x_2597_;
v_x_2593_ = v_t_2596_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_2592_) == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec_ref_known(v_x_2593_, 2);
lean_dec_ref(v_postNode_2591_);
lean_dec_ref(v_preNode_2590_);
v___x_2599_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_2600_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v___x_2599_, v___y_2594_);
return v___x_2600_;
}
else
{
lean_object* v_i_2601_; lean_object* v_children_2602_; lean_object* v_val_2603_; lean_object* v___x_2604_; lean_object* v_fst_2605_; uint8_t v___x_2606_; 
v_i_2601_ = lean_ctor_get(v_x_2593_, 0);
lean_inc_ref_n(v_i_2601_, 2);
v_children_2602_ = lean_ctor_get(v_x_2593_, 1);
lean_inc_ref_n(v_children_2602_, 2);
lean_dec_ref_known(v_x_2593_, 2);
v_val_2603_ = lean_ctor_get(v_x_2592_, 0);
lean_inc_n(v_val_2603_, 2);
lean_inc_ref(v_preNode_2590_);
v___x_2604_ = lean_apply_4(v_preNode_2590_, v_val_2603_, v_i_2601_, v_children_2602_, v___y_2594_);
v_fst_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_fst_2605_);
v___x_2606_ = lean_unbox(v_fst_2605_);
lean_dec(v_fst_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v_preNode_2590_);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_x_2592_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v_x_2592_, 0);
lean_dec(v_unused_2626_);
v___x_2608_ = v_x_2592_;
v_isShared_2609_ = v_isSharedCheck_2625_;
goto v_resetjp_2607_;
}
else
{
lean_dec(v_x_2592_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2625_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_snd_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v_fst_2613_; lean_object* v_snd_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2624_; 
v_snd_2610_ = lean_ctor_get(v___x_2604_, 1);
lean_inc(v_snd_2610_);
lean_dec_ref(v___x_2604_);
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_apply_5(v_postNode_2591_, v_val_2603_, v_i_2601_, v_children_2602_, v___x_2611_, v_snd_2610_);
v_fst_2613_ = lean_ctor_get(v___x_2612_, 0);
v_snd_2614_ = lean_ctor_get(v___x_2612_, 1);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2616_ = v___x_2612_;
v_isShared_2617_ = v_isSharedCheck_2624_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_snd_2614_);
lean_inc(v_fst_2613_);
lean_dec(v___x_2612_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2624_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v_fst_2613_);
v___x_2619_ = v___x_2608_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_fst_2613_);
v___x_2619_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2621_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_snd_2614_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
else
{
lean_object* v_snd_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v_fst_2632_; lean_object* v_snd_2633_; lean_object* v___x_2634_; lean_object* v_fst_2635_; lean_object* v_snd_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2644_; 
v_snd_2627_ = lean_ctor_get(v___x_2604_, 1);
lean_inc(v_snd_2627_);
lean_dec_ref(v___x_2604_);
v___x_2628_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2592_, v_i_2601_);
v___x_2629_ = l_Lean_PersistentArray_toList___redArg(v_children_2602_);
v___x_2630_ = lean_box(0);
lean_inc_ref(v_postNode_2591_);
v___x_2631_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2590_, v_postNode_2591_, v___x_2628_, v___x_2629_, v___x_2630_, v_snd_2627_);
v_fst_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_fst_2632_);
v_snd_2633_ = lean_ctor_get(v___x_2631_, 1);
lean_inc(v_snd_2633_);
lean_dec_ref(v___x_2631_);
v___x_2634_ = lean_apply_5(v_postNode_2591_, v_val_2603_, v_i_2601_, v_children_2602_, v_fst_2632_, v_snd_2633_);
v_fst_2635_ = lean_ctor_get(v___x_2634_, 0);
v_snd_2636_ = lean_ctor_get(v___x_2634_, 1);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2638_ = v___x_2634_;
v_isShared_2639_ = v_isSharedCheck_2644_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_snd_2636_);
lean_inc(v_fst_2635_);
lean_dec(v___x_2634_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2644_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_fst_2635_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2640_);
v___x_2642_ = v___x_2638_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_snd_2636_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
default: 
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_dec_ref_known(v_x_2593_, 1);
lean_dec(v_x_2592_);
lean_dec_ref(v_postNode_2591_);
lean_dec_ref(v_preNode_2590_);
v___x_2645_ = lean_box(0);
v___x_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
lean_ctor_set(v___x_2646_, 1, v___y_2594_);
return v___x_2646_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_2647_, lean_object* v_postNode_2648_, lean_object* v___x_2649_, lean_object* v_x_2650_, lean_object* v_x_2651_, lean_object* v___y_2652_){
_start:
{
if (lean_obj_tag(v_x_2650_) == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v___x_2649_);
lean_dec_ref(v_postNode_2648_);
lean_dec_ref(v_preNode_2647_);
v___x_2653_ = l_List_reverse___redArg(v_x_2651_);
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v___y_2652_);
return v___x_2654_;
}
else
{
lean_object* v_head_2655_; lean_object* v_tail_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2667_; 
v_head_2655_ = lean_ctor_get(v_x_2650_, 0);
v_tail_2656_ = lean_ctor_get(v_x_2650_, 1);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_x_2650_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2658_ = v_x_2650_;
v_isShared_2659_ = v_isSharedCheck_2667_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_tail_2656_);
lean_inc(v_head_2655_);
lean_dec(v_x_2650_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2667_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v_fst_2661_; lean_object* v_snd_2662_; lean_object* v___x_2664_; 
lean_inc(v___x_2649_);
lean_inc_ref(v_postNode_2648_);
lean_inc_ref(v_preNode_2647_);
v___x_2660_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2647_, v_postNode_2648_, v___x_2649_, v_head_2655_, v___y_2652_);
v_fst_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_fst_2661_);
v_snd_2662_ = lean_ctor_get(v___x_2660_, 1);
lean_inc(v_snd_2662_);
lean_dec_ref(v___x_2660_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v_x_2651_);
lean_ctor_set(v___x_2658_, 0, v_fst_2661_);
v___x_2664_ = v___x_2658_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_fst_2661_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_x_2651_);
v___x_2664_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
v_x_2650_ = v_tail_2656_;
v_x_2651_ = v___x_2664_;
v___y_2652_ = v_snd_2662_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object* v_preNode_2668_, lean_object* v_postNode_2669_, lean_object* v_ctx_x3f_2670_, lean_object* v_t_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___f_2673_; lean_object* v___x_2674_; lean_object* v_snd_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2683_; 
v___f_2673_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2673_, 0, v_postNode_2669_);
v___x_2674_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2668_, v___f_2673_, v_ctx_x3f_2670_, v_t_2671_, v___y_2672_);
v_snd_2675_ = lean_ctor_get(v___x_2674_, 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v___x_2674_, 0);
lean_dec(v_unused_2684_);
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2683_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_snd_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2683_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2679_ = lean_box(0);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2679_);
v___x_2681_ = v___x_2677_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_snd_2675_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(lean_object* v_text_2685_, lean_object* v_as_2686_, size_t v_sz_2687_, size_t v_i_2688_, lean_object* v_b_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v___x_2691_; 
v___x_2691_ = lean_usize_dec_lt(v_i_2688_, v_sz_2687_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; 
lean_dec_ref(v_text_2685_);
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_b_2689_);
lean_ctor_set(v___x_2692_, 1, v___y_2690_);
return v___x_2692_;
}
else
{
lean_object* v___x_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v_a_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v_snd_2699_; lean_object* v___x_2700_; size_t v___x_2701_; size_t v___x_2702_; 
v___x_2693_ = lean_box(v___x_2691_);
v___f_2694_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2694_, 0, v___x_2693_);
lean_inc_ref(v_text_2685_);
v___f_2695_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2695_, 0, v_text_2685_);
v_a_2696_ = lean_array_uget_borrowed(v_as_2686_, v_i_2688_);
v___x_2697_ = lean_box(0);
lean_inc(v_a_2696_);
v___x_2698_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(v___f_2694_, v___f_2695_, v___x_2697_, v_a_2696_, v___y_2690_);
v_snd_2699_ = lean_ctor_get(v___x_2698_, 1);
lean_inc(v_snd_2699_);
lean_dec_ref(v___x_2698_);
v___x_2700_ = lean_box(0);
v___x_2701_ = ((size_t)1ULL);
v___x_2702_ = lean_usize_add(v_i_2688_, v___x_2701_);
v_i_2688_ = v___x_2702_;
v_b_2689_ = v___x_2700_;
v___y_2690_ = v_snd_2699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___boxed(lean_object* v_text_2704_, lean_object* v_as_2705_, lean_object* v_sz_2706_, lean_object* v_i_2707_, lean_object* v_b_2708_, lean_object* v___y_2709_){
_start:
{
size_t v_sz_boxed_2710_; size_t v_i_boxed_2711_; lean_object* v_res_2712_; 
v_sz_boxed_2710_ = lean_unbox_usize(v_sz_2706_);
lean_dec(v_sz_2706_);
v_i_boxed_2711_ = lean_unbox_usize(v_i_2707_);
lean_dec(v_i_2707_);
v_res_2712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2704_, v_as_2705_, v_sz_boxed_2710_, v_i_boxed_2711_, v_b_2708_, v___y_2709_);
lean_dec_ref(v_as_2705_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences(lean_object* v_text_2713_, lean_object* v_trees_2714_){
_start:
{
lean_object* v___x_2715_; size_t v_sz_2716_; size_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v_snd_2720_; 
v___x_2715_ = lean_box(0);
v_sz_2716_ = lean_array_size(v_trees_2714_);
v___x_2717_ = ((size_t)0ULL);
v___x_2718_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_2719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2713_, v_trees_2714_, v_sz_2716_, v___x_2717_, v___x_2715_, v___x_2718_);
v_snd_2720_ = lean_ctor_get(v___x_2719_, 1);
lean_inc(v_snd_2720_);
lean_dec_ref(v___x_2719_);
return v_snd_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences___boxed(lean_object* v_text_2721_, lean_object* v_trees_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Server_findReferences(v_text_2721_, v_trees_2722_);
lean_dec_ref(v_trees_2722_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2724_, lean_object* v_msg_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v_msg_2725_, v___y_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object* v_00_u03b1_2728_, lean_object* v_preNode_2729_, lean_object* v_postNode_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2729_, v_postNode_2730_, v_x_2731_, v_x_2732_, v___y_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2735_, lean_object* v_preNode_2736_, lean_object* v_postNode_2737_, lean_object* v___x_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2736_, v_postNode_2737_, v___x_2738_, v_x_2739_, v_x_2740_, v___y_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(lean_object* v_a_2743_, lean_object* v_x_2744_){
_start:
{
lean_object* v_key_2745_; lean_object* v_value_2746_; lean_object* v_tail_2747_; uint8_t v___x_2748_; 
v_key_2745_ = lean_ctor_get(v_x_2744_, 0);
v_value_2746_ = lean_ctor_get(v_x_2744_, 1);
v_tail_2747_ = lean_ctor_get(v_x_2744_, 2);
v___x_2748_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2745_, v_a_2743_);
if (v___x_2748_ == 0)
{
v_x_2744_ = v_tail_2747_;
goto _start;
}
else
{
lean_inc(v_value_2746_);
return v_value_2746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg___boxed(lean_object* v_a_2750_, lean_object* v_x_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2750_, v_x_2751_);
lean_dec(v_x_2751_);
lean_dec_ref(v_a_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(lean_object* v_m_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_buckets_2755_; lean_object* v___x_2756_; uint64_t v___x_2757_; uint64_t v___x_2758_; uint64_t v___x_2759_; uint64_t v_fold_2760_; uint64_t v___x_2761_; uint64_t v___x_2762_; uint64_t v___x_2763_; size_t v___x_2764_; size_t v___x_2765_; size_t v___x_2766_; size_t v___x_2767_; size_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_buckets_2755_ = lean_ctor_get(v_m_2753_, 1);
v___x_2756_ = lean_array_get_size(v_buckets_2755_);
v___x_2757_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2754_);
v___x_2758_ = 32ULL;
v___x_2759_ = lean_uint64_shift_right(v___x_2757_, v___x_2758_);
v_fold_2760_ = lean_uint64_xor(v___x_2757_, v___x_2759_);
v___x_2761_ = 16ULL;
v___x_2762_ = lean_uint64_shift_right(v_fold_2760_, v___x_2761_);
v___x_2763_ = lean_uint64_xor(v_fold_2760_, v___x_2762_);
v___x_2764_ = lean_uint64_to_usize(v___x_2763_);
v___x_2765_ = lean_usize_of_nat(v___x_2756_);
v___x_2766_ = ((size_t)1ULL);
v___x_2767_ = lean_usize_sub(v___x_2765_, v___x_2766_);
v___x_2768_ = lean_usize_land(v___x_2764_, v___x_2767_);
v___x_2769_ = lean_array_uget_borrowed(v_buckets_2755_, v___x_2768_);
v___x_2770_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2754_, v___x_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg___boxed(lean_object* v_m_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2771_, v_a_2772_);
lean_dec_ref(v_a_2772_);
lean_dec_ref(v_m_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(lean_object* v_a_2774_, lean_object* v_x_2775_){
_start:
{
if (lean_obj_tag(v_x_2775_) == 0)
{
uint8_t v___x_2776_; 
v___x_2776_ = 0;
return v___x_2776_;
}
else
{
lean_object* v_key_2777_; lean_object* v_tail_2778_; uint8_t v___x_2779_; 
v_key_2777_ = lean_ctor_get(v_x_2775_, 0);
v_tail_2778_ = lean_ctor_get(v_x_2775_, 2);
v___x_2779_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2777_, v_a_2774_);
if (v___x_2779_ == 0)
{
v_x_2775_ = v_tail_2778_;
goto _start;
}
else
{
return v___x_2779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg___boxed(lean_object* v_a_2781_, lean_object* v_x_2782_){
_start:
{
uint8_t v_res_2783_; lean_object* v_r_2784_; 
v_res_2783_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2781_, v_x_2782_);
lean_dec(v_x_2782_);
lean_dec_ref(v_a_2781_);
v_r_2784_ = lean_box(v_res_2783_);
return v_r_2784_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(lean_object* v_m_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_buckets_2787_; lean_object* v___x_2788_; uint64_t v___x_2789_; uint64_t v___x_2790_; uint64_t v___x_2791_; uint64_t v_fold_2792_; uint64_t v___x_2793_; uint64_t v___x_2794_; uint64_t v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; size_t v___x_2798_; size_t v___x_2799_; size_t v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v_buckets_2787_ = lean_ctor_get(v_m_2785_, 1);
v___x_2788_ = lean_array_get_size(v_buckets_2787_);
v___x_2789_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2786_);
v___x_2790_ = 32ULL;
v___x_2791_ = lean_uint64_shift_right(v___x_2789_, v___x_2790_);
v_fold_2792_ = lean_uint64_xor(v___x_2789_, v___x_2791_);
v___x_2793_ = 16ULL;
v___x_2794_ = lean_uint64_shift_right(v_fold_2792_, v___x_2793_);
v___x_2795_ = lean_uint64_xor(v_fold_2792_, v___x_2794_);
v___x_2796_ = lean_uint64_to_usize(v___x_2795_);
v___x_2797_ = lean_usize_of_nat(v___x_2788_);
v___x_2798_ = ((size_t)1ULL);
v___x_2799_ = lean_usize_sub(v___x_2797_, v___x_2798_);
v___x_2800_ = lean_usize_land(v___x_2796_, v___x_2799_);
v___x_2801_ = lean_array_uget_borrowed(v_buckets_2787_, v___x_2800_);
v___x_2802_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2786_, v___x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg___boxed(lean_object* v_m_2803_, lean_object* v_a_2804_){
_start:
{
uint8_t v_res_2805_; lean_object* v_r_2806_; 
v_res_2805_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2803_, v_a_2804_);
lean_dec_ref(v_a_2804_);
lean_dec_ref(v_m_2803_);
v_r_2806_ = lean_box(v_res_2805_);
return v_r_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(lean_object* v_idMap_2807_, lean_object* v_a_2808_){
_start:
{
uint8_t v___x_2809_; 
v___x_2809_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_idMap_2807_, v_a_2808_);
if (v___x_2809_ == 0)
{
return v_a_2808_;
}
else
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_idMap_2807_, v_a_2808_);
lean_dec_ref(v_a_2808_);
v_a_2808_ = v___x_2810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg___boxed(lean_object* v_idMap_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2812_, v_a_2813_);
lean_dec_ref(v_idMap_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object* v_idMap_2815_, lean_object* v_id_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2815_, v_id_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object* v_idMap_2818_, lean_object* v_id_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(v_idMap_2818_, v_id_2819_);
lean_dec_ref(v_idMap_2818_);
return v_res_2820_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object* v_00_u03b2_2821_, lean_object* v_m_2822_, lean_object* v_a_2823_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2822_, v_a_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object* v_00_u03b2_2825_, lean_object* v_m_2826_, lean_object* v_a_2827_){
_start:
{
uint8_t v_res_2828_; lean_object* v_r_2829_; 
v_res_2828_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(v_00_u03b2_2825_, v_m_2826_, v_a_2827_);
lean_dec_ref(v_a_2827_);
lean_dec_ref(v_m_2826_);
v_r_2829_ = lean_box(v_res_2828_);
return v_r_2829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object* v_00_u03b2_2830_, lean_object* v_m_2831_, lean_object* v_a_2832_, lean_object* v_hma_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2831_, v_a_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object* v_00_u03b2_2835_, lean_object* v_m_2836_, lean_object* v_a_2837_, lean_object* v_hma_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(v_00_u03b2_2835_, v_m_2836_, v_a_2837_, v_hma_2838_);
lean_dec_ref(v_a_2837_);
lean_dec_ref(v_m_2836_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object* v_idMap_2840_, lean_object* v_inst_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2840_, v_a_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object* v_idMap_2844_, lean_object* v_inst_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2844_, v_inst_2845_, v_a_2846_);
lean_dec_ref(v_idMap_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(lean_object* v_00_u03b2_2848_, lean_object* v_a_2849_, lean_object* v_x_2850_){
_start:
{
uint8_t v___x_2851_; 
v___x_2851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2849_, v_x_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2852_, lean_object* v_a_2853_, lean_object* v_x_2854_){
_start:
{
uint8_t v_res_2855_; lean_object* v_r_2856_; 
v_res_2855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(v_00_u03b2_2852_, v_a_2853_, v_x_2854_);
lean_dec(v_x_2854_);
lean_dec_ref(v_a_2853_);
v_r_2856_ = lean_box(v_res_2855_);
return v_r_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(lean_object* v_00_u03b2_2857_, lean_object* v_a_2858_, lean_object* v_x_2859_, lean_object* v_x_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2858_, v_x_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2862_, lean_object* v_a_2863_, lean_object* v_x_2864_, lean_object* v_x_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(v_00_u03b2_2862_, v_a_2863_, v_x_2864_, v_x_2865_);
lean_dec(v_x_2864_);
lean_dec_ref(v_a_2863_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
if (lean_obj_tag(v_a_2867_) == 0)
{
lean_object* v___x_2869_; 
v___x_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2869_, 0, v_a_2868_);
return v___x_2869_;
}
else
{
if (lean_obj_tag(v_a_2868_) == 0)
{
lean_object* v_tail_2870_; 
v_tail_2870_ = lean_ctor_get(v_a_2867_, 2);
lean_inc(v_tail_2870_);
lean_dec_ref_known(v_a_2867_, 3);
v_a_2867_ = v_tail_2870_;
goto _start;
}
else
{
lean_object* v_key_2872_; 
v_key_2872_ = lean_ctor_get(v_a_2867_, 0);
if (lean_obj_tag(v_key_2872_) == 0)
{
lean_object* v_tail_2873_; 
lean_inc_ref(v_key_2872_);
lean_dec_ref_known(v_a_2868_, 2);
v_tail_2873_ = lean_ctor_get(v_a_2867_, 2);
lean_inc(v_tail_2873_);
lean_dec_ref_known(v_a_2867_, 3);
v_a_2867_ = v_tail_2873_;
v_a_2868_ = v_key_2872_;
goto _start;
}
else
{
lean_object* v_tail_2875_; 
v_tail_2875_ = lean_ctor_get(v_a_2867_, 2);
lean_inc(v_tail_2875_);
lean_dec_ref_known(v_a_2867_, 3);
v_a_2867_ = v_tail_2875_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(lean_object* v_as_2877_, size_t v_sz_2878_, size_t v_i_2879_, lean_object* v_b_2880_){
_start:
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_usize_dec_lt(v_i_2879_, v_sz_2878_);
if (v___x_2881_ == 0)
{
return v_b_2880_;
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2883_; 
v_a_2882_ = lean_array_uget_borrowed(v_as_2877_, v_i_2879_);
lean_inc(v_a_2882_);
v___x_2883_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(v_a_2882_, v_b_2880_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
return v_a_2884_;
}
else
{
lean_object* v_a_2885_; size_t v___x_2886_; size_t v___x_2887_; 
v_a_2885_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2886_ = ((size_t)1ULL);
v___x_2887_ = lean_usize_add(v_i_2879_, v___x_2886_);
v_i_2879_ = v___x_2887_;
v_b_2880_ = v_a_2885_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5___boxed(lean_object* v_as_2889_, lean_object* v_sz_2890_, lean_object* v_i_2891_, lean_object* v_b_2892_){
_start:
{
size_t v_sz_boxed_2893_; size_t v_i_boxed_2894_; lean_object* v_res_2895_; 
v_sz_boxed_2893_ = lean_unbox_usize(v_sz_2890_);
lean_dec(v_sz_2890_);
v_i_boxed_2894_ = lean_unbox_usize(v_i_2891_);
lean_dec(v_i_2891_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_as_2889_, v_sz_boxed_2893_, v_i_boxed_2894_, v_b_2892_);
lean_dec_ref(v_as_2889_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(lean_object* v_a_2896_, lean_object* v_b_2897_, lean_object* v_x_2898_){
_start:
{
if (lean_obj_tag(v_x_2898_) == 0)
{
lean_dec(v_b_2897_);
lean_dec_ref(v_a_2896_);
return v_x_2898_;
}
else
{
lean_object* v_key_2899_; lean_object* v_value_2900_; lean_object* v_tail_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2913_; 
v_key_2899_ = lean_ctor_get(v_x_2898_, 0);
v_value_2900_ = lean_ctor_get(v_x_2898_, 1);
v_tail_2901_ = lean_ctor_get(v_x_2898_, 2);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_x_2898_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2903_ = v_x_2898_;
v_isShared_2904_ = v_isSharedCheck_2913_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_tail_2901_);
lean_inc(v_value_2900_);
lean_inc(v_key_2899_);
lean_dec(v_x_2898_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2913_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
uint8_t v___x_2905_; 
v___x_2905_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2899_, v_a_2896_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2896_, v_b_2897_, v_tail_2901_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 2, v___x_2906_);
v___x_2908_ = v___x_2903_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_key_2899_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_value_2900_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
else
{
lean_object* v___x_2911_; 
lean_dec(v_value_2900_);
lean_dec(v_key_2899_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 1, v_b_2897_);
lean_ctor_set(v___x_2903_, 0, v_a_2896_);
v___x_2911_ = v___x_2903_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2896_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_b_2897_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_tail_2901_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
if (lean_obj_tag(v_x_2915_) == 0)
{
return v_x_2914_;
}
else
{
lean_object* v_key_2916_; lean_object* v_value_2917_; lean_object* v_tail_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2941_; 
v_key_2916_ = lean_ctor_get(v_x_2915_, 0);
v_value_2917_ = lean_ctor_get(v_x_2915_, 1);
v_tail_2918_ = lean_ctor_get(v_x_2915_, 2);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_x_2915_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2920_ = v_x_2915_;
v_isShared_2921_ = v_isSharedCheck_2941_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_tail_2918_);
lean_inc(v_value_2917_);
lean_inc(v_key_2916_);
lean_dec(v_x_2915_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2941_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; uint64_t v___x_2923_; uint64_t v___x_2924_; uint64_t v___x_2925_; uint64_t v_fold_2926_; uint64_t v___x_2927_; uint64_t v___x_2928_; uint64_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; size_t v___x_2933_; size_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2922_ = lean_array_get_size(v_x_2914_);
v___x_2923_ = l_Lean_Lsp_instHashableRefIdent_hash(v_key_2916_);
v___x_2924_ = 32ULL;
v___x_2925_ = lean_uint64_shift_right(v___x_2923_, v___x_2924_);
v_fold_2926_ = lean_uint64_xor(v___x_2923_, v___x_2925_);
v___x_2927_ = 16ULL;
v___x_2928_ = lean_uint64_shift_right(v_fold_2926_, v___x_2927_);
v___x_2929_ = lean_uint64_xor(v_fold_2926_, v___x_2928_);
v___x_2930_ = lean_uint64_to_usize(v___x_2929_);
v___x_2931_ = lean_usize_of_nat(v___x_2922_);
v___x_2932_ = ((size_t)1ULL);
v___x_2933_ = lean_usize_sub(v___x_2931_, v___x_2932_);
v___x_2934_ = lean_usize_land(v___x_2930_, v___x_2933_);
v___x_2935_ = lean_array_uget_borrowed(v_x_2914_, v___x_2934_);
lean_inc(v___x_2935_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 2, v___x_2935_);
v___x_2937_ = v___x_2920_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_key_2916_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_value_2917_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_array_uset(v_x_2914_, v___x_2934_, v___x_2937_);
v_x_2914_ = v___x_2938_;
v_x_2915_ = v_tail_2918_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(lean_object* v_i_2942_, lean_object* v_source_2943_, lean_object* v_target_2944_){
_start:
{
lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = lean_array_get_size(v_source_2943_);
v___x_2946_ = lean_nat_dec_lt(v_i_2942_, v___x_2945_);
if (v___x_2946_ == 0)
{
lean_dec_ref(v_source_2943_);
lean_dec(v_i_2942_);
return v_target_2944_;
}
else
{
lean_object* v_es_2947_; lean_object* v___x_2948_; lean_object* v_source_2949_; lean_object* v_target_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_es_2947_ = lean_array_fget(v_source_2943_, v_i_2942_);
v___x_2948_ = lean_box(0);
v_source_2949_ = lean_array_fset(v_source_2943_, v_i_2942_, v___x_2948_);
v_target_2950_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_target_2944_, v_es_2947_);
v___x_2951_ = lean_unsigned_to_nat(1u);
v___x_2952_ = lean_nat_add(v_i_2942_, v___x_2951_);
lean_dec(v_i_2942_);
v_i_2942_ = v___x_2952_;
v_source_2943_ = v_source_2949_;
v_target_2944_ = v_target_2950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(lean_object* v_data_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_nbuckets_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2955_ = lean_array_get_size(v_data_2954_);
v___x_2956_ = lean_unsigned_to_nat(2u);
v_nbuckets_2957_ = lean_nat_mul(v___x_2955_, v___x_2956_);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_mk_array(v_nbuckets_2957_, v___x_2959_);
v___x_2961_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2958_, v_data_2954_, v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object* v_m_2962_, lean_object* v_a_2963_, lean_object* v_b_2964_){
_start:
{
lean_object* v_size_2965_; lean_object* v_buckets_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3009_; 
v_size_2965_ = lean_ctor_get(v_m_2962_, 0);
v_buckets_2966_ = lean_ctor_get(v_m_2962_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_m_2962_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2968_ = v_m_2962_;
v_isShared_2969_ = v_isSharedCheck_3009_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_buckets_2966_);
lean_inc(v_size_2965_);
lean_dec(v_m_2962_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3009_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; uint64_t v___x_2971_; uint64_t v___x_2972_; uint64_t v___x_2973_; uint64_t v_fold_2974_; uint64_t v___x_2975_; uint64_t v___x_2976_; uint64_t v___x_2977_; size_t v___x_2978_; size_t v___x_2979_; size_t v___x_2980_; size_t v___x_2981_; size_t v___x_2982_; lean_object* v_bkt_2983_; uint8_t v___x_2984_; 
v___x_2970_ = lean_array_get_size(v_buckets_2966_);
v___x_2971_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2963_);
v___x_2972_ = 32ULL;
v___x_2973_ = lean_uint64_shift_right(v___x_2971_, v___x_2972_);
v_fold_2974_ = lean_uint64_xor(v___x_2971_, v___x_2973_);
v___x_2975_ = 16ULL;
v___x_2976_ = lean_uint64_shift_right(v_fold_2974_, v___x_2975_);
v___x_2977_ = lean_uint64_xor(v_fold_2974_, v___x_2976_);
v___x_2978_ = lean_uint64_to_usize(v___x_2977_);
v___x_2979_ = lean_usize_of_nat(v___x_2970_);
v___x_2980_ = ((size_t)1ULL);
v___x_2981_ = lean_usize_sub(v___x_2979_, v___x_2980_);
v___x_2982_ = lean_usize_land(v___x_2978_, v___x_2981_);
v_bkt_2983_ = lean_array_uget_borrowed(v_buckets_2966_, v___x_2982_);
v___x_2984_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2963_, v_bkt_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v_size_x27_2986_; lean_object* v___x_2987_; lean_object* v_buckets_x27_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v___x_2985_ = lean_unsigned_to_nat(1u);
v_size_x27_2986_ = lean_nat_add(v_size_2965_, v___x_2985_);
lean_dec(v_size_2965_);
lean_inc(v_bkt_2983_);
v___x_2987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2963_);
lean_ctor_set(v___x_2987_, 1, v_b_2964_);
lean_ctor_set(v___x_2987_, 2, v_bkt_2983_);
v_buckets_x27_2988_ = lean_array_uset(v_buckets_2966_, v___x_2982_, v___x_2987_);
v___x_2989_ = lean_unsigned_to_nat(4u);
v___x_2990_ = lean_nat_mul(v_size_x27_2986_, v___x_2989_);
v___x_2991_ = lean_unsigned_to_nat(3u);
v___x_2992_ = lean_nat_div(v___x_2990_, v___x_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_array_get_size(v_buckets_x27_2988_);
v___x_2994_ = lean_nat_dec_le(v___x_2992_, v___x_2993_);
lean_dec(v___x_2992_);
if (v___x_2994_ == 0)
{
lean_object* v_val_2995_; lean_object* v___x_2997_; 
v_val_2995_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_2988_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v_val_2995_);
lean_ctor_set(v___x_2968_, 0, v_size_x27_2986_);
v___x_2997_ = v___x_2968_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_size_x27_2986_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_val_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
else
{
lean_object* v___x_3000_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v_buckets_x27_2988_);
lean_ctor_set(v___x_2968_, 0, v_size_x27_2986_);
v___x_3000_ = v___x_2968_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_size_x27_2986_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_buckets_x27_2988_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
else
{
lean_object* v___x_3002_; lean_object* v_buckets_x27_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
lean_inc(v_bkt_2983_);
v___x_3002_ = lean_box(0);
v_buckets_x27_3003_ = lean_array_uset(v_buckets_2966_, v___x_2982_, v___x_3002_);
v___x_3004_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2963_, v_b_2964_, v_bkt_2983_);
v___x_3005_ = lean_array_uset(v_buckets_x27_3003_, v___x_2982_, v___x_3004_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v___x_3005_);
v___x_3007_ = v___x_2968_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_size_2965_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object* v___x_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
if (lean_obj_tag(v_a_3011_) == 0)
{
lean_object* v___x_3013_; 
lean_dec_ref(v___x_3010_);
v___x_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3013_, 0, v_a_3012_);
return v___x_3013_;
}
else
{
lean_object* v_key_3014_; lean_object* v_tail_3015_; uint8_t v___x_3016_; 
v_key_3014_ = lean_ctor_get(v_a_3011_, 0);
lean_inc(v_key_3014_);
v_tail_3015_ = lean_ctor_get(v_a_3011_, 2);
lean_inc(v_tail_3015_);
lean_dec_ref_known(v_a_3011_, 3);
v___x_3016_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3014_, v___x_3010_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
lean_inc_ref(v___x_3010_);
v___x_3017_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3012_, v_key_3014_, v___x_3010_);
v_a_3011_ = v_tail_3015_;
v_a_3012_ = v___x_3017_;
goto _start;
}
else
{
lean_dec(v_key_3014_);
v_a_3011_ = v_tail_3015_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object* v___x_3020_, lean_object* v_as_3021_, size_t v_sz_3022_, size_t v_i_3023_, lean_object* v_b_3024_){
_start:
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_usize_dec_lt(v_i_3023_, v_sz_3022_);
if (v___x_3025_ == 0)
{
lean_dec_ref(v___x_3020_);
return v_b_3024_;
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3027_; 
v_a_3026_ = lean_array_uget_borrowed(v_as_3021_, v_i_3023_);
lean_inc(v_a_3026_);
lean_inc_ref(v___x_3020_);
v___x_3027_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(v___x_3020_, v_a_3026_, v_b_3024_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; 
lean_dec_ref(v___x_3020_);
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
return v_a_3028_;
}
else
{
lean_object* v_a_3029_; size_t v___x_3030_; size_t v___x_3031_; 
v_a_3029_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3027_, 1);
v___x_3030_ = ((size_t)1ULL);
v___x_3031_ = lean_usize_add(v_i_3023_, v___x_3030_);
v_i_3023_ = v___x_3031_;
v_b_3024_ = v_a_3029_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object* v___x_3033_, lean_object* v_as_3034_, lean_object* v_sz_3035_, lean_object* v_i_3036_, lean_object* v_b_3037_){
_start:
{
size_t v_sz_boxed_3038_; size_t v_i_boxed_3039_; lean_object* v_res_3040_; 
v_sz_boxed_3038_ = lean_unbox_usize(v_sz_3035_);
lean_dec(v_sz_3035_);
v_i_boxed_3039_ = lean_unbox_usize(v_i_3036_);
lean_dec(v_i_3036_);
v_res_3040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3033_, v_as_3034_, v_sz_boxed_3038_, v_i_boxed_3039_, v_b_3037_);
lean_dec_ref(v_as_3034_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
if (lean_obj_tag(v_a_3041_) == 0)
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_a_3042_);
return v___x_3043_;
}
else
{
lean_object* v_value_3044_; lean_object* v_key_3045_; lean_object* v_tail_3046_; lean_object* v_buckets_3047_; size_t v_sz_3048_; size_t v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_value_3044_ = lean_ctor_get(v_a_3041_, 1);
lean_inc(v_value_3044_);
v_key_3045_ = lean_ctor_get(v_a_3041_, 0);
lean_inc(v_key_3045_);
v_tail_3046_ = lean_ctor_get(v_a_3041_, 2);
lean_inc(v_tail_3046_);
lean_dec_ref_known(v_a_3041_, 3);
v_buckets_3047_ = lean_ctor_get(v_value_3044_, 1);
lean_inc_ref(v_buckets_3047_);
lean_dec(v_value_3044_);
v_sz_3048_ = lean_array_size(v_buckets_3047_);
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_buckets_3047_, v_sz_3048_, v___x_3049_, v_key_3045_);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3050_, v_buckets_3047_, v_sz_3048_, v___x_3049_, v_a_3042_);
lean_dec_ref(v_buckets_3047_);
v_a_3041_ = v_tail_3046_;
v_a_3042_ = v___x_3051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object* v_as_3053_, size_t v_sz_3054_, size_t v_i_3055_, lean_object* v_b_3056_){
_start:
{
uint8_t v___x_3057_; 
v___x_3057_ = lean_usize_dec_lt(v_i_3055_, v_sz_3054_);
if (v___x_3057_ == 0)
{
return v_b_3056_;
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3059_; 
v_a_3058_ = lean_array_uget_borrowed(v_as_3053_, v_i_3055_);
lean_inc(v_a_3058_);
v___x_3059_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(v_a_3058_, v_b_3056_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
return v_a_3060_;
}
else
{
lean_object* v_a_3061_; size_t v___x_3062_; size_t v___x_3063_; 
v_a_3061_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3062_ = ((size_t)1ULL);
v___x_3063_ = lean_usize_add(v_i_3055_, v___x_3062_);
v_i_3055_ = v___x_3063_;
v_b_3056_ = v_a_3061_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object* v_as_3065_, lean_object* v_sz_3066_, lean_object* v_i_3067_, lean_object* v_b_3068_){
_start:
{
size_t v_sz_boxed_3069_; size_t v_i_boxed_3070_; lean_object* v_res_3071_; 
v_sz_boxed_3069_ = lean_unbox_usize(v_sz_3066_);
lean_dec(v_sz_3066_);
v_i_boxed_3070_ = lean_unbox_usize(v_i_3067_);
lean_dec(v_i_3067_);
v_res_3071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_as_3065_, v_sz_boxed_3069_, v_i_boxed_3070_, v_b_3068_);
lean_dec_ref(v_as_3065_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object* v_a_3072_, lean_object* v_x_3073_){
_start:
{
if (lean_obj_tag(v_x_3073_) == 0)
{
return v_x_3073_;
}
else
{
lean_object* v_key_3074_; lean_object* v_value_3075_; lean_object* v_tail_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3085_; 
v_key_3074_ = lean_ctor_get(v_x_3073_, 0);
v_value_3075_ = lean_ctor_get(v_x_3073_, 1);
v_tail_3076_ = lean_ctor_get(v_x_3073_, 2);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_x_3073_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3078_ = v_x_3073_;
v_isShared_3079_ = v_isSharedCheck_3085_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_tail_3076_);
lean_inc(v_value_3075_);
lean_inc(v_key_3074_);
lean_dec(v_x_3073_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3085_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
uint8_t v___x_3080_; 
v___x_3080_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3074_, v_a_3072_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3083_; 
v___x_3081_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3072_, v_tail_3076_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 2, v___x_3081_);
v___x_3083_ = v___x_3078_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_key_3074_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_value_3075_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v___x_3081_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
else
{
lean_del_object(v___x_3078_);
lean_dec(v_value_3075_);
lean_dec(v_key_3074_);
return v_tail_3076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object* v_a_3086_, lean_object* v_x_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3086_, v_x_3087_);
lean_dec_ref(v_a_3086_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object* v_m_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_size_3091_; lean_object* v_buckets_3092_; lean_object* v___x_3093_; uint64_t v___x_3094_; uint64_t v___x_3095_; uint64_t v___x_3096_; uint64_t v_fold_3097_; uint64_t v___x_3098_; uint64_t v___x_3099_; uint64_t v___x_3100_; size_t v___x_3101_; size_t v___x_3102_; size_t v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; lean_object* v_bkt_3106_; uint8_t v___x_3107_; 
v_size_3091_ = lean_ctor_get(v_m_3089_, 0);
v_buckets_3092_ = lean_ctor_get(v_m_3089_, 1);
v___x_3093_ = lean_array_get_size(v_buckets_3092_);
v___x_3094_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3090_);
v___x_3095_ = 32ULL;
v___x_3096_ = lean_uint64_shift_right(v___x_3094_, v___x_3095_);
v_fold_3097_ = lean_uint64_xor(v___x_3094_, v___x_3096_);
v___x_3098_ = 16ULL;
v___x_3099_ = lean_uint64_shift_right(v_fold_3097_, v___x_3098_);
v___x_3100_ = lean_uint64_xor(v_fold_3097_, v___x_3099_);
v___x_3101_ = lean_uint64_to_usize(v___x_3100_);
v___x_3102_ = lean_usize_of_nat(v___x_3093_);
v___x_3103_ = ((size_t)1ULL);
v___x_3104_ = lean_usize_sub(v___x_3102_, v___x_3103_);
v___x_3105_ = lean_usize_land(v___x_3101_, v___x_3104_);
v_bkt_3106_ = lean_array_uget_borrowed(v_buckets_3092_, v___x_3105_);
v___x_3107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3090_, v_bkt_3106_);
if (v___x_3107_ == 0)
{
return v_m_3089_;
}
else
{
lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3120_; 
lean_inc(v_bkt_3106_);
lean_inc_ref(v_buckets_3092_);
lean_inc(v_size_3091_);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_m_3089_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; lean_object* v_unused_3122_; 
v_unused_3121_ = lean_ctor_get(v_m_3089_, 1);
lean_dec(v_unused_3121_);
v_unused_3122_ = lean_ctor_get(v_m_3089_, 0);
lean_dec(v_unused_3122_);
v___x_3109_ = v_m_3089_;
v_isShared_3110_ = v_isSharedCheck_3120_;
goto v_resetjp_3108_;
}
else
{
lean_dec(v_m_3089_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3120_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v_buckets_x27_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3111_ = lean_box(0);
v_buckets_x27_3112_ = lean_array_uset(v_buckets_3092_, v___x_3105_, v___x_3111_);
v___x_3113_ = lean_unsigned_to_nat(1u);
v___x_3114_ = lean_nat_sub(v_size_3091_, v___x_3113_);
lean_dec(v_size_3091_);
v___x_3115_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3090_, v_bkt_3106_);
v___x_3116_ = lean_array_uset(v_buckets_x27_3112_, v___x_3105_, v___x_3115_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v___x_3116_);
lean_ctor_set(v___x_3109_, 0, v___x_3114_);
v___x_3118_ = v___x_3109_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object* v_m_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3123_, v_a_3124_);
lean_dec_ref(v_a_3124_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object* v_m_3126_, lean_object* v_a_3127_, lean_object* v_b_3128_){
_start:
{
lean_object* v_size_3129_; lean_object* v_buckets_3130_; lean_object* v___x_3131_; uint64_t v___x_3132_; uint64_t v___x_3133_; uint64_t v___x_3134_; uint64_t v_fold_3135_; uint64_t v___x_3136_; uint64_t v___x_3137_; uint64_t v___x_3138_; size_t v___x_3139_; size_t v___x_3140_; size_t v___x_3141_; size_t v___x_3142_; size_t v___x_3143_; lean_object* v_bkt_3144_; uint8_t v___x_3145_; 
v_size_3129_ = lean_ctor_get(v_m_3126_, 0);
v_buckets_3130_ = lean_ctor_get(v_m_3126_, 1);
v___x_3131_ = lean_array_get_size(v_buckets_3130_);
v___x_3132_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3127_);
v___x_3133_ = 32ULL;
v___x_3134_ = lean_uint64_shift_right(v___x_3132_, v___x_3133_);
v_fold_3135_ = lean_uint64_xor(v___x_3132_, v___x_3134_);
v___x_3136_ = 16ULL;
v___x_3137_ = lean_uint64_shift_right(v_fold_3135_, v___x_3136_);
v___x_3138_ = lean_uint64_xor(v_fold_3135_, v___x_3137_);
v___x_3139_ = lean_uint64_to_usize(v___x_3138_);
v___x_3140_ = lean_usize_of_nat(v___x_3131_);
v___x_3141_ = ((size_t)1ULL);
v___x_3142_ = lean_usize_sub(v___x_3140_, v___x_3141_);
v___x_3143_ = lean_usize_land(v___x_3139_, v___x_3142_);
v_bkt_3144_ = lean_array_uget_borrowed(v_buckets_3130_, v___x_3143_);
v___x_3145_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3127_, v_bkt_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3166_; 
lean_inc_ref(v_buckets_3130_);
lean_inc(v_size_3129_);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_m_3126_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; lean_object* v_unused_3168_; 
v_unused_3167_ = lean_ctor_get(v_m_3126_, 1);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_m_3126_, 0);
lean_dec(v_unused_3168_);
v___x_3147_ = v_m_3126_;
v_isShared_3148_ = v_isSharedCheck_3166_;
goto v_resetjp_3146_;
}
else
{
lean_dec(v_m_3126_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3166_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v_size_x27_3150_; lean_object* v___x_3151_; lean_object* v_buckets_x27_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3149_ = lean_unsigned_to_nat(1u);
v_size_x27_3150_ = lean_nat_add(v_size_3129_, v___x_3149_);
lean_dec(v_size_3129_);
lean_inc(v_bkt_3144_);
v___x_3151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3151_, 0, v_a_3127_);
lean_ctor_set(v___x_3151_, 1, v_b_3128_);
lean_ctor_set(v___x_3151_, 2, v_bkt_3144_);
v_buckets_x27_3152_ = lean_array_uset(v_buckets_3130_, v___x_3143_, v___x_3151_);
v___x_3153_ = lean_unsigned_to_nat(4u);
v___x_3154_ = lean_nat_mul(v_size_x27_3150_, v___x_3153_);
v___x_3155_ = lean_unsigned_to_nat(3u);
v___x_3156_ = lean_nat_div(v___x_3154_, v___x_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_array_get_size(v_buckets_x27_3152_);
v___x_3158_ = lean_nat_dec_le(v___x_3156_, v___x_3157_);
lean_dec(v___x_3156_);
if (v___x_3158_ == 0)
{
lean_object* v_val_3159_; lean_object* v___x_3161_; 
v_val_3159_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3152_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 1, v_val_3159_);
lean_ctor_set(v___x_3147_, 0, v_size_x27_3150_);
v___x_3161_ = v___x_3147_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_size_x27_3150_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_val_3159_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
else
{
lean_object* v___x_3164_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 1, v_buckets_x27_3152_);
lean_ctor_set(v___x_3147_, 0, v_size_x27_3150_);
v___x_3164_ = v___x_3147_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_size_x27_3150_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_buckets_x27_3152_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
else
{
lean_dec(v_b_3128_);
lean_dec_ref(v_a_3127_);
return v_m_3126_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object* v_a_3169_, lean_object* v_fallback_3170_, lean_object* v_x_3171_){
_start:
{
if (lean_obj_tag(v_x_3171_) == 0)
{
lean_inc(v_fallback_3170_);
return v_fallback_3170_;
}
else
{
lean_object* v_key_3172_; lean_object* v_value_3173_; lean_object* v_tail_3174_; uint8_t v___x_3175_; 
v_key_3172_ = lean_ctor_get(v_x_3171_, 0);
v_value_3173_ = lean_ctor_get(v_x_3171_, 1);
v_tail_3174_ = lean_ctor_get(v_x_3171_, 2);
v___x_3175_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3172_, v_a_3169_);
if (v___x_3175_ == 0)
{
v_x_3171_ = v_tail_3174_;
goto _start;
}
else
{
lean_inc(v_value_3173_);
return v_value_3173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object* v_a_3177_, lean_object* v_fallback_3178_, lean_object* v_x_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3177_, v_fallback_3178_, v_x_3179_);
lean_dec(v_x_3179_);
lean_dec(v_fallback_3178_);
lean_dec_ref(v_a_3177_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object* v_m_3181_, lean_object* v_a_3182_, lean_object* v_fallback_3183_){
_start:
{
lean_object* v_buckets_3184_; lean_object* v___x_3185_; uint64_t v___x_3186_; uint64_t v___x_3187_; uint64_t v___x_3188_; uint64_t v_fold_3189_; uint64_t v___x_3190_; uint64_t v___x_3191_; uint64_t v___x_3192_; size_t v___x_3193_; size_t v___x_3194_; size_t v___x_3195_; size_t v___x_3196_; size_t v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v_buckets_3184_ = lean_ctor_get(v_m_3181_, 1);
v___x_3185_ = lean_array_get_size(v_buckets_3184_);
v___x_3186_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3182_);
v___x_3187_ = 32ULL;
v___x_3188_ = lean_uint64_shift_right(v___x_3186_, v___x_3187_);
v_fold_3189_ = lean_uint64_xor(v___x_3186_, v___x_3188_);
v___x_3190_ = 16ULL;
v___x_3191_ = lean_uint64_shift_right(v_fold_3189_, v___x_3190_);
v___x_3192_ = lean_uint64_xor(v_fold_3189_, v___x_3191_);
v___x_3193_ = lean_uint64_to_usize(v___x_3192_);
v___x_3194_ = lean_usize_of_nat(v___x_3185_);
v___x_3195_ = ((size_t)1ULL);
v___x_3196_ = lean_usize_sub(v___x_3194_, v___x_3195_);
v___x_3197_ = lean_usize_land(v___x_3193_, v___x_3196_);
v___x_3198_ = lean_array_uget_borrowed(v_buckets_3184_, v___x_3197_);
v___x_3199_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3182_, v_fallback_3183_, v___x_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object* v_m_3200_, lean_object* v_a_3201_, lean_object* v_fallback_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3200_, v_a_3201_, v_fallback_3202_);
lean_dec(v_fallback_3202_);
lean_dec_ref(v_a_3201_);
lean_dec_ref(v_m_3200_);
return v_res_3203_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = lean_box(0);
v___x_3205_ = lean_unsigned_to_nat(16u);
v___x_3206_ = lean_mk_array(v___x_3205_, v___x_3204_);
return v___x_3206_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0);
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v___x_3207_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object* v_idMap_3210_, lean_object* v_classesById_3211_, lean_object* v_id_3212_){
_start:
{
lean_object* v_representative_3213_; lean_object* v___x_3214_; lean_object* v_class_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v_class_3218_; lean_object* v___x_3219_; 
lean_inc_ref(v_id_3212_);
v_representative_3213_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_3210_, v_id_3212_);
v___x_3214_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_class_3215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_classesById_3211_, v_representative_3213_, v___x_3214_);
v___x_3216_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_classesById_3211_, v_representative_3213_);
v___x_3217_ = lean_box(0);
v_class_3218_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_class_3215_, v_id_3212_, v___x_3217_);
v___x_3219_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v___x_3216_, v_representative_3213_, v_class_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object* v_idMap_3220_, lean_object* v_classesById_3221_, lean_object* v_id_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3220_, v_classesById_3221_, v_id_3222_);
lean_dec_ref(v_idMap_3220_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object* v_idMap_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
if (lean_obj_tag(v_a_3225_) == 0)
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_a_3226_);
return v___x_3227_;
}
else
{
lean_object* v_key_3228_; lean_object* v_value_3229_; lean_object* v_tail_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v_key_3228_ = lean_ctor_get(v_a_3225_, 0);
lean_inc(v_key_3228_);
v_value_3229_ = lean_ctor_get(v_a_3225_, 1);
lean_inc(v_value_3229_);
v_tail_3230_ = lean_ctor_get(v_a_3225_, 2);
lean_inc(v_tail_3230_);
lean_dec_ref_known(v_a_3225_, 3);
v___x_3231_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3224_, v_a_3226_, v_key_3228_);
v___x_3232_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3224_, v___x_3231_, v_value_3229_);
v_a_3225_ = v_tail_3230_;
v_a_3226_ = v___x_3232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object* v_idMap_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3234_, v_a_3235_, v_a_3236_);
lean_dec_ref(v_idMap_3234_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object* v_idMap_3238_, lean_object* v_as_3239_, size_t v_sz_3240_, size_t v_i_3241_, lean_object* v_b_3242_){
_start:
{
uint8_t v___x_3243_; 
v___x_3243_ = lean_usize_dec_lt(v_i_3241_, v_sz_3240_);
if (v___x_3243_ == 0)
{
return v_b_3242_;
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3245_; 
v_a_3244_ = lean_array_uget_borrowed(v_as_3239_, v_i_3241_);
lean_inc(v_a_3244_);
v___x_3245_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3238_, v_a_3244_, v_b_3242_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
return v_a_3246_;
}
else
{
lean_object* v_a_3247_; size_t v___x_3248_; size_t v___x_3249_; 
v_a_3247_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3245_, 1);
v___x_3248_ = ((size_t)1ULL);
v___x_3249_ = lean_usize_add(v_i_3241_, v___x_3248_);
v_i_3241_ = v___x_3249_;
v_b_3242_ = v_a_3247_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object* v_idMap_3251_, lean_object* v_as_3252_, lean_object* v_sz_3253_, lean_object* v_i_3254_, lean_object* v_b_3255_){
_start:
{
size_t v_sz_boxed_3256_; size_t v_i_boxed_3257_; lean_object* v_res_3258_; 
v_sz_boxed_3256_ = lean_unbox_usize(v_sz_3253_);
lean_dec(v_sz_3253_);
v_i_boxed_3257_ = lean_unbox_usize(v_i_3254_);
lean_dec(v_i_3254_);
v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3251_, v_as_3252_, v_sz_boxed_3256_, v_i_boxed_3257_, v_b_3255_);
lean_dec_ref(v_as_3252_);
lean_dec_ref(v_idMap_3251_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object* v_idMap_3259_){
_start:
{
lean_object* v_buckets_3260_; lean_object* v_classesById_3261_; size_t v_sz_3262_; size_t v___x_3263_; lean_object* v___x_3264_; lean_object* v_buckets_3265_; size_t v_sz_3266_; lean_object* v___x_3267_; 
v_buckets_3260_ = lean_ctor_get(v_idMap_3259_, 1);
v_classesById_3261_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_sz_3262_ = lean_array_size(v_buckets_3260_);
v___x_3263_ = ((size_t)0ULL);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3259_, v_buckets_3260_, v_sz_3262_, v___x_3263_, v_classesById_3261_);
v_buckets_3265_ = lean_ctor_get(v___x_3264_, 1);
lean_inc_ref(v_buckets_3265_);
lean_dec_ref(v___x_3264_);
v_sz_3266_ = lean_array_size(v_buckets_3265_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_buckets_3265_, v_sz_3266_, v___x_3263_, v_classesById_3261_);
lean_dec_ref(v_buckets_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object* v_idMap_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v_idMap_3268_);
lean_dec_ref(v_idMap_3268_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object* v_00_u03b2_3270_, lean_object* v_m_3271_, lean_object* v_a_3272_, lean_object* v_fallback_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3271_, v_a_3272_, v_fallback_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object* v_00_u03b2_3275_, lean_object* v_m_3276_, lean_object* v_a_3277_, lean_object* v_fallback_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(v_00_u03b2_3275_, v_m_3276_, v_a_3277_, v_fallback_3278_);
lean_dec(v_fallback_3278_);
lean_dec_ref(v_a_3277_);
lean_dec_ref(v_m_3276_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object* v_00_u03b2_3280_, lean_object* v_m_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3281_, v_a_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object* v_00_u03b2_3284_, lean_object* v_m_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(v_00_u03b2_3284_, v_m_3285_, v_a_3286_);
lean_dec_ref(v_a_3286_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object* v_00_u03b2_3288_, lean_object* v_m_3289_, lean_object* v_a_3290_, lean_object* v_b_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_m_3289_, v_a_3290_, v_b_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object* v_00_u03b2_3293_, lean_object* v_m_3294_, lean_object* v_a_3295_, lean_object* v_b_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_m_3294_, v_a_3295_, v_b_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object* v_00_u03b2_3298_, lean_object* v_a_3299_, lean_object* v_fallback_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3299_, v_fallback_3300_, v_x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3303_, lean_object* v_a_3304_, lean_object* v_fallback_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(v_00_u03b2_3303_, v_a_3304_, v_fallback_3305_, v_x_3306_);
lean_dec(v_x_3306_);
lean_dec(v_fallback_3305_);
lean_dec_ref(v_a_3304_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object* v_00_u03b2_3308_, lean_object* v_a_3309_, lean_object* v_x_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3309_, v_x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3312_, lean_object* v_a_3313_, lean_object* v_x_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(v_00_u03b2_3312_, v_a_3313_, v_x_3314_);
lean_dec_ref(v_a_3313_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object* v_00_u03b2_3316_, lean_object* v_data_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_data_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object* v_00_u03b2_3319_, lean_object* v_a_3320_, lean_object* v_b_3321_, lean_object* v_x_3322_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_3320_, v_b_3321_, v_x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3324_, lean_object* v_i_3325_, lean_object* v_source_3326_, lean_object* v_target_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v_i_3325_, v_source_3326_, v_target_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object* v_00_u03b2_3329_, lean_object* v_x_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_x_3330_, v_x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object* v_id_3333_, lean_object* v_baseId_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v___x_3336_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3335_, v_id_3333_);
v___x_3337_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3335_, v_baseId_3334_);
v___x_3338_ = l_Lean_Lsp_instBEqRefIdent_beq(v___x_3337_, v___x_3336_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = lean_box(0);
v___x_3340_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3335_, v___x_3336_, v___x_3337_);
v___x_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3339_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
return v___x_3341_;
}
else
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
lean_dec_ref(v___x_3337_);
lean_dec_ref(v___x_3336_);
v___x_3342_ = lean_box(0);
v___x_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
lean_ctor_set(v___x_3343_, 1, v_a_3335_);
return v___x_3343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object* v_ci_3344_, lean_object* v_info_3345_, lean_object* v_x_3346_, lean_object* v___y_3347_){
_start:
{
if (lean_obj_tag(v_info_3345_) == 11)
{
lean_object* v_toCommandContextInfo_3348_; lean_object* v_i_3349_; lean_object* v_env_3350_; lean_object* v___x_3351_; lean_object* v_mainModule_3352_; lean_object* v_id_3353_; lean_object* v_baseId_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v_toCommandContextInfo_3348_ = lean_ctor_get(v_ci_3344_, 0);
v_i_3349_ = lean_ctor_get(v_info_3345_, 0);
lean_inc_ref(v_i_3349_);
lean_dec_ref_known(v_info_3345_, 1);
v_env_3350_ = lean_ctor_get(v_toCommandContextInfo_3348_, 0);
v___x_3351_ = l_Lean_Environment_header(v_env_3350_);
v_mainModule_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_mainModule_3352_);
lean_dec_ref(v___x_3351_);
v_id_3353_ = lean_ctor_get(v_i_3349_, 1);
lean_inc(v_id_3353_);
v_baseId_3354_ = lean_ctor_get(v_i_3349_, 2);
lean_inc(v_baseId_3354_);
lean_dec_ref(v_i_3349_);
v___x_3355_ = 1;
v___x_3356_ = l_Lean_Name_toString(v_mainModule_3352_, v___x_3355_);
v___x_3357_ = l_Lean_Name_toString(v_id_3353_, v___x_3355_);
lean_inc_ref(v___x_3356_);
v___x_3358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = l_Lean_Name_toString(v_baseId_3354_, v___x_3355_);
v___x_3360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3356_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v___x_3358_, v___x_3360_, v___y_3347_);
return v___x_3361_;
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec_ref(v_info_3345_);
v___x_3362_ = lean_box(0);
v___x_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
lean_ctor_set(v___x_3363_, 1, v___y_3347_);
return v___x_3363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object* v_ci_3364_, lean_object* v_info_3365_, lean_object* v_x_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(v_ci_3364_, v_info_3365_, v_x_3366_, v___y_3367_);
lean_dec_ref(v_x_3366_);
lean_dec_ref(v_ci_3364_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object* v_x_3369_, lean_object* v_x_3370_, lean_object* v_x_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = 1;
v___x_3374_ = lean_box(v___x_3373_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
lean_ctor_set(v___x_3375_, 1, v___y_3372_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object* v_x_3376_, lean_object* v_x_3377_, lean_object* v_x_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(v_x_3376_, v_x_3377_, v_x_3378_, v___y_3379_);
lean_dec_ref(v_x_3378_);
lean_dec_ref(v_x_3377_);
lean_dec_ref(v_x_3376_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3381_, lean_object* v_ci_3382_, lean_object* v_i_3383_, lean_object* v_cs_3384_, lean_object* v_x_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_apply_4(v_postNode_3381_, v_ci_3382_, v_i_3383_, v_cs_3384_, v___y_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3388_, lean_object* v_ci_3389_, lean_object* v_i_3390_, lean_object* v_cs_3391_, lean_object* v_x_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3388_, v_ci_3389_, v_i_3390_, v_cs_3391_, v_x_3392_, v___y_3393_);
lean_dec(v_x_3392_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v___f_3397_; lean_object* v___f_3398_; lean_object* v___f_3399_; lean_object* v___f_3400_; lean_object* v___f_3401_; lean_object* v___f_3402_; lean_object* v___f_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___f_3407_; lean_object* v___f_3408_; lean_object* v___f_3409_; lean_object* v___f_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3750__overap_3419_; lean_object* v___x_3420_; 
v___f_3397_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3398_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3399_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3400_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3401_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3402_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3403_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___f_3397_);
lean_ctor_set(v___x_3404_, 1, v___f_3398_);
v___x_3405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v___f_3399_);
lean_ctor_set(v___x_3405_, 2, v___f_3400_);
lean_ctor_set(v___x_3405_, 3, v___f_3401_);
lean_ctor_set(v___x_3405_, 4, v___f_3402_);
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v___f_3403_);
lean_inc_ref_n(v___x_3406_, 6);
v___f_3407_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3407_, 0, v___x_3406_);
v___f_3408_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3408_, 0, v___x_3406_);
v___f_3409_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3409_, 0, v___x_3406_);
v___f_3410_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3410_, 0, v___x_3406_);
v___x_3411_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3411_, 0, lean_box(0));
lean_closure_set(v___x_3411_, 1, lean_box(0));
lean_closure_set(v___x_3411_, 2, v___x_3406_);
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
lean_ctor_set(v___x_3412_, 1, v___f_3407_);
v___x_3413_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3413_, 0, lean_box(0));
lean_closure_set(v___x_3413_, 1, lean_box(0));
lean_closure_set(v___x_3413_, 2, v___x_3406_);
v___x_3414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3412_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
lean_ctor_set(v___x_3414_, 2, v___f_3408_);
lean_ctor_set(v___x_3414_, 3, v___f_3409_);
lean_ctor_set(v___x_3414_, 4, v___f_3410_);
v___x_3415_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3415_, 0, lean_box(0));
lean_closure_set(v___x_3415_, 1, lean_box(0));
lean_closure_set(v___x_3415_, 2, v___x_3406_);
v___x_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = lean_box(0);
v___x_3418_ = l_instInhabitedOfMonad___redArg(v___x_3416_, v___x_3417_);
v___x_3750__overap_3419_ = lean_panic_fn_borrowed(v___x_3418_, v_msg_3395_);
lean_dec(v___x_3418_);
v___x_3420_ = lean_apply_1(v___x_3750__overap_3419_, v___y_3396_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3421_, lean_object* v_postNode_3422_, lean_object* v_x_3423_, lean_object* v_x_3424_, lean_object* v___y_3425_){
_start:
{
switch(lean_obj_tag(v_x_3424_))
{
case 0:
{
lean_object* v_i_3426_; lean_object* v_t_3427_; lean_object* v___x_3428_; 
v_i_3426_ = lean_ctor_get(v_x_3424_, 0);
lean_inc_ref(v_i_3426_);
v_t_3427_ = lean_ctor_get(v_x_3424_, 1);
lean_inc_ref(v_t_3427_);
lean_dec_ref_known(v_x_3424_, 2);
v___x_3428_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3426_, v_x_3423_);
v_x_3423_ = v___x_3428_;
v_x_3424_ = v_t_3427_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3423_) == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec_ref_known(v_x_3424_, 2);
lean_dec_ref(v_postNode_3422_);
lean_dec_ref(v_preNode_3421_);
v___x_3430_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3431_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3430_, v___y_3425_);
return v___x_3431_;
}
else
{
lean_object* v_i_3432_; lean_object* v_children_3433_; lean_object* v_val_3434_; lean_object* v___x_3435_; lean_object* v_fst_3436_; uint8_t v___x_3437_; 
v_i_3432_ = lean_ctor_get(v_x_3424_, 0);
lean_inc_ref_n(v_i_3432_, 2);
v_children_3433_ = lean_ctor_get(v_x_3424_, 1);
lean_inc_ref_n(v_children_3433_, 2);
lean_dec_ref_known(v_x_3424_, 2);
v_val_3434_ = lean_ctor_get(v_x_3423_, 0);
lean_inc_n(v_val_3434_, 2);
lean_inc_ref(v_preNode_3421_);
v___x_3435_ = lean_apply_4(v_preNode_3421_, v_val_3434_, v_i_3432_, v_children_3433_, v___y_3425_);
v_fst_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_fst_3436_);
v___x_3437_ = lean_unbox(v_fst_3436_);
lean_dec(v_fst_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3456_; 
lean_dec_ref(v_preNode_3421_);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_x_3423_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; 
v_unused_3457_ = lean_ctor_get(v_x_3423_, 0);
lean_dec(v_unused_3457_);
v___x_3439_ = v_x_3423_;
v_isShared_3440_ = v_isSharedCheck_3456_;
goto v_resetjp_3438_;
}
else
{
lean_dec(v_x_3423_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3456_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v_snd_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v_fst_3444_; lean_object* v_snd_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3455_; 
v_snd_3441_ = lean_ctor_get(v___x_3435_, 1);
lean_inc(v_snd_3441_);
lean_dec_ref(v___x_3435_);
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_apply_5(v_postNode_3422_, v_val_3434_, v_i_3432_, v_children_3433_, v___x_3442_, v_snd_3441_);
v_fst_3444_ = lean_ctor_get(v___x_3443_, 0);
v_snd_3445_ = lean_ctor_get(v___x_3443_, 1);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3447_ = v___x_3443_;
v_isShared_3448_ = v_isSharedCheck_3455_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_snd_3445_);
lean_inc(v_fst_3444_);
lean_dec(v___x_3443_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3455_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v_fst_3444_);
v___x_3450_ = v___x_3439_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3444_);
v___x_3450_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3450_);
v___x_3452_ = v___x_3447_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_snd_3445_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
else
{
lean_object* v_snd_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v_fst_3463_; lean_object* v_snd_3464_; lean_object* v___x_3465_; lean_object* v_fst_3466_; lean_object* v_snd_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
v_snd_3458_ = lean_ctor_get(v___x_3435_, 1);
lean_inc(v_snd_3458_);
lean_dec_ref(v___x_3435_);
v___x_3459_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3423_, v_i_3432_);
v___x_3460_ = l_Lean_PersistentArray_toList___redArg(v_children_3433_);
v___x_3461_ = lean_box(0);
lean_inc_ref(v_postNode_3422_);
v___x_3462_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3421_, v_postNode_3422_, v___x_3459_, v___x_3460_, v___x_3461_, v_snd_3458_);
v_fst_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_fst_3463_);
v_snd_3464_ = lean_ctor_get(v___x_3462_, 1);
lean_inc(v_snd_3464_);
lean_dec_ref(v___x_3462_);
v___x_3465_ = lean_apply_5(v_postNode_3422_, v_val_3434_, v_i_3432_, v_children_3433_, v_fst_3463_, v_snd_3464_);
v_fst_3466_ = lean_ctor_get(v___x_3465_, 0);
v_snd_3467_ = lean_ctor_get(v___x_3465_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3469_ = v___x_3465_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_snd_3467_);
lean_inc(v_fst_3466_);
lean_dec(v___x_3465_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v_fst_3466_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_snd_3467_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
default: 
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_dec_ref_known(v_x_3424_, 1);
lean_dec(v_x_3423_);
lean_dec_ref(v_postNode_3422_);
lean_dec_ref(v_preNode_3421_);
v___x_3476_ = lean_box(0);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v___y_3425_);
return v___x_3477_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3478_, lean_object* v_postNode_3479_, lean_object* v___x_3480_, lean_object* v_x_3481_, lean_object* v_x_3482_, lean_object* v___y_3483_){
_start:
{
if (lean_obj_tag(v_x_3481_) == 0)
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
lean_dec(v___x_3480_);
lean_dec_ref(v_postNode_3479_);
lean_dec_ref(v_preNode_3478_);
v___x_3484_ = l_List_reverse___redArg(v_x_3482_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set(v___x_3485_, 1, v___y_3483_);
return v___x_3485_;
}
else
{
lean_object* v_head_3486_; lean_object* v_tail_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3498_; 
v_head_3486_ = lean_ctor_get(v_x_3481_, 0);
v_tail_3487_ = lean_ctor_get(v_x_3481_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_x_3481_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3489_ = v_x_3481_;
v_isShared_3490_ = v_isSharedCheck_3498_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_tail_3487_);
lean_inc(v_head_3486_);
lean_dec(v_x_3481_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3498_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v_fst_3492_; lean_object* v_snd_3493_; lean_object* v___x_3495_; 
lean_inc(v___x_3480_);
lean_inc_ref(v_postNode_3479_);
lean_inc_ref(v_preNode_3478_);
v___x_3491_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3478_, v_postNode_3479_, v___x_3480_, v_head_3486_, v___y_3483_);
v_fst_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_fst_3492_);
v_snd_3493_ = lean_ctor_get(v___x_3491_, 1);
lean_inc(v_snd_3493_);
lean_dec_ref(v___x_3491_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 1, v_x_3482_);
lean_ctor_set(v___x_3489_, 0, v_fst_3492_);
v___x_3495_ = v___x_3489_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_fst_3492_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_x_3482_);
v___x_3495_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
v_x_3481_ = v_tail_3487_;
v_x_3482_ = v___x_3495_;
v___y_3483_ = v_snd_3493_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3499_, lean_object* v_postNode_3500_, lean_object* v_ctx_x3f_3501_, lean_object* v_t_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v___f_3504_; lean_object* v___x_3505_; lean_object* v_snd_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3514_; 
v___f_3504_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3504_, 0, v_postNode_3500_);
v___x_3505_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3499_, v___f_3504_, v_ctx_x3f_3501_, v_t_3502_, v___y_3503_);
v_snd_3506_ = lean_ctor_get(v___x_3505_, 1);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3514_ == 0)
{
lean_object* v_unused_3515_; 
v_unused_3515_ = lean_ctor_get(v___x_3505_, 0);
lean_dec(v_unused_3515_);
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_snd_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3514_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
v___x_3510_ = lean_box(0);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3510_);
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_snd_3506_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(lean_object* v_as_3518_, size_t v_i_3519_, size_t v_stop_3520_, lean_object* v_b_3521_, lean_object* v___y_3522_){
_start:
{
uint8_t v___x_3523_; 
v___x_3523_ = lean_usize_dec_eq(v_i_3519_, v_stop_3520_);
if (v___x_3523_ == 0)
{
lean_object* v___f_3524_; lean_object* v___f_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v_fst_3529_; lean_object* v_snd_3530_; size_t v___x_3531_; size_t v___x_3532_; 
v___f_3524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0));
v___f_3525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1));
v___x_3526_ = lean_array_uget_borrowed(v_as_3518_, v_i_3519_);
v___x_3527_ = lean_box(0);
lean_inc(v___x_3526_);
v___x_3528_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(v___f_3524_, v___f_3525_, v___x_3527_, v___x_3526_, v___y_3522_);
v_fst_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_fst_3529_);
v_snd_3530_ = lean_ctor_get(v___x_3528_, 1);
lean_inc(v_snd_3530_);
lean_dec_ref(v___x_3528_);
v___x_3531_ = ((size_t)1ULL);
v___x_3532_ = lean_usize_add(v_i_3519_, v___x_3531_);
v_i_3519_ = v___x_3532_;
v_b_3521_ = v_fst_3529_;
v___y_3522_ = v_snd_3530_;
goto _start;
}
else
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v_b_3521_);
lean_ctor_set(v___x_3534_, 1, v___y_3522_);
return v___x_3534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___boxed(lean_object* v_as_3535_, lean_object* v_i_3536_, lean_object* v_stop_3537_, lean_object* v_b_3538_, lean_object* v___y_3539_){
_start:
{
size_t v_i_boxed_3540_; size_t v_stop_boxed_3541_; lean_object* v_res_3542_; 
v_i_boxed_3540_ = lean_unbox_usize(v_i_3536_);
lean_dec(v_i_3536_);
v_stop_boxed_3541_ = lean_unbox_usize(v_stop_3537_);
lean_dec(v_stop_3537_);
v_res_3542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_as_3535_, v_i_boxed_3540_, v_stop_boxed_3541_, v_b_3538_, v___y_3539_);
lean_dec_ref(v_as_3535_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(lean_object* v_a_3543_, lean_object* v_x_3544_){
_start:
{
if (lean_obj_tag(v_x_3544_) == 0)
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_box(0);
return v___x_3545_;
}
else
{
lean_object* v_key_3546_; lean_object* v_value_3547_; lean_object* v_tail_3548_; uint8_t v___x_3549_; 
v_key_3546_ = lean_ctor_get(v_x_3544_, 0);
v_value_3547_ = lean_ctor_get(v_x_3544_, 1);
v_tail_3548_ = lean_ctor_get(v_x_3544_, 2);
v___x_3549_ = l_Lean_Lsp_instBEqRange_beq(v_key_3546_, v_a_3543_);
if (v___x_3549_ == 0)
{
v_x_3544_ = v_tail_3548_;
goto _start;
}
else
{
lean_object* v___x_3551_; 
lean_inc(v_value_3547_);
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v_value_3547_);
return v___x_3551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_3552_, lean_object* v_x_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3552_, v_x_3553_);
lean_dec(v_x_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(lean_object* v_m_3555_, lean_object* v_a_3556_){
_start:
{
lean_object* v_buckets_3557_; lean_object* v___x_3558_; uint64_t v___x_3559_; uint64_t v___x_3560_; uint64_t v___x_3561_; uint64_t v_fold_3562_; uint64_t v___x_3563_; uint64_t v___x_3564_; uint64_t v___x_3565_; size_t v___x_3566_; size_t v___x_3567_; size_t v___x_3568_; size_t v___x_3569_; size_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v_buckets_3557_ = lean_ctor_get(v_m_3555_, 1);
v___x_3558_ = lean_array_get_size(v_buckets_3557_);
v___x_3559_ = l_Lean_Lsp_instHashableRange_hash(v_a_3556_);
v___x_3560_ = 32ULL;
v___x_3561_ = lean_uint64_shift_right(v___x_3559_, v___x_3560_);
v_fold_3562_ = lean_uint64_xor(v___x_3559_, v___x_3561_);
v___x_3563_ = 16ULL;
v___x_3564_ = lean_uint64_shift_right(v_fold_3562_, v___x_3563_);
v___x_3565_ = lean_uint64_xor(v_fold_3562_, v___x_3564_);
v___x_3566_ = lean_uint64_to_usize(v___x_3565_);
v___x_3567_ = lean_usize_of_nat(v___x_3558_);
v___x_3568_ = ((size_t)1ULL);
v___x_3569_ = lean_usize_sub(v___x_3567_, v___x_3568_);
v___x_3570_ = lean_usize_land(v___x_3566_, v___x_3569_);
v___x_3571_ = lean_array_uget_borrowed(v_buckets_3557_, v___x_3570_);
v___x_3572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3556_, v___x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg___boxed(lean_object* v_m_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3573_, v_a_3574_);
lean_dec_ref(v_a_3574_);
lean_dec_ref(v_m_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(lean_object* v_posMap_3576_, lean_object* v_as_3577_, size_t v_sz_3578_, size_t v_i_3579_, lean_object* v_b_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v_a_3583_; lean_object* v_snd_3584_; uint8_t v___x_3588_; 
v___x_3588_ = lean_usize_dec_lt(v_i_3579_, v_sz_3578_);
if (v___x_3588_ == 0)
{
lean_object* v___x_3589_; 
v___x_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3589_, 0, v_b_3580_);
lean_ctor_set(v___x_3589_, 1, v___y_3581_);
return v___x_3589_;
}
else
{
lean_object* v_a_3590_; lean_object* v_ident_3591_; lean_object* v_range_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v_a_3590_ = lean_array_uget_borrowed(v_as_3577_, v_i_3579_);
v_ident_3591_ = lean_ctor_get(v_a_3590_, 0);
v_range_3592_ = lean_ctor_get(v_a_3590_, 2);
v___x_3593_ = lean_box(0);
v___x_3594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_posMap_3576_, v_range_3592_);
if (lean_obj_tag(v___x_3594_) == 1)
{
lean_object* v_val_3595_; lean_object* v___x_3596_; lean_object* v_snd_3597_; 
v_val_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_val_3595_);
lean_dec_ref_known(v___x_3594_, 1);
lean_inc_ref(v_ident_3591_);
v___x_3596_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v_val_3595_, v_ident_3591_, v___y_3581_);
v_snd_3597_ = lean_ctor_get(v___x_3596_, 1);
lean_inc(v_snd_3597_);
lean_dec_ref(v___x_3596_);
v_a_3583_ = v___x_3593_;
v_snd_3584_ = v_snd_3597_;
goto v___jp_3582_;
}
else
{
lean_dec(v___x_3594_);
v_a_3583_ = v___x_3593_;
v_snd_3584_ = v___y_3581_;
goto v___jp_3582_;
}
}
v___jp_3582_:
{
size_t v___x_3585_; size_t v___x_3586_; 
v___x_3585_ = ((size_t)1ULL);
v___x_3586_ = lean_usize_add(v_i_3579_, v___x_3585_);
v_i_3579_ = v___x_3586_;
v_b_3580_ = v_a_3583_;
v___y_3581_ = v_snd_3584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2___boxed(lean_object* v_posMap_3598_, lean_object* v_as_3599_, lean_object* v_sz_3600_, lean_object* v_i_3601_, lean_object* v_b_3602_, lean_object* v___y_3603_){
_start:
{
size_t v_sz_boxed_3604_; size_t v_i_boxed_3605_; lean_object* v_res_3606_; 
v_sz_boxed_3604_ = lean_unbox_usize(v_sz_3600_);
lean_dec(v_sz_3600_);
v_i_boxed_3605_ = lean_unbox_usize(v_i_3601_);
lean_dec(v_i_3601_);
v_res_3606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3598_, v_as_3599_, v_sz_boxed_3604_, v_i_boxed_3605_, v_b_3602_, v___y_3603_);
lean_dec_ref(v_as_3599_);
lean_dec_ref(v_posMap_3598_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(lean_object* v_trees_3607_, lean_object* v_refs_3608_, lean_object* v_posMap_3609_){
_start:
{
lean_object* v___x_3610_; size_t v_sz_3611_; size_t v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v_snd_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3610_ = lean_box(0);
v_sz_3611_ = lean_array_size(v_refs_3608_);
v___x_3612_ = ((size_t)0ULL);
v___x_3613_ = lean_unsigned_to_nat(0u);
v___x_3614_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3609_, v_refs_3608_, v_sz_3611_, v___x_3612_, v___x_3610_, v___x_3614_);
v_snd_3616_ = lean_ctor_get(v___x_3615_, 1);
lean_inc(v_snd_3616_);
lean_dec_ref(v___x_3615_);
v___x_3617_ = lean_array_get_size(v_trees_3607_);
v___x_3618_ = lean_nat_dec_lt(v___x_3613_, v___x_3617_);
if (v___x_3618_ == 0)
{
return v_snd_3616_;
}
else
{
uint8_t v___x_3619_; 
v___x_3619_ = lean_nat_dec_le(v___x_3617_, v___x_3617_);
if (v___x_3619_ == 0)
{
if (v___x_3618_ == 0)
{
return v_snd_3616_;
}
else
{
size_t v___x_3620_; lean_object* v___x_3621_; lean_object* v_snd_3622_; 
v___x_3620_ = lean_usize_of_nat(v___x_3617_);
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3607_, v___x_3612_, v___x_3620_, v___x_3610_, v_snd_3616_);
v_snd_3622_ = lean_ctor_get(v___x_3621_, 1);
lean_inc(v_snd_3622_);
lean_dec_ref(v___x_3621_);
return v_snd_3622_;
}
}
else
{
size_t v___x_3623_; lean_object* v___x_3624_; lean_object* v_snd_3625_; 
v___x_3623_ = lean_usize_of_nat(v___x_3617_);
v___x_3624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3607_, v___x_3612_, v___x_3623_, v___x_3610_, v_snd_3616_);
v_snd_3625_ = lean_ctor_get(v___x_3624_, 1);
lean_inc(v_snd_3625_);
lean_dec_ref(v___x_3624_);
return v_snd_3625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap___boxed(lean_object* v_trees_3626_, lean_object* v_refs_3627_, lean_object* v_posMap_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3626_, v_refs_3627_, v_posMap_3628_);
lean_dec_ref(v_posMap_3628_);
lean_dec_ref(v_refs_3627_);
lean_dec_ref(v_trees_3626_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(lean_object* v_00_u03b2_3630_, lean_object* v_m_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3631_, v_a_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___boxed(lean_object* v_00_u03b2_3634_, lean_object* v_m_3635_, lean_object* v_a_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(v_00_u03b2_3634_, v_m_3635_, v_a_3636_);
lean_dec_ref(v_a_3636_);
lean_dec_ref(v_m_3635_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3638_, lean_object* v_msg_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v_msg_3639_, v___y_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object* v_00_u03b1_3642_, lean_object* v_preNode_3643_, lean_object* v_postNode_3644_, lean_object* v_x_3645_, lean_object* v_x_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3643_, v_postNode_3644_, v_x_3645_, v_x_3646_, v___y_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object* v_00_u03b2_3649_, lean_object* v_a_3650_, lean_object* v_x_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3650_, v_x_3651_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3653_, lean_object* v_a_3654_, lean_object* v_x_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(v_00_u03b2_3653_, v_a_3654_, v_x_3655_);
lean_dec(v_x_3655_);
lean_dec_ref(v_a_3654_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3657_, lean_object* v_preNode_3658_, lean_object* v_postNode_3659_, lean_object* v___x_3660_, lean_object* v_x_3661_, lean_object* v_x_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3658_, v_postNode_3659_, v___x_3660_, v_x_3661_, v_x_3662_, v___y_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(lean_object* v_a_3665_, lean_object* v_b_3666_, lean_object* v_x_3667_){
_start:
{
if (lean_obj_tag(v_x_3667_) == 0)
{
lean_dec(v_b_3666_);
lean_dec_ref(v_a_3665_);
return v_x_3667_;
}
else
{
lean_object* v_key_3668_; lean_object* v_value_3669_; lean_object* v_tail_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3682_; 
v_key_3668_ = lean_ctor_get(v_x_3667_, 0);
v_value_3669_ = lean_ctor_get(v_x_3667_, 1);
v_tail_3670_ = lean_ctor_get(v_x_3667_, 2);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_x_3667_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3672_ = v_x_3667_;
v_isShared_3673_ = v_isSharedCheck_3682_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_tail_3670_);
lean_inc(v_value_3669_);
lean_inc(v_key_3668_);
lean_dec(v_x_3667_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3682_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
uint8_t v___x_3674_; 
v___x_3674_ = l_Lean_Lsp_instBEqRange_beq(v_key_3668_, v_a_3665_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3675_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3665_, v_b_3666_, v_tail_3670_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 2, v___x_3675_);
v___x_3677_ = v___x_3672_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_key_3668_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_value_3669_);
lean_ctor_set(v_reuseFailAlloc_3678_, 2, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
else
{
lean_object* v___x_3680_; 
lean_dec(v_value_3669_);
lean_dec(v_key_3668_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 1, v_b_3666_);
lean_ctor_set(v___x_3672_, 0, v_a_3665_);
v___x_3680_ = v___x_3672_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3665_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v_b_3666_);
lean_ctor_set(v_reuseFailAlloc_3681_, 2, v_tail_3670_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_3683_, lean_object* v_x_3684_){
_start:
{
if (lean_obj_tag(v_x_3684_) == 0)
{
return v_x_3683_;
}
else
{
lean_object* v_key_3685_; lean_object* v_value_3686_; lean_object* v_tail_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3710_; 
v_key_3685_ = lean_ctor_get(v_x_3684_, 0);
v_value_3686_ = lean_ctor_get(v_x_3684_, 1);
v_tail_3687_ = lean_ctor_get(v_x_3684_, 2);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_x_3684_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3689_ = v_x_3684_;
v_isShared_3690_ = v_isSharedCheck_3710_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_tail_3687_);
lean_inc(v_value_3686_);
lean_inc(v_key_3685_);
lean_dec(v_x_3684_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3710_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; uint64_t v___x_3692_; uint64_t v___x_3693_; uint64_t v___x_3694_; uint64_t v_fold_3695_; uint64_t v___x_3696_; uint64_t v___x_3697_; uint64_t v___x_3698_; size_t v___x_3699_; size_t v___x_3700_; size_t v___x_3701_; size_t v___x_3702_; size_t v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3691_ = lean_array_get_size(v_x_3683_);
v___x_3692_ = l_Lean_Lsp_instHashableRange_hash(v_key_3685_);
v___x_3693_ = 32ULL;
v___x_3694_ = lean_uint64_shift_right(v___x_3692_, v___x_3693_);
v_fold_3695_ = lean_uint64_xor(v___x_3692_, v___x_3694_);
v___x_3696_ = 16ULL;
v___x_3697_ = lean_uint64_shift_right(v_fold_3695_, v___x_3696_);
v___x_3698_ = lean_uint64_xor(v_fold_3695_, v___x_3697_);
v___x_3699_ = lean_uint64_to_usize(v___x_3698_);
v___x_3700_ = lean_usize_of_nat(v___x_3691_);
v___x_3701_ = ((size_t)1ULL);
v___x_3702_ = lean_usize_sub(v___x_3700_, v___x_3701_);
v___x_3703_ = lean_usize_land(v___x_3699_, v___x_3702_);
v___x_3704_ = lean_array_uget_borrowed(v_x_3683_, v___x_3703_);
lean_inc(v___x_3704_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 2, v___x_3704_);
v___x_3706_ = v___x_3689_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_key_3685_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_value_3686_);
lean_ctor_set(v_reuseFailAlloc_3709_, 2, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; 
v___x_3707_ = lean_array_uset(v_x_3683_, v___x_3703_, v___x_3706_);
v_x_3683_ = v___x_3707_;
v_x_3684_ = v_tail_3687_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3711_, lean_object* v_source_3712_, lean_object* v_target_3713_){
_start:
{
lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3714_ = lean_array_get_size(v_source_3712_);
v___x_3715_ = lean_nat_dec_lt(v_i_3711_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_dec_ref(v_source_3712_);
lean_dec(v_i_3711_);
return v_target_3713_;
}
else
{
lean_object* v_es_3716_; lean_object* v___x_3717_; lean_object* v_source_3718_; lean_object* v_target_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_es_3716_ = lean_array_fget(v_source_3712_, v_i_3711_);
v___x_3717_ = lean_box(0);
v_source_3718_ = lean_array_fset(v_source_3712_, v_i_3711_, v___x_3717_);
v_target_3719_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3713_, v_es_3716_);
v___x_3720_ = lean_unsigned_to_nat(1u);
v___x_3721_ = lean_nat_add(v_i_3711_, v___x_3720_);
lean_dec(v_i_3711_);
v_i_3711_ = v___x_3721_;
v_source_3712_ = v_source_3718_;
v_target_3713_ = v_target_3719_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(lean_object* v_data_3723_){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v_nbuckets_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3724_ = lean_array_get_size(v_data_3723_);
v___x_3725_ = lean_unsigned_to_nat(2u);
v_nbuckets_3726_ = lean_nat_mul(v___x_3724_, v___x_3725_);
v___x_3727_ = lean_unsigned_to_nat(0u);
v___x_3728_ = lean_box(0);
v___x_3729_ = lean_mk_array(v_nbuckets_3726_, v___x_3728_);
v___x_3730_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v___x_3727_, v_data_3723_, v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object* v_a_3731_, lean_object* v_x_3732_){
_start:
{
if (lean_obj_tag(v_x_3732_) == 0)
{
uint8_t v___x_3733_; 
v___x_3733_ = 0;
return v___x_3733_;
}
else
{
lean_object* v_key_3734_; lean_object* v_tail_3735_; uint8_t v___x_3736_; 
v_key_3734_ = lean_ctor_get(v_x_3732_, 0);
v_tail_3735_ = lean_ctor_get(v_x_3732_, 2);
v___x_3736_ = l_Lean_Lsp_instBEqRange_beq(v_key_3734_, v_a_3731_);
if (v___x_3736_ == 0)
{
v_x_3732_ = v_tail_3735_;
goto _start;
}
else
{
return v___x_3736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object* v_a_3738_, lean_object* v_x_3739_){
_start:
{
uint8_t v_res_3740_; lean_object* v_r_3741_; 
v_res_3740_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3738_, v_x_3739_);
lean_dec(v_x_3739_);
lean_dec_ref(v_a_3738_);
v_r_3741_ = lean_box(v_res_3740_);
return v_r_3741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object* v_m_3742_, lean_object* v_a_3743_, lean_object* v_b_3744_){
_start:
{
lean_object* v_size_3745_; lean_object* v_buckets_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3789_; 
v_size_3745_ = lean_ctor_get(v_m_3742_, 0);
v_buckets_3746_ = lean_ctor_get(v_m_3742_, 1);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_m_3742_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3748_ = v_m_3742_;
v_isShared_3749_ = v_isSharedCheck_3789_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_buckets_3746_);
lean_inc(v_size_3745_);
lean_dec(v_m_3742_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3789_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; uint64_t v___x_3751_; uint64_t v___x_3752_; uint64_t v___x_3753_; uint64_t v_fold_3754_; uint64_t v___x_3755_; uint64_t v___x_3756_; uint64_t v___x_3757_; size_t v___x_3758_; size_t v___x_3759_; size_t v___x_3760_; size_t v___x_3761_; size_t v___x_3762_; lean_object* v_bkt_3763_; uint8_t v___x_3764_; 
v___x_3750_ = lean_array_get_size(v_buckets_3746_);
v___x_3751_ = l_Lean_Lsp_instHashableRange_hash(v_a_3743_);
v___x_3752_ = 32ULL;
v___x_3753_ = lean_uint64_shift_right(v___x_3751_, v___x_3752_);
v_fold_3754_ = lean_uint64_xor(v___x_3751_, v___x_3753_);
v___x_3755_ = 16ULL;
v___x_3756_ = lean_uint64_shift_right(v_fold_3754_, v___x_3755_);
v___x_3757_ = lean_uint64_xor(v_fold_3754_, v___x_3756_);
v___x_3758_ = lean_uint64_to_usize(v___x_3757_);
v___x_3759_ = lean_usize_of_nat(v___x_3750_);
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_sub(v___x_3759_, v___x_3760_);
v___x_3762_ = lean_usize_land(v___x_3758_, v___x_3761_);
v_bkt_3763_ = lean_array_uget_borrowed(v_buckets_3746_, v___x_3762_);
v___x_3764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3743_, v_bkt_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v_size_x27_3766_; lean_object* v___x_3767_; lean_object* v_buckets_x27_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; 
v___x_3765_ = lean_unsigned_to_nat(1u);
v_size_x27_3766_ = lean_nat_add(v_size_3745_, v___x_3765_);
lean_dec(v_size_3745_);
lean_inc(v_bkt_3763_);
v___x_3767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3767_, 0, v_a_3743_);
lean_ctor_set(v___x_3767_, 1, v_b_3744_);
lean_ctor_set(v___x_3767_, 2, v_bkt_3763_);
v_buckets_x27_3768_ = lean_array_uset(v_buckets_3746_, v___x_3762_, v___x_3767_);
v___x_3769_ = lean_unsigned_to_nat(4u);
v___x_3770_ = lean_nat_mul(v_size_x27_3766_, v___x_3769_);
v___x_3771_ = lean_unsigned_to_nat(3u);
v___x_3772_ = lean_nat_div(v___x_3770_, v___x_3771_);
lean_dec(v___x_3770_);
v___x_3773_ = lean_array_get_size(v_buckets_x27_3768_);
v___x_3774_ = lean_nat_dec_le(v___x_3772_, v___x_3773_);
lean_dec(v___x_3772_);
if (v___x_3774_ == 0)
{
lean_object* v_val_3775_; lean_object* v___x_3777_; 
v_val_3775_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_buckets_x27_3768_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 1, v_val_3775_);
lean_ctor_set(v___x_3748_, 0, v_size_x27_3766_);
v___x_3777_ = v___x_3748_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_size_x27_3766_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_val_3775_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
else
{
lean_object* v___x_3780_; 
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 1, v_buckets_x27_3768_);
lean_ctor_set(v___x_3748_, 0, v_size_x27_3766_);
v___x_3780_ = v___x_3748_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_size_x27_3766_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_buckets_x27_3768_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
else
{
lean_object* v___x_3782_; lean_object* v_buckets_x27_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3787_; 
lean_inc(v_bkt_3763_);
v___x_3782_ = lean_box(0);
v_buckets_x27_3783_ = lean_array_uset(v_buckets_3746_, v___x_3762_, v___x_3782_);
v___x_3784_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3743_, v_b_3744_, v_bkt_3763_);
v___x_3785_ = lean_array_uset(v_buckets_x27_3783_, v___x_3762_, v___x_3784_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 1, v___x_3785_);
v___x_3787_ = v___x_3748_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_size_3745_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object* v_as_3790_, size_t v_sz_3791_, size_t v_i_3792_, lean_object* v_b_3793_){
_start:
{
lean_object* v_a_3795_; uint8_t v___x_3799_; 
v___x_3799_ = lean_usize_dec_lt(v_i_3792_, v_sz_3791_);
if (v___x_3799_ == 0)
{
return v_b_3793_;
}
else
{
lean_object* v_a_3800_; uint8_t v_isBinder_3801_; 
v_a_3800_ = lean_array_uget_borrowed(v_as_3790_, v_i_3792_);
v_isBinder_3801_ = lean_ctor_get_uint8(v_a_3800_, sizeof(void*)*6);
if (v_isBinder_3801_ == 1)
{
lean_object* v_ident_3802_; lean_object* v_range_3803_; lean_object* v___x_3804_; 
v_ident_3802_ = lean_ctor_get(v_a_3800_, 0);
v_range_3803_ = lean_ctor_get(v_a_3800_, 2);
lean_inc_ref(v_ident_3802_);
lean_inc_ref(v_range_3803_);
v___x_3804_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_b_3793_, v_range_3803_, v_ident_3802_);
v_a_3795_ = v___x_3804_;
goto v___jp_3794_;
}
else
{
v_a_3795_ = v_b_3793_;
goto v___jp_3794_;
}
}
v___jp_3794_:
{
size_t v___x_3796_; size_t v___x_3797_; 
v___x_3796_ = ((size_t)1ULL);
v___x_3797_ = lean_usize_add(v_i_3792_, v___x_3796_);
v_i_3792_ = v___x_3797_;
v_b_3793_ = v_a_3795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object* v_as_3805_, lean_object* v_sz_3806_, lean_object* v_i_3807_, lean_object* v_b_3808_){
_start:
{
size_t v_sz_boxed_3809_; size_t v_i_boxed_3810_; lean_object* v_res_3811_; 
v_sz_boxed_3809_ = lean_unbox_usize(v_sz_3806_);
lean_dec(v_sz_3806_);
v_i_boxed_3810_ = lean_unbox_usize(v_i_3807_);
lean_dec(v_i_3807_);
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_as_3805_, v_sz_boxed_3809_, v_i_boxed_3810_, v_b_3808_);
lean_dec_ref(v_as_3805_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object* v___x_3812_, lean_object* v_as_3813_, size_t v_sz_3814_, size_t v_i_3815_, lean_object* v_b_3816_){
_start:
{
lean_object* v_a_3818_; uint8_t v___x_3822_; 
v___x_3822_ = lean_usize_dec_lt(v_i_3815_, v_sz_3814_);
if (v___x_3822_ == 0)
{
return v_b_3816_;
}
else
{
lean_object* v_a_3823_; lean_object* v_ident_3826_; lean_object* v_range_3827_; lean_object* v_stx_3828_; lean_object* v_ci_3829_; lean_object* v_info_3830_; uint8_t v_isBinder_3831_; uint8_t v___x_3832_; 
v_a_3823_ = lean_array_uget(v_as_3813_, v_i_3815_);
v_ident_3826_ = lean_ctor_get(v_a_3823_, 0);
v_range_3827_ = lean_ctor_get(v_a_3823_, 2);
v_stx_3828_ = lean_ctor_get(v_a_3823_, 3);
v_ci_3829_ = lean_ctor_get(v_a_3823_, 4);
v_info_3830_ = lean_ctor_get(v_a_3823_, 5);
v_isBinder_3831_ = lean_ctor_get_uint8(v_a_3823_, sizeof(void*)*6);
v___x_3832_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v___x_3812_, v_ident_3826_);
if (v___x_3832_ == 0)
{
if (v___x_3832_ == 0)
{
goto v___jp_3824_;
}
else
{
if (v___x_3832_ == 0)
{
lean_dec(v_a_3823_);
v_a_3818_ = v_b_3816_;
goto v___jp_3817_;
}
else
{
goto v___jp_3824_;
}
}
}
else
{
lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3844_; 
lean_inc_ref(v_info_3830_);
lean_inc_ref(v_ci_3829_);
lean_inc(v_stx_3828_);
lean_inc_ref(v_range_3827_);
lean_inc_ref(v_ident_3826_);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_a_3823_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; lean_object* v_unused_3846_; lean_object* v_unused_3847_; lean_object* v_unused_3848_; lean_object* v_unused_3849_; lean_object* v_unused_3850_; 
v_unused_3845_ = lean_ctor_get(v_a_3823_, 5);
lean_dec(v_unused_3845_);
v_unused_3846_ = lean_ctor_get(v_a_3823_, 4);
lean_dec(v_unused_3846_);
v_unused_3847_ = lean_ctor_get(v_a_3823_, 3);
lean_dec(v_unused_3847_);
v_unused_3848_ = lean_ctor_get(v_a_3823_, 2);
lean_dec(v_unused_3848_);
v_unused_3849_ = lean_ctor_get(v_a_3823_, 1);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_a_3823_, 0);
lean_dec(v_unused_3850_);
v___x_3834_ = v_a_3823_;
v_isShared_3835_ = v_isSharedCheck_3844_;
goto v_resetjp_3833_;
}
else
{
lean_dec(v_a_3823_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3844_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3841_; 
lean_inc_ref(v_ident_3826_);
v___x_3836_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v___x_3812_, v_ident_3826_);
v___x_3837_ = lean_unsigned_to_nat(1u);
v___x_3838_ = lean_mk_empty_array_with_capacity(v___x_3837_);
v___x_3839_ = lean_array_push(v___x_3838_, v_ident_3826_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 1, v___x_3839_);
lean_ctor_set(v___x_3834_, 0, v___x_3836_);
v___x_3841_ = v___x_3834_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v___x_3839_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v_range_3827_);
lean_ctor_set(v_reuseFailAlloc_3843_, 3, v_stx_3828_);
lean_ctor_set(v_reuseFailAlloc_3843_, 4, v_ci_3829_);
lean_ctor_set(v_reuseFailAlloc_3843_, 5, v_info_3830_);
lean_ctor_set_uint8(v_reuseFailAlloc_3843_, sizeof(void*)*6, v_isBinder_3831_);
v___x_3841_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_array_push(v_b_3816_, v___x_3841_);
v_a_3818_ = v___x_3842_;
goto v___jp_3817_;
}
}
}
v___jp_3824_:
{
lean_object* v___x_3825_; 
v___x_3825_ = lean_array_push(v_b_3816_, v_a_3823_);
v_a_3818_ = v___x_3825_;
goto v___jp_3817_;
}
}
v___jp_3817_:
{
size_t v___x_3819_; size_t v___x_3820_; 
v___x_3819_ = ((size_t)1ULL);
v___x_3820_ = lean_usize_add(v_i_3815_, v___x_3819_);
v_i_3815_ = v___x_3820_;
v_b_3816_ = v_a_3818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object* v___x_3851_, lean_object* v_as_3852_, lean_object* v_sz_3853_, lean_object* v_i_3854_, lean_object* v_b_3855_){
_start:
{
size_t v_sz_boxed_3856_; size_t v_i_boxed_3857_; lean_object* v_res_3858_; 
v_sz_boxed_3856_ = lean_unbox_usize(v_sz_3853_);
lean_dec(v_sz_3853_);
v_i_boxed_3857_ = lean_unbox_usize(v_i_3854_);
lean_dec(v_i_3854_);
v_res_3858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3851_, v_as_3852_, v_sz_boxed_3856_, v_i_boxed_3857_, v_b_3855_);
lean_dec_ref(v_as_3852_);
lean_dec_ref(v___x_3851_);
return v_res_3858_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__0(void){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = lean_box(0);
v___x_3860_ = lean_unsigned_to_nat(16u);
v___x_3861_ = lean_mk_array(v___x_3860_, v___x_3859_);
return v___x_3861_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__1(void){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v_posMap_3864_; 
v___x_3862_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__0, &l_Lean_Server_combineIdents___closed__0_once, _init_l_Lean_Server_combineIdents___closed__0);
v___x_3863_ = lean_unsigned_to_nat(0u);
v_posMap_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_posMap_3864_, 0, v___x_3863_);
lean_ctor_set(v_posMap_3864_, 1, v___x_3862_);
return v_posMap_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object* v_trees_3865_, lean_object* v_refs_3866_){
_start:
{
lean_object* v_posMap_3867_; size_t v_sz_3868_; size_t v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v_posMap_3867_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__1, &l_Lean_Server_combineIdents___closed__1_once, _init_l_Lean_Server_combineIdents___closed__1);
v_sz_3868_ = lean_array_size(v_refs_3866_);
v___x_3869_ = ((size_t)0ULL);
v___x_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_refs_3866_, v_sz_3868_, v___x_3869_, v_posMap_3867_);
v___x_3871_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3865_, v_refs_3866_, v___x_3870_);
lean_dec_ref(v___x_3870_);
v___x_3872_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v___x_3871_);
lean_dec_ref(v___x_3871_);
v___x_3873_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_3874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3872_, v_refs_3866_, v_sz_3868_, v___x_3869_, v___x_3873_);
lean_dec_ref(v___x_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object* v_trees_3875_, lean_object* v_refs_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_Server_combineIdents(v_trees_3875_, v_refs_3876_);
lean_dec_ref(v_refs_3876_);
lean_dec_ref(v_trees_3875_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object* v_00_u03b2_3878_, lean_object* v_m_3879_, lean_object* v_a_3880_, lean_object* v_b_3881_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_m_3879_, v_a_3880_, v_b_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object* v_00_u03b2_3883_, lean_object* v_a_3884_, lean_object* v_x_3885_){
_start:
{
uint8_t v___x_3886_; 
v___x_3886_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3884_, v_x_3885_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3887_, lean_object* v_a_3888_, lean_object* v_x_3889_){
_start:
{
uint8_t v_res_3890_; lean_object* v_r_3891_; 
v_res_3890_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(v_00_u03b2_3887_, v_a_3888_, v_x_3889_);
lean_dec(v_x_3889_);
lean_dec_ref(v_a_3888_);
v_r_3891_ = lean_box(v_res_3890_);
return v_r_3891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object* v_00_u03b2_3892_, lean_object* v_data_3893_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_data_3893_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object* v_00_u03b2_3895_, lean_object* v_a_3896_, lean_object* v_b_3897_, lean_object* v_x_3898_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3896_, v_b_3897_, v_x_3898_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3900_, lean_object* v_i_3901_, lean_object* v_source_3902_, lean_object* v_target_3903_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v_i_3901_, v_source_3902_, v_target_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3905_, lean_object* v_x_3906_, lean_object* v_x_3907_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3906_, v_x_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object* v_hi_3909_, lean_object* v_pivot_3910_, lean_object* v_as_3911_, lean_object* v_i_3912_, lean_object* v_k_3913_){
_start:
{
uint8_t v___x_3918_; 
v___x_3918_ = lean_nat_dec_lt(v_k_3913_, v_hi_3909_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec(v_k_3913_);
v___x_3919_ = lean_array_fswap(v_as_3911_, v_i_3912_, v_hi_3909_);
v___x_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3920_, 0, v_i_3912_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
return v___x_3920_;
}
else
{
lean_object* v___x_3921_; lean_object* v_range_3922_; lean_object* v_range_3923_; uint8_t v___x_3924_; 
v___x_3921_ = lean_array_fget_borrowed(v_as_3911_, v_k_3913_);
v_range_3922_ = lean_ctor_get(v___x_3921_, 2);
v_range_3923_ = lean_ctor_get(v_pivot_3910_, 2);
v___x_3924_ = l_Lean_Lsp_instOrdRange_ord(v_range_3922_, v_range_3923_);
if (v___x_3924_ == 0)
{
if (v___x_3918_ == 0)
{
goto v___jp_3914_;
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3925_ = lean_array_fswap(v_as_3911_, v_i_3912_, v_k_3913_);
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = lean_nat_add(v_i_3912_, v___x_3926_);
lean_dec(v_i_3912_);
v___x_3928_ = lean_nat_add(v_k_3913_, v___x_3926_);
lean_dec(v_k_3913_);
v_as_3911_ = v___x_3925_;
v_i_3912_ = v___x_3927_;
v_k_3913_ = v___x_3928_;
goto _start;
}
}
else
{
goto v___jp_3914_;
}
}
v___jp_3914_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_unsigned_to_nat(1u);
v___x_3916_ = lean_nat_add(v_k_3913_, v___x_3915_);
lean_dec(v_k_3913_);
v_k_3913_ = v___x_3916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object* v_hi_3930_, lean_object* v_pivot_3931_, lean_object* v_as_3932_, lean_object* v_i_3933_, lean_object* v_k_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3930_, v_pivot_3931_, v_as_3932_, v_i_3933_, v_k_3934_);
lean_dec_ref(v_pivot_3931_);
lean_dec(v_hi_3930_);
return v_res_3935_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3936_, lean_object* v_x1_3937_, lean_object* v_x2_3938_){
_start:
{
lean_object* v_range_3939_; lean_object* v_range_3940_; uint8_t v___x_3941_; 
v_range_3939_ = lean_ctor_get(v_x1_3937_, 2);
v_range_3940_ = lean_ctor_get(v_x2_3938_, 2);
v___x_3941_ = l_Lean_Lsp_instOrdRange_ord(v_range_3939_, v_range_3940_);
if (v___x_3941_ == 0)
{
return v___x_3936_;
}
else
{
uint8_t v___x_3942_; 
v___x_3942_ = 0;
return v___x_3942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3943_, lean_object* v_x1_3944_, lean_object* v_x2_3945_){
_start:
{
uint8_t v___x_2117__boxed_3946_; uint8_t v_res_3947_; lean_object* v_r_3948_; 
v___x_2117__boxed_3946_ = lean_unbox(v___x_3943_);
v_res_3947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_2117__boxed_3946_, v_x1_3944_, v_x2_3945_);
lean_dec_ref(v_x2_3945_);
lean_dec_ref(v_x1_3944_);
v_r_3948_ = lean_box(v_res_3947_);
return v_r_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_n_3949_, lean_object* v_as_3950_, lean_object* v_lo_3951_, lean_object* v_hi_3952_){
_start:
{
lean_object* v___y_3954_; uint8_t v___x_3964_; 
v___x_3964_ = lean_nat_dec_lt(v_lo_3951_, v_hi_3952_);
if (v___x_3964_ == 0)
{
lean_dec(v_lo_3951_);
return v_as_3950_;
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v_mid_3967_; lean_object* v___y_3969_; lean_object* v___y_3975_; lean_object* v___x_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v___x_3965_ = lean_nat_add(v_lo_3951_, v_hi_3952_);
v___x_3966_ = lean_unsigned_to_nat(1u);
v_mid_3967_ = lean_nat_shiftr(v___x_3965_, v___x_3966_);
lean_dec(v___x_3965_);
v___x_3980_ = lean_array_fget_borrowed(v_as_3950_, v_mid_3967_);
v___x_3981_ = lean_array_fget_borrowed(v_as_3950_, v_lo_3951_);
v___x_3982_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3964_, v___x_3980_, v___x_3981_);
if (v___x_3982_ == 0)
{
v___y_3975_ = v_as_3950_;
goto v___jp_3974_;
}
else
{
lean_object* v___x_3983_; 
v___x_3983_ = lean_array_fswap(v_as_3950_, v_lo_3951_, v_mid_3967_);
v___y_3975_ = v___x_3983_;
goto v___jp_3974_;
}
v___jp_3968_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3970_ = lean_array_fget_borrowed(v___y_3969_, v_mid_3967_);
v___x_3971_ = lean_array_fget_borrowed(v___y_3969_, v_hi_3952_);
v___x_3972_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3964_, v___x_3970_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_dec(v_mid_3967_);
v___y_3954_ = v___y_3969_;
goto v___jp_3953_;
}
else
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_array_fswap(v___y_3969_, v_mid_3967_, v_hi_3952_);
lean_dec(v_mid_3967_);
v___y_3954_ = v___x_3973_;
goto v___jp_3953_;
}
}
v___jp_3974_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3976_ = lean_array_fget_borrowed(v___y_3975_, v_hi_3952_);
v___x_3977_ = lean_array_fget_borrowed(v___y_3975_, v_lo_3951_);
v___x_3978_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3964_, v___x_3976_, v___x_3977_);
if (v___x_3978_ == 0)
{
v___y_3969_ = v___y_3975_;
goto v___jp_3968_;
}
else
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_array_fswap(v___y_3975_, v_lo_3951_, v_hi_3952_);
v___y_3969_ = v___x_3979_;
goto v___jp_3968_;
}
}
}
v___jp_3953_:
{
lean_object* v_pivot_3955_; lean_object* v___x_3956_; lean_object* v_fst_3957_; lean_object* v_snd_3958_; uint8_t v___x_3959_; 
v_pivot_3955_ = lean_array_fget(v___y_3954_, v_hi_3952_);
lean_inc_n(v_lo_3951_, 2);
v___x_3956_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3952_, v_pivot_3955_, v___y_3954_, v_lo_3951_, v_lo_3951_);
lean_dec(v_pivot_3955_);
v_fst_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_fst_3957_);
v_snd_3958_ = lean_ctor_get(v___x_3956_, 1);
lean_inc(v_snd_3958_);
lean_dec_ref(v___x_3956_);
v___x_3959_ = lean_nat_dec_le(v_hi_3952_, v_fst_3957_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3949_, v_snd_3958_, v_lo_3951_, v_fst_3957_);
v___x_3961_ = lean_unsigned_to_nat(1u);
v___x_3962_ = lean_nat_add(v_fst_3957_, v___x_3961_);
lean_dec(v_fst_3957_);
v_as_3950_ = v___x_3960_;
v_lo_3951_ = v___x_3962_;
goto _start;
}
else
{
lean_dec(v_fst_3957_);
lean_dec(v_lo_3951_);
return v_snd_3958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_n_3984_, lean_object* v_as_3985_, lean_object* v_lo_3986_, lean_object* v_hi_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3984_, v_as_3985_, v_lo_3986_, v_hi_3987_);
lean_dec(v_hi_3987_);
lean_dec(v_n_3984_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object* v_x_3989_, lean_object* v_x_3990_){
_start:
{
if (lean_obj_tag(v_x_3990_) == 0)
{
return v_x_3989_;
}
else
{
lean_object* v_key_3991_; lean_object* v_snd_3992_; lean_object* v_value_3993_; lean_object* v_tail_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4034_; 
v_key_3991_ = lean_ctor_get(v_x_3990_, 0);
lean_inc(v_key_3991_);
v_snd_3992_ = lean_ctor_get(v_key_3991_, 1);
v_value_3993_ = lean_ctor_get(v_x_3990_, 1);
v_tail_3994_ = lean_ctor_get(v_x_3990_, 2);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_x_3990_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; 
v_unused_4035_ = lean_ctor_get(v_x_3990_, 0);
lean_dec(v_unused_4035_);
v___x_3996_ = v_x_3990_;
v_isShared_3997_ = v_isSharedCheck_4034_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_tail_3994_);
lean_inc(v_value_3993_);
lean_dec(v_x_3990_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4034_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v_fst_3998_; lean_object* v_fst_3999_; lean_object* v_snd_4000_; lean_object* v___x_4001_; uint64_t v___x_4002_; uint64_t v___y_4004_; uint64_t v___y_4026_; 
v_fst_3998_ = lean_ctor_get(v_key_3991_, 0);
v_fst_3999_ = lean_ctor_get(v_snd_3992_, 0);
v_snd_4000_ = lean_ctor_get(v_snd_3992_, 1);
v___x_4001_ = lean_array_get_size(v_x_3989_);
v___x_4002_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_3998_);
if (lean_obj_tag(v_fst_3999_) == 0)
{
uint64_t v___x_4029_; 
v___x_4029_ = 11ULL;
v___y_4004_ = v___x_4029_;
goto v___jp_4003_;
}
else
{
lean_object* v_val_4030_; uint8_t v___x_4031_; 
v_val_4030_ = lean_ctor_get(v_fst_3999_, 0);
v___x_4031_ = lean_unbox(v_val_4030_);
if (v___x_4031_ == 0)
{
uint64_t v___x_4032_; 
v___x_4032_ = 13ULL;
v___y_4026_ = v___x_4032_;
goto v___jp_4025_;
}
else
{
uint64_t v___x_4033_; 
v___x_4033_ = 11ULL;
v___y_4026_ = v___x_4033_;
goto v___jp_4025_;
}
}
v___jp_4003_:
{
uint64_t v___x_4005_; uint64_t v___x_4006_; uint64_t v___x_4007_; uint64_t v___x_4008_; uint64_t v___x_4009_; uint64_t v_fold_4010_; uint64_t v___x_4011_; uint64_t v___x_4012_; uint64_t v___x_4013_; size_t v___x_4014_; size_t v___x_4015_; size_t v___x_4016_; size_t v___x_4017_; size_t v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4005_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4000_);
v___x_4006_ = lean_uint64_mix_hash(v___y_4004_, v___x_4005_);
v___x_4007_ = lean_uint64_mix_hash(v___x_4002_, v___x_4006_);
v___x_4008_ = 32ULL;
v___x_4009_ = lean_uint64_shift_right(v___x_4007_, v___x_4008_);
v_fold_4010_ = lean_uint64_xor(v___x_4007_, v___x_4009_);
v___x_4011_ = 16ULL;
v___x_4012_ = lean_uint64_shift_right(v_fold_4010_, v___x_4011_);
v___x_4013_ = lean_uint64_xor(v_fold_4010_, v___x_4012_);
v___x_4014_ = lean_uint64_to_usize(v___x_4013_);
v___x_4015_ = lean_usize_of_nat(v___x_4001_);
v___x_4016_ = ((size_t)1ULL);
v___x_4017_ = lean_usize_sub(v___x_4015_, v___x_4016_);
v___x_4018_ = lean_usize_land(v___x_4014_, v___x_4017_);
v___x_4019_ = lean_array_uget_borrowed(v_x_3989_, v___x_4018_);
lean_inc(v___x_4019_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 2, v___x_4019_);
v___x_4021_ = v___x_3996_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_key_3991_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_value_3993_);
lean_ctor_set(v_reuseFailAlloc_4024_, 2, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
lean_object* v___x_4022_; 
v___x_4022_ = lean_array_uset(v_x_3989_, v___x_4018_, v___x_4021_);
v_x_3989_ = v___x_4022_;
v_x_3990_ = v_tail_3994_;
goto _start;
}
}
v___jp_4025_:
{
uint64_t v___x_4027_; uint64_t v___x_4028_; 
v___x_4027_ = 13ULL;
v___x_4028_ = lean_uint64_mix_hash(v___y_4026_, v___x_4027_);
v___y_4004_ = v___x_4028_;
goto v___jp_4003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object* v_i_4036_, lean_object* v_source_4037_, lean_object* v_target_4038_){
_start:
{
lean_object* v___x_4039_; uint8_t v___x_4040_; 
v___x_4039_ = lean_array_get_size(v_source_4037_);
v___x_4040_ = lean_nat_dec_lt(v_i_4036_, v___x_4039_);
if (v___x_4040_ == 0)
{
lean_dec_ref(v_source_4037_);
lean_dec(v_i_4036_);
return v_target_4038_;
}
else
{
lean_object* v_es_4041_; lean_object* v___x_4042_; lean_object* v_source_4043_; lean_object* v_target_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v_es_4041_ = lean_array_fget(v_source_4037_, v_i_4036_);
v___x_4042_ = lean_box(0);
v_source_4043_ = lean_array_fset(v_source_4037_, v_i_4036_, v___x_4042_);
v_target_4044_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_target_4038_, v_es_4041_);
v___x_4045_ = lean_unsigned_to_nat(1u);
v___x_4046_ = lean_nat_add(v_i_4036_, v___x_4045_);
lean_dec(v_i_4036_);
v_i_4036_ = v___x_4046_;
v_source_4037_ = v_source_4043_;
v_target_4038_ = v_target_4044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object* v_data_4048_){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v_nbuckets_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4049_ = lean_array_get_size(v_data_4048_);
v___x_4050_ = lean_unsigned_to_nat(2u);
v_nbuckets_4051_ = lean_nat_mul(v___x_4049_, v___x_4050_);
v___x_4052_ = lean_unsigned_to_nat(0u);
v___x_4053_ = lean_box(0);
v___x_4054_ = lean_mk_array(v_nbuckets_4051_, v___x_4053_);
v___x_4055_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v___x_4052_, v_data_4048_, v___x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object* v_x_4056_, lean_object* v_x_4057_){
_start:
{
if (lean_obj_tag(v_x_4056_) == 0)
{
if (lean_obj_tag(v_x_4057_) == 0)
{
uint8_t v___x_4058_; 
v___x_4058_ = 1;
return v___x_4058_;
}
else
{
uint8_t v___x_4059_; 
v___x_4059_ = 0;
return v___x_4059_;
}
}
else
{
if (lean_obj_tag(v_x_4057_) == 0)
{
uint8_t v___x_4060_; 
v___x_4060_ = 0;
return v___x_4060_;
}
else
{
lean_object* v_val_4061_; uint8_t v___x_4062_; 
v_val_4061_ = lean_ctor_get(v_x_4057_, 0);
v___x_4062_ = lean_unbox(v_val_4061_);
if (v___x_4062_ == 0)
{
lean_object* v_val_4063_; uint8_t v___x_4064_; 
v_val_4063_ = lean_ctor_get(v_x_4056_, 0);
v___x_4064_ = lean_unbox(v_val_4063_);
if (v___x_4064_ == 0)
{
uint8_t v___x_4065_; 
v___x_4065_ = 1;
return v___x_4065_;
}
else
{
uint8_t v___x_4066_; 
v___x_4066_ = lean_unbox(v_val_4061_);
return v___x_4066_;
}
}
else
{
lean_object* v_val_4067_; uint8_t v___x_4068_; 
v_val_4067_ = lean_ctor_get(v_x_4056_, 0);
v___x_4068_ = lean_unbox(v_val_4067_);
return v___x_4068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object* v_x_4069_, lean_object* v_x_4070_){
_start:
{
uint8_t v_res_4071_; lean_object* v_r_4072_; 
v_res_4071_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_x_4069_, v_x_4070_);
lean_dec(v_x_4070_);
lean_dec(v_x_4069_);
v_r_4072_ = lean_box(v_res_4071_);
return v_r_4072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object* v_a_4073_, lean_object* v_x_4074_){
_start:
{
if (lean_obj_tag(v_x_4074_) == 0)
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_a_4073_);
return v___x_4075_;
}
else
{
lean_object* v_val_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4104_; 
v_val_4076_ = lean_ctor_get(v_x_4074_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_x_4074_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4078_ = v_x_4074_;
v_isShared_4079_ = v_isSharedCheck_4104_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_val_4076_);
lean_dec(v_x_4074_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4104_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v_ident_4080_; lean_object* v_aliases_4081_; lean_object* v_range_4082_; lean_object* v_stx_4083_; lean_object* v_ci_4084_; lean_object* v_info_4085_; uint8_t v_isBinder_4086_; lean_object* v_aliases_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4098_; 
v_ident_4080_ = lean_ctor_get(v_val_4076_, 0);
lean_inc_ref(v_ident_4080_);
v_aliases_4081_ = lean_ctor_get(v_val_4076_, 1);
lean_inc_ref(v_aliases_4081_);
v_range_4082_ = lean_ctor_get(v_val_4076_, 2);
lean_inc_ref(v_range_4082_);
v_stx_4083_ = lean_ctor_get(v_val_4076_, 3);
lean_inc(v_stx_4083_);
v_ci_4084_ = lean_ctor_get(v_val_4076_, 4);
lean_inc_ref(v_ci_4084_);
v_info_4085_ = lean_ctor_get(v_val_4076_, 5);
lean_inc_ref(v_info_4085_);
v_isBinder_4086_ = lean_ctor_get_uint8(v_val_4076_, sizeof(void*)*6);
lean_dec(v_val_4076_);
v_aliases_4087_ = lean_ctor_get(v_a_4073_, 1);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_a_4073_);
if (v_isSharedCheck_4098_ == 0)
{
lean_object* v_unused_4099_; lean_object* v_unused_4100_; lean_object* v_unused_4101_; lean_object* v_unused_4102_; lean_object* v_unused_4103_; 
v_unused_4099_ = lean_ctor_get(v_a_4073_, 5);
lean_dec(v_unused_4099_);
v_unused_4100_ = lean_ctor_get(v_a_4073_, 4);
lean_dec(v_unused_4100_);
v_unused_4101_ = lean_ctor_get(v_a_4073_, 3);
lean_dec(v_unused_4101_);
v_unused_4102_ = lean_ctor_get(v_a_4073_, 2);
lean_dec(v_unused_4102_);
v_unused_4103_ = lean_ctor_get(v_a_4073_, 0);
lean_dec(v_unused_4103_);
v___x_4089_ = v_a_4073_;
v_isShared_4090_ = v_isSharedCheck_4098_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_aliases_4087_);
lean_dec(v_a_4073_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4098_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4091_ = l_Array_append___redArg(v_aliases_4081_, v_aliases_4087_);
lean_dec_ref(v_aliases_4087_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 5, v_info_4085_);
lean_ctor_set(v___x_4089_, 4, v_ci_4084_);
lean_ctor_set(v___x_4089_, 3, v_stx_4083_);
lean_ctor_set(v___x_4089_, 2, v_range_4082_);
lean_ctor_set(v___x_4089_, 1, v___x_4091_);
lean_ctor_set(v___x_4089_, 0, v_ident_4080_);
v___x_4093_ = v___x_4089_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_ident_4080_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v___x_4091_);
lean_ctor_set(v_reuseFailAlloc_4097_, 2, v_range_4082_);
lean_ctor_set(v_reuseFailAlloc_4097_, 3, v_stx_4083_);
lean_ctor_set(v_reuseFailAlloc_4097_, 4, v_ci_4084_);
lean_ctor_set(v_reuseFailAlloc_4097_, 5, v_info_4085_);
v___x_4093_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4095_; 
lean_ctor_set_uint8(v___x_4093_, sizeof(void*)*6, v_isBinder_4086_);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 0, v___x_4093_);
v___x_4095_ = v___x_4078_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_x_4107_){
_start:
{
if (lean_obj_tag(v_x_4107_) == 0)
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v_val_4110_; lean_object* v___x_4111_; 
v___x_4108_ = lean_box(0);
v___x_4109_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4105_, v___x_4108_);
v_val_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_val_4110_);
lean_dec(v___x_4109_);
v___x_4111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4111_, 0, v_a_4106_);
lean_ctor_set(v___x_4111_, 1, v_val_4110_);
lean_ctor_set(v___x_4111_, 2, v_x_4107_);
return v___x_4111_;
}
else
{
lean_object* v_key_4112_; lean_object* v_value_4113_; lean_object* v_tail_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4141_; 
v_key_4112_ = lean_ctor_get(v_x_4107_, 0);
v_value_4113_ = lean_ctor_get(v_x_4107_, 1);
v_tail_4114_ = lean_ctor_get(v_x_4107_, 2);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_x_4107_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4116_ = v_x_4107_;
v_isShared_4117_ = v_isSharedCheck_4141_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_tail_4114_);
lean_inc(v_value_4113_);
lean_inc(v_key_4112_);
lean_dec(v_x_4107_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4141_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
uint8_t v___y_4119_; lean_object* v_fst_4130_; lean_object* v_snd_4131_; lean_object* v_fst_4132_; lean_object* v_snd_4133_; uint8_t v___x_4134_; 
v_fst_4130_ = lean_ctor_get(v_key_4112_, 0);
v_snd_4131_ = lean_ctor_get(v_key_4112_, 1);
v_fst_4132_ = lean_ctor_get(v_a_4106_, 0);
v_snd_4133_ = lean_ctor_get(v_a_4106_, 1);
v___x_4134_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4130_, v_fst_4132_);
if (v___x_4134_ == 0)
{
v___y_4119_ = v___x_4134_;
goto v___jp_4118_;
}
else
{
lean_object* v_fst_4135_; lean_object* v_snd_4136_; lean_object* v_fst_4137_; lean_object* v_snd_4138_; uint8_t v___x_4139_; 
v_fst_4135_ = lean_ctor_get(v_snd_4131_, 0);
v_snd_4136_ = lean_ctor_get(v_snd_4131_, 1);
v_fst_4137_ = lean_ctor_get(v_snd_4133_, 0);
v_snd_4138_ = lean_ctor_get(v_snd_4133_, 1);
v___x_4139_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4135_, v_fst_4137_);
if (v___x_4139_ == 0)
{
v___y_4119_ = v___x_4139_;
goto v___jp_4118_;
}
else
{
uint8_t v___x_4140_; 
v___x_4140_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4136_, v_snd_4138_);
v___y_4119_ = v___x_4140_;
goto v___jp_4118_;
}
}
v___jp_4118_:
{
if (v___y_4119_ == 0)
{
lean_object* v_tail_4120_; lean_object* v___x_4122_; 
v_tail_4120_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4105_, v_a_4106_, v_tail_4114_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 2, v_tail_4120_);
v___x_4122_ = v___x_4116_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_key_4112_);
lean_ctor_set(v_reuseFailAlloc_4123_, 1, v_value_4113_);
lean_ctor_set(v_reuseFailAlloc_4123_, 2, v_tail_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v_val_4126_; lean_object* v___x_4128_; 
lean_dec(v_key_4112_);
v___x_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4124_, 0, v_value_4113_);
v___x_4125_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4105_, v___x_4124_);
v_val_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_val_4126_);
lean_dec(v___x_4125_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 1, v_val_4126_);
lean_ctor_set(v___x_4116_, 0, v_a_4106_);
v___x_4128_ = v___x_4116_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4106_);
lean_ctor_set(v_reuseFailAlloc_4129_, 1, v_val_4126_);
lean_ctor_set(v_reuseFailAlloc_4129_, 2, v_tail_4114_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_a_4142_, lean_object* v_x_4143_){
_start:
{
if (lean_obj_tag(v_x_4143_) == 0)
{
uint8_t v___x_4144_; 
v___x_4144_ = 0;
return v___x_4144_;
}
else
{
lean_object* v_key_4145_; lean_object* v_tail_4146_; uint8_t v___y_4148_; lean_object* v_fst_4150_; lean_object* v_snd_4151_; lean_object* v_fst_4152_; lean_object* v_snd_4153_; uint8_t v___x_4154_; 
v_key_4145_ = lean_ctor_get(v_x_4143_, 0);
v_tail_4146_ = lean_ctor_get(v_x_4143_, 2);
v_fst_4150_ = lean_ctor_get(v_key_4145_, 0);
v_snd_4151_ = lean_ctor_get(v_key_4145_, 1);
v_fst_4152_ = lean_ctor_get(v_a_4142_, 0);
v_snd_4153_ = lean_ctor_get(v_a_4142_, 1);
v___x_4154_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4150_, v_fst_4152_);
if (v___x_4154_ == 0)
{
v___y_4148_ = v___x_4154_;
goto v___jp_4147_;
}
else
{
lean_object* v_fst_4155_; lean_object* v_snd_4156_; lean_object* v_fst_4157_; lean_object* v_snd_4158_; uint8_t v___x_4159_; 
v_fst_4155_ = lean_ctor_get(v_snd_4151_, 0);
v_snd_4156_ = lean_ctor_get(v_snd_4151_, 1);
v_fst_4157_ = lean_ctor_get(v_snd_4153_, 0);
v_snd_4158_ = lean_ctor_get(v_snd_4153_, 1);
v___x_4159_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4155_, v_fst_4157_);
if (v___x_4159_ == 0)
{
v___y_4148_ = v___x_4159_;
goto v___jp_4147_;
}
else
{
uint8_t v___x_4160_; 
v___x_4160_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4156_, v_snd_4158_);
v___y_4148_ = v___x_4160_;
goto v___jp_4147_;
}
}
v___jp_4147_:
{
if (v___y_4148_ == 0)
{
v_x_4143_ = v_tail_4146_;
goto _start;
}
else
{
return v___y_4148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object* v_a_4161_, lean_object* v_x_4162_){
_start:
{
uint8_t v_res_4163_; lean_object* v_r_4164_; 
v_res_4163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4161_, v_x_4162_);
lean_dec(v_x_4162_);
lean_dec_ref(v_a_4161_);
v_r_4164_ = lean_box(v_res_4163_);
return v_r_4164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4165_, lean_object* v_m_4166_, lean_object* v_a_4167_){
_start:
{
size_t v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v_snd_4175_; lean_object* v_size_4176_; lean_object* v_buckets_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4236_; 
v_snd_4175_ = lean_ctor_get(v_a_4167_, 1);
v_size_4176_ = lean_ctor_get(v_m_4166_, 0);
v_buckets_4177_ = lean_ctor_get(v_m_4166_, 1);
v_isSharedCheck_4236_ = !lean_is_exclusive(v_m_4166_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4179_ = v_m_4166_;
v_isShared_4180_ = v_isSharedCheck_4236_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_buckets_4177_);
lean_inc(v_size_4176_);
lean_dec(v_m_4166_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4236_;
goto v_resetjp_4178_;
}
v___jp_4168_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_array_uset(v___y_4170_, v___y_4169_, v___y_4171_);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___y_4172_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
return v___x_4174_;
}
v_resetjp_4178_:
{
lean_object* v_fst_4181_; lean_object* v_fst_4182_; lean_object* v_snd_4183_; lean_object* v___x_4184_; uint64_t v___x_4185_; uint64_t v___y_4187_; uint64_t v___y_4228_; 
v_fst_4181_ = lean_ctor_get(v_a_4167_, 0);
v_fst_4182_ = lean_ctor_get(v_snd_4175_, 0);
v_snd_4183_ = lean_ctor_get(v_snd_4175_, 1);
v___x_4184_ = lean_array_get_size(v_buckets_4177_);
v___x_4185_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4181_);
if (lean_obj_tag(v_fst_4182_) == 0)
{
uint64_t v___x_4231_; 
v___x_4231_ = 11ULL;
v___y_4187_ = v___x_4231_;
goto v___jp_4186_;
}
else
{
lean_object* v_val_4232_; uint8_t v___x_4233_; 
v_val_4232_ = lean_ctor_get(v_fst_4182_, 0);
v___x_4233_ = lean_unbox(v_val_4232_);
if (v___x_4233_ == 0)
{
uint64_t v___x_4234_; 
v___x_4234_ = 13ULL;
v___y_4228_ = v___x_4234_;
goto v___jp_4227_;
}
else
{
uint64_t v___x_4235_; 
v___x_4235_ = 11ULL;
v___y_4228_ = v___x_4235_;
goto v___jp_4227_;
}
}
v___jp_4186_:
{
uint64_t v___x_4188_; uint64_t v___x_4189_; uint64_t v___x_4190_; uint64_t v___x_4191_; uint64_t v___x_4192_; uint64_t v_fold_4193_; uint64_t v___x_4194_; uint64_t v___x_4195_; uint64_t v___x_4196_; size_t v___x_4197_; size_t v___x_4198_; size_t v___x_4199_; size_t v___x_4200_; size_t v___x_4201_; lean_object* v_bkt_4202_; uint8_t v___x_4203_; 
v___x_4188_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4183_);
v___x_4189_ = lean_uint64_mix_hash(v___y_4187_, v___x_4188_);
v___x_4190_ = lean_uint64_mix_hash(v___x_4185_, v___x_4189_);
v___x_4191_ = 32ULL;
v___x_4192_ = lean_uint64_shift_right(v___x_4190_, v___x_4191_);
v_fold_4193_ = lean_uint64_xor(v___x_4190_, v___x_4192_);
v___x_4194_ = 16ULL;
v___x_4195_ = lean_uint64_shift_right(v_fold_4193_, v___x_4194_);
v___x_4196_ = lean_uint64_xor(v_fold_4193_, v___x_4195_);
v___x_4197_ = lean_uint64_to_usize(v___x_4196_);
v___x_4198_ = lean_usize_of_nat(v___x_4184_);
v___x_4199_ = ((size_t)1ULL);
v___x_4200_ = lean_usize_sub(v___x_4198_, v___x_4199_);
v___x_4201_ = lean_usize_land(v___x_4197_, v___x_4200_);
v_bkt_4202_ = lean_array_uget_borrowed(v_buckets_4177_, v___x_4201_);
v___x_4203_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4167_, v_bkt_4202_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; lean_object* v_size_x27_4205_; lean_object* v___x_4206_; lean_object* v_buckets_x27_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4204_ = lean_unsigned_to_nat(1u);
v_size_x27_4205_ = lean_nat_add(v_size_4176_, v___x_4204_);
lean_dec(v_size_4176_);
lean_inc(v_bkt_4202_);
v___x_4206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4206_, 0, v_a_4167_);
lean_ctor_set(v___x_4206_, 1, v_a_4165_);
lean_ctor_set(v___x_4206_, 2, v_bkt_4202_);
v_buckets_x27_4207_ = lean_array_uset(v_buckets_4177_, v___x_4201_, v___x_4206_);
v___x_4208_ = lean_unsigned_to_nat(4u);
v___x_4209_ = lean_nat_mul(v_size_x27_4205_, v___x_4208_);
v___x_4210_ = lean_unsigned_to_nat(3u);
v___x_4211_ = lean_nat_div(v___x_4209_, v___x_4210_);
lean_dec(v___x_4209_);
v___x_4212_ = lean_array_get_size(v_buckets_x27_4207_);
v___x_4213_ = lean_nat_dec_le(v___x_4211_, v___x_4212_);
lean_dec(v___x_4211_);
if (v___x_4213_ == 0)
{
lean_object* v_val_4214_; lean_object* v___x_4216_; 
v_val_4214_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_buckets_x27_4207_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 1, v_val_4214_);
lean_ctor_set(v___x_4179_, 0, v_size_x27_4205_);
v___x_4216_ = v___x_4179_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_size_x27_4205_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_val_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
else
{
lean_object* v___x_4219_; 
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 1, v_buckets_x27_4207_);
lean_ctor_set(v___x_4179_, 0, v_size_x27_4205_);
v___x_4219_ = v___x_4179_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_size_x27_4205_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_buckets_x27_4207_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
else
{
lean_object* v___x_4221_; lean_object* v_buckets_x27_4222_; lean_object* v_bkt_x27_4223_; uint8_t v___x_4224_; 
lean_inc(v_bkt_4202_);
lean_del_object(v___x_4179_);
v___x_4221_ = lean_box(0);
v_buckets_x27_4222_ = lean_array_uset(v_buckets_4177_, v___x_4201_, v___x_4221_);
lean_inc_ref(v_a_4167_);
v_bkt_x27_4223_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4165_, v_a_4167_, v_bkt_4202_);
v___x_4224_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4167_, v_bkt_x27_4223_);
lean_dec_ref(v_a_4167_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = lean_nat_sub(v_size_4176_, v___x_4225_);
lean_dec(v_size_4176_);
v___y_4169_ = v___x_4201_;
v___y_4170_ = v_buckets_x27_4222_;
v___y_4171_ = v_bkt_x27_4223_;
v___y_4172_ = v___x_4226_;
goto v___jp_4168_;
}
else
{
v___y_4169_ = v___x_4201_;
v___y_4170_ = v_buckets_x27_4222_;
v___y_4171_ = v_bkt_x27_4223_;
v___y_4172_ = v_size_4176_;
goto v___jp_4168_;
}
}
}
v___jp_4227_:
{
uint64_t v___x_4229_; uint64_t v___x_4230_; 
v___x_4229_ = 13ULL;
v___x_4230_ = lean_uint64_mix_hash(v___y_4228_, v___x_4229_);
v___y_4187_ = v___x_4230_;
goto v___jp_4186_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4237_, lean_object* v_as_4238_, size_t v_sz_4239_, size_t v_i_4240_, lean_object* v_b_4241_){
_start:
{
uint8_t v___x_4242_; 
v___x_4242_ = lean_usize_dec_lt(v_i_4240_, v_sz_4239_);
if (v___x_4242_ == 0)
{
return v_b_4241_;
}
else
{
lean_object* v_a_4243_; lean_object* v___y_4245_; 
v_a_4243_ = lean_array_uget_borrowed(v_as_4238_, v_i_4240_);
if (v_allowSimultaneousBinderUse_4237_ == 0)
{
lean_object* v___x_4254_; 
v___x_4254_ = lean_box(0);
v___y_4245_ = v___x_4254_;
goto v___jp_4244_;
}
else
{
uint8_t v_isBinder_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v_isBinder_4255_ = lean_ctor_get_uint8(v_a_4243_, sizeof(void*)*6);
v___x_4256_ = lean_box(v_isBinder_4255_);
v___x_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
v___y_4245_ = v___x_4257_;
goto v___jp_4244_;
}
v___jp_4244_:
{
lean_object* v_ident_4246_; lean_object* v_range_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; size_t v___x_4251_; size_t v___x_4252_; 
v_ident_4246_ = lean_ctor_get(v_a_4243_, 0);
v_range_4247_ = lean_ctor_get(v_a_4243_, 2);
lean_inc_ref(v_range_4247_);
v___x_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___y_4245_);
lean_ctor_set(v___x_4248_, 1, v_range_4247_);
lean_inc_ref(v_ident_4246_);
v___x_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4249_, 0, v_ident_4246_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
lean_inc(v_a_4243_);
v___x_4250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4243_, v_b_4241_, v___x_4249_);
v___x_4251_ = ((size_t)1ULL);
v___x_4252_ = lean_usize_add(v_i_4240_, v___x_4251_);
v_i_4240_ = v___x_4252_;
v_b_4241_ = v___x_4250_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4258_, lean_object* v_as_4259_, lean_object* v_sz_4260_, lean_object* v_i_4261_, lean_object* v_b_4262_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4263_; size_t v_sz_boxed_4264_; size_t v_i_boxed_4265_; lean_object* v_res_4266_; 
v_allowSimultaneousBinderUse_boxed_4263_ = lean_unbox(v_allowSimultaneousBinderUse_4258_);
v_sz_boxed_4264_ = lean_unbox_usize(v_sz_4260_);
lean_dec(v_sz_4260_);
v_i_boxed_4265_ = lean_unbox_usize(v_i_4261_);
lean_dec(v_i_4261_);
v_res_4266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4263_, v_as_4259_, v_sz_boxed_4264_, v_i_boxed_4265_, v_b_4262_);
lean_dec_ref(v_as_4259_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4267_, lean_object* v_x_4268_){
_start:
{
if (lean_obj_tag(v_x_4268_) == 0)
{
return v_x_4267_;
}
else
{
lean_object* v_value_4269_; lean_object* v_tail_4270_; lean_object* v___x_4271_; 
v_value_4269_ = lean_ctor_get(v_x_4268_, 1);
lean_inc(v_value_4269_);
v_tail_4270_ = lean_ctor_get(v_x_4268_, 2);
lean_inc(v_tail_4270_);
lean_dec_ref_known(v_x_4268_, 3);
v___x_4271_ = lean_array_push(v_x_4267_, v_value_4269_);
v_x_4267_ = v___x_4271_;
v_x_4268_ = v_tail_4270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4273_, size_t v_i_4274_, size_t v_stop_4275_, lean_object* v_b_4276_){
_start:
{
uint8_t v___x_4277_; 
v___x_4277_ = lean_usize_dec_eq(v_i_4274_, v_stop_4275_);
if (v___x_4277_ == 0)
{
lean_object* v___x_4278_; lean_object* v___x_4279_; size_t v___x_4280_; size_t v___x_4281_; 
v___x_4278_ = lean_array_uget_borrowed(v_as_4273_, v_i_4274_);
lean_inc(v___x_4278_);
v___x_4279_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4276_, v___x_4278_);
v___x_4280_ = ((size_t)1ULL);
v___x_4281_ = lean_usize_add(v_i_4274_, v___x_4280_);
v_i_4274_ = v___x_4281_;
v_b_4276_ = v___x_4279_;
goto _start;
}
else
{
return v_b_4276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4283_, lean_object* v_i_4284_, lean_object* v_stop_4285_, lean_object* v_b_4286_){
_start:
{
size_t v_i_boxed_4287_; size_t v_stop_boxed_4288_; lean_object* v_res_4289_; 
v_i_boxed_4287_ = lean_unbox_usize(v_i_4284_);
lean_dec(v_i_4284_);
v_stop_boxed_4288_ = lean_unbox_usize(v_stop_4285_);
lean_dec(v_stop_4285_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4283_, v_i_boxed_4287_, v_stop_boxed_4288_, v_b_4286_);
lean_dec_ref(v_as_4283_);
return v_res_4289_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4290_ = lean_box(0);
v___x_4291_ = lean_unsigned_to_nat(16u);
v___x_4292_ = lean_mk_array(v___x_4291_, v___x_4290_);
return v___x_4292_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v_refsByIdAndRange_4295_; 
v___x_4293_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4294_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4295_, 0, v___x_4294_);
lean_ctor_set(v_refsByIdAndRange_4295_, 1, v___x_4293_);
return v_refsByIdAndRange_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4296_, uint8_t v_allowSimultaneousBinderUse_4297_){
_start:
{
lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4307_; lean_object* v___x_4314_; lean_object* v_refsByIdAndRange_4315_; size_t v_sz_4316_; size_t v___x_4317_; lean_object* v___x_4318_; lean_object* v_buckets_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; uint8_t v___x_4322_; 
v___x_4314_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4315_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4316_ = lean_array_size(v_refs_4296_);
v___x_4317_ = ((size_t)0ULL);
v___x_4318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4297_, v_refs_4296_, v_sz_4316_, v___x_4317_, v_refsByIdAndRange_4315_);
v_buckets_4319_ = lean_ctor_get(v___x_4318_, 1);
lean_inc_ref(v_buckets_4319_);
lean_dec_ref(v___x_4318_);
v___x_4320_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4321_ = lean_array_get_size(v_buckets_4319_);
v___x_4322_ = lean_nat_dec_lt(v___x_4314_, v___x_4321_);
if (v___x_4322_ == 0)
{
lean_dec_ref(v_buckets_4319_);
v___y_4307_ = v___x_4320_;
goto v___jp_4306_;
}
else
{
size_t v___x_4323_; lean_object* v___x_4324_; 
v___x_4323_ = lean_usize_of_nat(v___x_4321_);
v___x_4324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4319_, v___x_4317_, v___x_4323_, v___x_4320_);
lean_dec_ref(v_buckets_4319_);
v___y_4307_ = v___x_4324_;
goto v___jp_4306_;
}
v___jp_4298_:
{
uint8_t v___x_4303_; 
v___x_4303_ = lean_nat_dec_le(v___y_4302_, v___y_4301_);
if (v___x_4303_ == 0)
{
lean_object* v___x_4304_; 
lean_dec(v___y_4301_);
lean_inc(v___y_4302_);
v___x_4304_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4299_, v___y_4300_, v___y_4302_, v___y_4302_);
lean_dec(v___y_4302_);
lean_dec(v___y_4299_);
return v___x_4304_;
}
else
{
lean_object* v___x_4305_; 
v___x_4305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4299_, v___y_4300_, v___y_4302_, v___y_4301_);
lean_dec(v___y_4301_);
lean_dec(v___y_4299_);
return v___x_4305_;
}
}
v___jp_4306_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4308_ = lean_array_get_size(v___y_4307_);
v___x_4309_ = lean_unsigned_to_nat(0u);
v___x_4310_ = lean_nat_dec_eq(v___x_4308_, v___x_4309_);
if (v___x_4310_ == 0)
{
lean_object* v___x_4311_; lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4311_ = lean_unsigned_to_nat(1u);
v___x_4312_ = lean_nat_sub(v___x_4308_, v___x_4311_);
v___x_4313_ = lean_nat_dec_le(v___x_4309_, v___x_4312_);
if (v___x_4313_ == 0)
{
lean_inc(v___x_4312_);
v___y_4299_ = v___x_4308_;
v___y_4300_ = v___y_4307_;
v___y_4301_ = v___x_4312_;
v___y_4302_ = v___x_4312_;
goto v___jp_4298_;
}
else
{
v___y_4299_ = v___x_4308_;
v___y_4300_ = v___y_4307_;
v___y_4301_ = v___x_4312_;
v___y_4302_ = v___x_4309_;
goto v___jp_4298_;
}
}
else
{
return v___y_4307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object* v_refs_4325_, lean_object* v_allowSimultaneousBinderUse_4326_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4327_; lean_object* v_res_4328_; 
v_allowSimultaneousBinderUse_boxed_4327_ = lean_unbox(v_allowSimultaneousBinderUse_4326_);
v_res_4328_ = l_Lean_Server_dedupReferences(v_refs_4325_, v_allowSimultaneousBinderUse_boxed_4327_);
lean_dec_ref(v_refs_4325_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object* v_n_4329_, lean_object* v_as_4330_, lean_object* v_lo_4331_, lean_object* v_hi_4332_, lean_object* v_w_4333_, lean_object* v_hlo_4334_, lean_object* v_hhi_4335_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4329_, v_as_4330_, v_lo_4331_, v_hi_4332_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object* v_n_4337_, lean_object* v_as_4338_, lean_object* v_lo_4339_, lean_object* v_hi_4340_, lean_object* v_w_4341_, lean_object* v_hlo_4342_, lean_object* v_hhi_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(v_n_4337_, v_as_4338_, v_lo_4339_, v_hi_4340_, v_w_4341_, v_hlo_4342_, v_hhi_4343_);
lean_dec(v_hi_4340_);
lean_dec(v_n_4337_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(lean_object* v_n_4345_, lean_object* v_lo_4346_, lean_object* v_hi_4347_, lean_object* v_hhi_4348_, lean_object* v_pivot_4349_, lean_object* v_as_4350_, lean_object* v_i_4351_, lean_object* v_k_4352_, lean_object* v_ilo_4353_, lean_object* v_ik_4354_, lean_object* v_w_4355_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_4347_, v_pivot_4349_, v_as_4350_, v_i_4351_, v_k_4352_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___boxed(lean_object* v_n_4357_, lean_object* v_lo_4358_, lean_object* v_hi_4359_, lean_object* v_hhi_4360_, lean_object* v_pivot_4361_, lean_object* v_as_4362_, lean_object* v_i_4363_, lean_object* v_k_4364_, lean_object* v_ilo_4365_, lean_object* v_ik_4366_, lean_object* v_w_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(v_n_4357_, v_lo_4358_, v_hi_4359_, v_hhi_4360_, v_pivot_4361_, v_as_4362_, v_i_4363_, v_k_4364_, v_ilo_4365_, v_ik_4366_, v_w_4367_);
lean_dec_ref(v_pivot_4361_);
lean_dec(v_hi_4359_);
lean_dec(v_lo_4358_);
lean_dec(v_n_4357_);
return v_res_4368_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object* v_00_u03b2_4369_, lean_object* v_a_4370_, lean_object* v_x_4371_){
_start:
{
uint8_t v___x_4372_; 
v___x_4372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4370_, v_x_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4373_, lean_object* v_a_4374_, lean_object* v_x_4375_){
_start:
{
uint8_t v_res_4376_; lean_object* v_r_4377_; 
v_res_4376_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(v_00_u03b2_4373_, v_a_4374_, v_x_4375_);
lean_dec(v_x_4375_);
lean_dec_ref(v_a_4374_);
v_r_4377_ = lean_box(v_res_4376_);
return v_r_4377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object* v_00_u03b2_4378_, lean_object* v_data_4379_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_data_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4381_, lean_object* v_i_4382_, lean_object* v_source_4383_, lean_object* v_target_4384_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v_i_4382_, v_source_4383_, v_target_4384_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4386_, lean_object* v_x_4387_, lean_object* v_x_4388_){
_start:
{
lean_object* v___x_4389_; 
v___x_4389_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_x_4387_, v_x_4388_);
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object* v_as_4390_, size_t v_i_4391_, size_t v_stop_4392_, lean_object* v_b_4393_){
_start:
{
uint8_t v___x_4394_; 
v___x_4394_ = lean_usize_dec_eq(v_i_4391_, v_stop_4392_);
if (v___x_4394_ == 0)
{
lean_object* v___x_4395_; lean_object* v___x_4396_; size_t v___x_4397_; size_t v___x_4398_; 
v___x_4395_ = lean_array_uget_borrowed(v_as_4390_, v_i_4391_);
lean_inc(v___x_4395_);
v___x_4396_ = l_Lean_Server_ModuleRefs_addRef(v_b_4393_, v___x_4395_);
v___x_4397_ = ((size_t)1ULL);
v___x_4398_ = lean_usize_add(v_i_4391_, v___x_4397_);
v_i_4391_ = v___x_4398_;
v_b_4393_ = v___x_4396_;
goto _start;
}
else
{
return v_b_4393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object* v_as_4400_, lean_object* v_i_4401_, lean_object* v_stop_4402_, lean_object* v_b_4403_){
_start:
{
size_t v_i_boxed_4404_; size_t v_stop_boxed_4405_; lean_object* v_res_4406_; 
v_i_boxed_4404_ = lean_unbox_usize(v_i_4401_);
lean_dec(v_i_4401_);
v_stop_boxed_4405_ = lean_unbox_usize(v_stop_4402_);
lean_dec(v_stop_4402_);
v_res_4406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_as_4400_, v_i_boxed_4404_, v_stop_boxed_4405_, v_b_4403_);
lean_dec_ref(v_as_4400_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object* v_as_4407_, size_t v_i_4408_, size_t v_stop_4409_, lean_object* v_b_4410_){
_start:
{
lean_object* v___y_4412_; uint8_t v___x_4416_; 
v___x_4416_ = lean_usize_dec_eq(v_i_4408_, v_stop_4409_);
if (v___x_4416_ == 0)
{
lean_object* v___x_4417_; lean_object* v_ident_4418_; 
v___x_4417_ = lean_array_uget_borrowed(v_as_4407_, v_i_4408_);
v_ident_4418_ = lean_ctor_get(v___x_4417_, 0);
if (lean_obj_tag(v_ident_4418_) == 1)
{
v___y_4412_ = v_b_4410_;
goto v___jp_4411_;
}
else
{
lean_object* v___x_4419_; 
lean_inc(v___x_4417_);
v___x_4419_ = lean_array_push(v_b_4410_, v___x_4417_);
v___y_4412_ = v___x_4419_;
goto v___jp_4411_;
}
}
else
{
return v_b_4410_;
}
v___jp_4411_:
{
size_t v___x_4413_; size_t v___x_4414_; 
v___x_4413_ = ((size_t)1ULL);
v___x_4414_ = lean_usize_add(v_i_4408_, v___x_4413_);
v_i_4408_ = v___x_4414_;
v_b_4410_ = v___y_4412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object* v_as_4420_, lean_object* v_i_4421_, lean_object* v_stop_4422_, lean_object* v_b_4423_){
_start:
{
size_t v_i_boxed_4424_; size_t v_stop_boxed_4425_; lean_object* v_res_4426_; 
v_i_boxed_4424_ = lean_unbox_usize(v_i_4421_);
lean_dec(v_i_4421_);
v_stop_boxed_4425_ = lean_unbox_usize(v_stop_4422_);
lean_dec(v_stop_4422_);
v_res_4426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_as_4420_, v_i_boxed_4424_, v_stop_boxed_4425_, v_b_4423_);
lean_dec_ref(v_as_4420_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object* v_text_4427_, lean_object* v_trees_4428_, uint8_t v_localVars_4429_, uint8_t v_allowSimultaneousBinderUse_4430_){
_start:
{
lean_object* v_refs_4432_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v_refs_4446_; 
v___x_4444_ = l_Lean_Server_findReferences(v_text_4427_, v_trees_4428_);
v___x_4445_ = l_Lean_Server_combineIdents(v_trees_4428_, v___x_4444_);
lean_dec_ref(v___x_4444_);
v_refs_4446_ = l_Lean_Server_dedupReferences(v___x_4445_, v_allowSimultaneousBinderUse_4430_);
lean_dec_ref(v___x_4445_);
if (v_localVars_4429_ == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; uint8_t v___x_4450_; 
v___x_4447_ = lean_unsigned_to_nat(0u);
v___x_4448_ = lean_array_get_size(v_refs_4446_);
v___x_4449_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4450_ = lean_nat_dec_lt(v___x_4447_, v___x_4448_);
if (v___x_4450_ == 0)
{
lean_dec_ref(v_refs_4446_);
v_refs_4432_ = v___x_4449_;
goto v___jp_4431_;
}
else
{
uint8_t v___x_4451_; 
v___x_4451_ = lean_nat_dec_le(v___x_4448_, v___x_4448_);
if (v___x_4451_ == 0)
{
if (v___x_4450_ == 0)
{
lean_dec_ref(v_refs_4446_);
v_refs_4432_ = v___x_4449_;
goto v___jp_4431_;
}
else
{
size_t v___x_4452_; size_t v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = ((size_t)0ULL);
v___x_4453_ = lean_usize_of_nat(v___x_4448_);
v___x_4454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4446_, v___x_4452_, v___x_4453_, v___x_4449_);
lean_dec_ref(v_refs_4446_);
v_refs_4432_ = v___x_4454_;
goto v___jp_4431_;
}
}
else
{
size_t v___x_4455_; size_t v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = ((size_t)0ULL);
v___x_4456_ = lean_usize_of_nat(v___x_4448_);
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4446_, v___x_4455_, v___x_4456_, v___x_4449_);
lean_dec_ref(v_refs_4446_);
v_refs_4432_ = v___x_4457_;
goto v___jp_4431_;
}
}
}
else
{
v_refs_4432_ = v_refs_4446_;
goto v___jp_4431_;
}
v___jp_4431_:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; 
v___x_4433_ = lean_box(1);
v___x_4434_ = lean_unsigned_to_nat(0u);
v___x_4435_ = lean_array_get_size(v_refs_4432_);
v___x_4436_ = lean_nat_dec_lt(v___x_4434_, v___x_4435_);
if (v___x_4436_ == 0)
{
lean_dec_ref(v_refs_4432_);
return v___x_4433_;
}
else
{
uint8_t v___x_4437_; 
v___x_4437_ = lean_nat_dec_le(v___x_4435_, v___x_4435_);
if (v___x_4437_ == 0)
{
if (v___x_4436_ == 0)
{
lean_dec_ref(v_refs_4432_);
return v___x_4433_;
}
else
{
size_t v___x_4438_; size_t v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = ((size_t)0ULL);
v___x_4439_ = lean_usize_of_nat(v___x_4435_);
v___x_4440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4432_, v___x_4438_, v___x_4439_, v___x_4433_);
lean_dec_ref(v_refs_4432_);
return v___x_4440_;
}
}
else
{
size_t v___x_4441_; size_t v___x_4442_; lean_object* v___x_4443_; 
v___x_4441_ = ((size_t)0ULL);
v___x_4442_ = lean_usize_of_nat(v___x_4435_);
v___x_4443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4432_, v___x_4441_, v___x_4442_, v___x_4433_);
lean_dec_ref(v_refs_4432_);
return v___x_4443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object* v_text_4458_, lean_object* v_trees_4459_, lean_object* v_localVars_4460_, lean_object* v_allowSimultaneousBinderUse_4461_){
_start:
{
uint8_t v_localVars_boxed_4462_; uint8_t v_allowSimultaneousBinderUse_boxed_4463_; lean_object* v_res_4464_; 
v_localVars_boxed_4462_ = lean_unbox(v_localVars_4460_);
v_allowSimultaneousBinderUse_boxed_4463_ = lean_unbox(v_allowSimultaneousBinderUse_4461_);
v_res_4464_ = l_Lean_Server_findModuleRefs(v_text_4458_, v_trees_4459_, v_localVars_boxed_4462_, v_allowSimultaneousBinderUse_boxed_4463_);
lean_dec_ref(v_trees_4459_);
return v_res_4464_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t v_a_4472_, uint8_t v_a_4473_){
_start:
{
switch(v_a_4472_)
{
case 0:
{
if (v_a_4473_ == 1)
{
uint8_t v___x_4474_; 
v___x_4474_ = 2;
return v___x_4474_;
}
else
{
return v_a_4473_;
}
}
case 1:
{
if (v_a_4473_ == 0)
{
uint8_t v___x_4475_; 
v___x_4475_ = 2;
return v___x_4475_;
}
else
{
return v_a_4473_;
}
}
default: 
{
return v_a_4472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object* v_a_4476_, lean_object* v_a_4477_){
_start:
{
uint8_t v_a_46__boxed_4478_; uint8_t v_a_47__boxed_4479_; uint8_t v_res_4480_; lean_object* v_r_4481_; 
v_a_46__boxed_4478_ = lean_unbox(v_a_4476_);
v_a_47__boxed_4479_ = lean_unbox(v_a_4477_);
v_res_4480_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_a_46__boxed_4478_, v_a_47__boxed_4479_);
v_r_4481_ = lean_box(v_res_4480_);
return v_r_4481_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object* v_upperBound_4482_, lean_object* v_identicalImports_4483_, lean_object* v_a_4484_, lean_object* v_b_4485_){
_start:
{
uint8_t v___x_4486_; 
v___x_4486_ = lean_nat_dec_lt(v_a_4484_, v_upperBound_4482_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; 
lean_dec(v_a_4484_);
v___x_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4487_, 0, v_b_4485_);
return v___x_4487_;
}
else
{
lean_object* v_module_4488_; lean_object* v_uri_4489_; uint8_t v_isAll_4490_; uint8_t v_isPrivate_4491_; uint8_t v_metaKind_4492_; lean_object* v___x_4493_; lean_object* v_module_4494_; lean_object* v_uri_4495_; uint8_t v_isAll_4496_; uint8_t v_isPrivate_4497_; uint8_t v_metaKind_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4518_; 
v_module_4488_ = lean_ctor_get(v_b_4485_, 0);
lean_inc(v_module_4488_);
v_uri_4489_ = lean_ctor_get(v_b_4485_, 1);
lean_inc_ref(v_uri_4489_);
v_isAll_4490_ = lean_ctor_get_uint8(v_b_4485_, sizeof(void*)*2);
v_isPrivate_4491_ = lean_ctor_get_uint8(v_b_4485_, sizeof(void*)*2 + 1);
v_metaKind_4492_ = lean_ctor_get_uint8(v_b_4485_, sizeof(void*)*2 + 2);
lean_dec_ref(v_b_4485_);
v___x_4493_ = lean_array_fget(v_identicalImports_4483_, v_a_4484_);
v_module_4494_ = lean_ctor_get(v___x_4493_, 0);
v_uri_4495_ = lean_ctor_get(v___x_4493_, 1);
v_isAll_4496_ = lean_ctor_get_uint8(v___x_4493_, sizeof(void*)*2);
v_isPrivate_4497_ = lean_ctor_get_uint8(v___x_4493_, sizeof(void*)*2 + 1);
v_metaKind_4498_ = lean_ctor_get_uint8(v___x_4493_, sizeof(void*)*2 + 2);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4500_ = v___x_4493_;
v_isShared_4501_ = v_isSharedCheck_4518_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_uri_4495_);
lean_inc(v_module_4494_);
lean_dec(v___x_4493_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4518_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
uint8_t v___y_4503_; uint8_t v___y_4504_; uint8_t v___y_4513_; uint8_t v___x_4514_; 
v___x_4514_ = lean_name_eq(v_module_4488_, v_module_4494_);
lean_dec(v_module_4494_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; 
lean_del_object(v___x_4500_);
lean_dec_ref(v_uri_4495_);
lean_dec_ref(v_uri_4489_);
lean_dec(v_module_4488_);
lean_dec(v_a_4484_);
v___x_4515_ = lean_box(0);
return v___x_4515_;
}
else
{
uint8_t v___x_4516_; 
v___x_4516_ = lean_string_dec_eq(v_uri_4489_, v_uri_4495_);
lean_dec_ref(v_uri_4495_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; 
lean_del_object(v___x_4500_);
lean_dec_ref(v_uri_4489_);
lean_dec(v_module_4488_);
lean_dec(v_a_4484_);
v___x_4517_ = lean_box(0);
return v___x_4517_;
}
else
{
if (v_isAll_4490_ == 0)
{
v___y_4513_ = v_isAll_4496_;
goto v___jp_4512_;
}
else
{
v___y_4513_ = v___x_4486_;
goto v___jp_4512_;
}
}
}
v___jp_4502_:
{
uint8_t v___x_4505_; lean_object* v___x_4507_; 
v___x_4505_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_metaKind_4492_, v_metaKind_4498_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 1, v_uri_4489_);
lean_ctor_set(v___x_4500_, 0, v_module_4488_);
v___x_4507_ = v___x_4500_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_module_4488_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_uri_4489_);
v___x_4507_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; 
lean_ctor_set_uint8(v___x_4507_, sizeof(void*)*2, v___y_4503_);
lean_ctor_set_uint8(v___x_4507_, sizeof(void*)*2 + 1, v___y_4504_);
lean_ctor_set_uint8(v___x_4507_, sizeof(void*)*2 + 2, v___x_4505_);
v___x_4508_ = lean_unsigned_to_nat(1u);
v___x_4509_ = lean_nat_add(v_a_4484_, v___x_4508_);
lean_dec(v_a_4484_);
v_a_4484_ = v___x_4509_;
v_b_4485_ = v___x_4507_;
goto _start;
}
}
v___jp_4512_:
{
if (v_isPrivate_4491_ == 0)
{
v___y_4503_ = v___y_4513_;
v___y_4504_ = v_isPrivate_4491_;
goto v___jp_4502_;
}
else
{
v___y_4503_ = v___y_4513_;
v___y_4504_ = v_isPrivate_4497_;
goto v___jp_4502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_4519_, lean_object* v_identicalImports_4520_, lean_object* v_a_4521_, lean_object* v_b_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4519_, v_identicalImports_4520_, v_a_4521_, v_b_4522_);
lean_dec_ref(v_identicalImports_4520_);
lean_dec(v_upperBound_4519_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object* v_identicalImports_4524_){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4525_ = lean_unsigned_to_nat(0u);
v___x_4526_ = lean_array_get_size(v_identicalImports_4524_);
v___x_4527_ = lean_nat_dec_lt(v___x_4525_, v___x_4526_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; 
v___x_4528_ = lean_box(0);
return v___x_4528_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = lean_unsigned_to_nat(1u);
v___x_4530_ = lean_array_fget_borrowed(v_identicalImports_4524_, v___x_4525_);
lean_inc(v___x_4530_);
v___x_4531_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v___x_4526_, v_identicalImports_4524_, v___x_4529_, v___x_4530_);
return v___x_4531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object* v_identicalImports_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_identicalImports_4532_);
lean_dec_ref(v_identicalImports_4532_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object* v_upperBound_4534_, lean_object* v_identicalImports_4535_, lean_object* v_inst_4536_, lean_object* v_R_4537_, lean_object* v_a_4538_, lean_object* v_b_4539_, lean_object* v_c_4540_){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4534_, v_identicalImports_4535_, v_a_4538_, v_b_4539_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object* v_upperBound_4542_, lean_object* v_identicalImports_4543_, lean_object* v_inst_4544_, lean_object* v_R_4545_, lean_object* v_a_4546_, lean_object* v_b_4547_, lean_object* v_c_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(v_upperBound_4542_, v_identicalImports_4543_, v_inst_4544_, v_R_4545_, v_a_4546_, v_b_4547_, v_c_4548_);
lean_dec_ref(v_identicalImports_4543_);
lean_dec(v_upperBound_4542_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object* v_x_4556_){
_start:
{
lean_object* v_module_4557_; 
v_module_4557_ = lean_ctor_get(v_x_4556_, 0);
lean_inc(v_module_4557_);
return v_module_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object* v_x_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_Server_DirectImports_convertImportInfos___lam__0(v_x_4558_);
lean_dec_ref(v_x_4558_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object* v_x_4560_, lean_object* v_x_4561_){
_start:
{
if (lean_obj_tag(v_x_4561_) == 0)
{
return v_x_4560_;
}
else
{
lean_object* v_key_4562_; lean_object* v_value_4563_; lean_object* v_tail_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v_key_4562_ = lean_ctor_get(v_x_4561_, 0);
v_value_4563_ = lean_ctor_get(v_x_4561_, 1);
v_tail_4564_ = lean_ctor_get(v_x_4561_, 2);
lean_inc(v_value_4563_);
lean_inc(v_key_4562_);
v___x_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4565_, 0, v_key_4562_);
lean_ctor_set(v___x_4565_, 1, v_value_4563_);
v___x_4566_ = lean_array_push(v_x_4560_, v___x_4565_);
v_x_4560_ = v___x_4566_;
v_x_4561_ = v_tail_4564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object* v_x_4568_, lean_object* v_x_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_x_4568_, v_x_4569_);
lean_dec(v_x_4569_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object* v_as_4571_, size_t v_i_4572_, size_t v_stop_4573_, lean_object* v_b_4574_){
_start:
{
uint8_t v___x_4575_; 
v___x_4575_ = lean_usize_dec_eq(v_i_4572_, v_stop_4573_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; lean_object* v___x_4577_; size_t v___x_4578_; size_t v___x_4579_; 
v___x_4576_ = lean_array_uget_borrowed(v_as_4571_, v_i_4572_);
v___x_4577_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_b_4574_, v___x_4576_);
v___x_4578_ = ((size_t)1ULL);
v___x_4579_ = lean_usize_add(v_i_4572_, v___x_4578_);
v_i_4572_ = v___x_4579_;
v_b_4574_ = v___x_4577_;
goto _start;
}
else
{
return v_b_4574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object* v_as_4581_, lean_object* v_i_4582_, lean_object* v_stop_4583_, lean_object* v_b_4584_){
_start:
{
size_t v_i_boxed_4585_; size_t v_stop_boxed_4586_; lean_object* v_res_4587_; 
v_i_boxed_4585_ = lean_unbox_usize(v_i_4582_);
lean_dec(v_i_4582_);
v_stop_boxed_4586_ = lean_unbox_usize(v_stop_4583_);
lean_dec(v_stop_4583_);
v_res_4587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_as_4581_, v_i_boxed_4585_, v_stop_boxed_4586_, v_b_4584_);
lean_dec_ref(v_as_4581_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object* v_as_4588_, size_t v_i_4589_, size_t v_stop_4590_, lean_object* v_b_4591_){
_start:
{
uint8_t v___x_4593_; 
v___x_4593_ = lean_usize_dec_eq(v_i_4589_, v_stop_4590_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; lean_object* v_module_4595_; uint8_t v_isPrivate_4596_; uint8_t v_isAll_4597_; uint8_t v_isMeta_4598_; lean_object* v_module_4599_; lean_object* v___x_4600_; 
v___x_4594_ = lean_array_uget_borrowed(v_as_4588_, v_i_4589_);
v_module_4595_ = lean_ctor_get(v___x_4594_, 0);
v_isPrivate_4596_ = lean_ctor_get_uint8(v___x_4594_, sizeof(void*)*1);
v_isAll_4597_ = lean_ctor_get_uint8(v___x_4594_, sizeof(void*)*1 + 1);
v_isMeta_4598_ = lean_ctor_get_uint8(v___x_4594_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4595_);
v_module_4599_ = l_String_toName(v_module_4595_);
lean_inc(v_module_4599_);
v___x_4600_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4599_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v_a_4601_; lean_object* v_a_4603_; 
v_a_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc(v_a_4601_);
lean_dec_ref_known(v___x_4600_, 1);
if (lean_obj_tag(v_a_4601_) == 1)
{
lean_object* v_val_4607_; uint8_t v___y_4609_; 
v_val_4607_ = lean_ctor_get(v_a_4601_, 0);
lean_inc(v_val_4607_);
lean_dec_ref_known(v_a_4601_, 1);
if (v_isMeta_4598_ == 0)
{
uint8_t v___x_4612_; 
v___x_4612_ = 0;
v___y_4609_ = v___x_4612_;
goto v___jp_4608_;
}
else
{
uint8_t v___x_4613_; 
v___x_4613_ = 1;
v___y_4609_ = v___x_4613_;
goto v___jp_4608_;
}
v___jp_4608_:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4610_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4610_, 0, v_module_4599_);
lean_ctor_set(v___x_4610_, 1, v_val_4607_);
lean_ctor_set_uint8(v___x_4610_, sizeof(void*)*2, v_isAll_4597_);
lean_ctor_set_uint8(v___x_4610_, sizeof(void*)*2 + 1, v_isPrivate_4596_);
lean_ctor_set_uint8(v___x_4610_, sizeof(void*)*2 + 2, v___y_4609_);
v___x_4611_ = lean_array_push(v_b_4591_, v___x_4610_);
v_a_4603_ = v___x_4611_;
goto v___jp_4602_;
}
}
else
{
lean_dec(v_a_4601_);
lean_dec(v_module_4599_);
v_a_4603_ = v_b_4591_;
goto v___jp_4602_;
}
v___jp_4602_:
{
size_t v___x_4604_; size_t v___x_4605_; 
v___x_4604_ = ((size_t)1ULL);
v___x_4605_ = lean_usize_add(v_i_4589_, v___x_4604_);
v_i_4589_ = v___x_4605_;
v_b_4591_ = v_a_4603_;
goto _start;
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
lean_dec(v_module_4599_);
lean_dec_ref(v_b_4591_);
v_a_4614_ = lean_ctor_get(v___x_4600_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4600_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4600_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
else
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v_b_4591_);
return v___x_4622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object* v_as_4623_, lean_object* v_i_4624_, lean_object* v_stop_4625_, lean_object* v_b_4626_, lean_object* v___y_4627_){
_start:
{
size_t v_i_boxed_4628_; size_t v_stop_boxed_4629_; lean_object* v_res_4630_; 
v_i_boxed_4628_ = lean_unbox_usize(v_i_4624_);
lean_dec(v_i_4624_);
v_stop_boxed_4629_ = lean_unbox_usize(v_stop_4625_);
lean_dec(v_stop_4625_);
v_res_4630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4623_, v_i_boxed_4628_, v_stop_boxed_4629_, v_b_4626_);
lean_dec_ref(v_as_4623_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object* v_as_4631_, lean_object* v_start_4632_, lean_object* v_stop_4633_){
_start:
{
lean_object* v___x_4635_; uint8_t v___x_4636_; 
v___x_4635_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_4636_ = lean_nat_dec_lt(v_start_4632_, v_stop_4633_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; 
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4635_);
return v___x_4637_;
}
else
{
lean_object* v___x_4638_; uint8_t v___x_4639_; 
v___x_4638_ = lean_array_get_size(v_as_4631_);
v___x_4639_ = lean_nat_dec_le(v_stop_4633_, v___x_4638_);
if (v___x_4639_ == 0)
{
uint8_t v___x_4640_; 
v___x_4640_ = lean_nat_dec_lt(v_start_4632_, v___x_4638_);
if (v___x_4640_ == 0)
{
lean_object* v___x_4641_; 
v___x_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4641_, 0, v___x_4635_);
return v___x_4641_;
}
else
{
size_t v___x_4642_; size_t v___x_4643_; lean_object* v___x_4644_; 
v___x_4642_ = lean_usize_of_nat(v_start_4632_);
v___x_4643_ = lean_usize_of_nat(v___x_4638_);
v___x_4644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4631_, v___x_4642_, v___x_4643_, v___x_4635_);
return v___x_4644_;
}
}
else
{
size_t v___x_4645_; size_t v___x_4646_; lean_object* v___x_4647_; 
v___x_4645_ = lean_usize_of_nat(v_start_4632_);
v___x_4646_ = lean_usize_of_nat(v_stop_4633_);
v___x_4647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4631_, v___x_4645_, v___x_4646_, v___x_4635_);
return v___x_4647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object* v_as_4648_, lean_object* v_start_4649_, lean_object* v_stop_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_as_4648_, v_start_4649_, v_stop_4650_);
lean_dec(v_stop_4650_);
lean_dec(v_start_4649_);
lean_dec_ref(v_as_4648_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object* v_k_4653_, lean_object* v_v_4654_, lean_object* v_t_4655_){
_start:
{
if (lean_obj_tag(v_t_4655_) == 0)
{
lean_object* v_size_4656_; lean_object* v_k_4657_; lean_object* v_v_4658_; lean_object* v_l_4659_; lean_object* v_r_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4940_; 
v_size_4656_ = lean_ctor_get(v_t_4655_, 0);
v_k_4657_ = lean_ctor_get(v_t_4655_, 1);
v_v_4658_ = lean_ctor_get(v_t_4655_, 2);
v_l_4659_ = lean_ctor_get(v_t_4655_, 3);
v_r_4660_ = lean_ctor_get(v_t_4655_, 4);
v_isSharedCheck_4940_ = !lean_is_exclusive(v_t_4655_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4662_ = v_t_4655_;
v_isShared_4663_ = v_isSharedCheck_4940_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_r_4660_);
lean_inc(v_l_4659_);
lean_inc(v_v_4658_);
lean_inc(v_k_4657_);
lean_inc(v_size_4656_);
lean_dec(v_t_4655_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4940_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
uint8_t v___x_4664_; 
v___x_4664_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4653_, v_k_4657_);
switch(v___x_4664_)
{
case 0:
{
lean_object* v_impl_4665_; lean_object* v___x_4666_; 
lean_dec(v_size_4656_);
v_impl_4665_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4653_, v_v_4654_, v_l_4659_);
v___x_4666_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4660_) == 0)
{
lean_object* v_size_4667_; lean_object* v_size_4668_; lean_object* v_k_4669_; lean_object* v_v_4670_; lean_object* v_l_4671_; lean_object* v_r_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; 
v_size_4667_ = lean_ctor_get(v_r_4660_, 0);
v_size_4668_ = lean_ctor_get(v_impl_4665_, 0);
lean_inc(v_size_4668_);
v_k_4669_ = lean_ctor_get(v_impl_4665_, 1);
lean_inc(v_k_4669_);
v_v_4670_ = lean_ctor_get(v_impl_4665_, 2);
lean_inc(v_v_4670_);
v_l_4671_ = lean_ctor_get(v_impl_4665_, 3);
lean_inc(v_l_4671_);
v_r_4672_ = lean_ctor_get(v_impl_4665_, 4);
lean_inc(v_r_4672_);
v___x_4673_ = lean_unsigned_to_nat(3u);
v___x_4674_ = lean_nat_mul(v___x_4673_, v_size_4667_);
v___x_4675_ = lean_nat_dec_lt(v___x_4674_, v_size_4668_);
lean_dec(v___x_4674_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
lean_dec(v_r_4672_);
lean_dec(v_l_4671_);
lean_dec(v_v_4670_);
lean_dec(v_k_4669_);
v___x_4676_ = lean_nat_add(v___x_4666_, v_size_4668_);
lean_dec(v_size_4668_);
v___x_4677_ = lean_nat_add(v___x_4676_, v_size_4667_);
lean_dec(v___x_4676_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 3, v_impl_4665_);
lean_ctor_set(v___x_4662_, 0, v___x_4677_);
v___x_4679_ = v___x_4662_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4680_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4680_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4680_, 3, v_impl_4665_);
lean_ctor_set(v_reuseFailAlloc_4680_, 4, v_r_4660_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
else
{
lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4746_; 
v_isSharedCheck_4746_ = !lean_is_exclusive(v_impl_4665_);
if (v_isSharedCheck_4746_ == 0)
{
lean_object* v_unused_4747_; lean_object* v_unused_4748_; lean_object* v_unused_4749_; lean_object* v_unused_4750_; lean_object* v_unused_4751_; 
v_unused_4747_ = lean_ctor_get(v_impl_4665_, 4);
lean_dec(v_unused_4747_);
v_unused_4748_ = lean_ctor_get(v_impl_4665_, 3);
lean_dec(v_unused_4748_);
v_unused_4749_ = lean_ctor_get(v_impl_4665_, 2);
lean_dec(v_unused_4749_);
v_unused_4750_ = lean_ctor_get(v_impl_4665_, 1);
lean_dec(v_unused_4750_);
v_unused_4751_ = lean_ctor_get(v_impl_4665_, 0);
lean_dec(v_unused_4751_);
v___x_4682_ = v_impl_4665_;
v_isShared_4683_ = v_isSharedCheck_4746_;
goto v_resetjp_4681_;
}
else
{
lean_dec(v_impl_4665_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4746_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v_size_4684_; lean_object* v_size_4685_; lean_object* v_k_4686_; lean_object* v_v_4687_; lean_object* v_l_4688_; lean_object* v_r_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; 
v_size_4684_ = lean_ctor_get(v_l_4671_, 0);
v_size_4685_ = lean_ctor_get(v_r_4672_, 0);
v_k_4686_ = lean_ctor_get(v_r_4672_, 1);
v_v_4687_ = lean_ctor_get(v_r_4672_, 2);
v_l_4688_ = lean_ctor_get(v_r_4672_, 3);
v_r_4689_ = lean_ctor_get(v_r_4672_, 4);
v___x_4690_ = lean_unsigned_to_nat(2u);
v___x_4691_ = lean_nat_mul(v___x_4690_, v_size_4684_);
v___x_4692_ = lean_nat_dec_lt(v_size_4685_, v___x_4691_);
lean_dec(v___x_4691_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4721_; 
lean_inc(v_r_4689_);
lean_inc(v_l_4688_);
lean_inc(v_v_4687_);
lean_inc(v_k_4686_);
v_isSharedCheck_4721_ = !lean_is_exclusive(v_r_4672_);
if (v_isSharedCheck_4721_ == 0)
{
lean_object* v_unused_4722_; lean_object* v_unused_4723_; lean_object* v_unused_4724_; lean_object* v_unused_4725_; lean_object* v_unused_4726_; 
v_unused_4722_ = lean_ctor_get(v_r_4672_, 4);
lean_dec(v_unused_4722_);
v_unused_4723_ = lean_ctor_get(v_r_4672_, 3);
lean_dec(v_unused_4723_);
v_unused_4724_ = lean_ctor_get(v_r_4672_, 2);
lean_dec(v_unused_4724_);
v_unused_4725_ = lean_ctor_get(v_r_4672_, 1);
lean_dec(v_unused_4725_);
v_unused_4726_ = lean_ctor_get(v_r_4672_, 0);
lean_dec(v_unused_4726_);
v___x_4694_ = v_r_4672_;
v_isShared_4695_ = v_isSharedCheck_4721_;
goto v_resetjp_4693_;
}
else
{
lean_dec(v_r_4672_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4721_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___y_4699_; lean_object* v___y_4700_; lean_object* v___y_4701_; lean_object* v___x_4709_; lean_object* v___y_4711_; 
v___x_4696_ = lean_nat_add(v___x_4666_, v_size_4668_);
lean_dec(v_size_4668_);
v___x_4697_ = lean_nat_add(v___x_4696_, v_size_4667_);
lean_dec(v___x_4696_);
v___x_4709_ = lean_nat_add(v___x_4666_, v_size_4684_);
if (lean_obj_tag(v_l_4688_) == 0)
{
lean_object* v_size_4719_; 
v_size_4719_ = lean_ctor_get(v_l_4688_, 0);
lean_inc(v_size_4719_);
v___y_4711_ = v_size_4719_;
goto v___jp_4710_;
}
else
{
lean_object* v___x_4720_; 
v___x_4720_ = lean_unsigned_to_nat(0u);
v___y_4711_ = v___x_4720_;
goto v___jp_4710_;
}
v___jp_4698_:
{
lean_object* v___x_4702_; lean_object* v___x_4704_; 
v___x_4702_ = lean_nat_add(v___y_4699_, v___y_4701_);
lean_dec(v___y_4701_);
lean_dec(v___y_4699_);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 4, v_r_4660_);
lean_ctor_set(v___x_4694_, 3, v_r_4689_);
lean_ctor_set(v___x_4694_, 2, v_v_4658_);
lean_ctor_set(v___x_4694_, 1, v_k_4657_);
lean_ctor_set(v___x_4694_, 0, v___x_4702_);
v___x_4704_ = v___x_4694_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4702_);
lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4708_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4708_, 3, v_r_4689_);
lean_ctor_set(v_reuseFailAlloc_4708_, 4, v_r_4660_);
v___x_4704_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
lean_object* v___x_4706_; 
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 4, v___x_4704_);
lean_ctor_set(v___x_4682_, 3, v___y_4700_);
lean_ctor_set(v___x_4682_, 2, v_v_4687_);
lean_ctor_set(v___x_4682_, 1, v_k_4686_);
lean_ctor_set(v___x_4682_, 0, v___x_4697_);
v___x_4706_ = v___x_4682_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4707_, 1, v_k_4686_);
lean_ctor_set(v_reuseFailAlloc_4707_, 2, v_v_4687_);
lean_ctor_set(v_reuseFailAlloc_4707_, 3, v___y_4700_);
lean_ctor_set(v_reuseFailAlloc_4707_, 4, v___x_4704_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
v___jp_4710_:
{
lean_object* v___x_4712_; lean_object* v___x_4714_; 
v___x_4712_ = lean_nat_add(v___x_4709_, v___y_4711_);
lean_dec(v___y_4711_);
lean_dec(v___x_4709_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v_l_4688_);
lean_ctor_set(v___x_4662_, 3, v_l_4671_);
lean_ctor_set(v___x_4662_, 2, v_v_4670_);
lean_ctor_set(v___x_4662_, 1, v_k_4669_);
lean_ctor_set(v___x_4662_, 0, v___x_4712_);
v___x_4714_ = v___x_4662_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v___x_4712_);
lean_ctor_set(v_reuseFailAlloc_4718_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4718_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4718_, 3, v_l_4671_);
lean_ctor_set(v_reuseFailAlloc_4718_, 4, v_l_4688_);
v___x_4714_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
lean_object* v___x_4715_; 
v___x_4715_ = lean_nat_add(v___x_4666_, v_size_4667_);
if (lean_obj_tag(v_r_4689_) == 0)
{
lean_object* v_size_4716_; 
v_size_4716_ = lean_ctor_get(v_r_4689_, 0);
lean_inc(v_size_4716_);
v___y_4699_ = v___x_4715_;
v___y_4700_ = v___x_4714_;
v___y_4701_ = v_size_4716_;
goto v___jp_4698_;
}
else
{
lean_object* v___x_4717_; 
v___x_4717_ = lean_unsigned_to_nat(0u);
v___y_4699_ = v___x_4715_;
v___y_4700_ = v___x_4714_;
v___y_4701_ = v___x_4717_;
goto v___jp_4698_;
}
}
}
}
}
else
{
lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4732_; 
lean_del_object(v___x_4662_);
v___x_4727_ = lean_nat_add(v___x_4666_, v_size_4668_);
lean_dec(v_size_4668_);
v___x_4728_ = lean_nat_add(v___x_4727_, v_size_4667_);
lean_dec(v___x_4727_);
v___x_4729_ = lean_nat_add(v___x_4666_, v_size_4667_);
v___x_4730_ = lean_nat_add(v___x_4729_, v_size_4685_);
lean_dec(v___x_4729_);
lean_inc_ref(v_r_4660_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 4, v_r_4660_);
lean_ctor_set(v___x_4682_, 3, v_r_4672_);
lean_ctor_set(v___x_4682_, 2, v_v_4658_);
lean_ctor_set(v___x_4682_, 1, v_k_4657_);
lean_ctor_set(v___x_4682_, 0, v___x_4730_);
v___x_4732_ = v___x_4682_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4730_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4745_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4745_, 3, v_r_4672_);
lean_ctor_set(v_reuseFailAlloc_4745_, 4, v_r_4660_);
v___x_4732_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
v_isSharedCheck_4739_ = !lean_is_exclusive(v_r_4660_);
if (v_isSharedCheck_4739_ == 0)
{
lean_object* v_unused_4740_; lean_object* v_unused_4741_; lean_object* v_unused_4742_; lean_object* v_unused_4743_; lean_object* v_unused_4744_; 
v_unused_4740_ = lean_ctor_get(v_r_4660_, 4);
lean_dec(v_unused_4740_);
v_unused_4741_ = lean_ctor_get(v_r_4660_, 3);
lean_dec(v_unused_4741_);
v_unused_4742_ = lean_ctor_get(v_r_4660_, 2);
lean_dec(v_unused_4742_);
v_unused_4743_ = lean_ctor_get(v_r_4660_, 1);
lean_dec(v_unused_4743_);
v_unused_4744_ = lean_ctor_get(v_r_4660_, 0);
lean_dec(v_unused_4744_);
v___x_4734_ = v_r_4660_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_dec(v_r_4660_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 4, v___x_4732_);
lean_ctor_set(v___x_4734_, 3, v_l_4671_);
lean_ctor_set(v___x_4734_, 2, v_v_4670_);
lean_ctor_set(v___x_4734_, 1, v_k_4669_);
lean_ctor_set(v___x_4734_, 0, v___x_4728_);
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v___x_4728_);
lean_ctor_set(v_reuseFailAlloc_4738_, 1, v_k_4669_);
lean_ctor_set(v_reuseFailAlloc_4738_, 2, v_v_4670_);
lean_ctor_set(v_reuseFailAlloc_4738_, 3, v_l_4671_);
lean_ctor_set(v_reuseFailAlloc_4738_, 4, v___x_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4752_; 
v_l_4752_ = lean_ctor_get(v_impl_4665_, 3);
lean_inc(v_l_4752_);
if (lean_obj_tag(v_l_4752_) == 0)
{
lean_object* v_r_4753_; lean_object* v_k_4754_; lean_object* v_v_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4766_; 
v_r_4753_ = lean_ctor_get(v_impl_4665_, 4);
v_k_4754_ = lean_ctor_get(v_impl_4665_, 1);
v_v_4755_ = lean_ctor_get(v_impl_4665_, 2);
v_isSharedCheck_4766_ = !lean_is_exclusive(v_impl_4665_);
if (v_isSharedCheck_4766_ == 0)
{
lean_object* v_unused_4767_; lean_object* v_unused_4768_; 
v_unused_4767_ = lean_ctor_get(v_impl_4665_, 3);
lean_dec(v_unused_4767_);
v_unused_4768_ = lean_ctor_get(v_impl_4665_, 0);
lean_dec(v_unused_4768_);
v___x_4757_ = v_impl_4665_;
v_isShared_4758_ = v_isSharedCheck_4766_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_r_4753_);
lean_inc(v_v_4755_);
lean_inc(v_k_4754_);
lean_dec(v_impl_4665_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4766_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4759_; lean_object* v___x_4761_; 
v___x_4759_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4753_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set(v___x_4757_, 3, v_r_4753_);
lean_ctor_set(v___x_4757_, 2, v_v_4658_);
lean_ctor_set(v___x_4757_, 1, v_k_4657_);
lean_ctor_set(v___x_4757_, 0, v___x_4666_);
v___x_4761_ = v___x_4757_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4666_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4765_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4765_, 3, v_r_4753_);
lean_ctor_set(v_reuseFailAlloc_4765_, 4, v_r_4753_);
v___x_4761_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
lean_object* v___x_4763_; 
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v___x_4761_);
lean_ctor_set(v___x_4662_, 3, v_l_4752_);
lean_ctor_set(v___x_4662_, 2, v_v_4755_);
lean_ctor_set(v___x_4662_, 1, v_k_4754_);
lean_ctor_set(v___x_4662_, 0, v___x_4759_);
v___x_4763_ = v___x_4662_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4759_);
lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_k_4754_);
lean_ctor_set(v_reuseFailAlloc_4764_, 2, v_v_4755_);
lean_ctor_set(v_reuseFailAlloc_4764_, 3, v_l_4752_);
lean_ctor_set(v_reuseFailAlloc_4764_, 4, v___x_4761_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
else
{
lean_object* v_r_4769_; 
v_r_4769_ = lean_ctor_get(v_impl_4665_, 4);
lean_inc(v_r_4769_);
if (lean_obj_tag(v_r_4769_) == 0)
{
lean_object* v_k_4770_; lean_object* v_v_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4794_; 
v_k_4770_ = lean_ctor_get(v_impl_4665_, 1);
v_v_4771_ = lean_ctor_get(v_impl_4665_, 2);
v_isSharedCheck_4794_ = !lean_is_exclusive(v_impl_4665_);
if (v_isSharedCheck_4794_ == 0)
{
lean_object* v_unused_4795_; lean_object* v_unused_4796_; lean_object* v_unused_4797_; 
v_unused_4795_ = lean_ctor_get(v_impl_4665_, 4);
lean_dec(v_unused_4795_);
v_unused_4796_ = lean_ctor_get(v_impl_4665_, 3);
lean_dec(v_unused_4796_);
v_unused_4797_ = lean_ctor_get(v_impl_4665_, 0);
lean_dec(v_unused_4797_);
v___x_4773_ = v_impl_4665_;
v_isShared_4774_ = v_isSharedCheck_4794_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_v_4771_);
lean_inc(v_k_4770_);
lean_dec(v_impl_4665_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4794_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v_k_4775_; lean_object* v_v_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4790_; 
v_k_4775_ = lean_ctor_get(v_r_4769_, 1);
v_v_4776_ = lean_ctor_get(v_r_4769_, 2);
v_isSharedCheck_4790_ = !lean_is_exclusive(v_r_4769_);
if (v_isSharedCheck_4790_ == 0)
{
lean_object* v_unused_4791_; lean_object* v_unused_4792_; lean_object* v_unused_4793_; 
v_unused_4791_ = lean_ctor_get(v_r_4769_, 4);
lean_dec(v_unused_4791_);
v_unused_4792_ = lean_ctor_get(v_r_4769_, 3);
lean_dec(v_unused_4792_);
v_unused_4793_ = lean_ctor_get(v_r_4769_, 0);
lean_dec(v_unused_4793_);
v___x_4778_ = v_r_4769_;
v_isShared_4779_ = v_isSharedCheck_4790_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_v_4776_);
lean_inc(v_k_4775_);
lean_dec(v_r_4769_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4790_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4780_; lean_object* v___x_4782_; 
v___x_4780_ = lean_unsigned_to_nat(3u);
if (v_isShared_4779_ == 0)
{
lean_ctor_set(v___x_4778_, 4, v_l_4752_);
lean_ctor_set(v___x_4778_, 3, v_l_4752_);
lean_ctor_set(v___x_4778_, 2, v_v_4771_);
lean_ctor_set(v___x_4778_, 1, v_k_4770_);
lean_ctor_set(v___x_4778_, 0, v___x_4666_);
v___x_4782_ = v___x_4778_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4666_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_k_4770_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_v_4771_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v_l_4752_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v_l_4752_);
v___x_4782_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
lean_object* v___x_4784_; 
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 4, v_l_4752_);
lean_ctor_set(v___x_4773_, 2, v_v_4658_);
lean_ctor_set(v___x_4773_, 1, v_k_4657_);
lean_ctor_set(v___x_4773_, 0, v___x_4666_);
v___x_4784_ = v___x_4773_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4666_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4788_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4788_, 3, v_l_4752_);
lean_ctor_set(v_reuseFailAlloc_4788_, 4, v_l_4752_);
v___x_4784_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
lean_object* v___x_4786_; 
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v___x_4784_);
lean_ctor_set(v___x_4662_, 3, v___x_4782_);
lean_ctor_set(v___x_4662_, 2, v_v_4776_);
lean_ctor_set(v___x_4662_, 1, v_k_4775_);
lean_ctor_set(v___x_4662_, 0, v___x_4780_);
v___x_4786_ = v___x_4662_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4780_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v_k_4775_);
lean_ctor_set(v_reuseFailAlloc_4787_, 2, v_v_4776_);
lean_ctor_set(v_reuseFailAlloc_4787_, 3, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4787_, 4, v___x_4784_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
}
else
{
lean_object* v___x_4798_; lean_object* v___x_4800_; 
v___x_4798_ = lean_unsigned_to_nat(2u);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v_r_4769_);
lean_ctor_set(v___x_4662_, 3, v_impl_4665_);
lean_ctor_set(v___x_4662_, 0, v___x_4798_);
v___x_4800_ = v___x_4662_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4798_);
lean_ctor_set(v_reuseFailAlloc_4801_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4801_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4801_, 3, v_impl_4665_);
lean_ctor_set(v_reuseFailAlloc_4801_, 4, v_r_4769_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4803_; 
lean_dec(v_v_4658_);
lean_dec(v_k_4657_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 2, v_v_4654_);
lean_ctor_set(v___x_4662_, 1, v_k_4653_);
v___x_4803_ = v___x_4662_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_size_4656_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_k_4653_);
lean_ctor_set(v_reuseFailAlloc_4804_, 2, v_v_4654_);
lean_ctor_set(v_reuseFailAlloc_4804_, 3, v_l_4659_);
lean_ctor_set(v_reuseFailAlloc_4804_, 4, v_r_4660_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
default: 
{
lean_object* v_impl_4805_; lean_object* v___x_4806_; 
lean_dec(v_size_4656_);
v_impl_4805_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4653_, v_v_4654_, v_r_4660_);
v___x_4806_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4659_) == 0)
{
lean_object* v_size_4807_; lean_object* v_size_4808_; lean_object* v_k_4809_; lean_object* v_v_4810_; lean_object* v_l_4811_; lean_object* v_r_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; 
v_size_4807_ = lean_ctor_get(v_l_4659_, 0);
v_size_4808_ = lean_ctor_get(v_impl_4805_, 0);
lean_inc(v_size_4808_);
v_k_4809_ = lean_ctor_get(v_impl_4805_, 1);
lean_inc(v_k_4809_);
v_v_4810_ = lean_ctor_get(v_impl_4805_, 2);
lean_inc(v_v_4810_);
v_l_4811_ = lean_ctor_get(v_impl_4805_, 3);
lean_inc(v_l_4811_);
v_r_4812_ = lean_ctor_get(v_impl_4805_, 4);
lean_inc(v_r_4812_);
v___x_4813_ = lean_unsigned_to_nat(3u);
v___x_4814_ = lean_nat_mul(v___x_4813_, v_size_4807_);
v___x_4815_ = lean_nat_dec_lt(v___x_4814_, v_size_4808_);
lean_dec(v___x_4814_);
if (v___x_4815_ == 0)
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4819_; 
lean_dec(v_r_4812_);
lean_dec(v_l_4811_);
lean_dec(v_v_4810_);
lean_dec(v_k_4809_);
v___x_4816_ = lean_nat_add(v___x_4806_, v_size_4807_);
v___x_4817_ = lean_nat_add(v___x_4816_, v_size_4808_);
lean_dec(v_size_4808_);
lean_dec(v___x_4816_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v_impl_4805_);
lean_ctor_set(v___x_4662_, 0, v___x_4817_);
v___x_4819_ = v___x_4662_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4817_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4820_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4820_, 3, v_l_4659_);
lean_ctor_set(v_reuseFailAlloc_4820_, 4, v_impl_4805_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
else
{
lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4884_; 
v_isSharedCheck_4884_ = !lean_is_exclusive(v_impl_4805_);
if (v_isSharedCheck_4884_ == 0)
{
lean_object* v_unused_4885_; lean_object* v_unused_4886_; lean_object* v_unused_4887_; lean_object* v_unused_4888_; lean_object* v_unused_4889_; 
v_unused_4885_ = lean_ctor_get(v_impl_4805_, 4);
lean_dec(v_unused_4885_);
v_unused_4886_ = lean_ctor_get(v_impl_4805_, 3);
lean_dec(v_unused_4886_);
v_unused_4887_ = lean_ctor_get(v_impl_4805_, 2);
lean_dec(v_unused_4887_);
v_unused_4888_ = lean_ctor_get(v_impl_4805_, 1);
lean_dec(v_unused_4888_);
v_unused_4889_ = lean_ctor_get(v_impl_4805_, 0);
lean_dec(v_unused_4889_);
v___x_4822_ = v_impl_4805_;
v_isShared_4823_ = v_isSharedCheck_4884_;
goto v_resetjp_4821_;
}
else
{
lean_dec(v_impl_4805_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4884_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v_size_4824_; lean_object* v_k_4825_; lean_object* v_v_4826_; lean_object* v_l_4827_; lean_object* v_r_4828_; lean_object* v_size_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; 
v_size_4824_ = lean_ctor_get(v_l_4811_, 0);
v_k_4825_ = lean_ctor_get(v_l_4811_, 1);
v_v_4826_ = lean_ctor_get(v_l_4811_, 2);
v_l_4827_ = lean_ctor_get(v_l_4811_, 3);
v_r_4828_ = lean_ctor_get(v_l_4811_, 4);
v_size_4829_ = lean_ctor_get(v_r_4812_, 0);
v___x_4830_ = lean_unsigned_to_nat(2u);
v___x_4831_ = lean_nat_mul(v___x_4830_, v_size_4829_);
v___x_4832_ = lean_nat_dec_lt(v_size_4824_, v___x_4831_);
lean_dec(v___x_4831_);
if (v___x_4832_ == 0)
{
lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4860_; 
lean_inc(v_r_4828_);
lean_inc(v_l_4827_);
lean_inc(v_v_4826_);
lean_inc(v_k_4825_);
v_isSharedCheck_4860_ = !lean_is_exclusive(v_l_4811_);
if (v_isSharedCheck_4860_ == 0)
{
lean_object* v_unused_4861_; lean_object* v_unused_4862_; lean_object* v_unused_4863_; lean_object* v_unused_4864_; lean_object* v_unused_4865_; 
v_unused_4861_ = lean_ctor_get(v_l_4811_, 4);
lean_dec(v_unused_4861_);
v_unused_4862_ = lean_ctor_get(v_l_4811_, 3);
lean_dec(v_unused_4862_);
v_unused_4863_ = lean_ctor_get(v_l_4811_, 2);
lean_dec(v_unused_4863_);
v_unused_4864_ = lean_ctor_get(v_l_4811_, 1);
lean_dec(v_unused_4864_);
v_unused_4865_ = lean_ctor_get(v_l_4811_, 0);
lean_dec(v_unused_4865_);
v___x_4834_ = v_l_4811_;
v_isShared_4835_ = v_isSharedCheck_4860_;
goto v_resetjp_4833_;
}
else
{
lean_dec(v_l_4811_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4860_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___y_4839_; lean_object* v___y_4840_; lean_object* v___y_4841_; lean_object* v___y_4850_; 
v___x_4836_ = lean_nat_add(v___x_4806_, v_size_4807_);
v___x_4837_ = lean_nat_add(v___x_4836_, v_size_4808_);
lean_dec(v_size_4808_);
if (lean_obj_tag(v_l_4827_) == 0)
{
lean_object* v_size_4858_; 
v_size_4858_ = lean_ctor_get(v_l_4827_, 0);
lean_inc(v_size_4858_);
v___y_4850_ = v_size_4858_;
goto v___jp_4849_;
}
else
{
lean_object* v___x_4859_; 
v___x_4859_ = lean_unsigned_to_nat(0u);
v___y_4850_ = v___x_4859_;
goto v___jp_4849_;
}
v___jp_4838_:
{
lean_object* v___x_4842_; lean_object* v___x_4844_; 
v___x_4842_ = lean_nat_add(v___y_4840_, v___y_4841_);
lean_dec(v___y_4841_);
lean_dec(v___y_4840_);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 4, v_r_4812_);
lean_ctor_set(v___x_4834_, 3, v_r_4828_);
lean_ctor_set(v___x_4834_, 2, v_v_4810_);
lean_ctor_set(v___x_4834_, 1, v_k_4809_);
lean_ctor_set(v___x_4834_, 0, v___x_4842_);
v___x_4844_ = v___x_4834_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4842_);
lean_ctor_set(v_reuseFailAlloc_4848_, 1, v_k_4809_);
lean_ctor_set(v_reuseFailAlloc_4848_, 2, v_v_4810_);
lean_ctor_set(v_reuseFailAlloc_4848_, 3, v_r_4828_);
lean_ctor_set(v_reuseFailAlloc_4848_, 4, v_r_4812_);
v___x_4844_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
lean_object* v___x_4846_; 
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 4, v___x_4844_);
lean_ctor_set(v___x_4822_, 3, v___y_4839_);
lean_ctor_set(v___x_4822_, 2, v_v_4826_);
lean_ctor_set(v___x_4822_, 1, v_k_4825_);
lean_ctor_set(v___x_4822_, 0, v___x_4837_);
v___x_4846_ = v___x_4822_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4837_);
lean_ctor_set(v_reuseFailAlloc_4847_, 1, v_k_4825_);
lean_ctor_set(v_reuseFailAlloc_4847_, 2, v_v_4826_);
lean_ctor_set(v_reuseFailAlloc_4847_, 3, v___y_4839_);
lean_ctor_set(v_reuseFailAlloc_4847_, 4, v___x_4844_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
v___jp_4849_:
{
lean_object* v___x_4851_; lean_object* v___x_4853_; 
v___x_4851_ = lean_nat_add(v___x_4836_, v___y_4850_);
lean_dec(v___y_4850_);
lean_dec(v___x_4836_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v_l_4827_);
lean_ctor_set(v___x_4662_, 0, v___x_4851_);
v___x_4853_ = v___x_4662_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4851_);
lean_ctor_set(v_reuseFailAlloc_4857_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4857_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4857_, 3, v_l_4659_);
lean_ctor_set(v_reuseFailAlloc_4857_, 4, v_l_4827_);
v___x_4853_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
lean_object* v___x_4854_; 
v___x_4854_ = lean_nat_add(v___x_4806_, v_size_4829_);
if (lean_obj_tag(v_r_4828_) == 0)
{
lean_object* v_size_4855_; 
v_size_4855_ = lean_ctor_get(v_r_4828_, 0);
lean_inc(v_size_4855_);
v___y_4839_ = v___x_4853_;
v___y_4840_ = v___x_4854_;
v___y_4841_ = v_size_4855_;
goto v___jp_4838_;
}
else
{
lean_object* v___x_4856_; 
v___x_4856_ = lean_unsigned_to_nat(0u);
v___y_4839_ = v___x_4853_;
v___y_4840_ = v___x_4854_;
v___y_4841_ = v___x_4856_;
goto v___jp_4838_;
}
}
}
}
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4870_; 
lean_del_object(v___x_4662_);
v___x_4866_ = lean_nat_add(v___x_4806_, v_size_4807_);
v___x_4867_ = lean_nat_add(v___x_4866_, v_size_4808_);
lean_dec(v_size_4808_);
v___x_4868_ = lean_nat_add(v___x_4866_, v_size_4824_);
lean_dec(v___x_4866_);
lean_inc_ref(v_l_4659_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 4, v_l_4811_);
lean_ctor_set(v___x_4822_, 3, v_l_4659_);
lean_ctor_set(v___x_4822_, 2, v_v_4658_);
lean_ctor_set(v___x_4822_, 1, v_k_4657_);
lean_ctor_set(v___x_4822_, 0, v___x_4868_);
v___x_4870_ = v___x_4822_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4868_);
lean_ctor_set(v_reuseFailAlloc_4883_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4883_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4883_, 3, v_l_4659_);
lean_ctor_set(v_reuseFailAlloc_4883_, 4, v_l_4811_);
v___x_4870_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4877_; 
v_isSharedCheck_4877_ = !lean_is_exclusive(v_l_4659_);
if (v_isSharedCheck_4877_ == 0)
{
lean_object* v_unused_4878_; lean_object* v_unused_4879_; lean_object* v_unused_4880_; lean_object* v_unused_4881_; lean_object* v_unused_4882_; 
v_unused_4878_ = lean_ctor_get(v_l_4659_, 4);
lean_dec(v_unused_4878_);
v_unused_4879_ = lean_ctor_get(v_l_4659_, 3);
lean_dec(v_unused_4879_);
v_unused_4880_ = lean_ctor_get(v_l_4659_, 2);
lean_dec(v_unused_4880_);
v_unused_4881_ = lean_ctor_get(v_l_4659_, 1);
lean_dec(v_unused_4881_);
v_unused_4882_ = lean_ctor_get(v_l_4659_, 0);
lean_dec(v_unused_4882_);
v___x_4872_ = v_l_4659_;
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
else
{
lean_dec(v_l_4659_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4875_; 
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 4, v_r_4812_);
lean_ctor_set(v___x_4872_, 3, v___x_4870_);
lean_ctor_set(v___x_4872_, 2, v_v_4810_);
lean_ctor_set(v___x_4872_, 1, v_k_4809_);
lean_ctor_set(v___x_4872_, 0, v___x_4867_);
v___x_4875_ = v___x_4872_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4867_);
lean_ctor_set(v_reuseFailAlloc_4876_, 1, v_k_4809_);
lean_ctor_set(v_reuseFailAlloc_4876_, 2, v_v_4810_);
lean_ctor_set(v_reuseFailAlloc_4876_, 3, v___x_4870_);
lean_ctor_set(v_reuseFailAlloc_4876_, 4, v_r_4812_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4890_; 
v_l_4890_ = lean_ctor_get(v_impl_4805_, 3);
lean_inc(v_l_4890_);
if (lean_obj_tag(v_l_4890_) == 0)
{
lean_object* v_r_4891_; lean_object* v_k_4892_; lean_object* v_v_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4916_; 
v_r_4891_ = lean_ctor_get(v_impl_4805_, 4);
v_k_4892_ = lean_ctor_get(v_impl_4805_, 1);
v_v_4893_ = lean_ctor_get(v_impl_4805_, 2);
v_isSharedCheck_4916_ = !lean_is_exclusive(v_impl_4805_);
if (v_isSharedCheck_4916_ == 0)
{
lean_object* v_unused_4917_; lean_object* v_unused_4918_; 
v_unused_4917_ = lean_ctor_get(v_impl_4805_, 3);
lean_dec(v_unused_4917_);
v_unused_4918_ = lean_ctor_get(v_impl_4805_, 0);
lean_dec(v_unused_4918_);
v___x_4895_ = v_impl_4805_;
v_isShared_4896_ = v_isSharedCheck_4916_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_r_4891_);
lean_inc(v_v_4893_);
lean_inc(v_k_4892_);
lean_dec(v_impl_4805_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4916_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v_k_4897_; lean_object* v_v_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4912_; 
v_k_4897_ = lean_ctor_get(v_l_4890_, 1);
v_v_4898_ = lean_ctor_get(v_l_4890_, 2);
v_isSharedCheck_4912_ = !lean_is_exclusive(v_l_4890_);
if (v_isSharedCheck_4912_ == 0)
{
lean_object* v_unused_4913_; lean_object* v_unused_4914_; lean_object* v_unused_4915_; 
v_unused_4913_ = lean_ctor_get(v_l_4890_, 4);
lean_dec(v_unused_4913_);
v_unused_4914_ = lean_ctor_get(v_l_4890_, 3);
lean_dec(v_unused_4914_);
v_unused_4915_ = lean_ctor_get(v_l_4890_, 0);
lean_dec(v_unused_4915_);
v___x_4900_ = v_l_4890_;
v_isShared_4901_ = v_isSharedCheck_4912_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_v_4898_);
lean_inc(v_k_4897_);
lean_dec(v_l_4890_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4912_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4902_; lean_object* v___x_4904_; 
v___x_4902_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4891_, 2);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 4, v_r_4891_);
lean_ctor_set(v___x_4900_, 3, v_r_4891_);
lean_ctor_set(v___x_4900_, 2, v_v_4658_);
lean_ctor_set(v___x_4900_, 1, v_k_4657_);
lean_ctor_set(v___x_4900_, 0, v___x_4806_);
v___x_4904_ = v___x_4900_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4806_);
lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4911_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4911_, 3, v_r_4891_);
lean_ctor_set(v_reuseFailAlloc_4911_, 4, v_r_4891_);
v___x_4904_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
lean_object* v___x_4906_; 
lean_inc(v_r_4891_);
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 3, v_r_4891_);
lean_ctor_set(v___x_4895_, 0, v___x_4806_);
v___x_4906_ = v___x_4895_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4806_);
lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_k_4892_);
lean_ctor_set(v_reuseFailAlloc_4910_, 2, v_v_4893_);
lean_ctor_set(v_reuseFailAlloc_4910_, 3, v_r_4891_);
lean_ctor_set(v_reuseFailAlloc_4910_, 4, v_r_4891_);
v___x_4906_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4908_; 
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v___x_4906_);
lean_ctor_set(v___x_4662_, 3, v___x_4904_);
lean_ctor_set(v___x_4662_, 2, v_v_4898_);
lean_ctor_set(v___x_4662_, 1, v_k_4897_);
lean_ctor_set(v___x_4662_, 0, v___x_4902_);
v___x_4908_ = v___x_4662_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4902_);
lean_ctor_set(v_reuseFailAlloc_4909_, 1, v_k_4897_);
lean_ctor_set(v_reuseFailAlloc_4909_, 2, v_v_4898_);
lean_ctor_set(v_reuseFailAlloc_4909_, 3, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4909_, 4, v___x_4906_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
}
}
else
{
lean_object* v_r_4919_; 
v_r_4919_ = lean_ctor_get(v_impl_4805_, 4);
lean_inc(v_r_4919_);
if (lean_obj_tag(v_r_4919_) == 0)
{
lean_object* v_k_4920_; lean_object* v_v_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4932_; 
v_k_4920_ = lean_ctor_get(v_impl_4805_, 1);
v_v_4921_ = lean_ctor_get(v_impl_4805_, 2);
v_isSharedCheck_4932_ = !lean_is_exclusive(v_impl_4805_);
if (v_isSharedCheck_4932_ == 0)
{
lean_object* v_unused_4933_; lean_object* v_unused_4934_; lean_object* v_unused_4935_; 
v_unused_4933_ = lean_ctor_get(v_impl_4805_, 4);
lean_dec(v_unused_4933_);
v_unused_4934_ = lean_ctor_get(v_impl_4805_, 3);
lean_dec(v_unused_4934_);
v_unused_4935_ = lean_ctor_get(v_impl_4805_, 0);
lean_dec(v_unused_4935_);
v___x_4923_ = v_impl_4805_;
v_isShared_4924_ = v_isSharedCheck_4932_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_v_4921_);
lean_inc(v_k_4920_);
lean_dec(v_impl_4805_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4932_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4925_; lean_object* v___x_4927_; 
v___x_4925_ = lean_unsigned_to_nat(3u);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 4, v_l_4890_);
lean_ctor_set(v___x_4923_, 2, v_v_4658_);
lean_ctor_set(v___x_4923_, 1, v_k_4657_);
lean_ctor_set(v___x_4923_, 0, v___x_4806_);
v___x_4927_ = v___x_4923_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4806_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4931_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4931_, 3, v_l_4890_);
lean_ctor_set(v_reuseFailAlloc_4931_, 4, v_l_4890_);
v___x_4927_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
lean_object* v___x_4929_; 
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v_r_4919_);
lean_ctor_set(v___x_4662_, 3, v___x_4927_);
lean_ctor_set(v___x_4662_, 2, v_v_4921_);
lean_ctor_set(v___x_4662_, 1, v_k_4920_);
lean_ctor_set(v___x_4662_, 0, v___x_4925_);
v___x_4929_ = v___x_4662_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4925_);
lean_ctor_set(v_reuseFailAlloc_4930_, 1, v_k_4920_);
lean_ctor_set(v_reuseFailAlloc_4930_, 2, v_v_4921_);
lean_ctor_set(v_reuseFailAlloc_4930_, 3, v___x_4927_);
lean_ctor_set(v_reuseFailAlloc_4930_, 4, v_r_4919_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
else
{
lean_object* v___x_4936_; lean_object* v___x_4938_; 
v___x_4936_ = lean_unsigned_to_nat(2u);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 4, v_impl_4805_);
lean_ctor_set(v___x_4662_, 3, v_r_4919_);
lean_ctor_set(v___x_4662_, 0, v___x_4936_);
v___x_4938_ = v___x_4662_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4936_);
lean_ctor_set(v_reuseFailAlloc_4939_, 1, v_k_4657_);
lean_ctor_set(v_reuseFailAlloc_4939_, 2, v_v_4658_);
lean_ctor_set(v_reuseFailAlloc_4939_, 3, v_r_4919_);
lean_ctor_set(v_reuseFailAlloc_4939_, 4, v_impl_4805_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
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
lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4941_ = lean_unsigned_to_nat(1u);
v___x_4942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4941_);
lean_ctor_set(v___x_4942_, 1, v_k_4653_);
lean_ctor_set(v___x_4942_, 2, v_v_4654_);
lean_ctor_set(v___x_4942_, 3, v_t_4655_);
lean_ctor_set(v___x_4942_, 4, v_t_4655_);
return v___x_4942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object* v_as_4943_, size_t v_sz_4944_, size_t v_i_4945_, lean_object* v_b_4946_){
_start:
{
uint8_t v___x_4947_; 
v___x_4947_ = lean_usize_dec_lt(v_i_4945_, v_sz_4944_);
if (v___x_4947_ == 0)
{
return v_b_4946_;
}
else
{
lean_object* v_a_4948_; lean_object* v_fst_4949_; lean_object* v_snd_4950_; lean_object* v_r_4951_; size_t v___x_4952_; size_t v___x_4953_; 
v_a_4948_ = lean_array_uget_borrowed(v_as_4943_, v_i_4945_);
v_fst_4949_ = lean_ctor_get(v_a_4948_, 0);
v_snd_4950_ = lean_ctor_get(v_a_4948_, 1);
lean_inc(v_snd_4950_);
lean_inc(v_fst_4949_);
v_r_4951_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_fst_4949_, v_snd_4950_, v_b_4946_);
v___x_4952_ = ((size_t)1ULL);
v___x_4953_ = lean_usize_add(v_i_4945_, v___x_4952_);
v_i_4945_ = v___x_4953_;
v_b_4946_ = v_r_4951_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object* v_as_4955_, lean_object* v_sz_4956_, lean_object* v_i_4957_, lean_object* v_b_4958_){
_start:
{
size_t v_sz_boxed_4959_; size_t v_i_boxed_4960_; lean_object* v_res_4961_; 
v_sz_boxed_4959_ = lean_unbox_usize(v_sz_4956_);
lean_dec(v_sz_4956_);
v_i_boxed_4960_ = lean_unbox_usize(v_i_4957_);
lean_dec(v_i_4957_);
v_res_4961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v_as_4955_, v_sz_boxed_4959_, v_i_boxed_4960_, v_b_4958_);
lean_dec_ref(v_as_4955_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object* v_a_4964_, lean_object* v_x_4965_){
_start:
{
lean_object* v___y_4967_; 
if (lean_obj_tag(v_x_4965_) == 0)
{
lean_object* v___x_4970_; 
v___x_4970_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___y_4967_ = v___x_4970_;
goto v___jp_4966_;
}
else
{
lean_object* v_val_4971_; 
v_val_4971_ = lean_ctor_get(v_x_4965_, 0);
lean_inc(v_val_4971_);
lean_dec_ref_known(v_x_4965_, 1);
v___y_4967_ = v_val_4971_;
goto v___jp_4966_;
}
v___jp_4966_:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = lean_array_push(v___y_4967_, v_a_4964_);
v___x_4969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
return v___x_4969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_x_4974_){
_start:
{
if (lean_obj_tag(v_x_4974_) == 0)
{
lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v_val_4977_; lean_object* v___x_4978_; 
v___x_4975_ = lean_box(0);
v___x_4976_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4972_, v___x_4975_);
v_val_4977_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_val_4977_);
lean_dec(v___x_4976_);
v___x_4978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4978_, 0, v_a_4973_);
lean_ctor_set(v___x_4978_, 1, v_val_4977_);
lean_ctor_set(v___x_4978_, 2, v_x_4974_);
return v___x_4978_;
}
else
{
lean_object* v_key_4979_; lean_object* v_value_4980_; lean_object* v_tail_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4996_; 
v_key_4979_ = lean_ctor_get(v_x_4974_, 0);
v_value_4980_ = lean_ctor_get(v_x_4974_, 1);
v_tail_4981_ = lean_ctor_get(v_x_4974_, 2);
v_isSharedCheck_4996_ = !lean_is_exclusive(v_x_4974_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4983_ = v_x_4974_;
v_isShared_4984_ = v_isSharedCheck_4996_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_tail_4981_);
lean_inc(v_value_4980_);
lean_inc(v_key_4979_);
lean_dec(v_x_4974_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4996_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
uint8_t v___x_4985_; 
v___x_4985_ = lean_name_eq(v_key_4979_, v_a_4973_);
if (v___x_4985_ == 0)
{
lean_object* v_tail_4986_; lean_object* v___x_4988_; 
v_tail_4986_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4972_, v_a_4973_, v_tail_4981_);
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 2, v_tail_4986_);
v___x_4988_ = v___x_4983_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_key_4979_);
lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_value_4980_);
lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_tail_4986_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
else
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v_val_4992_; lean_object* v___x_4994_; 
lean_dec(v_key_4979_);
v___x_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4990_, 0, v_value_4980_);
v___x_4991_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4972_, v___x_4990_);
v_val_4992_ = lean_ctor_get(v___x_4991_, 0);
lean_inc(v_val_4992_);
lean_dec(v___x_4991_);
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v_val_4992_);
lean_ctor_set(v___x_4983_, 0, v_a_4973_);
v___x_4994_ = v___x_4983_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4973_);
lean_ctor_set(v_reuseFailAlloc_4995_, 1, v_val_4992_);
lean_ctor_set(v_reuseFailAlloc_4995_, 2, v_tail_4981_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_4997_, lean_object* v_x_4998_){
_start:
{
if (lean_obj_tag(v_x_4998_) == 0)
{
return v_x_4997_;
}
else
{
lean_object* v_key_4999_; lean_object* v_value_5000_; lean_object* v_tail_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5027_; 
v_key_4999_ = lean_ctor_get(v_x_4998_, 0);
v_value_5000_ = lean_ctor_get(v_x_4998_, 1);
v_tail_5001_ = lean_ctor_get(v_x_4998_, 2);
v_isSharedCheck_5027_ = !lean_is_exclusive(v_x_4998_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5003_ = v_x_4998_;
v_isShared_5004_ = v_isSharedCheck_5027_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_tail_5001_);
lean_inc(v_value_5000_);
lean_inc(v_key_4999_);
lean_dec(v_x_4998_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5027_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5005_; uint64_t v___y_5007_; 
v___x_5005_ = lean_array_get_size(v_x_4997_);
if (lean_obj_tag(v_key_4999_) == 0)
{
uint64_t v___x_5025_; 
v___x_5025_ = 1723ULL;
v___y_5007_ = v___x_5025_;
goto v___jp_5006_;
}
else
{
uint64_t v_hash_5026_; 
v_hash_5026_ = lean_ctor_get_uint64(v_key_4999_, sizeof(void*)*2);
v___y_5007_ = v_hash_5026_;
goto v___jp_5006_;
}
v___jp_5006_:
{
uint64_t v___x_5008_; uint64_t v___x_5009_; uint64_t v_fold_5010_; uint64_t v___x_5011_; uint64_t v___x_5012_; uint64_t v___x_5013_; size_t v___x_5014_; size_t v___x_5015_; size_t v___x_5016_; size_t v___x_5017_; size_t v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5008_ = 32ULL;
v___x_5009_ = lean_uint64_shift_right(v___y_5007_, v___x_5008_);
v_fold_5010_ = lean_uint64_xor(v___y_5007_, v___x_5009_);
v___x_5011_ = 16ULL;
v___x_5012_ = lean_uint64_shift_right(v_fold_5010_, v___x_5011_);
v___x_5013_ = lean_uint64_xor(v_fold_5010_, v___x_5012_);
v___x_5014_ = lean_uint64_to_usize(v___x_5013_);
v___x_5015_ = lean_usize_of_nat(v___x_5005_);
v___x_5016_ = ((size_t)1ULL);
v___x_5017_ = lean_usize_sub(v___x_5015_, v___x_5016_);
v___x_5018_ = lean_usize_land(v___x_5014_, v___x_5017_);
v___x_5019_ = lean_array_uget_borrowed(v_x_4997_, v___x_5018_);
lean_inc(v___x_5019_);
if (v_isShared_5004_ == 0)
{
lean_ctor_set(v___x_5003_, 2, v___x_5019_);
v___x_5021_ = v___x_5003_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_key_4999_);
lean_ctor_set(v_reuseFailAlloc_5024_, 1, v_value_5000_);
lean_ctor_set(v_reuseFailAlloc_5024_, 2, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
lean_object* v___x_5022_; 
v___x_5022_ = lean_array_uset(v_x_4997_, v___x_5018_, v___x_5021_);
v_x_4997_ = v___x_5022_;
v_x_4998_ = v_tail_5001_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object* v_i_5028_, lean_object* v_source_5029_, lean_object* v_target_5030_){
_start:
{
lean_object* v___x_5031_; uint8_t v___x_5032_; 
v___x_5031_ = lean_array_get_size(v_source_5029_);
v___x_5032_ = lean_nat_dec_lt(v_i_5028_, v___x_5031_);
if (v___x_5032_ == 0)
{
lean_dec_ref(v_source_5029_);
lean_dec(v_i_5028_);
return v_target_5030_;
}
else
{
lean_object* v_es_5033_; lean_object* v___x_5034_; lean_object* v_source_5035_; lean_object* v_target_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v_es_5033_ = lean_array_fget(v_source_5029_, v_i_5028_);
v___x_5034_ = lean_box(0);
v_source_5035_ = lean_array_fset(v_source_5029_, v_i_5028_, v___x_5034_);
v_target_5036_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_target_5030_, v_es_5033_);
v___x_5037_ = lean_unsigned_to_nat(1u);
v___x_5038_ = lean_nat_add(v_i_5028_, v___x_5037_);
lean_dec(v_i_5028_);
v_i_5028_ = v___x_5038_;
v_source_5029_ = v_source_5035_;
v_target_5030_ = v_target_5036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object* v_data_5040_){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v_nbuckets_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5041_ = lean_array_get_size(v_data_5040_);
v___x_5042_ = lean_unsigned_to_nat(2u);
v_nbuckets_5043_ = lean_nat_mul(v___x_5041_, v___x_5042_);
v___x_5044_ = lean_unsigned_to_nat(0u);
v___x_5045_ = lean_box(0);
v___x_5046_ = lean_mk_array(v_nbuckets_5043_, v___x_5045_);
v___x_5047_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_5044_, v_data_5040_, v___x_5046_);
return v___x_5047_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_5048_, lean_object* v_x_5049_){
_start:
{
if (lean_obj_tag(v_x_5049_) == 0)
{
uint8_t v___x_5050_; 
v___x_5050_ = 0;
return v___x_5050_;
}
else
{
lean_object* v_key_5051_; lean_object* v_tail_5052_; uint8_t v___x_5053_; 
v_key_5051_ = lean_ctor_get(v_x_5049_, 0);
v_tail_5052_ = lean_ctor_get(v_x_5049_, 2);
v___x_5053_ = lean_name_eq(v_key_5051_, v_a_5048_);
if (v___x_5053_ == 0)
{
v_x_5049_ = v_tail_5052_;
goto _start;
}
else
{
return v___x_5053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_5055_, lean_object* v_x_5056_){
_start:
{
uint8_t v_res_5057_; lean_object* v_r_5058_; 
v_res_5057_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5055_, v_x_5056_);
lean_dec(v_x_5056_);
lean_dec(v_a_5055_);
v_r_5058_ = lean_box(v_res_5057_);
return v_r_5058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_5059_, lean_object* v_m_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v___y_5063_; lean_object* v___y_5064_; size_t v___y_5065_; lean_object* v___y_5066_; lean_object* v_size_5069_; lean_object* v_buckets_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5117_; 
v_size_5069_ = lean_ctor_get(v_m_5060_, 0);
v_buckets_5070_ = lean_ctor_get(v_m_5060_, 1);
v_isSharedCheck_5117_ = !lean_is_exclusive(v_m_5060_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5072_ = v_m_5060_;
v_isShared_5073_ = v_isSharedCheck_5117_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_buckets_5070_);
lean_inc(v_size_5069_);
lean_dec(v_m_5060_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5117_;
goto v_resetjp_5071_;
}
v___jp_5062_:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = lean_array_uset(v___y_5064_, v___y_5065_, v___y_5063_);
v___x_5068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___y_5066_);
lean_ctor_set(v___x_5068_, 1, v___x_5067_);
return v___x_5068_;
}
v_resetjp_5071_:
{
lean_object* v___x_5074_; uint64_t v___y_5076_; 
v___x_5074_ = lean_array_get_size(v_buckets_5070_);
if (lean_obj_tag(v_a_5061_) == 0)
{
uint64_t v___x_5115_; 
v___x_5115_ = 1723ULL;
v___y_5076_ = v___x_5115_;
goto v___jp_5075_;
}
else
{
uint64_t v_hash_5116_; 
v_hash_5116_ = lean_ctor_get_uint64(v_a_5061_, sizeof(void*)*2);
v___y_5076_ = v_hash_5116_;
goto v___jp_5075_;
}
v___jp_5075_:
{
uint64_t v___x_5077_; uint64_t v___x_5078_; uint64_t v_fold_5079_; uint64_t v___x_5080_; uint64_t v___x_5081_; uint64_t v___x_5082_; size_t v___x_5083_; size_t v___x_5084_; size_t v___x_5085_; size_t v___x_5086_; size_t v___x_5087_; lean_object* v_bkt_5088_; uint8_t v___x_5089_; 
v___x_5077_ = 32ULL;
v___x_5078_ = lean_uint64_shift_right(v___y_5076_, v___x_5077_);
v_fold_5079_ = lean_uint64_xor(v___y_5076_, v___x_5078_);
v___x_5080_ = 16ULL;
v___x_5081_ = lean_uint64_shift_right(v_fold_5079_, v___x_5080_);
v___x_5082_ = lean_uint64_xor(v_fold_5079_, v___x_5081_);
v___x_5083_ = lean_uint64_to_usize(v___x_5082_);
v___x_5084_ = lean_usize_of_nat(v___x_5074_);
v___x_5085_ = ((size_t)1ULL);
v___x_5086_ = lean_usize_sub(v___x_5084_, v___x_5085_);
v___x_5087_ = lean_usize_land(v___x_5083_, v___x_5086_);
v_bkt_5088_ = lean_array_uget_borrowed(v_buckets_5070_, v___x_5087_);
v___x_5089_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5061_, v_bkt_5088_);
if (v___x_5089_ == 0)
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v_size_x27_5093_; lean_object* v___x_5094_; lean_object* v_buckets_x27_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; uint8_t v___x_5101_; 
v___x_5090_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_5091_ = lean_array_push(v___x_5090_, v_a_5059_);
v___x_5092_ = lean_unsigned_to_nat(1u);
v_size_x27_5093_ = lean_nat_add(v_size_5069_, v___x_5092_);
lean_dec(v_size_5069_);
lean_inc(v_bkt_5088_);
v___x_5094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5094_, 0, v_a_5061_);
lean_ctor_set(v___x_5094_, 1, v___x_5091_);
lean_ctor_set(v___x_5094_, 2, v_bkt_5088_);
v_buckets_x27_5095_ = lean_array_uset(v_buckets_5070_, v___x_5087_, v___x_5094_);
v___x_5096_ = lean_unsigned_to_nat(4u);
v___x_5097_ = lean_nat_mul(v_size_x27_5093_, v___x_5096_);
v___x_5098_ = lean_unsigned_to_nat(3u);
v___x_5099_ = lean_nat_div(v___x_5097_, v___x_5098_);
lean_dec(v___x_5097_);
v___x_5100_ = lean_array_get_size(v_buckets_x27_5095_);
v___x_5101_ = lean_nat_dec_le(v___x_5099_, v___x_5100_);
lean_dec(v___x_5099_);
if (v___x_5101_ == 0)
{
lean_object* v_val_5102_; lean_object* v___x_5104_; 
v_val_5102_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5095_);
if (v_isShared_5073_ == 0)
{
lean_ctor_set(v___x_5072_, 1, v_val_5102_);
lean_ctor_set(v___x_5072_, 0, v_size_x27_5093_);
v___x_5104_ = v___x_5072_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_size_x27_5093_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v_val_5102_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
else
{
lean_object* v___x_5107_; 
if (v_isShared_5073_ == 0)
{
lean_ctor_set(v___x_5072_, 1, v_buckets_x27_5095_);
lean_ctor_set(v___x_5072_, 0, v_size_x27_5093_);
v___x_5107_ = v___x_5072_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_size_x27_5093_);
lean_ctor_set(v_reuseFailAlloc_5108_, 1, v_buckets_x27_5095_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
}
else
{
lean_object* v___x_5109_; lean_object* v_buckets_x27_5110_; lean_object* v_bkt_x27_5111_; uint8_t v___x_5112_; 
lean_inc(v_bkt_5088_);
lean_del_object(v___x_5072_);
v___x_5109_ = lean_box(0);
v_buckets_x27_5110_ = lean_array_uset(v_buckets_5070_, v___x_5087_, v___x_5109_);
lean_inc(v_a_5061_);
v_bkt_x27_5111_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5059_, v_a_5061_, v_bkt_5088_);
v___x_5112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5061_, v_bkt_x27_5111_);
lean_dec(v_a_5061_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5113_ = lean_unsigned_to_nat(1u);
v___x_5114_ = lean_nat_sub(v_size_5069_, v___x_5113_);
lean_dec(v_size_5069_);
v___y_5063_ = v_bkt_x27_5111_;
v___y_5064_ = v_buckets_x27_5110_;
v___y_5065_ = v___x_5087_;
v___y_5066_ = v___x_5114_;
goto v___jp_5062_;
}
else
{
v___y_5063_ = v_bkt_x27_5111_;
v___y_5064_ = v_buckets_x27_5110_;
v___y_5065_ = v___x_5087_;
v___y_5066_ = v_size_5069_;
goto v___jp_5062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5118_, lean_object* v_as_5119_, size_t v_sz_5120_, size_t v_i_5121_, lean_object* v_b_5122_){
_start:
{
uint8_t v___x_5123_; 
v___x_5123_ = lean_usize_dec_lt(v_i_5121_, v_sz_5120_);
if (v___x_5123_ == 0)
{
lean_dec_ref(v_key_5118_);
return v_b_5122_;
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; size_t v___x_5127_; size_t v___x_5128_; 
v_a_5124_ = lean_array_uget_borrowed(v_as_5119_, v_i_5121_);
lean_inc_ref(v_key_5118_);
lean_inc_n(v_a_5124_, 2);
v___x_5125_ = lean_apply_1(v_key_5118_, v_a_5124_);
v___x_5126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5124_, v_b_5122_, v___x_5125_);
v___x_5127_ = ((size_t)1ULL);
v___x_5128_ = lean_usize_add(v_i_5121_, v___x_5127_);
v_i_5121_ = v___x_5128_;
v_b_5122_ = v___x_5126_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5130_, lean_object* v_as_5131_, lean_object* v_sz_5132_, lean_object* v_i_5133_, lean_object* v_b_5134_){
_start:
{
size_t v_sz_boxed_5135_; size_t v_i_boxed_5136_; lean_object* v_res_5137_; 
v_sz_boxed_5135_ = lean_unbox_usize(v_sz_5132_);
lean_dec(v_sz_5132_);
v_i_boxed_5136_ = lean_unbox_usize(v_i_5133_);
lean_dec(v_i_5133_);
v_res_5137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5130_, v_as_5131_, v_sz_boxed_5135_, v_i_boxed_5136_, v_b_5134_);
lean_dec_ref(v_as_5131_);
return v_res_5137_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5138_ = lean_box(0);
v___x_5139_ = lean_unsigned_to_nat(16u);
v___x_5140_ = lean_mk_array(v___x_5139_, v___x_5138_);
return v___x_5140_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v_groups_5143_; 
v___x_5141_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5142_ = lean_unsigned_to_nat(0u);
v_groups_5143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5143_, 0, v___x_5142_);
lean_ctor_set(v_groups_5143_, 1, v___x_5141_);
return v_groups_5143_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5144_, lean_object* v_xs_5145_){
_start:
{
lean_object* v_groups_5146_; size_t v_sz_5147_; size_t v___x_5148_; lean_object* v___x_5149_; 
v_groups_5146_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5147_ = lean_array_size(v_xs_5145_);
v___x_5148_ = ((size_t)0ULL);
v___x_5149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5144_, v_xs_5145_, v_sz_5147_, v___x_5148_, v_groups_5146_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5150_, lean_object* v_xs_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5150_, v_xs_5151_);
lean_dec_ref(v_xs_5151_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5154_){
_start:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; 
v___x_5156_ = lean_unsigned_to_nat(0u);
v___x_5157_ = lean_array_get_size(v_infos_5154_);
v___x_5158_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5154_, v___x_5156_, v___x_5157_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5183_; 
v_a_5159_ = lean_ctor_get(v___x_5158_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5161_ = v___x_5158_;
v_isShared_5162_ = v_isSharedCheck_5183_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5158_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5183_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___y_5164_; lean_object* v___f_5173_; lean_object* v___x_5174_; lean_object* v_size_5175_; lean_object* v_buckets_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; uint8_t v___x_5179_; 
v___f_5173_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5174_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5173_, v_a_5159_);
v_size_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc(v_size_5175_);
v_buckets_5176_ = lean_ctor_get(v___x_5174_, 1);
lean_inc_ref(v_buckets_5176_);
lean_dec_ref(v___x_5174_);
v___x_5177_ = lean_mk_empty_array_with_capacity(v_size_5175_);
lean_dec(v_size_5175_);
v___x_5178_ = lean_array_get_size(v_buckets_5176_);
v___x_5179_ = lean_nat_dec_lt(v___x_5156_, v___x_5178_);
if (v___x_5179_ == 0)
{
lean_dec_ref(v_buckets_5176_);
v___y_5164_ = v___x_5177_;
goto v___jp_5163_;
}
else
{
size_t v___x_5180_; size_t v___x_5181_; lean_object* v___x_5182_; 
v___x_5180_ = ((size_t)0ULL);
v___x_5181_ = lean_usize_of_nat(v___x_5178_);
v___x_5182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5176_, v___x_5180_, v___x_5181_, v___x_5177_);
lean_dec_ref(v_buckets_5176_);
v___y_5164_ = v___x_5182_;
goto v___jp_5163_;
}
v___jp_5163_:
{
lean_object* v_r_5165_; size_t v_sz_5166_; size_t v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5171_; 
v_r_5165_ = lean_box(1);
v_sz_5166_ = lean_array_size(v___y_5164_);
v___x_5167_ = ((size_t)0ULL);
v___x_5168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5164_, v_sz_5166_, v___x_5167_, v_r_5165_);
lean_dec_ref(v___y_5164_);
v___x_5169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5169_, 0, v_a_5159_);
lean_ctor_set(v___x_5169_, 1, v___x_5168_);
if (v_isShared_5162_ == 0)
{
lean_ctor_set(v___x_5161_, 0, v___x_5169_);
v___x_5171_ = v___x_5161_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v___x_5169_);
v___x_5171_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
return v___x_5171_;
}
}
}
}
else
{
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5191_; 
v_a_5184_ = lean_ctor_get(v___x_5158_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5186_ = v___x_5158_;
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_5158_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5189_; 
if (v_isShared_5187_ == 0)
{
v___x_5189_ = v___x_5186_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5192_, lean_object* v_a_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5192_);
lean_dec_ref(v_infos_5192_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5195_, lean_object* v_k_5196_, lean_object* v_v_5197_, lean_object* v_t_5198_, lean_object* v_hl_5199_){
_start:
{
lean_object* v___x_5200_; 
v___x_5200_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5196_, v_v_5197_, v_t_5198_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5201_, lean_object* v_key_5202_, lean_object* v_xs_5203_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5202_, v_xs_5203_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5205_, lean_object* v_key_5206_, lean_object* v_xs_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5205_, v_key_5206_, v_xs_5207_);
lean_dec_ref(v_xs_5207_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5209_, lean_object* v_a_5210_, lean_object* v_m_5211_, lean_object* v_a_5212_){
_start:
{
lean_object* v___x_5213_; 
v___x_5213_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5210_, v_m_5211_, v_a_5212_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5214_, lean_object* v_key_5215_, lean_object* v_as_5216_, size_t v_sz_5217_, size_t v_i_5218_, lean_object* v_b_5219_){
_start:
{
lean_object* v___x_5220_; 
v___x_5220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5215_, v_as_5216_, v_sz_5217_, v_i_5218_, v_b_5219_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5221_, lean_object* v_key_5222_, lean_object* v_as_5223_, lean_object* v_sz_5224_, lean_object* v_i_5225_, lean_object* v_b_5226_){
_start:
{
size_t v_sz_boxed_5227_; size_t v_i_boxed_5228_; lean_object* v_res_5229_; 
v_sz_boxed_5227_ = lean_unbox_usize(v_sz_5224_);
lean_dec(v_sz_5224_);
v_i_boxed_5228_ = lean_unbox_usize(v_i_5225_);
lean_dec(v_i_5225_);
v_res_5229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5221_, v_key_5222_, v_as_5223_, v_sz_boxed_5227_, v_i_boxed_5228_, v_b_5226_);
lean_dec_ref(v_as_5223_);
return v_res_5229_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5230_, lean_object* v_a_5231_, lean_object* v_x_5232_){
_start:
{
uint8_t v___x_5233_; 
v___x_5233_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5231_, v_x_5232_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5234_, lean_object* v_a_5235_, lean_object* v_x_5236_){
_start:
{
uint8_t v_res_5237_; lean_object* v_r_5238_; 
v_res_5237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5234_, v_a_5235_, v_x_5236_);
lean_dec(v_x_5236_);
lean_dec(v_a_5235_);
v_r_5238_ = lean_box(v_res_5237_);
return v_r_5238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5239_, lean_object* v_data_5240_){
_start:
{
lean_object* v___x_5241_; 
v___x_5241_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5240_);
return v___x_5241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_x_5245_){
_start:
{
lean_object* v___x_5246_; 
v___x_5246_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5243_, v_a_5244_, v_x_5245_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5247_, lean_object* v_i_5248_, lean_object* v_source_5249_, lean_object* v_target_5250_){
_start:
{
lean_object* v___x_5251_; 
v___x_5251_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5248_, v_source_5249_, v_target_5250_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5252_, lean_object* v_x_5253_, lean_object* v_x_5254_){
_start:
{
lean_object* v___x_5255_; 
v___x_5255_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5253_, v_x_5254_);
return v___x_5255_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5256_){
_start:
{
lean_object* v_isSetupFailure_x3f_5257_; 
v_isSetupFailure_x3f_5257_ = lean_ctor_get(v_i_5256_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5257_) == 0)
{
uint8_t v___x_5258_; 
v___x_5258_ = 0;
return v___x_5258_;
}
else
{
lean_object* v_val_5259_; uint8_t v___x_5260_; 
v_val_5259_ = lean_ctor_get(v_isSetupFailure_x3f_5257_, 0);
v___x_5260_ = lean_unbox(v_val_5259_);
if (v___x_5260_ == 0)
{
uint8_t v___x_5261_; 
v___x_5261_ = 1;
return v___x_5261_;
}
else
{
uint8_t v___x_5262_; 
v___x_5262_ = 0;
return v___x_5262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5263_){
_start:
{
uint8_t v_res_5264_; lean_object* v_r_5265_; 
v_res_5264_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5263_);
lean_dec_ref(v_i_5263_);
v_r_5265_ = lean_box(v_res_5264_);
return v_r_5265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5271_, lean_object* v_path_5272_, lean_object* v_ilean_5273_){
_start:
{
lean_object* v_module_5275_; lean_object* v_directImports_5276_; lean_object* v_references_5277_; lean_object* v_decls_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5330_; 
v_module_5275_ = lean_ctor_get(v_ilean_5273_, 1);
v_directImports_5276_ = lean_ctor_get(v_ilean_5273_, 2);
v_references_5277_ = lean_ctor_get(v_ilean_5273_, 3);
v_decls_5278_ = lean_ctor_get(v_ilean_5273_, 4);
v_isSharedCheck_5330_ = !lean_is_exclusive(v_ilean_5273_);
if (v_isSharedCheck_5330_ == 0)
{
lean_object* v_unused_5331_; 
v_unused_5331_ = lean_ctor_get(v_ilean_5273_, 0);
lean_dec(v_unused_5331_);
v___x_5280_ = v_ilean_5273_;
v_isShared_5281_ = v_isSharedCheck_5330_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_decls_5278_);
lean_inc(v_references_5277_);
lean_inc(v_directImports_5276_);
lean_inc(v_module_5275_);
lean_dec(v_ilean_5273_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5330_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v___x_5282_; 
lean_inc(v_module_5275_);
v___x_5282_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5275_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v_a_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5321_; 
v_a_5283_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5285_ = v___x_5282_;
v_isShared_5286_ = v_isSharedCheck_5321_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_a_5283_);
lean_dec(v___x_5282_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5321_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
if (lean_obj_tag(v_a_5283_) == 1)
{
lean_object* v_val_5287_; lean_object* v___x_5288_; 
lean_del_object(v___x_5285_);
v_val_5287_ = lean_ctor_get(v_a_5283_, 0);
lean_inc(v_val_5287_);
lean_dec_ref_known(v_a_5283_, 1);
v___x_5288_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5276_);
lean_dec_ref(v_directImports_5276_);
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5309_; 
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5291_ = v___x_5288_;
v_isShared_5292_ = v_isSharedCheck_5309_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5288_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5309_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v_ileans_5293_; lean_object* v_workers_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5308_; 
v_ileans_5293_ = lean_ctor_get(v_self_5271_, 0);
v_workers_5294_ = lean_ctor_get(v_self_5271_, 1);
v_isSharedCheck_5308_ = !lean_is_exclusive(v_self_5271_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5296_ = v_self_5271_;
v_isShared_5297_ = v_isSharedCheck_5308_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_workers_5294_);
lean_inc(v_ileans_5293_);
lean_dec(v_self_5271_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5308_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v___x_5299_; 
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 2, v_a_5289_);
lean_ctor_set(v___x_5280_, 1, v_path_5272_);
lean_ctor_set(v___x_5280_, 0, v_val_5287_);
v___x_5299_ = v___x_5280_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_val_5287_);
lean_ctor_set(v_reuseFailAlloc_5307_, 1, v_path_5272_);
lean_ctor_set(v_reuseFailAlloc_5307_, 2, v_a_5289_);
lean_ctor_set(v_reuseFailAlloc_5307_, 3, v_references_5277_);
lean_ctor_set(v_reuseFailAlloc_5307_, 4, v_decls_5278_);
v___x_5299_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; lean_object* v___x_5302_; 
v___x_5300_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5275_, v___x_5299_, v_ileans_5293_);
if (v_isShared_5297_ == 0)
{
lean_ctor_set(v___x_5296_, 0, v___x_5300_);
v___x_5302_ = v___x_5296_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5300_);
lean_ctor_set(v_reuseFailAlloc_5306_, 1, v_workers_5294_);
v___x_5302_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
lean_object* v___x_5304_; 
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 0, v___x_5302_);
v___x_5304_ = v___x_5291_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v___x_5302_);
v___x_5304_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
return v___x_5304_;
}
}
}
}
}
}
else
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5317_; 
lean_dec(v_val_5287_);
lean_del_object(v___x_5280_);
lean_dec(v_decls_5278_);
lean_dec(v_references_5277_);
lean_dec(v_module_5275_);
lean_dec_ref(v_path_5272_);
lean_dec_ref(v_self_5271_);
v_a_5310_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5312_ = v___x_5288_;
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5288_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5315_; 
if (v_isShared_5313_ == 0)
{
v___x_5315_ = v___x_5312_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
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
else
{
lean_object* v___x_5319_; 
lean_dec(v_a_5283_);
lean_del_object(v___x_5280_);
lean_dec(v_decls_5278_);
lean_dec(v_references_5277_);
lean_dec_ref(v_directImports_5276_);
lean_dec(v_module_5275_);
lean_dec_ref(v_path_5272_);
if (v_isShared_5286_ == 0)
{
lean_ctor_set(v___x_5285_, 0, v_self_5271_);
v___x_5319_ = v___x_5285_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_self_5271_);
v___x_5319_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
return v___x_5319_;
}
}
}
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5329_; 
lean_del_object(v___x_5280_);
lean_dec(v_decls_5278_);
lean_dec(v_references_5277_);
lean_dec_ref(v_directImports_5276_);
lean_dec(v_module_5275_);
lean_dec_ref(v_path_5272_);
lean_dec_ref(v_self_5271_);
v_a_5322_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5324_ = v___x_5282_;
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5282_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5327_; 
if (v_isShared_5325_ == 0)
{
v___x_5327_ = v___x_5324_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5322_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5332_, lean_object* v_path_5333_, lean_object* v_ilean_5334_, lean_object* v_a_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_Lean_Server_References_addIlean(v_self_5332_, v_path_5333_, v_ilean_5334_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5337_, lean_object* v_t_5338_){
_start:
{
if (lean_obj_tag(v_t_5338_) == 0)
{
lean_object* v_v_5339_; lean_object* v_k_5340_; lean_object* v_l_5341_; lean_object* v_r_5342_; lean_object* v_ileanPath_5343_; uint8_t v___x_5344_; 
v_v_5339_ = lean_ctor_get(v_t_5338_, 2);
lean_inc(v_v_5339_);
v_k_5340_ = lean_ctor_get(v_t_5338_, 1);
lean_inc(v_k_5340_);
v_l_5341_ = lean_ctor_get(v_t_5338_, 3);
lean_inc(v_l_5341_);
v_r_5342_ = lean_ctor_get(v_t_5338_, 4);
lean_inc(v_r_5342_);
lean_dec_ref_known(v_t_5338_, 5);
v_ileanPath_5343_ = lean_ctor_get(v_v_5339_, 1);
v___x_5344_ = lean_string_dec_eq(v_ileanPath_5343_, v_path_5337_);
if (v___x_5344_ == 0)
{
lean_object* v_impl_5345_; lean_object* v_impl_5346_; lean_object* v___x_5347_; 
lean_dec(v_k_5340_);
lean_dec(v_v_5339_);
v_impl_5345_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5337_, v_l_5341_);
v_impl_5346_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5337_, v_r_5342_);
v___x_5347_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5345_, v_impl_5346_);
return v___x_5347_;
}
else
{
lean_object* v_impl_5348_; lean_object* v_impl_5349_; lean_object* v___x_5350_; 
v_impl_5348_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5337_, v_l_5341_);
v_impl_5349_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5337_, v_r_5342_);
v___x_5350_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5340_, v_v_5339_, v_impl_5348_, v_impl_5349_);
return v___x_5350_;
}
}
else
{
return v_t_5338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5351_, lean_object* v_t_5352_){
_start:
{
lean_object* v_res_5353_; 
v_res_5353_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5351_, v_t_5352_);
lean_dec_ref(v_path_5351_);
return v_res_5353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5354_, lean_object* v_t_5355_){
_start:
{
if (lean_obj_tag(v_t_5355_) == 0)
{
lean_object* v_k_5356_; lean_object* v_v_5357_; lean_object* v_l_5358_; lean_object* v_r_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_6013_; 
v_k_5356_ = lean_ctor_get(v_t_5355_, 1);
v_v_5357_ = lean_ctor_get(v_t_5355_, 2);
v_l_5358_ = lean_ctor_get(v_t_5355_, 3);
v_r_5359_ = lean_ctor_get(v_t_5355_, 4);
v_isSharedCheck_6013_ = !lean_is_exclusive(v_t_5355_);
if (v_isSharedCheck_6013_ == 0)
{
lean_object* v_unused_6014_; 
v_unused_6014_ = lean_ctor_get(v_t_5355_, 0);
lean_dec(v_unused_6014_);
v___x_5361_ = v_t_5355_;
v_isShared_5362_ = v_isSharedCheck_6013_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_r_5359_);
lean_inc(v_l_5358_);
lean_inc(v_v_5357_);
lean_inc(v_k_5356_);
lean_dec(v_t_5355_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_6013_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
uint8_t v___x_5363_; 
v___x_5363_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5354_, v_k_5356_);
switch(v___x_5363_)
{
case 0:
{
lean_object* v_impl_5364_; lean_object* v___x_5365_; 
v_impl_5364_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5354_, v_l_5358_);
v___x_5365_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5364_) == 0)
{
if (lean_obj_tag(v_r_5359_) == 0)
{
lean_object* v_size_5366_; lean_object* v_size_5367_; lean_object* v_k_5368_; lean_object* v_v_5369_; lean_object* v_l_5370_; lean_object* v_r_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; uint8_t v___x_5374_; 
v_size_5366_ = lean_ctor_get(v_impl_5364_, 0);
lean_inc(v_size_5366_);
v_size_5367_ = lean_ctor_get(v_r_5359_, 0);
v_k_5368_ = lean_ctor_get(v_r_5359_, 1);
v_v_5369_ = lean_ctor_get(v_r_5359_, 2);
v_l_5370_ = lean_ctor_get(v_r_5359_, 3);
lean_inc(v_l_5370_);
v_r_5371_ = lean_ctor_get(v_r_5359_, 4);
v___x_5372_ = lean_unsigned_to_nat(3u);
v___x_5373_ = lean_nat_mul(v___x_5372_, v_size_5366_);
v___x_5374_ = lean_nat_dec_lt(v___x_5373_, v_size_5367_);
lean_dec(v___x_5373_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5378_; 
lean_dec(v_l_5370_);
v___x_5375_ = lean_nat_add(v___x_5365_, v_size_5366_);
lean_dec(v_size_5366_);
v___x_5376_ = lean_nat_add(v___x_5375_, v_size_5367_);
lean_dec(v___x_5375_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 3, v_impl_5364_);
lean_ctor_set(v___x_5361_, 0, v___x_5376_);
v___x_5378_ = v___x_5361_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v___x_5376_);
lean_ctor_set(v_reuseFailAlloc_5379_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5379_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5379_, 3, v_impl_5364_);
lean_ctor_set(v_reuseFailAlloc_5379_, 4, v_r_5359_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
else
{
lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5443_; 
lean_inc(v_r_5371_);
lean_inc(v_v_5369_);
lean_inc(v_k_5368_);
lean_inc(v_size_5367_);
v_isSharedCheck_5443_ = !lean_is_exclusive(v_r_5359_);
if (v_isSharedCheck_5443_ == 0)
{
lean_object* v_unused_5444_; lean_object* v_unused_5445_; lean_object* v_unused_5446_; lean_object* v_unused_5447_; lean_object* v_unused_5448_; 
v_unused_5444_ = lean_ctor_get(v_r_5359_, 4);
lean_dec(v_unused_5444_);
v_unused_5445_ = lean_ctor_get(v_r_5359_, 3);
lean_dec(v_unused_5445_);
v_unused_5446_ = lean_ctor_get(v_r_5359_, 2);
lean_dec(v_unused_5446_);
v_unused_5447_ = lean_ctor_get(v_r_5359_, 1);
lean_dec(v_unused_5447_);
v_unused_5448_ = lean_ctor_get(v_r_5359_, 0);
lean_dec(v_unused_5448_);
v___x_5381_ = v_r_5359_;
v_isShared_5382_ = v_isSharedCheck_5443_;
goto v_resetjp_5380_;
}
else
{
lean_dec(v_r_5359_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5443_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v_size_5383_; lean_object* v_k_5384_; lean_object* v_v_5385_; lean_object* v_l_5386_; lean_object* v_r_5387_; lean_object* v_size_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; 
v_size_5383_ = lean_ctor_get(v_l_5370_, 0);
v_k_5384_ = lean_ctor_get(v_l_5370_, 1);
v_v_5385_ = lean_ctor_get(v_l_5370_, 2);
v_l_5386_ = lean_ctor_get(v_l_5370_, 3);
v_r_5387_ = lean_ctor_get(v_l_5370_, 4);
v_size_5388_ = lean_ctor_get(v_r_5371_, 0);
v___x_5389_ = lean_unsigned_to_nat(2u);
v___x_5390_ = lean_nat_mul(v___x_5389_, v_size_5388_);
v___x_5391_ = lean_nat_dec_lt(v_size_5383_, v___x_5390_);
lean_dec(v___x_5390_);
if (v___x_5391_ == 0)
{
lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5419_; 
lean_inc(v_r_5387_);
lean_inc(v_l_5386_);
lean_inc(v_v_5385_);
lean_inc(v_k_5384_);
v_isSharedCheck_5419_ = !lean_is_exclusive(v_l_5370_);
if (v_isSharedCheck_5419_ == 0)
{
lean_object* v_unused_5420_; lean_object* v_unused_5421_; lean_object* v_unused_5422_; lean_object* v_unused_5423_; lean_object* v_unused_5424_; 
v_unused_5420_ = lean_ctor_get(v_l_5370_, 4);
lean_dec(v_unused_5420_);
v_unused_5421_ = lean_ctor_get(v_l_5370_, 3);
lean_dec(v_unused_5421_);
v_unused_5422_ = lean_ctor_get(v_l_5370_, 2);
lean_dec(v_unused_5422_);
v_unused_5423_ = lean_ctor_get(v_l_5370_, 1);
lean_dec(v_unused_5423_);
v_unused_5424_ = lean_ctor_get(v_l_5370_, 0);
lean_dec(v_unused_5424_);
v___x_5393_ = v_l_5370_;
v_isShared_5394_ = v_isSharedCheck_5419_;
goto v_resetjp_5392_;
}
else
{
lean_dec(v_l_5370_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5419_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___y_5398_; lean_object* v___y_5399_; lean_object* v___y_5400_; lean_object* v___y_5409_; 
v___x_5395_ = lean_nat_add(v___x_5365_, v_size_5366_);
lean_dec(v_size_5366_);
v___x_5396_ = lean_nat_add(v___x_5395_, v_size_5367_);
lean_dec(v_size_5367_);
if (lean_obj_tag(v_l_5386_) == 0)
{
lean_object* v_size_5417_; 
v_size_5417_ = lean_ctor_get(v_l_5386_, 0);
lean_inc(v_size_5417_);
v___y_5409_ = v_size_5417_;
goto v___jp_5408_;
}
else
{
lean_object* v___x_5418_; 
v___x_5418_ = lean_unsigned_to_nat(0u);
v___y_5409_ = v___x_5418_;
goto v___jp_5408_;
}
v___jp_5397_:
{
lean_object* v___x_5401_; lean_object* v___x_5403_; 
v___x_5401_ = lean_nat_add(v___y_5398_, v___y_5400_);
lean_dec(v___y_5400_);
lean_dec(v___y_5398_);
if (v_isShared_5394_ == 0)
{
lean_ctor_set(v___x_5393_, 4, v_r_5371_);
lean_ctor_set(v___x_5393_, 3, v_r_5387_);
lean_ctor_set(v___x_5393_, 2, v_v_5369_);
lean_ctor_set(v___x_5393_, 1, v_k_5368_);
lean_ctor_set(v___x_5393_, 0, v___x_5401_);
v___x_5403_ = v___x_5393_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v___x_5401_);
lean_ctor_set(v_reuseFailAlloc_5407_, 1, v_k_5368_);
lean_ctor_set(v_reuseFailAlloc_5407_, 2, v_v_5369_);
lean_ctor_set(v_reuseFailAlloc_5407_, 3, v_r_5387_);
lean_ctor_set(v_reuseFailAlloc_5407_, 4, v_r_5371_);
v___x_5403_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
lean_object* v___x_5405_; 
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 4, v___x_5403_);
lean_ctor_set(v___x_5381_, 3, v___y_5399_);
lean_ctor_set(v___x_5381_, 2, v_v_5385_);
lean_ctor_set(v___x_5381_, 1, v_k_5384_);
lean_ctor_set(v___x_5381_, 0, v___x_5396_);
v___x_5405_ = v___x_5381_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5396_);
lean_ctor_set(v_reuseFailAlloc_5406_, 1, v_k_5384_);
lean_ctor_set(v_reuseFailAlloc_5406_, 2, v_v_5385_);
lean_ctor_set(v_reuseFailAlloc_5406_, 3, v___y_5399_);
lean_ctor_set(v_reuseFailAlloc_5406_, 4, v___x_5403_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
v___jp_5408_:
{
lean_object* v___x_5410_; lean_object* v___x_5412_; 
v___x_5410_ = lean_nat_add(v___x_5395_, v___y_5409_);
lean_dec(v___y_5409_);
lean_dec(v___x_5395_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v_l_5386_);
lean_ctor_set(v___x_5361_, 3, v_impl_5364_);
lean_ctor_set(v___x_5361_, 0, v___x_5410_);
v___x_5412_ = v___x_5361_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v___x_5410_);
lean_ctor_set(v_reuseFailAlloc_5416_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5416_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5416_, 3, v_impl_5364_);
lean_ctor_set(v_reuseFailAlloc_5416_, 4, v_l_5386_);
v___x_5412_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
lean_object* v___x_5413_; 
v___x_5413_ = lean_nat_add(v___x_5365_, v_size_5388_);
if (lean_obj_tag(v_r_5387_) == 0)
{
lean_object* v_size_5414_; 
v_size_5414_ = lean_ctor_get(v_r_5387_, 0);
lean_inc(v_size_5414_);
v___y_5398_ = v___x_5413_;
v___y_5399_ = v___x_5412_;
v___y_5400_ = v_size_5414_;
goto v___jp_5397_;
}
else
{
lean_object* v___x_5415_; 
v___x_5415_ = lean_unsigned_to_nat(0u);
v___y_5398_ = v___x_5413_;
v___y_5399_ = v___x_5412_;
v___y_5400_ = v___x_5415_;
goto v___jp_5397_;
}
}
}
}
}
else
{
lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5429_; 
lean_del_object(v___x_5361_);
v___x_5425_ = lean_nat_add(v___x_5365_, v_size_5366_);
lean_dec(v_size_5366_);
v___x_5426_ = lean_nat_add(v___x_5425_, v_size_5367_);
lean_dec(v_size_5367_);
v___x_5427_ = lean_nat_add(v___x_5425_, v_size_5383_);
lean_dec(v___x_5425_);
lean_inc_ref(v_impl_5364_);
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 4, v_l_5370_);
lean_ctor_set(v___x_5381_, 3, v_impl_5364_);
lean_ctor_set(v___x_5381_, 2, v_v_5357_);
lean_ctor_set(v___x_5381_, 1, v_k_5356_);
lean_ctor_set(v___x_5381_, 0, v___x_5427_);
v___x_5429_ = v___x_5381_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v___x_5427_);
lean_ctor_set(v_reuseFailAlloc_5442_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5442_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5442_, 3, v_impl_5364_);
lean_ctor_set(v_reuseFailAlloc_5442_, 4, v_l_5370_);
v___x_5429_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
v_isSharedCheck_5436_ = !lean_is_exclusive(v_impl_5364_);
if (v_isSharedCheck_5436_ == 0)
{
lean_object* v_unused_5437_; lean_object* v_unused_5438_; lean_object* v_unused_5439_; lean_object* v_unused_5440_; lean_object* v_unused_5441_; 
v_unused_5437_ = lean_ctor_get(v_impl_5364_, 4);
lean_dec(v_unused_5437_);
v_unused_5438_ = lean_ctor_get(v_impl_5364_, 3);
lean_dec(v_unused_5438_);
v_unused_5439_ = lean_ctor_get(v_impl_5364_, 2);
lean_dec(v_unused_5439_);
v_unused_5440_ = lean_ctor_get(v_impl_5364_, 1);
lean_dec(v_unused_5440_);
v_unused_5441_ = lean_ctor_get(v_impl_5364_, 0);
lean_dec(v_unused_5441_);
v___x_5431_ = v_impl_5364_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_dec(v_impl_5364_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
lean_ctor_set(v___x_5431_, 4, v_r_5371_);
lean_ctor_set(v___x_5431_, 3, v___x_5429_);
lean_ctor_set(v___x_5431_, 2, v_v_5369_);
lean_ctor_set(v___x_5431_, 1, v_k_5368_);
lean_ctor_set(v___x_5431_, 0, v___x_5426_);
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v___x_5426_);
lean_ctor_set(v_reuseFailAlloc_5435_, 1, v_k_5368_);
lean_ctor_set(v_reuseFailAlloc_5435_, 2, v_v_5369_);
lean_ctor_set(v_reuseFailAlloc_5435_, 3, v___x_5429_);
lean_ctor_set(v_reuseFailAlloc_5435_, 4, v_r_5371_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5449_; lean_object* v___x_5450_; lean_object* v___x_5452_; 
v_size_5449_ = lean_ctor_get(v_impl_5364_, 0);
lean_inc(v_size_5449_);
v___x_5450_ = lean_nat_add(v___x_5365_, v_size_5449_);
lean_dec(v_size_5449_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 3, v_impl_5364_);
lean_ctor_set(v___x_5361_, 0, v___x_5450_);
v___x_5452_ = v___x_5361_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v___x_5450_);
lean_ctor_set(v_reuseFailAlloc_5453_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5453_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5453_, 3, v_impl_5364_);
lean_ctor_set(v_reuseFailAlloc_5453_, 4, v_r_5359_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
else
{
if (lean_obj_tag(v_r_5359_) == 0)
{
lean_object* v_l_5454_; 
v_l_5454_ = lean_ctor_get(v_r_5359_, 3);
lean_inc(v_l_5454_);
if (lean_obj_tag(v_l_5454_) == 0)
{
lean_object* v_r_5455_; 
v_r_5455_ = lean_ctor_get(v_r_5359_, 4);
lean_inc(v_r_5455_);
if (lean_obj_tag(v_r_5455_) == 0)
{
lean_object* v_size_5456_; lean_object* v_k_5457_; lean_object* v_v_5458_; lean_object* v___x_5460_; uint8_t v_isShared_5461_; uint8_t v_isSharedCheck_5471_; 
v_size_5456_ = lean_ctor_get(v_r_5359_, 0);
v_k_5457_ = lean_ctor_get(v_r_5359_, 1);
v_v_5458_ = lean_ctor_get(v_r_5359_, 2);
v_isSharedCheck_5471_ = !lean_is_exclusive(v_r_5359_);
if (v_isSharedCheck_5471_ == 0)
{
lean_object* v_unused_5472_; lean_object* v_unused_5473_; 
v_unused_5472_ = lean_ctor_get(v_r_5359_, 4);
lean_dec(v_unused_5472_);
v_unused_5473_ = lean_ctor_get(v_r_5359_, 3);
lean_dec(v_unused_5473_);
v___x_5460_ = v_r_5359_;
v_isShared_5461_ = v_isSharedCheck_5471_;
goto v_resetjp_5459_;
}
else
{
lean_inc(v_v_5458_);
lean_inc(v_k_5457_);
lean_inc(v_size_5456_);
lean_dec(v_r_5359_);
v___x_5460_ = lean_box(0);
v_isShared_5461_ = v_isSharedCheck_5471_;
goto v_resetjp_5459_;
}
v_resetjp_5459_:
{
lean_object* v_size_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5466_; 
v_size_5462_ = lean_ctor_get(v_l_5454_, 0);
v___x_5463_ = lean_nat_add(v___x_5365_, v_size_5456_);
lean_dec(v_size_5456_);
v___x_5464_ = lean_nat_add(v___x_5365_, v_size_5462_);
if (v_isShared_5461_ == 0)
{
lean_ctor_set(v___x_5460_, 4, v_l_5454_);
lean_ctor_set(v___x_5460_, 3, v_impl_5364_);
lean_ctor_set(v___x_5460_, 2, v_v_5357_);
lean_ctor_set(v___x_5460_, 1, v_k_5356_);
lean_ctor_set(v___x_5460_, 0, v___x_5464_);
v___x_5466_ = v___x_5460_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v___x_5464_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5470_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5470_, 3, v_impl_5364_);
lean_ctor_set(v_reuseFailAlloc_5470_, 4, v_l_5454_);
v___x_5466_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
lean_object* v___x_5468_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v_r_5455_);
lean_ctor_set(v___x_5361_, 3, v___x_5466_);
lean_ctor_set(v___x_5361_, 2, v_v_5458_);
lean_ctor_set(v___x_5361_, 1, v_k_5457_);
lean_ctor_set(v___x_5361_, 0, v___x_5463_);
v___x_5468_ = v___x_5361_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v___x_5463_);
lean_ctor_set(v_reuseFailAlloc_5469_, 1, v_k_5457_);
lean_ctor_set(v_reuseFailAlloc_5469_, 2, v_v_5458_);
lean_ctor_set(v_reuseFailAlloc_5469_, 3, v___x_5466_);
lean_ctor_set(v_reuseFailAlloc_5469_, 4, v_r_5455_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
else
{
lean_object* v_k_5474_; lean_object* v_v_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5498_; 
v_k_5474_ = lean_ctor_get(v_r_5359_, 1);
v_v_5475_ = lean_ctor_get(v_r_5359_, 2);
v_isSharedCheck_5498_ = !lean_is_exclusive(v_r_5359_);
if (v_isSharedCheck_5498_ == 0)
{
lean_object* v_unused_5499_; lean_object* v_unused_5500_; lean_object* v_unused_5501_; 
v_unused_5499_ = lean_ctor_get(v_r_5359_, 4);
lean_dec(v_unused_5499_);
v_unused_5500_ = lean_ctor_get(v_r_5359_, 3);
lean_dec(v_unused_5500_);
v_unused_5501_ = lean_ctor_get(v_r_5359_, 0);
lean_dec(v_unused_5501_);
v___x_5477_ = v_r_5359_;
v_isShared_5478_ = v_isSharedCheck_5498_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_v_5475_);
lean_inc(v_k_5474_);
lean_dec(v_r_5359_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5498_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v_k_5479_; lean_object* v_v_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5494_; 
v_k_5479_ = lean_ctor_get(v_l_5454_, 1);
v_v_5480_ = lean_ctor_get(v_l_5454_, 2);
v_isSharedCheck_5494_ = !lean_is_exclusive(v_l_5454_);
if (v_isSharedCheck_5494_ == 0)
{
lean_object* v_unused_5495_; lean_object* v_unused_5496_; lean_object* v_unused_5497_; 
v_unused_5495_ = lean_ctor_get(v_l_5454_, 4);
lean_dec(v_unused_5495_);
v_unused_5496_ = lean_ctor_get(v_l_5454_, 3);
lean_dec(v_unused_5496_);
v_unused_5497_ = lean_ctor_get(v_l_5454_, 0);
lean_dec(v_unused_5497_);
v___x_5482_ = v_l_5454_;
v_isShared_5483_ = v_isSharedCheck_5494_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_v_5480_);
lean_inc(v_k_5479_);
lean_dec(v_l_5454_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5494_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5484_; lean_object* v___x_5486_; 
v___x_5484_ = lean_unsigned_to_nat(3u);
if (v_isShared_5483_ == 0)
{
lean_ctor_set(v___x_5482_, 4, v_r_5455_);
lean_ctor_set(v___x_5482_, 3, v_r_5455_);
lean_ctor_set(v___x_5482_, 2, v_v_5357_);
lean_ctor_set(v___x_5482_, 1, v_k_5356_);
lean_ctor_set(v___x_5482_, 0, v___x_5365_);
v___x_5486_ = v___x_5482_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5365_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5493_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5493_, 3, v_r_5455_);
lean_ctor_set(v_reuseFailAlloc_5493_, 4, v_r_5455_);
v___x_5486_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
lean_object* v___x_5488_; 
if (v_isShared_5478_ == 0)
{
lean_ctor_set(v___x_5477_, 3, v_r_5455_);
lean_ctor_set(v___x_5477_, 0, v___x_5365_);
v___x_5488_ = v___x_5477_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___x_5365_);
lean_ctor_set(v_reuseFailAlloc_5492_, 1, v_k_5474_);
lean_ctor_set(v_reuseFailAlloc_5492_, 2, v_v_5475_);
lean_ctor_set(v_reuseFailAlloc_5492_, 3, v_r_5455_);
lean_ctor_set(v_reuseFailAlloc_5492_, 4, v_r_5455_);
v___x_5488_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
lean_object* v___x_5490_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v___x_5488_);
lean_ctor_set(v___x_5361_, 3, v___x_5486_);
lean_ctor_set(v___x_5361_, 2, v_v_5480_);
lean_ctor_set(v___x_5361_, 1, v_k_5479_);
lean_ctor_set(v___x_5361_, 0, v___x_5484_);
v___x_5490_ = v___x_5361_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5484_);
lean_ctor_set(v_reuseFailAlloc_5491_, 1, v_k_5479_);
lean_ctor_set(v_reuseFailAlloc_5491_, 2, v_v_5480_);
lean_ctor_set(v_reuseFailAlloc_5491_, 3, v___x_5486_);
lean_ctor_set(v_reuseFailAlloc_5491_, 4, v___x_5488_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_5502_; 
v_r_5502_ = lean_ctor_get(v_r_5359_, 4);
lean_inc(v_r_5502_);
if (lean_obj_tag(v_r_5502_) == 0)
{
lean_object* v_k_5503_; lean_object* v_v_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5515_; 
v_k_5503_ = lean_ctor_get(v_r_5359_, 1);
v_v_5504_ = lean_ctor_get(v_r_5359_, 2);
v_isSharedCheck_5515_ = !lean_is_exclusive(v_r_5359_);
if (v_isSharedCheck_5515_ == 0)
{
lean_object* v_unused_5516_; lean_object* v_unused_5517_; lean_object* v_unused_5518_; 
v_unused_5516_ = lean_ctor_get(v_r_5359_, 4);
lean_dec(v_unused_5516_);
v_unused_5517_ = lean_ctor_get(v_r_5359_, 3);
lean_dec(v_unused_5517_);
v_unused_5518_ = lean_ctor_get(v_r_5359_, 0);
lean_dec(v_unused_5518_);
v___x_5506_ = v_r_5359_;
v_isShared_5507_ = v_isSharedCheck_5515_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_v_5504_);
lean_inc(v_k_5503_);
lean_dec(v_r_5359_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5515_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5508_; lean_object* v___x_5510_; 
v___x_5508_ = lean_unsigned_to_nat(3u);
if (v_isShared_5507_ == 0)
{
lean_ctor_set(v___x_5506_, 4, v_l_5454_);
lean_ctor_set(v___x_5506_, 2, v_v_5357_);
lean_ctor_set(v___x_5506_, 1, v_k_5356_);
lean_ctor_set(v___x_5506_, 0, v___x_5365_);
v___x_5510_ = v___x_5506_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v___x_5365_);
lean_ctor_set(v_reuseFailAlloc_5514_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5514_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5514_, 3, v_l_5454_);
lean_ctor_set(v_reuseFailAlloc_5514_, 4, v_l_5454_);
v___x_5510_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5512_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v_r_5502_);
lean_ctor_set(v___x_5361_, 3, v___x_5510_);
lean_ctor_set(v___x_5361_, 2, v_v_5504_);
lean_ctor_set(v___x_5361_, 1, v_k_5503_);
lean_ctor_set(v___x_5361_, 0, v___x_5508_);
v___x_5512_ = v___x_5361_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v___x_5508_);
lean_ctor_set(v_reuseFailAlloc_5513_, 1, v_k_5503_);
lean_ctor_set(v_reuseFailAlloc_5513_, 2, v_v_5504_);
lean_ctor_set(v_reuseFailAlloc_5513_, 3, v___x_5510_);
lean_ctor_set(v_reuseFailAlloc_5513_, 4, v_r_5502_);
v___x_5512_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
return v___x_5512_;
}
}
}
}
else
{
lean_object* v_size_5519_; lean_object* v_k_5520_; lean_object* v_v_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5532_; 
v_size_5519_ = lean_ctor_get(v_r_5359_, 0);
v_k_5520_ = lean_ctor_get(v_r_5359_, 1);
v_v_5521_ = lean_ctor_get(v_r_5359_, 2);
v_isSharedCheck_5532_ = !lean_is_exclusive(v_r_5359_);
if (v_isSharedCheck_5532_ == 0)
{
lean_object* v_unused_5533_; lean_object* v_unused_5534_; 
v_unused_5533_ = lean_ctor_get(v_r_5359_, 4);
lean_dec(v_unused_5533_);
v_unused_5534_ = lean_ctor_get(v_r_5359_, 3);
lean_dec(v_unused_5534_);
v___x_5523_ = v_r_5359_;
v_isShared_5524_ = v_isSharedCheck_5532_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_v_5521_);
lean_inc(v_k_5520_);
lean_inc(v_size_5519_);
lean_dec(v_r_5359_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5532_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5526_; 
if (v_isShared_5524_ == 0)
{
lean_ctor_set(v___x_5523_, 3, v_r_5502_);
v___x_5526_ = v___x_5523_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_size_5519_);
lean_ctor_set(v_reuseFailAlloc_5531_, 1, v_k_5520_);
lean_ctor_set(v_reuseFailAlloc_5531_, 2, v_v_5521_);
lean_ctor_set(v_reuseFailAlloc_5531_, 3, v_r_5502_);
lean_ctor_set(v_reuseFailAlloc_5531_, 4, v_r_5502_);
v___x_5526_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5527_; lean_object* v___x_5529_; 
v___x_5527_ = lean_unsigned_to_nat(2u);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v___x_5526_);
lean_ctor_set(v___x_5361_, 3, v_r_5502_);
lean_ctor_set(v___x_5361_, 0, v___x_5527_);
v___x_5529_ = v___x_5361_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5527_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5530_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5530_, 3, v_r_5502_);
lean_ctor_set(v_reuseFailAlloc_5530_, 4, v___x_5526_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
}
}
else
{
lean_object* v___x_5536_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 3, v_r_5359_);
lean_ctor_set(v___x_5361_, 0, v___x_5365_);
v___x_5536_ = v___x_5361_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v___x_5365_);
lean_ctor_set(v_reuseFailAlloc_5537_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5537_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5537_, 3, v_r_5359_);
lean_ctor_set(v_reuseFailAlloc_5537_, 4, v_r_5359_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
}
case 1:
{
lean_del_object(v___x_5361_);
lean_dec(v_v_5357_);
lean_dec(v_k_5356_);
if (lean_obj_tag(v_l_5358_) == 0)
{
if (lean_obj_tag(v_r_5359_) == 0)
{
lean_object* v_size_5538_; lean_object* v_k_5539_; lean_object* v_v_5540_; lean_object* v_l_5541_; lean_object* v_r_5542_; lean_object* v_size_5543_; lean_object* v_k_5544_; lean_object* v_v_5545_; lean_object* v_l_5546_; lean_object* v_r_5547_; lean_object* v___x_5548_; uint8_t v___x_5549_; 
v_size_5538_ = lean_ctor_get(v_l_5358_, 0);
v_k_5539_ = lean_ctor_get(v_l_5358_, 1);
v_v_5540_ = lean_ctor_get(v_l_5358_, 2);
v_l_5541_ = lean_ctor_get(v_l_5358_, 3);
v_r_5542_ = lean_ctor_get(v_l_5358_, 4);
lean_inc(v_r_5542_);
v_size_5543_ = lean_ctor_get(v_r_5359_, 0);
v_k_5544_ = lean_ctor_get(v_r_5359_, 1);
v_v_5545_ = lean_ctor_get(v_r_5359_, 2);
v_l_5546_ = lean_ctor_get(v_r_5359_, 3);
lean_inc(v_l_5546_);
v_r_5547_ = lean_ctor_get(v_r_5359_, 4);
v___x_5548_ = lean_unsigned_to_nat(1u);
v___x_5549_ = lean_nat_dec_lt(v_size_5538_, v_size_5543_);
if (v___x_5549_ == 0)
{
lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5685_; 
lean_inc(v_l_5541_);
lean_inc(v_v_5540_);
lean_inc(v_k_5539_);
v_isSharedCheck_5685_ = !lean_is_exclusive(v_l_5358_);
if (v_isSharedCheck_5685_ == 0)
{
lean_object* v_unused_5686_; lean_object* v_unused_5687_; lean_object* v_unused_5688_; lean_object* v_unused_5689_; lean_object* v_unused_5690_; 
v_unused_5686_ = lean_ctor_get(v_l_5358_, 4);
lean_dec(v_unused_5686_);
v_unused_5687_ = lean_ctor_get(v_l_5358_, 3);
lean_dec(v_unused_5687_);
v_unused_5688_ = lean_ctor_get(v_l_5358_, 2);
lean_dec(v_unused_5688_);
v_unused_5689_ = lean_ctor_get(v_l_5358_, 1);
lean_dec(v_unused_5689_);
v_unused_5690_ = lean_ctor_get(v_l_5358_, 0);
lean_dec(v_unused_5690_);
v___x_5551_ = v_l_5358_;
v_isShared_5552_ = v_isSharedCheck_5685_;
goto v_resetjp_5550_;
}
else
{
lean_dec(v_l_5358_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5685_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5553_; lean_object* v_tree_5554_; 
v___x_5553_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5539_, v_v_5540_, v_l_5541_, v_r_5542_);
v_tree_5554_ = lean_ctor_get(v___x_5553_, 2);
lean_inc(v_tree_5554_);
if (lean_obj_tag(v_tree_5554_) == 0)
{
lean_object* v_k_5555_; lean_object* v_v_5556_; lean_object* v_size_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; uint8_t v___x_5560_; 
v_k_5555_ = lean_ctor_get(v___x_5553_, 0);
lean_inc(v_k_5555_);
v_v_5556_ = lean_ctor_get(v___x_5553_, 1);
lean_inc(v_v_5556_);
lean_dec_ref(v___x_5553_);
v_size_5557_ = lean_ctor_get(v_tree_5554_, 0);
v___x_5558_ = lean_unsigned_to_nat(3u);
v___x_5559_ = lean_nat_mul(v___x_5558_, v_size_5557_);
v___x_5560_ = lean_nat_dec_lt(v___x_5559_, v_size_5543_);
lean_dec(v___x_5559_);
if (v___x_5560_ == 0)
{
lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5564_; 
lean_dec(v_l_5546_);
v___x_5561_ = lean_nat_add(v___x_5548_, v_size_5557_);
v___x_5562_ = lean_nat_add(v___x_5561_, v_size_5543_);
lean_dec(v___x_5561_);
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 4, v_r_5359_);
lean_ctor_set(v___x_5551_, 3, v_tree_5554_);
lean_ctor_set(v___x_5551_, 2, v_v_5556_);
lean_ctor_set(v___x_5551_, 1, v_k_5555_);
lean_ctor_set(v___x_5551_, 0, v___x_5562_);
v___x_5564_ = v___x_5551_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5562_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5565_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5565_, 3, v_tree_5554_);
lean_ctor_set(v_reuseFailAlloc_5565_, 4, v_r_5359_);
v___x_5564_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
return v___x_5564_;
}
}
else
{
lean_object* v___x_5567_; uint8_t v_isShared_5568_; uint8_t v_isSharedCheck_5620_; 
lean_inc(v_r_5547_);
lean_inc(v_v_5545_);
lean_inc(v_k_5544_);
lean_inc(v_size_5543_);
v_isSharedCheck_5620_ = !lean_is_exclusive(v_r_5359_);
if (v_isSharedCheck_5620_ == 0)
{
lean_object* v_unused_5621_; lean_object* v_unused_5622_; lean_object* v_unused_5623_; lean_object* v_unused_5624_; lean_object* v_unused_5625_; 
v_unused_5621_ = lean_ctor_get(v_r_5359_, 4);
lean_dec(v_unused_5621_);
v_unused_5622_ = lean_ctor_get(v_r_5359_, 3);
lean_dec(v_unused_5622_);
v_unused_5623_ = lean_ctor_get(v_r_5359_, 2);
lean_dec(v_unused_5623_);
v_unused_5624_ = lean_ctor_get(v_r_5359_, 1);
lean_dec(v_unused_5624_);
v_unused_5625_ = lean_ctor_get(v_r_5359_, 0);
lean_dec(v_unused_5625_);
v___x_5567_ = v_r_5359_;
v_isShared_5568_ = v_isSharedCheck_5620_;
goto v_resetjp_5566_;
}
else
{
lean_dec(v_r_5359_);
v___x_5567_ = lean_box(0);
v_isShared_5568_ = v_isSharedCheck_5620_;
goto v_resetjp_5566_;
}
v_resetjp_5566_:
{
lean_object* v_size_5569_; lean_object* v_k_5570_; lean_object* v_v_5571_; lean_object* v_l_5572_; lean_object* v_r_5573_; lean_object* v_size_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; uint8_t v___x_5577_; 
v_size_5569_ = lean_ctor_get(v_l_5546_, 0);
v_k_5570_ = lean_ctor_get(v_l_5546_, 1);
v_v_5571_ = lean_ctor_get(v_l_5546_, 2);
v_l_5572_ = lean_ctor_get(v_l_5546_, 3);
v_r_5573_ = lean_ctor_get(v_l_5546_, 4);
v_size_5574_ = lean_ctor_get(v_r_5547_, 0);
v___x_5575_ = lean_unsigned_to_nat(2u);
v___x_5576_ = lean_nat_mul(v___x_5575_, v_size_5574_);
v___x_5577_ = lean_nat_dec_lt(v_size_5569_, v___x_5576_);
lean_dec(v___x_5576_);
if (v___x_5577_ == 0)
{
lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5605_; 
lean_inc(v_r_5573_);
lean_inc(v_l_5572_);
lean_inc(v_v_5571_);
lean_inc(v_k_5570_);
v_isSharedCheck_5605_ = !lean_is_exclusive(v_l_5546_);
if (v_isSharedCheck_5605_ == 0)
{
lean_object* v_unused_5606_; lean_object* v_unused_5607_; lean_object* v_unused_5608_; lean_object* v_unused_5609_; lean_object* v_unused_5610_; 
v_unused_5606_ = lean_ctor_get(v_l_5546_, 4);
lean_dec(v_unused_5606_);
v_unused_5607_ = lean_ctor_get(v_l_5546_, 3);
lean_dec(v_unused_5607_);
v_unused_5608_ = lean_ctor_get(v_l_5546_, 2);
lean_dec(v_unused_5608_);
v_unused_5609_ = lean_ctor_get(v_l_5546_, 1);
lean_dec(v_unused_5609_);
v_unused_5610_ = lean_ctor_get(v_l_5546_, 0);
lean_dec(v_unused_5610_);
v___x_5579_ = v_l_5546_;
v_isShared_5580_ = v_isSharedCheck_5605_;
goto v_resetjp_5578_;
}
else
{
lean_dec(v_l_5546_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5605_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___y_5584_; lean_object* v___y_5585_; lean_object* v___y_5586_; lean_object* v___y_5595_; 
v___x_5581_ = lean_nat_add(v___x_5548_, v_size_5557_);
v___x_5582_ = lean_nat_add(v___x_5581_, v_size_5543_);
lean_dec(v_size_5543_);
if (lean_obj_tag(v_l_5572_) == 0)
{
lean_object* v_size_5603_; 
v_size_5603_ = lean_ctor_get(v_l_5572_, 0);
lean_inc(v_size_5603_);
v___y_5595_ = v_size_5603_;
goto v___jp_5594_;
}
else
{
lean_object* v___x_5604_; 
v___x_5604_ = lean_unsigned_to_nat(0u);
v___y_5595_ = v___x_5604_;
goto v___jp_5594_;
}
v___jp_5583_:
{
lean_object* v___x_5587_; lean_object* v___x_5589_; 
v___x_5587_ = lean_nat_add(v___y_5584_, v___y_5586_);
lean_dec(v___y_5586_);
lean_dec(v___y_5584_);
if (v_isShared_5580_ == 0)
{
lean_ctor_set(v___x_5579_, 4, v_r_5547_);
lean_ctor_set(v___x_5579_, 3, v_r_5573_);
lean_ctor_set(v___x_5579_, 2, v_v_5545_);
lean_ctor_set(v___x_5579_, 1, v_k_5544_);
lean_ctor_set(v___x_5579_, 0, v___x_5587_);
v___x_5589_ = v___x_5579_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v___x_5587_);
lean_ctor_set(v_reuseFailAlloc_5593_, 1, v_k_5544_);
lean_ctor_set(v_reuseFailAlloc_5593_, 2, v_v_5545_);
lean_ctor_set(v_reuseFailAlloc_5593_, 3, v_r_5573_);
lean_ctor_set(v_reuseFailAlloc_5593_, 4, v_r_5547_);
v___x_5589_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
lean_object* v___x_5591_; 
if (v_isShared_5568_ == 0)
{
lean_ctor_set(v___x_5567_, 4, v___x_5589_);
lean_ctor_set(v___x_5567_, 3, v___y_5585_);
lean_ctor_set(v___x_5567_, 2, v_v_5571_);
lean_ctor_set(v___x_5567_, 1, v_k_5570_);
lean_ctor_set(v___x_5567_, 0, v___x_5582_);
v___x_5591_ = v___x_5567_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5582_);
lean_ctor_set(v_reuseFailAlloc_5592_, 1, v_k_5570_);
lean_ctor_set(v_reuseFailAlloc_5592_, 2, v_v_5571_);
lean_ctor_set(v_reuseFailAlloc_5592_, 3, v___y_5585_);
lean_ctor_set(v_reuseFailAlloc_5592_, 4, v___x_5589_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
v___jp_5594_:
{
lean_object* v___x_5596_; lean_object* v___x_5598_; 
v___x_5596_ = lean_nat_add(v___x_5581_, v___y_5595_);
lean_dec(v___y_5595_);
lean_dec(v___x_5581_);
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 4, v_l_5572_);
lean_ctor_set(v___x_5551_, 3, v_tree_5554_);
lean_ctor_set(v___x_5551_, 2, v_v_5556_);
lean_ctor_set(v___x_5551_, 1, v_k_5555_);
lean_ctor_set(v___x_5551_, 0, v___x_5596_);
v___x_5598_ = v___x_5551_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v___x_5596_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5602_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5602_, 3, v_tree_5554_);
lean_ctor_set(v_reuseFailAlloc_5602_, 4, v_l_5572_);
v___x_5598_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5599_; 
v___x_5599_ = lean_nat_add(v___x_5548_, v_size_5574_);
if (lean_obj_tag(v_r_5573_) == 0)
{
lean_object* v_size_5600_; 
v_size_5600_ = lean_ctor_get(v_r_5573_, 0);
lean_inc(v_size_5600_);
v___y_5584_ = v___x_5599_;
v___y_5585_ = v___x_5598_;
v___y_5586_ = v_size_5600_;
goto v___jp_5583_;
}
else
{
lean_object* v___x_5601_; 
v___x_5601_ = lean_unsigned_to_nat(0u);
v___y_5584_ = v___x_5599_;
v___y_5585_ = v___x_5598_;
v___y_5586_ = v___x_5601_;
goto v___jp_5583_;
}
}
}
}
}
else
{
lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5615_; 
v___x_5611_ = lean_nat_add(v___x_5548_, v_size_5557_);
v___x_5612_ = lean_nat_add(v___x_5611_, v_size_5543_);
lean_dec(v_size_5543_);
v___x_5613_ = lean_nat_add(v___x_5611_, v_size_5569_);
lean_dec(v___x_5611_);
if (v_isShared_5568_ == 0)
{
lean_ctor_set(v___x_5567_, 4, v_l_5546_);
lean_ctor_set(v___x_5567_, 3, v_tree_5554_);
lean_ctor_set(v___x_5567_, 2, v_v_5556_);
lean_ctor_set(v___x_5567_, 1, v_k_5555_);
lean_ctor_set(v___x_5567_, 0, v___x_5613_);
v___x_5615_ = v___x_5567_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5613_);
lean_ctor_set(v_reuseFailAlloc_5619_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5619_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5619_, 3, v_tree_5554_);
lean_ctor_set(v_reuseFailAlloc_5619_, 4, v_l_5546_);
v___x_5615_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
lean_object* v___x_5617_; 
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 4, v_r_5547_);
lean_ctor_set(v___x_5551_, 3, v___x_5615_);
lean_ctor_set(v___x_5551_, 2, v_v_5545_);
lean_ctor_set(v___x_5551_, 1, v_k_5544_);
lean_ctor_set(v___x_5551_, 0, v___x_5612_);
v___x_5617_ = v___x_5551_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5612_);
lean_ctor_set(v_reuseFailAlloc_5618_, 1, v_k_5544_);
lean_ctor_set(v_reuseFailAlloc_5618_, 2, v_v_5545_);
lean_ctor_set(v_reuseFailAlloc_5618_, 3, v___x_5615_);
lean_ctor_set(v_reuseFailAlloc_5618_, 4, v_r_5547_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
}
}
}
else
{
lean_object* v___x_5627_; uint8_t v_isShared_5628_; uint8_t v_isSharedCheck_5679_; 
lean_inc(v_r_5547_);
lean_inc(v_v_5545_);
lean_inc(v_k_5544_);
lean_inc(v_size_5543_);
v_isSharedCheck_5679_ = !lean_is_exclusive(v_r_5359_);
if (v_isSharedCheck_5679_ == 0)
{
lean_object* v_unused_5680_; lean_object* v_unused_5681_; lean_object* v_unused_5682_; lean_object* v_unused_5683_; lean_object* v_unused_5684_; 
v_unused_5680_ = lean_ctor_get(v_r_5359_, 4);
lean_dec(v_unused_5680_);
v_unused_5681_ = lean_ctor_get(v_r_5359_, 3);
lean_dec(v_unused_5681_);
v_unused_5682_ = lean_ctor_get(v_r_5359_, 2);
lean_dec(v_unused_5682_);
v_unused_5683_ = lean_ctor_get(v_r_5359_, 1);
lean_dec(v_unused_5683_);
v_unused_5684_ = lean_ctor_get(v_r_5359_, 0);
lean_dec(v_unused_5684_);
v___x_5627_ = v_r_5359_;
v_isShared_5628_ = v_isSharedCheck_5679_;
goto v_resetjp_5626_;
}
else
{
lean_dec(v_r_5359_);
v___x_5627_ = lean_box(0);
v_isShared_5628_ = v_isSharedCheck_5679_;
goto v_resetjp_5626_;
}
v_resetjp_5626_:
{
if (lean_obj_tag(v_l_5546_) == 0)
{
if (lean_obj_tag(v_r_5547_) == 0)
{
lean_object* v_k_5629_; lean_object* v_v_5630_; lean_object* v_size_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5635_; 
v_k_5629_ = lean_ctor_get(v___x_5553_, 0);
lean_inc(v_k_5629_);
v_v_5630_ = lean_ctor_get(v___x_5553_, 1);
lean_inc(v_v_5630_);
lean_dec_ref(v___x_5553_);
v_size_5631_ = lean_ctor_get(v_l_5546_, 0);
v___x_5632_ = lean_nat_add(v___x_5548_, v_size_5543_);
lean_dec(v_size_5543_);
v___x_5633_ = lean_nat_add(v___x_5548_, v_size_5631_);
if (v_isShared_5628_ == 0)
{
lean_ctor_set(v___x_5627_, 4, v_l_5546_);
lean_ctor_set(v___x_5627_, 3, v_tree_5554_);
lean_ctor_set(v___x_5627_, 2, v_v_5630_);
lean_ctor_set(v___x_5627_, 1, v_k_5629_);
lean_ctor_set(v___x_5627_, 0, v___x_5633_);
v___x_5635_ = v___x_5627_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5633_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v_k_5629_);
lean_ctor_set(v_reuseFailAlloc_5639_, 2, v_v_5630_);
lean_ctor_set(v_reuseFailAlloc_5639_, 3, v_tree_5554_);
lean_ctor_set(v_reuseFailAlloc_5639_, 4, v_l_5546_);
v___x_5635_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
lean_object* v___x_5637_; 
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 4, v_r_5547_);
lean_ctor_set(v___x_5551_, 3, v___x_5635_);
lean_ctor_set(v___x_5551_, 2, v_v_5545_);
lean_ctor_set(v___x_5551_, 1, v_k_5544_);
lean_ctor_set(v___x_5551_, 0, v___x_5632_);
v___x_5637_ = v___x_5551_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v___x_5632_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v_k_5544_);
lean_ctor_set(v_reuseFailAlloc_5638_, 2, v_v_5545_);
lean_ctor_set(v_reuseFailAlloc_5638_, 3, v___x_5635_);
lean_ctor_set(v_reuseFailAlloc_5638_, 4, v_r_5547_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
else
{
lean_object* v_k_5640_; lean_object* v_v_5641_; lean_object* v_k_5642_; lean_object* v_v_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5657_; 
lean_dec(v_size_5543_);
v_k_5640_ = lean_ctor_get(v___x_5553_, 0);
lean_inc(v_k_5640_);
v_v_5641_ = lean_ctor_get(v___x_5553_, 1);
lean_inc(v_v_5641_);
lean_dec_ref(v___x_5553_);
v_k_5642_ = lean_ctor_get(v_l_5546_, 1);
v_v_5643_ = lean_ctor_get(v_l_5546_, 2);
v_isSharedCheck_5657_ = !lean_is_exclusive(v_l_5546_);
if (v_isSharedCheck_5657_ == 0)
{
lean_object* v_unused_5658_; lean_object* v_unused_5659_; lean_object* v_unused_5660_; 
v_unused_5658_ = lean_ctor_get(v_l_5546_, 4);
lean_dec(v_unused_5658_);
v_unused_5659_ = lean_ctor_get(v_l_5546_, 3);
lean_dec(v_unused_5659_);
v_unused_5660_ = lean_ctor_get(v_l_5546_, 0);
lean_dec(v_unused_5660_);
v___x_5645_ = v_l_5546_;
v_isShared_5646_ = v_isSharedCheck_5657_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_v_5643_);
lean_inc(v_k_5642_);
lean_dec(v_l_5546_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5657_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5647_; lean_object* v___x_5649_; 
v___x_5647_ = lean_unsigned_to_nat(3u);
if (v_isShared_5646_ == 0)
{
lean_ctor_set(v___x_5645_, 4, v_r_5547_);
lean_ctor_set(v___x_5645_, 3, v_r_5547_);
lean_ctor_set(v___x_5645_, 2, v_v_5641_);
lean_ctor_set(v___x_5645_, 1, v_k_5640_);
lean_ctor_set(v___x_5645_, 0, v___x_5548_);
v___x_5649_ = v___x_5645_;
goto v_reusejp_5648_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5656_, 1, v_k_5640_);
lean_ctor_set(v_reuseFailAlloc_5656_, 2, v_v_5641_);
lean_ctor_set(v_reuseFailAlloc_5656_, 3, v_r_5547_);
lean_ctor_set(v_reuseFailAlloc_5656_, 4, v_r_5547_);
v___x_5649_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5648_;
}
v_reusejp_5648_:
{
lean_object* v___x_5651_; 
if (v_isShared_5628_ == 0)
{
lean_ctor_set(v___x_5627_, 3, v_r_5547_);
lean_ctor_set(v___x_5627_, 0, v___x_5548_);
v___x_5651_ = v___x_5627_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5655_, 1, v_k_5544_);
lean_ctor_set(v_reuseFailAlloc_5655_, 2, v_v_5545_);
lean_ctor_set(v_reuseFailAlloc_5655_, 3, v_r_5547_);
lean_ctor_set(v_reuseFailAlloc_5655_, 4, v_r_5547_);
v___x_5651_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
lean_object* v___x_5653_; 
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 4, v___x_5651_);
lean_ctor_set(v___x_5551_, 3, v___x_5649_);
lean_ctor_set(v___x_5551_, 2, v_v_5643_);
lean_ctor_set(v___x_5551_, 1, v_k_5642_);
lean_ctor_set(v___x_5551_, 0, v___x_5647_);
v___x_5653_ = v___x_5551_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v___x_5647_);
lean_ctor_set(v_reuseFailAlloc_5654_, 1, v_k_5642_);
lean_ctor_set(v_reuseFailAlloc_5654_, 2, v_v_5643_);
lean_ctor_set(v_reuseFailAlloc_5654_, 3, v___x_5649_);
lean_ctor_set(v_reuseFailAlloc_5654_, 4, v___x_5651_);
v___x_5653_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
return v___x_5653_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5547_) == 0)
{
lean_object* v_k_5661_; lean_object* v_v_5662_; lean_object* v___x_5663_; lean_object* v___x_5665_; 
lean_dec(v_size_5543_);
v_k_5661_ = lean_ctor_get(v___x_5553_, 0);
lean_inc(v_k_5661_);
v_v_5662_ = lean_ctor_get(v___x_5553_, 1);
lean_inc(v_v_5662_);
lean_dec_ref(v___x_5553_);
v___x_5663_ = lean_unsigned_to_nat(3u);
if (v_isShared_5628_ == 0)
{
lean_ctor_set(v___x_5627_, 4, v_l_5546_);
lean_ctor_set(v___x_5627_, 2, v_v_5662_);
lean_ctor_set(v___x_5627_, 1, v_k_5661_);
lean_ctor_set(v___x_5627_, 0, v___x_5548_);
v___x_5665_ = v___x_5627_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5669_, 1, v_k_5661_);
lean_ctor_set(v_reuseFailAlloc_5669_, 2, v_v_5662_);
lean_ctor_set(v_reuseFailAlloc_5669_, 3, v_l_5546_);
lean_ctor_set(v_reuseFailAlloc_5669_, 4, v_l_5546_);
v___x_5665_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
lean_object* v___x_5667_; 
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 4, v_r_5547_);
lean_ctor_set(v___x_5551_, 3, v___x_5665_);
lean_ctor_set(v___x_5551_, 2, v_v_5545_);
lean_ctor_set(v___x_5551_, 1, v_k_5544_);
lean_ctor_set(v___x_5551_, 0, v___x_5663_);
v___x_5667_ = v___x_5551_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v___x_5663_);
lean_ctor_set(v_reuseFailAlloc_5668_, 1, v_k_5544_);
lean_ctor_set(v_reuseFailAlloc_5668_, 2, v_v_5545_);
lean_ctor_set(v_reuseFailAlloc_5668_, 3, v___x_5665_);
lean_ctor_set(v_reuseFailAlloc_5668_, 4, v_r_5547_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
}
else
{
lean_object* v_k_5670_; lean_object* v_v_5671_; lean_object* v___x_5673_; 
v_k_5670_ = lean_ctor_get(v___x_5553_, 0);
lean_inc(v_k_5670_);
v_v_5671_ = lean_ctor_get(v___x_5553_, 1);
lean_inc(v_v_5671_);
lean_dec_ref(v___x_5553_);
if (v_isShared_5628_ == 0)
{
lean_ctor_set(v___x_5627_, 3, v_r_5547_);
v___x_5673_ = v___x_5627_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_size_5543_);
lean_ctor_set(v_reuseFailAlloc_5678_, 1, v_k_5544_);
lean_ctor_set(v_reuseFailAlloc_5678_, 2, v_v_5545_);
lean_ctor_set(v_reuseFailAlloc_5678_, 3, v_r_5547_);
lean_ctor_set(v_reuseFailAlloc_5678_, 4, v_r_5547_);
v___x_5673_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
lean_object* v___x_5674_; lean_object* v___x_5676_; 
v___x_5674_ = lean_unsigned_to_nat(2u);
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 4, v___x_5673_);
lean_ctor_set(v___x_5551_, 3, v_r_5547_);
lean_ctor_set(v___x_5551_, 2, v_v_5671_);
lean_ctor_set(v___x_5551_, 1, v_k_5670_);
lean_ctor_set(v___x_5551_, 0, v___x_5674_);
v___x_5676_ = v___x_5551_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v___x_5674_);
lean_ctor_set(v_reuseFailAlloc_5677_, 1, v_k_5670_);
lean_ctor_set(v_reuseFailAlloc_5677_, 2, v_v_5671_);
lean_ctor_set(v_reuseFailAlloc_5677_, 3, v_r_5547_);
lean_ctor_set(v_reuseFailAlloc_5677_, 4, v___x_5673_);
v___x_5676_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
return v___x_5676_;
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
lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5843_; 
lean_inc(v_r_5547_);
lean_inc(v_v_5545_);
lean_inc(v_k_5544_);
v_isSharedCheck_5843_ = !lean_is_exclusive(v_r_5359_);
if (v_isSharedCheck_5843_ == 0)
{
lean_object* v_unused_5844_; lean_object* v_unused_5845_; lean_object* v_unused_5846_; lean_object* v_unused_5847_; lean_object* v_unused_5848_; 
v_unused_5844_ = lean_ctor_get(v_r_5359_, 4);
lean_dec(v_unused_5844_);
v_unused_5845_ = lean_ctor_get(v_r_5359_, 3);
lean_dec(v_unused_5845_);
v_unused_5846_ = lean_ctor_get(v_r_5359_, 2);
lean_dec(v_unused_5846_);
v_unused_5847_ = lean_ctor_get(v_r_5359_, 1);
lean_dec(v_unused_5847_);
v_unused_5848_ = lean_ctor_get(v_r_5359_, 0);
lean_dec(v_unused_5848_);
v___x_5692_ = v_r_5359_;
v_isShared_5693_ = v_isSharedCheck_5843_;
goto v_resetjp_5691_;
}
else
{
lean_dec(v_r_5359_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5843_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5694_; lean_object* v_tree_5695_; 
v___x_5694_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5544_, v_v_5545_, v_l_5546_, v_r_5547_);
v_tree_5695_ = lean_ctor_get(v___x_5694_, 2);
lean_inc(v_tree_5695_);
if (lean_obj_tag(v_tree_5695_) == 0)
{
lean_object* v_k_5696_; lean_object* v_v_5697_; lean_object* v_size_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; uint8_t v___x_5701_; 
v_k_5696_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_k_5696_);
v_v_5697_ = lean_ctor_get(v___x_5694_, 1);
lean_inc(v_v_5697_);
lean_dec_ref(v___x_5694_);
v_size_5698_ = lean_ctor_get(v_tree_5695_, 0);
v___x_5699_ = lean_unsigned_to_nat(3u);
v___x_5700_ = lean_nat_mul(v___x_5699_, v_size_5698_);
v___x_5701_ = lean_nat_dec_lt(v___x_5700_, v_size_5538_);
lean_dec(v___x_5700_);
if (v___x_5701_ == 0)
{
lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5705_; 
lean_dec(v_r_5542_);
v___x_5702_ = lean_nat_add(v___x_5548_, v_size_5538_);
v___x_5703_ = lean_nat_add(v___x_5702_, v_size_5698_);
lean_dec(v___x_5702_);
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 4, v_tree_5695_);
lean_ctor_set(v___x_5692_, 3, v_l_5358_);
lean_ctor_set(v___x_5692_, 2, v_v_5697_);
lean_ctor_set(v___x_5692_, 1, v_k_5696_);
lean_ctor_set(v___x_5692_, 0, v___x_5703_);
v___x_5705_ = v___x_5692_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5706_; 
v_reuseFailAlloc_5706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5706_, 0, v___x_5703_);
lean_ctor_set(v_reuseFailAlloc_5706_, 1, v_k_5696_);
lean_ctor_set(v_reuseFailAlloc_5706_, 2, v_v_5697_);
lean_ctor_set(v_reuseFailAlloc_5706_, 3, v_l_5358_);
lean_ctor_set(v_reuseFailAlloc_5706_, 4, v_tree_5695_);
v___x_5705_ = v_reuseFailAlloc_5706_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
return v___x_5705_;
}
}
else
{
lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5772_; 
lean_inc(v_l_5541_);
lean_inc(v_v_5540_);
lean_inc(v_k_5539_);
lean_inc(v_size_5538_);
v_isSharedCheck_5772_ = !lean_is_exclusive(v_l_5358_);
if (v_isSharedCheck_5772_ == 0)
{
lean_object* v_unused_5773_; lean_object* v_unused_5774_; lean_object* v_unused_5775_; lean_object* v_unused_5776_; lean_object* v_unused_5777_; 
v_unused_5773_ = lean_ctor_get(v_l_5358_, 4);
lean_dec(v_unused_5773_);
v_unused_5774_ = lean_ctor_get(v_l_5358_, 3);
lean_dec(v_unused_5774_);
v_unused_5775_ = lean_ctor_get(v_l_5358_, 2);
lean_dec(v_unused_5775_);
v_unused_5776_ = lean_ctor_get(v_l_5358_, 1);
lean_dec(v_unused_5776_);
v_unused_5777_ = lean_ctor_get(v_l_5358_, 0);
lean_dec(v_unused_5777_);
v___x_5708_ = v_l_5358_;
v_isShared_5709_ = v_isSharedCheck_5772_;
goto v_resetjp_5707_;
}
else
{
lean_dec(v_l_5358_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5772_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v_size_5710_; lean_object* v_size_5711_; lean_object* v_k_5712_; lean_object* v_v_5713_; lean_object* v_l_5714_; lean_object* v_r_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; uint8_t v___x_5718_; 
v_size_5710_ = lean_ctor_get(v_l_5541_, 0);
v_size_5711_ = lean_ctor_get(v_r_5542_, 0);
v_k_5712_ = lean_ctor_get(v_r_5542_, 1);
v_v_5713_ = lean_ctor_get(v_r_5542_, 2);
v_l_5714_ = lean_ctor_get(v_r_5542_, 3);
v_r_5715_ = lean_ctor_get(v_r_5542_, 4);
v___x_5716_ = lean_unsigned_to_nat(2u);
v___x_5717_ = lean_nat_mul(v___x_5716_, v_size_5710_);
v___x_5718_ = lean_nat_dec_lt(v_size_5711_, v___x_5717_);
lean_dec(v___x_5717_);
if (v___x_5718_ == 0)
{
lean_object* v___x_5720_; uint8_t v_isShared_5721_; uint8_t v_isSharedCheck_5756_; 
lean_inc(v_r_5715_);
lean_inc(v_l_5714_);
lean_inc(v_v_5713_);
lean_inc(v_k_5712_);
lean_del_object(v___x_5708_);
v_isSharedCheck_5756_ = !lean_is_exclusive(v_r_5542_);
if (v_isSharedCheck_5756_ == 0)
{
lean_object* v_unused_5757_; lean_object* v_unused_5758_; lean_object* v_unused_5759_; lean_object* v_unused_5760_; lean_object* v_unused_5761_; 
v_unused_5757_ = lean_ctor_get(v_r_5542_, 4);
lean_dec(v_unused_5757_);
v_unused_5758_ = lean_ctor_get(v_r_5542_, 3);
lean_dec(v_unused_5758_);
v_unused_5759_ = lean_ctor_get(v_r_5542_, 2);
lean_dec(v_unused_5759_);
v_unused_5760_ = lean_ctor_get(v_r_5542_, 1);
lean_dec(v_unused_5760_);
v_unused_5761_ = lean_ctor_get(v_r_5542_, 0);
lean_dec(v_unused_5761_);
v___x_5720_ = v_r_5542_;
v_isShared_5721_ = v_isSharedCheck_5756_;
goto v_resetjp_5719_;
}
else
{
lean_dec(v_r_5542_);
v___x_5720_ = lean_box(0);
v_isShared_5721_ = v_isSharedCheck_5756_;
goto v_resetjp_5719_;
}
v_resetjp_5719_:
{
lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___y_5725_; lean_object* v___y_5726_; lean_object* v___y_5727_; lean_object* v___x_5744_; lean_object* v___y_5746_; 
v___x_5722_ = lean_nat_add(v___x_5548_, v_size_5538_);
lean_dec(v_size_5538_);
v___x_5723_ = lean_nat_add(v___x_5722_, v_size_5698_);
lean_dec(v___x_5722_);
v___x_5744_ = lean_nat_add(v___x_5548_, v_size_5710_);
if (lean_obj_tag(v_l_5714_) == 0)
{
lean_object* v_size_5754_; 
v_size_5754_ = lean_ctor_get(v_l_5714_, 0);
lean_inc(v_size_5754_);
v___y_5746_ = v_size_5754_;
goto v___jp_5745_;
}
else
{
lean_object* v___x_5755_; 
v___x_5755_ = lean_unsigned_to_nat(0u);
v___y_5746_ = v___x_5755_;
goto v___jp_5745_;
}
v___jp_5724_:
{
lean_object* v___x_5728_; lean_object* v___x_5730_; 
v___x_5728_ = lean_nat_add(v___y_5726_, v___y_5727_);
lean_dec(v___y_5727_);
lean_dec(v___y_5726_);
lean_inc_ref(v_tree_5695_);
if (v_isShared_5721_ == 0)
{
lean_ctor_set(v___x_5720_, 4, v_tree_5695_);
lean_ctor_set(v___x_5720_, 3, v_r_5715_);
lean_ctor_set(v___x_5720_, 2, v_v_5697_);
lean_ctor_set(v___x_5720_, 1, v_k_5696_);
lean_ctor_set(v___x_5720_, 0, v___x_5728_);
v___x_5730_ = v___x_5720_;
goto v_reusejp_5729_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v___x_5728_);
lean_ctor_set(v_reuseFailAlloc_5743_, 1, v_k_5696_);
lean_ctor_set(v_reuseFailAlloc_5743_, 2, v_v_5697_);
lean_ctor_set(v_reuseFailAlloc_5743_, 3, v_r_5715_);
lean_ctor_set(v_reuseFailAlloc_5743_, 4, v_tree_5695_);
v___x_5730_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5729_;
}
v_reusejp_5729_:
{
lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5737_; 
v_isSharedCheck_5737_ = !lean_is_exclusive(v_tree_5695_);
if (v_isSharedCheck_5737_ == 0)
{
lean_object* v_unused_5738_; lean_object* v_unused_5739_; lean_object* v_unused_5740_; lean_object* v_unused_5741_; lean_object* v_unused_5742_; 
v_unused_5738_ = lean_ctor_get(v_tree_5695_, 4);
lean_dec(v_unused_5738_);
v_unused_5739_ = lean_ctor_get(v_tree_5695_, 3);
lean_dec(v_unused_5739_);
v_unused_5740_ = lean_ctor_get(v_tree_5695_, 2);
lean_dec(v_unused_5740_);
v_unused_5741_ = lean_ctor_get(v_tree_5695_, 1);
lean_dec(v_unused_5741_);
v_unused_5742_ = lean_ctor_get(v_tree_5695_, 0);
lean_dec(v_unused_5742_);
v___x_5732_ = v_tree_5695_;
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
else
{
lean_dec(v_tree_5695_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5735_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 4, v___x_5730_);
lean_ctor_set(v___x_5732_, 3, v___y_5725_);
lean_ctor_set(v___x_5732_, 2, v_v_5713_);
lean_ctor_set(v___x_5732_, 1, v_k_5712_);
lean_ctor_set(v___x_5732_, 0, v___x_5723_);
v___x_5735_ = v___x_5732_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v___x_5723_);
lean_ctor_set(v_reuseFailAlloc_5736_, 1, v_k_5712_);
lean_ctor_set(v_reuseFailAlloc_5736_, 2, v_v_5713_);
lean_ctor_set(v_reuseFailAlloc_5736_, 3, v___y_5725_);
lean_ctor_set(v_reuseFailAlloc_5736_, 4, v___x_5730_);
v___x_5735_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
return v___x_5735_;
}
}
}
}
v___jp_5745_:
{
lean_object* v___x_5747_; lean_object* v___x_5749_; 
v___x_5747_ = lean_nat_add(v___x_5744_, v___y_5746_);
lean_dec(v___y_5746_);
lean_dec(v___x_5744_);
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 4, v_l_5714_);
lean_ctor_set(v___x_5692_, 3, v_l_5541_);
lean_ctor_set(v___x_5692_, 2, v_v_5540_);
lean_ctor_set(v___x_5692_, 1, v_k_5539_);
lean_ctor_set(v___x_5692_, 0, v___x_5747_);
v___x_5749_ = v___x_5692_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v___x_5747_);
lean_ctor_set(v_reuseFailAlloc_5753_, 1, v_k_5539_);
lean_ctor_set(v_reuseFailAlloc_5753_, 2, v_v_5540_);
lean_ctor_set(v_reuseFailAlloc_5753_, 3, v_l_5541_);
lean_ctor_set(v_reuseFailAlloc_5753_, 4, v_l_5714_);
v___x_5749_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
lean_object* v___x_5750_; 
v___x_5750_ = lean_nat_add(v___x_5548_, v_size_5698_);
if (lean_obj_tag(v_r_5715_) == 0)
{
lean_object* v_size_5751_; 
v_size_5751_ = lean_ctor_get(v_r_5715_, 0);
lean_inc(v_size_5751_);
v___y_5725_ = v___x_5749_;
v___y_5726_ = v___x_5750_;
v___y_5727_ = v_size_5751_;
goto v___jp_5724_;
}
else
{
lean_object* v___x_5752_; 
v___x_5752_ = lean_unsigned_to_nat(0u);
v___y_5725_ = v___x_5749_;
v___y_5726_ = v___x_5750_;
v___y_5727_ = v___x_5752_;
goto v___jp_5724_;
}
}
}
}
}
else
{
lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5767_; 
v___x_5762_ = lean_nat_add(v___x_5548_, v_size_5538_);
lean_dec(v_size_5538_);
v___x_5763_ = lean_nat_add(v___x_5762_, v_size_5698_);
lean_dec(v___x_5762_);
v___x_5764_ = lean_nat_add(v___x_5548_, v_size_5698_);
v___x_5765_ = lean_nat_add(v___x_5764_, v_size_5711_);
lean_dec(v___x_5764_);
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 4, v_tree_5695_);
lean_ctor_set(v___x_5692_, 3, v_r_5542_);
lean_ctor_set(v___x_5692_, 2, v_v_5697_);
lean_ctor_set(v___x_5692_, 1, v_k_5696_);
lean_ctor_set(v___x_5692_, 0, v___x_5765_);
v___x_5767_ = v___x_5692_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v___x_5765_);
lean_ctor_set(v_reuseFailAlloc_5771_, 1, v_k_5696_);
lean_ctor_set(v_reuseFailAlloc_5771_, 2, v_v_5697_);
lean_ctor_set(v_reuseFailAlloc_5771_, 3, v_r_5542_);
lean_ctor_set(v_reuseFailAlloc_5771_, 4, v_tree_5695_);
v___x_5767_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
lean_object* v___x_5769_; 
if (v_isShared_5709_ == 0)
{
lean_ctor_set(v___x_5708_, 4, v___x_5767_);
lean_ctor_set(v___x_5708_, 0, v___x_5763_);
v___x_5769_ = v___x_5708_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v___x_5763_);
lean_ctor_set(v_reuseFailAlloc_5770_, 1, v_k_5539_);
lean_ctor_set(v_reuseFailAlloc_5770_, 2, v_v_5540_);
lean_ctor_set(v_reuseFailAlloc_5770_, 3, v_l_5541_);
lean_ctor_set(v_reuseFailAlloc_5770_, 4, v___x_5767_);
v___x_5769_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
return v___x_5769_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_5541_) == 0)
{
lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5801_; 
lean_inc_ref(v_l_5541_);
lean_inc(v_v_5540_);
lean_inc(v_k_5539_);
lean_inc(v_size_5538_);
v_isSharedCheck_5801_ = !lean_is_exclusive(v_l_5358_);
if (v_isSharedCheck_5801_ == 0)
{
lean_object* v_unused_5802_; lean_object* v_unused_5803_; lean_object* v_unused_5804_; lean_object* v_unused_5805_; lean_object* v_unused_5806_; 
v_unused_5802_ = lean_ctor_get(v_l_5358_, 4);
lean_dec(v_unused_5802_);
v_unused_5803_ = lean_ctor_get(v_l_5358_, 3);
lean_dec(v_unused_5803_);
v_unused_5804_ = lean_ctor_get(v_l_5358_, 2);
lean_dec(v_unused_5804_);
v_unused_5805_ = lean_ctor_get(v_l_5358_, 1);
lean_dec(v_unused_5805_);
v_unused_5806_ = lean_ctor_get(v_l_5358_, 0);
lean_dec(v_unused_5806_);
v___x_5779_ = v_l_5358_;
v_isShared_5780_ = v_isSharedCheck_5801_;
goto v_resetjp_5778_;
}
else
{
lean_dec(v_l_5358_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5801_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
if (lean_obj_tag(v_r_5542_) == 0)
{
lean_object* v_k_5781_; lean_object* v_v_5782_; lean_object* v_size_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5787_; 
v_k_5781_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_k_5781_);
v_v_5782_ = lean_ctor_get(v___x_5694_, 1);
lean_inc(v_v_5782_);
lean_dec_ref(v___x_5694_);
v_size_5783_ = lean_ctor_get(v_r_5542_, 0);
v___x_5784_ = lean_nat_add(v___x_5548_, v_size_5538_);
lean_dec(v_size_5538_);
v___x_5785_ = lean_nat_add(v___x_5548_, v_size_5783_);
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 4, v_tree_5695_);
lean_ctor_set(v___x_5692_, 3, v_r_5542_);
lean_ctor_set(v___x_5692_, 2, v_v_5782_);
lean_ctor_set(v___x_5692_, 1, v_k_5781_);
lean_ctor_set(v___x_5692_, 0, v___x_5785_);
v___x_5787_ = v___x_5692_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5791_; 
v_reuseFailAlloc_5791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5791_, 0, v___x_5785_);
lean_ctor_set(v_reuseFailAlloc_5791_, 1, v_k_5781_);
lean_ctor_set(v_reuseFailAlloc_5791_, 2, v_v_5782_);
lean_ctor_set(v_reuseFailAlloc_5791_, 3, v_r_5542_);
lean_ctor_set(v_reuseFailAlloc_5791_, 4, v_tree_5695_);
v___x_5787_ = v_reuseFailAlloc_5791_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
lean_object* v___x_5789_; 
if (v_isShared_5780_ == 0)
{
lean_ctor_set(v___x_5779_, 4, v___x_5787_);
lean_ctor_set(v___x_5779_, 0, v___x_5784_);
v___x_5789_ = v___x_5779_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v___x_5784_);
lean_ctor_set(v_reuseFailAlloc_5790_, 1, v_k_5539_);
lean_ctor_set(v_reuseFailAlloc_5790_, 2, v_v_5540_);
lean_ctor_set(v_reuseFailAlloc_5790_, 3, v_l_5541_);
lean_ctor_set(v_reuseFailAlloc_5790_, 4, v___x_5787_);
v___x_5789_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
return v___x_5789_;
}
}
}
else
{
lean_object* v_k_5792_; lean_object* v_v_5793_; lean_object* v___x_5794_; lean_object* v___x_5796_; 
lean_dec(v_size_5538_);
v_k_5792_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_k_5792_);
v_v_5793_ = lean_ctor_get(v___x_5694_, 1);
lean_inc(v_v_5793_);
lean_dec_ref(v___x_5694_);
v___x_5794_ = lean_unsigned_to_nat(3u);
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 4, v_r_5542_);
lean_ctor_set(v___x_5692_, 3, v_r_5542_);
lean_ctor_set(v___x_5692_, 2, v_v_5793_);
lean_ctor_set(v___x_5692_, 1, v_k_5792_);
lean_ctor_set(v___x_5692_, 0, v___x_5548_);
v___x_5796_ = v___x_5692_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5800_, 1, v_k_5792_);
lean_ctor_set(v_reuseFailAlloc_5800_, 2, v_v_5793_);
lean_ctor_set(v_reuseFailAlloc_5800_, 3, v_r_5542_);
lean_ctor_set(v_reuseFailAlloc_5800_, 4, v_r_5542_);
v___x_5796_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
lean_object* v___x_5798_; 
if (v_isShared_5780_ == 0)
{
lean_ctor_set(v___x_5779_, 4, v___x_5796_);
lean_ctor_set(v___x_5779_, 0, v___x_5794_);
v___x_5798_ = v___x_5779_;
goto v_reusejp_5797_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v___x_5794_);
lean_ctor_set(v_reuseFailAlloc_5799_, 1, v_k_5539_);
lean_ctor_set(v_reuseFailAlloc_5799_, 2, v_v_5540_);
lean_ctor_set(v_reuseFailAlloc_5799_, 3, v_l_5541_);
lean_ctor_set(v_reuseFailAlloc_5799_, 4, v___x_5796_);
v___x_5798_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5797_;
}
v_reusejp_5797_:
{
return v___x_5798_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5542_) == 0)
{
lean_object* v___x_5808_; uint8_t v_isShared_5809_; uint8_t v_isSharedCheck_5831_; 
lean_inc(v_l_5541_);
lean_inc(v_v_5540_);
lean_inc(v_k_5539_);
v_isSharedCheck_5831_ = !lean_is_exclusive(v_l_5358_);
if (v_isSharedCheck_5831_ == 0)
{
lean_object* v_unused_5832_; lean_object* v_unused_5833_; lean_object* v_unused_5834_; lean_object* v_unused_5835_; lean_object* v_unused_5836_; 
v_unused_5832_ = lean_ctor_get(v_l_5358_, 4);
lean_dec(v_unused_5832_);
v_unused_5833_ = lean_ctor_get(v_l_5358_, 3);
lean_dec(v_unused_5833_);
v_unused_5834_ = lean_ctor_get(v_l_5358_, 2);
lean_dec(v_unused_5834_);
v_unused_5835_ = lean_ctor_get(v_l_5358_, 1);
lean_dec(v_unused_5835_);
v_unused_5836_ = lean_ctor_get(v_l_5358_, 0);
lean_dec(v_unused_5836_);
v___x_5808_ = v_l_5358_;
v_isShared_5809_ = v_isSharedCheck_5831_;
goto v_resetjp_5807_;
}
else
{
lean_dec(v_l_5358_);
v___x_5808_ = lean_box(0);
v_isShared_5809_ = v_isSharedCheck_5831_;
goto v_resetjp_5807_;
}
v_resetjp_5807_:
{
lean_object* v_k_5810_; lean_object* v_v_5811_; lean_object* v_k_5812_; lean_object* v_v_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5827_; 
v_k_5810_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_k_5810_);
v_v_5811_ = lean_ctor_get(v___x_5694_, 1);
lean_inc(v_v_5811_);
lean_dec_ref(v___x_5694_);
v_k_5812_ = lean_ctor_get(v_r_5542_, 1);
v_v_5813_ = lean_ctor_get(v_r_5542_, 2);
v_isSharedCheck_5827_ = !lean_is_exclusive(v_r_5542_);
if (v_isSharedCheck_5827_ == 0)
{
lean_object* v_unused_5828_; lean_object* v_unused_5829_; lean_object* v_unused_5830_; 
v_unused_5828_ = lean_ctor_get(v_r_5542_, 4);
lean_dec(v_unused_5828_);
v_unused_5829_ = lean_ctor_get(v_r_5542_, 3);
lean_dec(v_unused_5829_);
v_unused_5830_ = lean_ctor_get(v_r_5542_, 0);
lean_dec(v_unused_5830_);
v___x_5815_ = v_r_5542_;
v_isShared_5816_ = v_isSharedCheck_5827_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_v_5813_);
lean_inc(v_k_5812_);
lean_dec(v_r_5542_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5827_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
lean_object* v___x_5817_; lean_object* v___x_5819_; 
v___x_5817_ = lean_unsigned_to_nat(3u);
if (v_isShared_5816_ == 0)
{
lean_ctor_set(v___x_5815_, 4, v_l_5541_);
lean_ctor_set(v___x_5815_, 3, v_l_5541_);
lean_ctor_set(v___x_5815_, 2, v_v_5540_);
lean_ctor_set(v___x_5815_, 1, v_k_5539_);
lean_ctor_set(v___x_5815_, 0, v___x_5548_);
v___x_5819_ = v___x_5815_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5826_, 1, v_k_5539_);
lean_ctor_set(v_reuseFailAlloc_5826_, 2, v_v_5540_);
lean_ctor_set(v_reuseFailAlloc_5826_, 3, v_l_5541_);
lean_ctor_set(v_reuseFailAlloc_5826_, 4, v_l_5541_);
v___x_5819_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
lean_object* v___x_5821_; 
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 4, v_l_5541_);
lean_ctor_set(v___x_5692_, 3, v_l_5541_);
lean_ctor_set(v___x_5692_, 2, v_v_5811_);
lean_ctor_set(v___x_5692_, 1, v_k_5810_);
lean_ctor_set(v___x_5692_, 0, v___x_5548_);
v___x_5821_ = v___x_5692_;
goto v_reusejp_5820_;
}
else
{
lean_object* v_reuseFailAlloc_5825_; 
v_reuseFailAlloc_5825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5825_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5825_, 1, v_k_5810_);
lean_ctor_set(v_reuseFailAlloc_5825_, 2, v_v_5811_);
lean_ctor_set(v_reuseFailAlloc_5825_, 3, v_l_5541_);
lean_ctor_set(v_reuseFailAlloc_5825_, 4, v_l_5541_);
v___x_5821_ = v_reuseFailAlloc_5825_;
goto v_reusejp_5820_;
}
v_reusejp_5820_:
{
lean_object* v___x_5823_; 
if (v_isShared_5809_ == 0)
{
lean_ctor_set(v___x_5808_, 4, v___x_5821_);
lean_ctor_set(v___x_5808_, 3, v___x_5819_);
lean_ctor_set(v___x_5808_, 2, v_v_5813_);
lean_ctor_set(v___x_5808_, 1, v_k_5812_);
lean_ctor_set(v___x_5808_, 0, v___x_5817_);
v___x_5823_ = v___x_5808_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v___x_5817_);
lean_ctor_set(v_reuseFailAlloc_5824_, 1, v_k_5812_);
lean_ctor_set(v_reuseFailAlloc_5824_, 2, v_v_5813_);
lean_ctor_set(v_reuseFailAlloc_5824_, 3, v___x_5819_);
lean_ctor_set(v_reuseFailAlloc_5824_, 4, v___x_5821_);
v___x_5823_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
return v___x_5823_;
}
}
}
}
}
}
else
{
lean_object* v_k_5837_; lean_object* v_v_5838_; lean_object* v___x_5839_; lean_object* v___x_5841_; 
v_k_5837_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_k_5837_);
v_v_5838_ = lean_ctor_get(v___x_5694_, 1);
lean_inc(v_v_5838_);
lean_dec_ref(v___x_5694_);
v___x_5839_ = lean_unsigned_to_nat(2u);
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 4, v_r_5542_);
lean_ctor_set(v___x_5692_, 3, v_l_5358_);
lean_ctor_set(v___x_5692_, 2, v_v_5838_);
lean_ctor_set(v___x_5692_, 1, v_k_5837_);
lean_ctor_set(v___x_5692_, 0, v___x_5839_);
v___x_5841_ = v___x_5692_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v___x_5839_);
lean_ctor_set(v_reuseFailAlloc_5842_, 1, v_k_5837_);
lean_ctor_set(v_reuseFailAlloc_5842_, 2, v_v_5838_);
lean_ctor_set(v_reuseFailAlloc_5842_, 3, v_l_5358_);
lean_ctor_set(v_reuseFailAlloc_5842_, 4, v_r_5542_);
v___x_5841_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
return v___x_5841_;
}
}
}
}
}
}
}
else
{
return v_l_5358_;
}
}
else
{
return v_r_5359_;
}
}
default: 
{
lean_object* v_impl_5849_; lean_object* v___x_5850_; 
v_impl_5849_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5354_, v_r_5359_);
v___x_5850_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5849_) == 0)
{
if (lean_obj_tag(v_l_5358_) == 0)
{
lean_object* v_size_5851_; lean_object* v_size_5852_; lean_object* v_k_5853_; lean_object* v_v_5854_; lean_object* v_l_5855_; lean_object* v_r_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; uint8_t v___x_5859_; 
v_size_5851_ = lean_ctor_get(v_impl_5849_, 0);
lean_inc(v_size_5851_);
v_size_5852_ = lean_ctor_get(v_l_5358_, 0);
v_k_5853_ = lean_ctor_get(v_l_5358_, 1);
v_v_5854_ = lean_ctor_get(v_l_5358_, 2);
v_l_5855_ = lean_ctor_get(v_l_5358_, 3);
v_r_5856_ = lean_ctor_get(v_l_5358_, 4);
lean_inc(v_r_5856_);
v___x_5857_ = lean_unsigned_to_nat(3u);
v___x_5858_ = lean_nat_mul(v___x_5857_, v_size_5851_);
v___x_5859_ = lean_nat_dec_lt(v___x_5858_, v_size_5852_);
lean_dec(v___x_5858_);
if (v___x_5859_ == 0)
{
lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5863_; 
lean_dec(v_r_5856_);
v___x_5860_ = lean_nat_add(v___x_5850_, v_size_5852_);
v___x_5861_ = lean_nat_add(v___x_5860_, v_size_5851_);
lean_dec(v_size_5851_);
lean_dec(v___x_5860_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v_impl_5849_);
lean_ctor_set(v___x_5361_, 0, v___x_5861_);
v___x_5863_ = v___x_5361_;
goto v_reusejp_5862_;
}
else
{
lean_object* v_reuseFailAlloc_5864_; 
v_reuseFailAlloc_5864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5864_, 0, v___x_5861_);
lean_ctor_set(v_reuseFailAlloc_5864_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5864_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5864_, 3, v_l_5358_);
lean_ctor_set(v_reuseFailAlloc_5864_, 4, v_impl_5849_);
v___x_5863_ = v_reuseFailAlloc_5864_;
goto v_reusejp_5862_;
}
v_reusejp_5862_:
{
return v___x_5863_;
}
}
else
{
lean_object* v___x_5866_; uint8_t v_isShared_5867_; uint8_t v_isSharedCheck_5930_; 
lean_inc(v_l_5855_);
lean_inc(v_v_5854_);
lean_inc(v_k_5853_);
lean_inc(v_size_5852_);
v_isSharedCheck_5930_ = !lean_is_exclusive(v_l_5358_);
if (v_isSharedCheck_5930_ == 0)
{
lean_object* v_unused_5931_; lean_object* v_unused_5932_; lean_object* v_unused_5933_; lean_object* v_unused_5934_; lean_object* v_unused_5935_; 
v_unused_5931_ = lean_ctor_get(v_l_5358_, 4);
lean_dec(v_unused_5931_);
v_unused_5932_ = lean_ctor_get(v_l_5358_, 3);
lean_dec(v_unused_5932_);
v_unused_5933_ = lean_ctor_get(v_l_5358_, 2);
lean_dec(v_unused_5933_);
v_unused_5934_ = lean_ctor_get(v_l_5358_, 1);
lean_dec(v_unused_5934_);
v_unused_5935_ = lean_ctor_get(v_l_5358_, 0);
lean_dec(v_unused_5935_);
v___x_5866_ = v_l_5358_;
v_isShared_5867_ = v_isSharedCheck_5930_;
goto v_resetjp_5865_;
}
else
{
lean_dec(v_l_5358_);
v___x_5866_ = lean_box(0);
v_isShared_5867_ = v_isSharedCheck_5930_;
goto v_resetjp_5865_;
}
v_resetjp_5865_:
{
lean_object* v_size_5868_; lean_object* v_size_5869_; lean_object* v_k_5870_; lean_object* v_v_5871_; lean_object* v_l_5872_; lean_object* v_r_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; uint8_t v___x_5876_; 
v_size_5868_ = lean_ctor_get(v_l_5855_, 0);
v_size_5869_ = lean_ctor_get(v_r_5856_, 0);
v_k_5870_ = lean_ctor_get(v_r_5856_, 1);
v_v_5871_ = lean_ctor_get(v_r_5856_, 2);
v_l_5872_ = lean_ctor_get(v_r_5856_, 3);
v_r_5873_ = lean_ctor_get(v_r_5856_, 4);
v___x_5874_ = lean_unsigned_to_nat(2u);
v___x_5875_ = lean_nat_mul(v___x_5874_, v_size_5868_);
v___x_5876_ = lean_nat_dec_lt(v_size_5869_, v___x_5875_);
lean_dec(v___x_5875_);
if (v___x_5876_ == 0)
{
lean_object* v___x_5878_; uint8_t v_isShared_5879_; uint8_t v_isSharedCheck_5905_; 
lean_inc(v_r_5873_);
lean_inc(v_l_5872_);
lean_inc(v_v_5871_);
lean_inc(v_k_5870_);
v_isSharedCheck_5905_ = !lean_is_exclusive(v_r_5856_);
if (v_isSharedCheck_5905_ == 0)
{
lean_object* v_unused_5906_; lean_object* v_unused_5907_; lean_object* v_unused_5908_; lean_object* v_unused_5909_; lean_object* v_unused_5910_; 
v_unused_5906_ = lean_ctor_get(v_r_5856_, 4);
lean_dec(v_unused_5906_);
v_unused_5907_ = lean_ctor_get(v_r_5856_, 3);
lean_dec(v_unused_5907_);
v_unused_5908_ = lean_ctor_get(v_r_5856_, 2);
lean_dec(v_unused_5908_);
v_unused_5909_ = lean_ctor_get(v_r_5856_, 1);
lean_dec(v_unused_5909_);
v_unused_5910_ = lean_ctor_get(v_r_5856_, 0);
lean_dec(v_unused_5910_);
v___x_5878_ = v_r_5856_;
v_isShared_5879_ = v_isSharedCheck_5905_;
goto v_resetjp_5877_;
}
else
{
lean_dec(v_r_5856_);
v___x_5878_ = lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5905_;
goto v_resetjp_5877_;
}
v_resetjp_5877_:
{
lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___y_5883_; lean_object* v___y_5884_; lean_object* v___y_5885_; lean_object* v___x_5893_; lean_object* v___y_5895_; 
v___x_5880_ = lean_nat_add(v___x_5850_, v_size_5852_);
lean_dec(v_size_5852_);
v___x_5881_ = lean_nat_add(v___x_5880_, v_size_5851_);
lean_dec(v___x_5880_);
v___x_5893_ = lean_nat_add(v___x_5850_, v_size_5868_);
if (lean_obj_tag(v_l_5872_) == 0)
{
lean_object* v_size_5903_; 
v_size_5903_ = lean_ctor_get(v_l_5872_, 0);
lean_inc(v_size_5903_);
v___y_5895_ = v_size_5903_;
goto v___jp_5894_;
}
else
{
lean_object* v___x_5904_; 
v___x_5904_ = lean_unsigned_to_nat(0u);
v___y_5895_ = v___x_5904_;
goto v___jp_5894_;
}
v___jp_5882_:
{
lean_object* v___x_5886_; lean_object* v___x_5888_; 
v___x_5886_ = lean_nat_add(v___y_5883_, v___y_5885_);
lean_dec(v___y_5885_);
lean_dec(v___y_5883_);
if (v_isShared_5879_ == 0)
{
lean_ctor_set(v___x_5878_, 4, v_impl_5849_);
lean_ctor_set(v___x_5878_, 3, v_r_5873_);
lean_ctor_set(v___x_5878_, 2, v_v_5357_);
lean_ctor_set(v___x_5878_, 1, v_k_5356_);
lean_ctor_set(v___x_5878_, 0, v___x_5886_);
v___x_5888_ = v___x_5878_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5892_; 
v_reuseFailAlloc_5892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5892_, 0, v___x_5886_);
lean_ctor_set(v_reuseFailAlloc_5892_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5892_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5892_, 3, v_r_5873_);
lean_ctor_set(v_reuseFailAlloc_5892_, 4, v_impl_5849_);
v___x_5888_ = v_reuseFailAlloc_5892_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
lean_object* v___x_5890_; 
if (v_isShared_5867_ == 0)
{
lean_ctor_set(v___x_5866_, 4, v___x_5888_);
lean_ctor_set(v___x_5866_, 3, v___y_5884_);
lean_ctor_set(v___x_5866_, 2, v_v_5871_);
lean_ctor_set(v___x_5866_, 1, v_k_5870_);
lean_ctor_set(v___x_5866_, 0, v___x_5881_);
v___x_5890_ = v___x_5866_;
goto v_reusejp_5889_;
}
else
{
lean_object* v_reuseFailAlloc_5891_; 
v_reuseFailAlloc_5891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5891_, 0, v___x_5881_);
lean_ctor_set(v_reuseFailAlloc_5891_, 1, v_k_5870_);
lean_ctor_set(v_reuseFailAlloc_5891_, 2, v_v_5871_);
lean_ctor_set(v_reuseFailAlloc_5891_, 3, v___y_5884_);
lean_ctor_set(v_reuseFailAlloc_5891_, 4, v___x_5888_);
v___x_5890_ = v_reuseFailAlloc_5891_;
goto v_reusejp_5889_;
}
v_reusejp_5889_:
{
return v___x_5890_;
}
}
}
v___jp_5894_:
{
lean_object* v___x_5896_; lean_object* v___x_5898_; 
v___x_5896_ = lean_nat_add(v___x_5893_, v___y_5895_);
lean_dec(v___y_5895_);
lean_dec(v___x_5893_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v_l_5872_);
lean_ctor_set(v___x_5361_, 3, v_l_5855_);
lean_ctor_set(v___x_5361_, 2, v_v_5854_);
lean_ctor_set(v___x_5361_, 1, v_k_5853_);
lean_ctor_set(v___x_5361_, 0, v___x_5896_);
v___x_5898_ = v___x_5361_;
goto v_reusejp_5897_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v___x_5896_);
lean_ctor_set(v_reuseFailAlloc_5902_, 1, v_k_5853_);
lean_ctor_set(v_reuseFailAlloc_5902_, 2, v_v_5854_);
lean_ctor_set(v_reuseFailAlloc_5902_, 3, v_l_5855_);
lean_ctor_set(v_reuseFailAlloc_5902_, 4, v_l_5872_);
v___x_5898_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5897_;
}
v_reusejp_5897_:
{
lean_object* v___x_5899_; 
v___x_5899_ = lean_nat_add(v___x_5850_, v_size_5851_);
lean_dec(v_size_5851_);
if (lean_obj_tag(v_r_5873_) == 0)
{
lean_object* v_size_5900_; 
v_size_5900_ = lean_ctor_get(v_r_5873_, 0);
lean_inc(v_size_5900_);
v___y_5883_ = v___x_5899_;
v___y_5884_ = v___x_5898_;
v___y_5885_ = v_size_5900_;
goto v___jp_5882_;
}
else
{
lean_object* v___x_5901_; 
v___x_5901_ = lean_unsigned_to_nat(0u);
v___y_5883_ = v___x_5899_;
v___y_5884_ = v___x_5898_;
v___y_5885_ = v___x_5901_;
goto v___jp_5882_;
}
}
}
}
}
else
{
lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5916_; 
lean_del_object(v___x_5361_);
v___x_5911_ = lean_nat_add(v___x_5850_, v_size_5852_);
lean_dec(v_size_5852_);
v___x_5912_ = lean_nat_add(v___x_5911_, v_size_5851_);
lean_dec(v___x_5911_);
v___x_5913_ = lean_nat_add(v___x_5850_, v_size_5851_);
lean_dec(v_size_5851_);
v___x_5914_ = lean_nat_add(v___x_5913_, v_size_5869_);
lean_dec(v___x_5913_);
lean_inc_ref(v_impl_5849_);
if (v_isShared_5867_ == 0)
{
lean_ctor_set(v___x_5866_, 4, v_impl_5849_);
lean_ctor_set(v___x_5866_, 3, v_r_5856_);
lean_ctor_set(v___x_5866_, 2, v_v_5357_);
lean_ctor_set(v___x_5866_, 1, v_k_5356_);
lean_ctor_set(v___x_5866_, 0, v___x_5914_);
v___x_5916_ = v___x_5866_;
goto v_reusejp_5915_;
}
else
{
lean_object* v_reuseFailAlloc_5929_; 
v_reuseFailAlloc_5929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5929_, 0, v___x_5914_);
lean_ctor_set(v_reuseFailAlloc_5929_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5929_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5929_, 3, v_r_5856_);
lean_ctor_set(v_reuseFailAlloc_5929_, 4, v_impl_5849_);
v___x_5916_ = v_reuseFailAlloc_5929_;
goto v_reusejp_5915_;
}
v_reusejp_5915_:
{
lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5923_; 
v_isSharedCheck_5923_ = !lean_is_exclusive(v_impl_5849_);
if (v_isSharedCheck_5923_ == 0)
{
lean_object* v_unused_5924_; lean_object* v_unused_5925_; lean_object* v_unused_5926_; lean_object* v_unused_5927_; lean_object* v_unused_5928_; 
v_unused_5924_ = lean_ctor_get(v_impl_5849_, 4);
lean_dec(v_unused_5924_);
v_unused_5925_ = lean_ctor_get(v_impl_5849_, 3);
lean_dec(v_unused_5925_);
v_unused_5926_ = lean_ctor_get(v_impl_5849_, 2);
lean_dec(v_unused_5926_);
v_unused_5927_ = lean_ctor_get(v_impl_5849_, 1);
lean_dec(v_unused_5927_);
v_unused_5928_ = lean_ctor_get(v_impl_5849_, 0);
lean_dec(v_unused_5928_);
v___x_5918_ = v_impl_5849_;
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
else
{
lean_dec(v_impl_5849_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5921_; 
if (v_isShared_5919_ == 0)
{
lean_ctor_set(v___x_5918_, 4, v___x_5916_);
lean_ctor_set(v___x_5918_, 3, v_l_5855_);
lean_ctor_set(v___x_5918_, 2, v_v_5854_);
lean_ctor_set(v___x_5918_, 1, v_k_5853_);
lean_ctor_set(v___x_5918_, 0, v___x_5912_);
v___x_5921_ = v___x_5918_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5912_);
lean_ctor_set(v_reuseFailAlloc_5922_, 1, v_k_5853_);
lean_ctor_set(v_reuseFailAlloc_5922_, 2, v_v_5854_);
lean_ctor_set(v_reuseFailAlloc_5922_, 3, v_l_5855_);
lean_ctor_set(v_reuseFailAlloc_5922_, 4, v___x_5916_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5936_; lean_object* v___x_5937_; lean_object* v___x_5939_; 
v_size_5936_ = lean_ctor_get(v_impl_5849_, 0);
lean_inc(v_size_5936_);
v___x_5937_ = lean_nat_add(v___x_5850_, v_size_5936_);
lean_dec(v_size_5936_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v_impl_5849_);
lean_ctor_set(v___x_5361_, 0, v___x_5937_);
v___x_5939_ = v___x_5361_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v___x_5937_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5940_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5940_, 3, v_l_5358_);
lean_ctor_set(v_reuseFailAlloc_5940_, 4, v_impl_5849_);
v___x_5939_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
return v___x_5939_;
}
}
}
else
{
if (lean_obj_tag(v_l_5358_) == 0)
{
lean_object* v_l_5941_; 
v_l_5941_ = lean_ctor_get(v_l_5358_, 3);
if (lean_obj_tag(v_l_5941_) == 0)
{
lean_object* v_r_5942_; 
lean_inc_ref(v_l_5941_);
v_r_5942_ = lean_ctor_get(v_l_5358_, 4);
lean_inc(v_r_5942_);
if (lean_obj_tag(v_r_5942_) == 0)
{
lean_object* v_size_5943_; lean_object* v_k_5944_; lean_object* v_v_5945_; lean_object* v___x_5947_; uint8_t v_isShared_5948_; uint8_t v_isSharedCheck_5958_; 
v_size_5943_ = lean_ctor_get(v_l_5358_, 0);
v_k_5944_ = lean_ctor_get(v_l_5358_, 1);
v_v_5945_ = lean_ctor_get(v_l_5358_, 2);
v_isSharedCheck_5958_ = !lean_is_exclusive(v_l_5358_);
if (v_isSharedCheck_5958_ == 0)
{
lean_object* v_unused_5959_; lean_object* v_unused_5960_; 
v_unused_5959_ = lean_ctor_get(v_l_5358_, 4);
lean_dec(v_unused_5959_);
v_unused_5960_ = lean_ctor_get(v_l_5358_, 3);
lean_dec(v_unused_5960_);
v___x_5947_ = v_l_5358_;
v_isShared_5948_ = v_isSharedCheck_5958_;
goto v_resetjp_5946_;
}
else
{
lean_inc(v_v_5945_);
lean_inc(v_k_5944_);
lean_inc(v_size_5943_);
lean_dec(v_l_5358_);
v___x_5947_ = lean_box(0);
v_isShared_5948_ = v_isSharedCheck_5958_;
goto v_resetjp_5946_;
}
v_resetjp_5946_:
{
lean_object* v_size_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5953_; 
v_size_5949_ = lean_ctor_get(v_r_5942_, 0);
v___x_5950_ = lean_nat_add(v___x_5850_, v_size_5943_);
lean_dec(v_size_5943_);
v___x_5951_ = lean_nat_add(v___x_5850_, v_size_5949_);
if (v_isShared_5948_ == 0)
{
lean_ctor_set(v___x_5947_, 4, v_impl_5849_);
lean_ctor_set(v___x_5947_, 3, v_r_5942_);
lean_ctor_set(v___x_5947_, 2, v_v_5357_);
lean_ctor_set(v___x_5947_, 1, v_k_5356_);
lean_ctor_set(v___x_5947_, 0, v___x_5951_);
v___x_5953_ = v___x_5947_;
goto v_reusejp_5952_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v___x_5951_);
lean_ctor_set(v_reuseFailAlloc_5957_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5957_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5957_, 3, v_r_5942_);
lean_ctor_set(v_reuseFailAlloc_5957_, 4, v_impl_5849_);
v___x_5953_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5952_;
}
v_reusejp_5952_:
{
lean_object* v___x_5955_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v___x_5953_);
lean_ctor_set(v___x_5361_, 3, v_l_5941_);
lean_ctor_set(v___x_5361_, 2, v_v_5945_);
lean_ctor_set(v___x_5361_, 1, v_k_5944_);
lean_ctor_set(v___x_5361_, 0, v___x_5950_);
v___x_5955_ = v___x_5361_;
goto v_reusejp_5954_;
}
else
{
lean_object* v_reuseFailAlloc_5956_; 
v_reuseFailAlloc_5956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5956_, 0, v___x_5950_);
lean_ctor_set(v_reuseFailAlloc_5956_, 1, v_k_5944_);
lean_ctor_set(v_reuseFailAlloc_5956_, 2, v_v_5945_);
lean_ctor_set(v_reuseFailAlloc_5956_, 3, v_l_5941_);
lean_ctor_set(v_reuseFailAlloc_5956_, 4, v___x_5953_);
v___x_5955_ = v_reuseFailAlloc_5956_;
goto v_reusejp_5954_;
}
v_reusejp_5954_:
{
return v___x_5955_;
}
}
}
}
else
{
lean_object* v_k_5961_; lean_object* v_v_5962_; lean_object* v___x_5964_; uint8_t v_isShared_5965_; uint8_t v_isSharedCheck_5973_; 
v_k_5961_ = lean_ctor_get(v_l_5358_, 1);
v_v_5962_ = lean_ctor_get(v_l_5358_, 2);
v_isSharedCheck_5973_ = !lean_is_exclusive(v_l_5358_);
if (v_isSharedCheck_5973_ == 0)
{
lean_object* v_unused_5974_; lean_object* v_unused_5975_; lean_object* v_unused_5976_; 
v_unused_5974_ = lean_ctor_get(v_l_5358_, 4);
lean_dec(v_unused_5974_);
v_unused_5975_ = lean_ctor_get(v_l_5358_, 3);
lean_dec(v_unused_5975_);
v_unused_5976_ = lean_ctor_get(v_l_5358_, 0);
lean_dec(v_unused_5976_);
v___x_5964_ = v_l_5358_;
v_isShared_5965_ = v_isSharedCheck_5973_;
goto v_resetjp_5963_;
}
else
{
lean_inc(v_v_5962_);
lean_inc(v_k_5961_);
lean_dec(v_l_5358_);
v___x_5964_ = lean_box(0);
v_isShared_5965_ = v_isSharedCheck_5973_;
goto v_resetjp_5963_;
}
v_resetjp_5963_:
{
lean_object* v___x_5966_; lean_object* v___x_5968_; 
v___x_5966_ = lean_unsigned_to_nat(3u);
if (v_isShared_5965_ == 0)
{
lean_ctor_set(v___x_5964_, 3, v_r_5942_);
lean_ctor_set(v___x_5964_, 2, v_v_5357_);
lean_ctor_set(v___x_5964_, 1, v_k_5356_);
lean_ctor_set(v___x_5964_, 0, v___x_5850_);
v___x_5968_ = v___x_5964_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v___x_5850_);
lean_ctor_set(v_reuseFailAlloc_5972_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5972_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5972_, 3, v_r_5942_);
lean_ctor_set(v_reuseFailAlloc_5972_, 4, v_r_5942_);
v___x_5968_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
lean_object* v___x_5970_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v___x_5968_);
lean_ctor_set(v___x_5361_, 3, v_l_5941_);
lean_ctor_set(v___x_5361_, 2, v_v_5962_);
lean_ctor_set(v___x_5361_, 1, v_k_5961_);
lean_ctor_set(v___x_5361_, 0, v___x_5966_);
v___x_5970_ = v___x_5361_;
goto v_reusejp_5969_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v___x_5966_);
lean_ctor_set(v_reuseFailAlloc_5971_, 1, v_k_5961_);
lean_ctor_set(v_reuseFailAlloc_5971_, 2, v_v_5962_);
lean_ctor_set(v_reuseFailAlloc_5971_, 3, v_l_5941_);
lean_ctor_set(v_reuseFailAlloc_5971_, 4, v___x_5968_);
v___x_5970_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5969_;
}
v_reusejp_5969_:
{
return v___x_5970_;
}
}
}
}
}
else
{
lean_object* v_r_5977_; 
v_r_5977_ = lean_ctor_get(v_l_5358_, 4);
lean_inc(v_r_5977_);
if (lean_obj_tag(v_r_5977_) == 0)
{
lean_object* v_k_5978_; lean_object* v_v_5979_; lean_object* v___x_5981_; uint8_t v_isShared_5982_; uint8_t v_isSharedCheck_6002_; 
lean_inc(v_l_5941_);
v_k_5978_ = lean_ctor_get(v_l_5358_, 1);
v_v_5979_ = lean_ctor_get(v_l_5358_, 2);
v_isSharedCheck_6002_ = !lean_is_exclusive(v_l_5358_);
if (v_isSharedCheck_6002_ == 0)
{
lean_object* v_unused_6003_; lean_object* v_unused_6004_; lean_object* v_unused_6005_; 
v_unused_6003_ = lean_ctor_get(v_l_5358_, 4);
lean_dec(v_unused_6003_);
v_unused_6004_ = lean_ctor_get(v_l_5358_, 3);
lean_dec(v_unused_6004_);
v_unused_6005_ = lean_ctor_get(v_l_5358_, 0);
lean_dec(v_unused_6005_);
v___x_5981_ = v_l_5358_;
v_isShared_5982_ = v_isSharedCheck_6002_;
goto v_resetjp_5980_;
}
else
{
lean_inc(v_v_5979_);
lean_inc(v_k_5978_);
lean_dec(v_l_5358_);
v___x_5981_ = lean_box(0);
v_isShared_5982_ = v_isSharedCheck_6002_;
goto v_resetjp_5980_;
}
v_resetjp_5980_:
{
lean_object* v_k_5983_; lean_object* v_v_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_5998_; 
v_k_5983_ = lean_ctor_get(v_r_5977_, 1);
v_v_5984_ = lean_ctor_get(v_r_5977_, 2);
v_isSharedCheck_5998_ = !lean_is_exclusive(v_r_5977_);
if (v_isSharedCheck_5998_ == 0)
{
lean_object* v_unused_5999_; lean_object* v_unused_6000_; lean_object* v_unused_6001_; 
v_unused_5999_ = lean_ctor_get(v_r_5977_, 4);
lean_dec(v_unused_5999_);
v_unused_6000_ = lean_ctor_get(v_r_5977_, 3);
lean_dec(v_unused_6000_);
v_unused_6001_ = lean_ctor_get(v_r_5977_, 0);
lean_dec(v_unused_6001_);
v___x_5986_ = v_r_5977_;
v_isShared_5987_ = v_isSharedCheck_5998_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_v_5984_);
lean_inc(v_k_5983_);
lean_dec(v_r_5977_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_5998_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v___x_5988_; lean_object* v___x_5990_; 
v___x_5988_ = lean_unsigned_to_nat(3u);
if (v_isShared_5987_ == 0)
{
lean_ctor_set(v___x_5986_, 4, v_l_5941_);
lean_ctor_set(v___x_5986_, 3, v_l_5941_);
lean_ctor_set(v___x_5986_, 2, v_v_5979_);
lean_ctor_set(v___x_5986_, 1, v_k_5978_);
lean_ctor_set(v___x_5986_, 0, v___x_5850_);
v___x_5990_ = v___x_5986_;
goto v_reusejp_5989_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v___x_5850_);
lean_ctor_set(v_reuseFailAlloc_5997_, 1, v_k_5978_);
lean_ctor_set(v_reuseFailAlloc_5997_, 2, v_v_5979_);
lean_ctor_set(v_reuseFailAlloc_5997_, 3, v_l_5941_);
lean_ctor_set(v_reuseFailAlloc_5997_, 4, v_l_5941_);
v___x_5990_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5989_;
}
v_reusejp_5989_:
{
lean_object* v___x_5992_; 
if (v_isShared_5982_ == 0)
{
lean_ctor_set(v___x_5981_, 4, v_l_5941_);
lean_ctor_set(v___x_5981_, 2, v_v_5357_);
lean_ctor_set(v___x_5981_, 1, v_k_5356_);
lean_ctor_set(v___x_5981_, 0, v___x_5850_);
v___x_5992_ = v___x_5981_;
goto v_reusejp_5991_;
}
else
{
lean_object* v_reuseFailAlloc_5996_; 
v_reuseFailAlloc_5996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5996_, 0, v___x_5850_);
lean_ctor_set(v_reuseFailAlloc_5996_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5996_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5996_, 3, v_l_5941_);
lean_ctor_set(v_reuseFailAlloc_5996_, 4, v_l_5941_);
v___x_5992_ = v_reuseFailAlloc_5996_;
goto v_reusejp_5991_;
}
v_reusejp_5991_:
{
lean_object* v___x_5994_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v___x_5992_);
lean_ctor_set(v___x_5361_, 3, v___x_5990_);
lean_ctor_set(v___x_5361_, 2, v_v_5984_);
lean_ctor_set(v___x_5361_, 1, v_k_5983_);
lean_ctor_set(v___x_5361_, 0, v___x_5988_);
v___x_5994_ = v___x_5361_;
goto v_reusejp_5993_;
}
else
{
lean_object* v_reuseFailAlloc_5995_; 
v_reuseFailAlloc_5995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5995_, 0, v___x_5988_);
lean_ctor_set(v_reuseFailAlloc_5995_, 1, v_k_5983_);
lean_ctor_set(v_reuseFailAlloc_5995_, 2, v_v_5984_);
lean_ctor_set(v_reuseFailAlloc_5995_, 3, v___x_5990_);
lean_ctor_set(v_reuseFailAlloc_5995_, 4, v___x_5992_);
v___x_5994_ = v_reuseFailAlloc_5995_;
goto v_reusejp_5993_;
}
v_reusejp_5993_:
{
return v___x_5994_;
}
}
}
}
}
}
else
{
lean_object* v___x_6006_; lean_object* v___x_6008_; 
v___x_6006_ = lean_unsigned_to_nat(2u);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v_r_5977_);
lean_ctor_set(v___x_5361_, 0, v___x_6006_);
v___x_6008_ = v___x_5361_;
goto v_reusejp_6007_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v___x_6006_);
lean_ctor_set(v_reuseFailAlloc_6009_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_6009_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_6009_, 3, v_l_5358_);
lean_ctor_set(v_reuseFailAlloc_6009_, 4, v_r_5977_);
v___x_6008_ = v_reuseFailAlloc_6009_;
goto v_reusejp_6007_;
}
v_reusejp_6007_:
{
return v___x_6008_;
}
}
}
}
else
{
lean_object* v___x_6011_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 4, v_l_5358_);
lean_ctor_set(v___x_5361_, 0, v___x_5850_);
v___x_6011_ = v___x_5361_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v___x_5850_);
lean_ctor_set(v_reuseFailAlloc_6012_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_6012_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_6012_, 3, v_l_5358_);
lean_ctor_set(v_reuseFailAlloc_6012_, 4, v_l_5358_);
v___x_6011_ = v_reuseFailAlloc_6012_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
return v___x_6011_;
}
}
}
}
}
}
}
else
{
return v_t_5355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_6015_, lean_object* v_t_6016_){
_start:
{
lean_object* v_res_6017_; 
v_res_6017_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6015_, v_t_6016_);
lean_dec(v_k_6015_);
return v_res_6017_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_6018_, lean_object* v_x_6019_){
_start:
{
if (lean_obj_tag(v_x_6019_) == 0)
{
lean_object* v_k_6020_; lean_object* v_l_6021_; lean_object* v_r_6022_; lean_object* v___x_6023_; lean_object* v_ileans_6024_; lean_object* v_workers_6025_; lean_object* v___x_6027_; uint8_t v_isShared_6028_; uint8_t v_isSharedCheck_6034_; 
v_k_6020_ = lean_ctor_get(v_x_6019_, 1);
v_l_6021_ = lean_ctor_get(v_x_6019_, 3);
v_r_6022_ = lean_ctor_get(v_x_6019_, 4);
v___x_6023_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6018_, v_l_6021_);
v_ileans_6024_ = lean_ctor_get(v___x_6023_, 0);
v_workers_6025_ = lean_ctor_get(v___x_6023_, 1);
v_isSharedCheck_6034_ = !lean_is_exclusive(v___x_6023_);
if (v_isSharedCheck_6034_ == 0)
{
v___x_6027_ = v___x_6023_;
v_isShared_6028_ = v_isSharedCheck_6034_;
goto v_resetjp_6026_;
}
else
{
lean_inc(v_workers_6025_);
lean_inc(v_ileans_6024_);
lean_dec(v___x_6023_);
v___x_6027_ = lean_box(0);
v_isShared_6028_ = v_isSharedCheck_6034_;
goto v_resetjp_6026_;
}
v_resetjp_6026_:
{
lean_object* v___x_6029_; lean_object* v___x_6031_; 
v___x_6029_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6020_, v_ileans_6024_);
if (v_isShared_6028_ == 0)
{
lean_ctor_set(v___x_6027_, 0, v___x_6029_);
v___x_6031_ = v___x_6027_;
goto v_reusejp_6030_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v___x_6029_);
lean_ctor_set(v_reuseFailAlloc_6033_, 1, v_workers_6025_);
v___x_6031_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6030_;
}
v_reusejp_6030_:
{
v_init_6018_ = v___x_6031_;
v_x_6019_ = v_r_6022_;
goto _start;
}
}
}
else
{
return v_init_6018_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_6035_, lean_object* v_x_6036_){
_start:
{
lean_object* v_res_6037_; 
v_res_6037_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6035_, v_x_6036_);
lean_dec(v_x_6036_);
return v_res_6037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_6038_, lean_object* v_path_6039_){
_start:
{
lean_object* v_ileans_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; 
v_ileans_6040_ = lean_ctor_get(v_self_6038_, 0);
lean_inc(v_ileans_6040_);
v___x_6041_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6039_, v_ileans_6040_);
v___x_6042_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_6038_, v___x_6041_);
lean_dec(v___x_6041_);
return v___x_6042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_6043_, lean_object* v_path_6044_){
_start:
{
lean_object* v_res_6045_; 
v_res_6045_ = l_Lean_Server_References_removeIlean(v_self_6043_, v_path_6044_);
lean_dec_ref(v_path_6044_);
return v_res_6045_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_6046_, lean_object* v_k_6047_, lean_object* v_t_6048_, lean_object* v_h_6049_){
_start:
{
lean_object* v___x_6050_; 
v___x_6050_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6047_, v_t_6048_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_6051_, lean_object* v_k_6052_, lean_object* v_t_6053_, lean_object* v_h_6054_){
_start:
{
lean_object* v_res_6055_; 
v_res_6055_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_6051_, v_k_6052_, v_t_6053_, v_h_6054_);
lean_dec(v_k_6052_);
return v_res_6055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_6056_, lean_object* v_t_6057_, lean_object* v_hl_6058_){
_start:
{
lean_object* v___x_6059_; 
v___x_6059_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6056_, v_t_6057_);
return v___x_6059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_6060_, lean_object* v_t_6061_, lean_object* v_hl_6062_){
_start:
{
lean_object* v_res_6063_; 
v_res_6063_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_6060_, v_t_6061_, v_hl_6062_);
lean_dec_ref(v_path_6060_);
return v_res_6063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_6064_, lean_object* v_t_6065_){
_start:
{
lean_object* v___x_6066_; 
v___x_6066_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6064_, v_t_6065_);
return v___x_6066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_6067_, lean_object* v_t_6068_){
_start:
{
lean_object* v_res_6069_; 
v_res_6069_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_6067_, v_t_6068_);
lean_dec(v_t_6068_);
return v_res_6069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_6070_, lean_object* v_k_6071_){
_start:
{
if (lean_obj_tag(v_t_6070_) == 0)
{
lean_object* v_k_6072_; lean_object* v_v_6073_; lean_object* v_l_6074_; lean_object* v_r_6075_; uint8_t v___x_6076_; 
v_k_6072_ = lean_ctor_get(v_t_6070_, 1);
v_v_6073_ = lean_ctor_get(v_t_6070_, 2);
v_l_6074_ = lean_ctor_get(v_t_6070_, 3);
v_r_6075_ = lean_ctor_get(v_t_6070_, 4);
v___x_6076_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6071_, v_k_6072_);
switch(v___x_6076_)
{
case 0:
{
v_t_6070_ = v_l_6074_;
goto _start;
}
case 1:
{
lean_object* v___x_6078_; 
lean_inc(v_v_6073_);
v___x_6078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6078_, 0, v_v_6073_);
return v___x_6078_;
}
default: 
{
v_t_6070_ = v_r_6075_;
goto _start;
}
}
}
else
{
lean_object* v___x_6080_; 
v___x_6080_ = lean_box(0);
return v___x_6080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_6081_, lean_object* v_k_6082_){
_start:
{
lean_object* v_res_6083_; 
v_res_6083_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6081_, v_k_6082_);
lean_dec(v_k_6082_);
lean_dec(v_t_6081_);
return v_res_6083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_6084_, lean_object* v_name_6085_, lean_object* v_moduleUri_6086_, lean_object* v_version_6087_, lean_object* v_directImports_6088_, uint8_t v_isSetupFailure_6089_){
_start:
{
lean_object* v___x_6091_; 
v___x_6091_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_6088_);
if (lean_obj_tag(v___x_6091_) == 0)
{
lean_object* v_a_6092_; lean_object* v___x_6094_; uint8_t v_isShared_6095_; uint8_t v_isSharedCheck_6158_; 
v_a_6092_ = lean_ctor_get(v___x_6091_, 0);
v_isSharedCheck_6158_ = !lean_is_exclusive(v___x_6091_);
if (v_isSharedCheck_6158_ == 0)
{
v___x_6094_ = v___x_6091_;
v_isShared_6095_ = v_isSharedCheck_6158_;
goto v_resetjp_6093_;
}
else
{
lean_inc(v_a_6092_);
lean_dec(v___x_6091_);
v___x_6094_ = lean_box(0);
v_isShared_6095_ = v_isSharedCheck_6158_;
goto v_resetjp_6093_;
}
v_resetjp_6093_:
{
lean_object* v_ileans_6096_; lean_object* v_workers_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; 
v_ileans_6096_ = lean_ctor_get(v_self_6084_, 0);
v_workers_6097_ = lean_ctor_get(v_self_6084_, 1);
v___x_6098_ = lean_box(1);
v___x_6099_ = lean_box(v_isSetupFailure_6089_);
v___x_6100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
v___x_6101_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6097_, v_name_6085_);
if (lean_obj_tag(v___x_6101_) == 1)
{
lean_object* v_val_6102_; lean_object* v_version_6103_; lean_object* v_refs_6104_; lean_object* v_decls_6105_; lean_object* v___x_6107_; uint8_t v_isShared_6108_; uint8_t v_isSharedCheck_6140_; 
v_val_6102_ = lean_ctor_get(v___x_6101_, 0);
lean_inc(v_val_6102_);
lean_dec_ref_known(v___x_6101_, 1);
v_version_6103_ = lean_ctor_get(v_val_6102_, 1);
v_refs_6104_ = lean_ctor_get(v_val_6102_, 4);
v_decls_6105_ = lean_ctor_get(v_val_6102_, 5);
v_isSharedCheck_6140_ = !lean_is_exclusive(v_val_6102_);
if (v_isSharedCheck_6140_ == 0)
{
lean_object* v_unused_6141_; lean_object* v_unused_6142_; lean_object* v_unused_6143_; 
v_unused_6141_ = lean_ctor_get(v_val_6102_, 3);
lean_dec(v_unused_6141_);
v_unused_6142_ = lean_ctor_get(v_val_6102_, 2);
lean_dec(v_unused_6142_);
v_unused_6143_ = lean_ctor_get(v_val_6102_, 0);
lean_dec(v_unused_6143_);
v___x_6107_ = v_val_6102_;
v_isShared_6108_ = v_isSharedCheck_6140_;
goto v_resetjp_6106_;
}
else
{
lean_inc(v_decls_6105_);
lean_inc(v_refs_6104_);
lean_inc(v_version_6103_);
lean_dec(v_val_6102_);
v___x_6107_ = lean_box(0);
v_isShared_6108_ = v_isSharedCheck_6140_;
goto v_resetjp_6106_;
}
v_resetjp_6106_:
{
uint8_t v___x_6109_; 
v___x_6109_ = lean_nat_dec_lt(v_version_6087_, v_version_6103_);
if (v___x_6109_ == 0)
{
lean_object* v___x_6111_; uint8_t v_isShared_6112_; uint8_t v_isSharedCheck_6134_; 
lean_inc(v_workers_6097_);
lean_inc(v_ileans_6096_);
v_isSharedCheck_6134_ = !lean_is_exclusive(v_self_6084_);
if (v_isSharedCheck_6134_ == 0)
{
lean_object* v_unused_6135_; lean_object* v_unused_6136_; 
v_unused_6135_ = lean_ctor_get(v_self_6084_, 1);
lean_dec(v_unused_6135_);
v_unused_6136_ = lean_ctor_get(v_self_6084_, 0);
lean_dec(v_unused_6136_);
v___x_6111_ = v_self_6084_;
v_isShared_6112_ = v_isSharedCheck_6134_;
goto v_resetjp_6110_;
}
else
{
lean_dec(v_self_6084_);
v___x_6111_ = lean_box(0);
v_isShared_6112_ = v_isSharedCheck_6134_;
goto v_resetjp_6110_;
}
v_resetjp_6110_:
{
uint8_t v___x_6113_; 
v___x_6113_ = lean_nat_dec_eq(v_version_6087_, v_version_6103_);
lean_dec(v_version_6103_);
if (v___x_6113_ == 0)
{
lean_object* v___x_6115_; 
lean_dec(v_decls_6105_);
lean_dec(v_refs_6104_);
if (v_isShared_6108_ == 0)
{
lean_ctor_set(v___x_6107_, 5, v___x_6098_);
lean_ctor_set(v___x_6107_, 4, v___x_6098_);
lean_ctor_set(v___x_6107_, 3, v___x_6100_);
lean_ctor_set(v___x_6107_, 2, v_a_6092_);
lean_ctor_set(v___x_6107_, 1, v_version_6087_);
lean_ctor_set(v___x_6107_, 0, v_moduleUri_6086_);
v___x_6115_ = v___x_6107_;
goto v_reusejp_6114_;
}
else
{
lean_object* v_reuseFailAlloc_6123_; 
v_reuseFailAlloc_6123_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6123_, 0, v_moduleUri_6086_);
lean_ctor_set(v_reuseFailAlloc_6123_, 1, v_version_6087_);
lean_ctor_set(v_reuseFailAlloc_6123_, 2, v_a_6092_);
lean_ctor_set(v_reuseFailAlloc_6123_, 3, v___x_6100_);
lean_ctor_set(v_reuseFailAlloc_6123_, 4, v___x_6098_);
lean_ctor_set(v_reuseFailAlloc_6123_, 5, v___x_6098_);
v___x_6115_ = v_reuseFailAlloc_6123_;
goto v_reusejp_6114_;
}
v_reusejp_6114_:
{
lean_object* v___x_6116_; lean_object* v___x_6118_; 
v___x_6116_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6085_, v___x_6115_, v_workers_6097_);
if (v_isShared_6112_ == 0)
{
lean_ctor_set(v___x_6111_, 1, v___x_6116_);
v___x_6118_ = v___x_6111_;
goto v_reusejp_6117_;
}
else
{
lean_object* v_reuseFailAlloc_6122_; 
v_reuseFailAlloc_6122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6122_, 0, v_ileans_6096_);
lean_ctor_set(v_reuseFailAlloc_6122_, 1, v___x_6116_);
v___x_6118_ = v_reuseFailAlloc_6122_;
goto v_reusejp_6117_;
}
v_reusejp_6117_:
{
lean_object* v___x_6120_; 
if (v_isShared_6095_ == 0)
{
lean_ctor_set(v___x_6094_, 0, v___x_6118_);
v___x_6120_ = v___x_6094_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v___x_6118_);
v___x_6120_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
return v___x_6120_;
}
}
}
}
else
{
lean_object* v___x_6125_; 
if (v_isShared_6108_ == 0)
{
lean_ctor_set(v___x_6107_, 3, v___x_6100_);
lean_ctor_set(v___x_6107_, 2, v_a_6092_);
lean_ctor_set(v___x_6107_, 1, v_version_6087_);
lean_ctor_set(v___x_6107_, 0, v_moduleUri_6086_);
v___x_6125_ = v___x_6107_;
goto v_reusejp_6124_;
}
else
{
lean_object* v_reuseFailAlloc_6133_; 
v_reuseFailAlloc_6133_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6133_, 0, v_moduleUri_6086_);
lean_ctor_set(v_reuseFailAlloc_6133_, 1, v_version_6087_);
lean_ctor_set(v_reuseFailAlloc_6133_, 2, v_a_6092_);
lean_ctor_set(v_reuseFailAlloc_6133_, 3, v___x_6100_);
lean_ctor_set(v_reuseFailAlloc_6133_, 4, v_refs_6104_);
lean_ctor_set(v_reuseFailAlloc_6133_, 5, v_decls_6105_);
v___x_6125_ = v_reuseFailAlloc_6133_;
goto v_reusejp_6124_;
}
v_reusejp_6124_:
{
lean_object* v___x_6126_; lean_object* v___x_6128_; 
v___x_6126_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6085_, v___x_6125_, v_workers_6097_);
if (v_isShared_6112_ == 0)
{
lean_ctor_set(v___x_6111_, 1, v___x_6126_);
v___x_6128_ = v___x_6111_;
goto v_reusejp_6127_;
}
else
{
lean_object* v_reuseFailAlloc_6132_; 
v_reuseFailAlloc_6132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_ileans_6096_);
lean_ctor_set(v_reuseFailAlloc_6132_, 1, v___x_6126_);
v___x_6128_ = v_reuseFailAlloc_6132_;
goto v_reusejp_6127_;
}
v_reusejp_6127_:
{
lean_object* v___x_6130_; 
if (v_isShared_6095_ == 0)
{
lean_ctor_set(v___x_6094_, 0, v___x_6128_);
v___x_6130_ = v___x_6094_;
goto v_reusejp_6129_;
}
else
{
lean_object* v_reuseFailAlloc_6131_; 
v_reuseFailAlloc_6131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6131_, 0, v___x_6128_);
v___x_6130_ = v_reuseFailAlloc_6131_;
goto v_reusejp_6129_;
}
v_reusejp_6129_:
{
return v___x_6130_;
}
}
}
}
}
}
else
{
lean_object* v___x_6138_; 
lean_del_object(v___x_6107_);
lean_dec(v_decls_6105_);
lean_dec(v_refs_6104_);
lean_dec(v_version_6103_);
lean_dec_ref_known(v___x_6100_, 1);
lean_dec(v_a_6092_);
lean_dec(v_version_6087_);
lean_dec_ref(v_moduleUri_6086_);
lean_dec(v_name_6085_);
if (v_isShared_6095_ == 0)
{
lean_ctor_set(v___x_6094_, 0, v_self_6084_);
v___x_6138_ = v___x_6094_;
goto v_reusejp_6137_;
}
else
{
lean_object* v_reuseFailAlloc_6139_; 
v_reuseFailAlloc_6139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6139_, 0, v_self_6084_);
v___x_6138_ = v_reuseFailAlloc_6139_;
goto v_reusejp_6137_;
}
v_reusejp_6137_:
{
return v___x_6138_;
}
}
}
}
else
{
lean_object* v___x_6145_; uint8_t v_isShared_6146_; uint8_t v_isSharedCheck_6155_; 
lean_inc(v_workers_6097_);
lean_inc(v_ileans_6096_);
lean_dec(v___x_6101_);
v_isSharedCheck_6155_ = !lean_is_exclusive(v_self_6084_);
if (v_isSharedCheck_6155_ == 0)
{
lean_object* v_unused_6156_; lean_object* v_unused_6157_; 
v_unused_6156_ = lean_ctor_get(v_self_6084_, 1);
lean_dec(v_unused_6156_);
v_unused_6157_ = lean_ctor_get(v_self_6084_, 0);
lean_dec(v_unused_6157_);
v___x_6145_ = v_self_6084_;
v_isShared_6146_ = v_isSharedCheck_6155_;
goto v_resetjp_6144_;
}
else
{
lean_dec(v_self_6084_);
v___x_6145_ = lean_box(0);
v_isShared_6146_ = v_isSharedCheck_6155_;
goto v_resetjp_6144_;
}
v_resetjp_6144_:
{
lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6150_; 
v___x_6147_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6147_, 0, v_moduleUri_6086_);
lean_ctor_set(v___x_6147_, 1, v_version_6087_);
lean_ctor_set(v___x_6147_, 2, v_a_6092_);
lean_ctor_set(v___x_6147_, 3, v___x_6100_);
lean_ctor_set(v___x_6147_, 4, v___x_6098_);
lean_ctor_set(v___x_6147_, 5, v___x_6098_);
v___x_6148_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6085_, v___x_6147_, v_workers_6097_);
if (v_isShared_6146_ == 0)
{
lean_ctor_set(v___x_6145_, 1, v___x_6148_);
v___x_6150_ = v___x_6145_;
goto v_reusejp_6149_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_ileans_6096_);
lean_ctor_set(v_reuseFailAlloc_6154_, 1, v___x_6148_);
v___x_6150_ = v_reuseFailAlloc_6154_;
goto v_reusejp_6149_;
}
v_reusejp_6149_:
{
lean_object* v___x_6152_; 
if (v_isShared_6095_ == 0)
{
lean_ctor_set(v___x_6094_, 0, v___x_6150_);
v___x_6152_ = v___x_6094_;
goto v_reusejp_6151_;
}
else
{
lean_object* v_reuseFailAlloc_6153_; 
v_reuseFailAlloc_6153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6153_, 0, v___x_6150_);
v___x_6152_ = v_reuseFailAlloc_6153_;
goto v_reusejp_6151_;
}
v_reusejp_6151_:
{
return v___x_6152_;
}
}
}
}
}
}
else
{
lean_object* v_a_6159_; lean_object* v___x_6161_; uint8_t v_isShared_6162_; uint8_t v_isSharedCheck_6166_; 
lean_dec(v_version_6087_);
lean_dec_ref(v_moduleUri_6086_);
lean_dec(v_name_6085_);
lean_dec_ref(v_self_6084_);
v_a_6159_ = lean_ctor_get(v___x_6091_, 0);
v_isSharedCheck_6166_ = !lean_is_exclusive(v___x_6091_);
if (v_isSharedCheck_6166_ == 0)
{
v___x_6161_ = v___x_6091_;
v_isShared_6162_ = v_isSharedCheck_6166_;
goto v_resetjp_6160_;
}
else
{
lean_inc(v_a_6159_);
lean_dec(v___x_6091_);
v___x_6161_ = lean_box(0);
v_isShared_6162_ = v_isSharedCheck_6166_;
goto v_resetjp_6160_;
}
v_resetjp_6160_:
{
lean_object* v___x_6164_; 
if (v_isShared_6162_ == 0)
{
v___x_6164_ = v___x_6161_;
goto v_reusejp_6163_;
}
else
{
lean_object* v_reuseFailAlloc_6165_; 
v_reuseFailAlloc_6165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6165_, 0, v_a_6159_);
v___x_6164_ = v_reuseFailAlloc_6165_;
goto v_reusejp_6163_;
}
v_reusejp_6163_:
{
return v___x_6164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6167_, lean_object* v_name_6168_, lean_object* v_moduleUri_6169_, lean_object* v_version_6170_, lean_object* v_directImports_6171_, lean_object* v_isSetupFailure_6172_, lean_object* v_a_6173_){
_start:
{
uint8_t v_isSetupFailure_boxed_6174_; lean_object* v_res_6175_; 
v_isSetupFailure_boxed_6174_ = lean_unbox(v_isSetupFailure_6172_);
v_res_6175_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6167_, v_name_6168_, v_moduleUri_6169_, v_version_6170_, v_directImports_6171_, v_isSetupFailure_boxed_6174_);
lean_dec_ref(v_directImports_6171_);
return v_res_6175_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6176_, lean_object* v_t_6177_, lean_object* v_k_6178_){
_start:
{
lean_object* v___x_6179_; 
v___x_6179_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6177_, v_k_6178_);
return v___x_6179_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6180_, lean_object* v_t_6181_, lean_object* v_k_6182_){
_start:
{
lean_object* v_res_6183_; 
v_res_6183_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6180_, v_t_6181_, v_k_6182_);
lean_dec(v_k_6182_);
lean_dec(v_t_6181_);
return v_res_6183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6184_, lean_object* v_____s_6185_){
_start:
{
lean_object* v_fst_6186_; lean_object* v_snd_6187_; lean_object* v_r_6188_; lean_object* v___x_6189_; 
v_fst_6186_ = lean_ctor_get(v_x_6184_, 0);
lean_inc(v_fst_6186_);
v_snd_6187_ = lean_ctor_get(v_x_6184_, 1);
lean_inc(v_snd_6187_);
lean_dec_ref(v_x_6184_);
v_r_6188_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6186_, v_snd_6187_, v_____s_6185_);
v___x_6189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6189_, 0, v_r_6188_);
return v___x_6189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6190_, lean_object* v_k_6191_, lean_object* v_fallback_6192_){
_start:
{
if (lean_obj_tag(v_t_6190_) == 0)
{
lean_object* v_k_6193_; lean_object* v_v_6194_; lean_object* v_l_6195_; lean_object* v_r_6196_; uint8_t v___x_6197_; 
v_k_6193_ = lean_ctor_get(v_t_6190_, 1);
v_v_6194_ = lean_ctor_get(v_t_6190_, 2);
v_l_6195_ = lean_ctor_get(v_t_6190_, 3);
v_r_6196_ = lean_ctor_get(v_t_6190_, 4);
v___x_6197_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6191_, v_k_6193_);
switch(v___x_6197_)
{
case 0:
{
v_t_6190_ = v_l_6195_;
goto _start;
}
case 1:
{
lean_inc(v_v_6194_);
return v_v_6194_;
}
default: 
{
v_t_6190_ = v_r_6196_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6192_);
return v_fallback_6192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6200_, lean_object* v_k_6201_, lean_object* v_fallback_6202_){
_start:
{
lean_object* v_res_6203_; 
v_res_6203_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6200_, v_k_6201_, v_fallback_6202_);
lean_dec(v_fallback_6202_);
lean_dec_ref(v_k_6201_);
lean_dec(v_t_6200_);
return v_res_6203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6204_, lean_object* v_x_6205_){
_start:
{
if (lean_obj_tag(v_x_6205_) == 0)
{
lean_object* v_k_6206_; lean_object* v_v_6207_; lean_object* v_l_6208_; lean_object* v_r_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; 
v_k_6206_ = lean_ctor_get(v_x_6205_, 1);
lean_inc(v_k_6206_);
v_v_6207_ = lean_ctor_get(v_x_6205_, 2);
lean_inc(v_v_6207_);
v_l_6208_ = lean_ctor_get(v_x_6205_, 3);
lean_inc(v_l_6208_);
v_r_6209_ = lean_ctor_get(v_x_6205_, 4);
lean_inc(v_r_6209_);
lean_dec_ref_known(v_x_6205_, 5);
v___x_6210_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6204_, v_l_6208_);
v___x_6211_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6212_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6210_, v_k_6206_, v___x_6211_);
v___x_6213_ = l_Lean_Lsp_RefInfo_merge(v___x_6212_, v_v_6207_);
v___x_6214_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6206_, v___x_6213_, v___x_6210_);
v_init_6204_ = v___x_6214_;
v_x_6205_ = v_r_6209_;
goto _start;
}
else
{
return v_init_6204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6217_, lean_object* v_name_6218_, lean_object* v_moduleUri_6219_, lean_object* v_version_6220_, lean_object* v_refs_6221_, lean_object* v_decls_6222_){
_start:
{
lean_object* v_ileans_6224_; lean_object* v_workers_6225_; lean_object* v___x_6226_; 
v_ileans_6224_ = lean_ctor_get(v_self_6217_, 0);
v_workers_6225_ = lean_ctor_get(v_self_6217_, 1);
v___x_6226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6225_, v_name_6218_);
if (lean_obj_tag(v___x_6226_) == 1)
{
lean_object* v_val_6227_; lean_object* v___x_6229_; uint8_t v_isShared_6230_; uint8_t v_isSharedCheck_6275_; 
v_val_6227_ = lean_ctor_get(v___x_6226_, 0);
v_isSharedCheck_6275_ = !lean_is_exclusive(v___x_6226_);
if (v_isSharedCheck_6275_ == 0)
{
v___x_6229_ = v___x_6226_;
v_isShared_6230_ = v_isSharedCheck_6275_;
goto v_resetjp_6228_;
}
else
{
lean_inc(v_val_6227_);
lean_dec(v___x_6226_);
v___x_6229_ = lean_box(0);
v_isShared_6230_ = v_isSharedCheck_6275_;
goto v_resetjp_6228_;
}
v_resetjp_6228_:
{
lean_object* v_version_6231_; lean_object* v_directImports_6232_; lean_object* v_isSetupFailure_x3f_6233_; lean_object* v_refs_6234_; lean_object* v_decls_6235_; lean_object* v___x_6237_; uint8_t v_isShared_6238_; uint8_t v_isSharedCheck_6273_; 
v_version_6231_ = lean_ctor_get(v_val_6227_, 1);
v_directImports_6232_ = lean_ctor_get(v_val_6227_, 2);
v_isSetupFailure_x3f_6233_ = lean_ctor_get(v_val_6227_, 3);
v_refs_6234_ = lean_ctor_get(v_val_6227_, 4);
v_decls_6235_ = lean_ctor_get(v_val_6227_, 5);
v_isSharedCheck_6273_ = !lean_is_exclusive(v_val_6227_);
if (v_isSharedCheck_6273_ == 0)
{
lean_object* v_unused_6274_; 
v_unused_6274_ = lean_ctor_get(v_val_6227_, 0);
lean_dec(v_unused_6274_);
v___x_6237_ = v_val_6227_;
v_isShared_6238_ = v_isSharedCheck_6273_;
goto v_resetjp_6236_;
}
else
{
lean_inc(v_decls_6235_);
lean_inc(v_refs_6234_);
lean_inc(v_isSetupFailure_x3f_6233_);
lean_inc(v_directImports_6232_);
lean_inc(v_version_6231_);
lean_dec(v_val_6227_);
v___x_6237_ = lean_box(0);
v_isShared_6238_ = v_isSharedCheck_6273_;
goto v_resetjp_6236_;
}
v_resetjp_6236_:
{
uint8_t v___x_6239_; 
v___x_6239_ = lean_nat_dec_lt(v_version_6220_, v_version_6231_);
if (v___x_6239_ == 0)
{
lean_object* v___x_6241_; uint8_t v_isShared_6242_; uint8_t v_isSharedCheck_6267_; 
lean_inc(v_workers_6225_);
lean_inc(v_ileans_6224_);
v_isSharedCheck_6267_ = !lean_is_exclusive(v_self_6217_);
if (v_isSharedCheck_6267_ == 0)
{
lean_object* v_unused_6268_; lean_object* v_unused_6269_; 
v_unused_6268_ = lean_ctor_get(v_self_6217_, 1);
lean_dec(v_unused_6268_);
v_unused_6269_ = lean_ctor_get(v_self_6217_, 0);
lean_dec(v_unused_6269_);
v___x_6241_ = v_self_6217_;
v_isShared_6242_ = v_isSharedCheck_6267_;
goto v_resetjp_6240_;
}
else
{
lean_dec(v_self_6217_);
v___x_6241_ = lean_box(0);
v_isShared_6242_ = v_isSharedCheck_6267_;
goto v_resetjp_6240_;
}
v_resetjp_6240_:
{
uint8_t v___x_6243_; 
v___x_6243_ = lean_nat_dec_eq(v_version_6220_, v_version_6231_);
lean_dec(v_version_6231_);
if (v___x_6243_ == 0)
{
lean_object* v___x_6245_; 
lean_dec(v_decls_6235_);
lean_dec(v_refs_6234_);
if (v_isShared_6238_ == 0)
{
lean_ctor_set(v___x_6237_, 5, v_decls_6222_);
lean_ctor_set(v___x_6237_, 4, v_refs_6221_);
lean_ctor_set(v___x_6237_, 1, v_version_6220_);
lean_ctor_set(v___x_6237_, 0, v_moduleUri_6219_);
v___x_6245_ = v___x_6237_;
goto v_reusejp_6244_;
}
else
{
lean_object* v_reuseFailAlloc_6253_; 
v_reuseFailAlloc_6253_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6253_, 0, v_moduleUri_6219_);
lean_ctor_set(v_reuseFailAlloc_6253_, 1, v_version_6220_);
lean_ctor_set(v_reuseFailAlloc_6253_, 2, v_directImports_6232_);
lean_ctor_set(v_reuseFailAlloc_6253_, 3, v_isSetupFailure_x3f_6233_);
lean_ctor_set(v_reuseFailAlloc_6253_, 4, v_refs_6221_);
lean_ctor_set(v_reuseFailAlloc_6253_, 5, v_decls_6222_);
v___x_6245_ = v_reuseFailAlloc_6253_;
goto v_reusejp_6244_;
}
v_reusejp_6244_:
{
lean_object* v___x_6246_; lean_object* v___x_6248_; 
v___x_6246_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6218_, v___x_6245_, v_workers_6225_);
if (v_isShared_6242_ == 0)
{
lean_ctor_set(v___x_6241_, 1, v___x_6246_);
v___x_6248_ = v___x_6241_;
goto v_reusejp_6247_;
}
else
{
lean_object* v_reuseFailAlloc_6252_; 
v_reuseFailAlloc_6252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6252_, 0, v_ileans_6224_);
lean_ctor_set(v_reuseFailAlloc_6252_, 1, v___x_6246_);
v___x_6248_ = v_reuseFailAlloc_6252_;
goto v_reusejp_6247_;
}
v_reusejp_6247_:
{
lean_object* v___x_6250_; 
if (v_isShared_6230_ == 0)
{
lean_ctor_set_tag(v___x_6229_, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6248_);
v___x_6250_ = v___x_6229_;
goto v_reusejp_6249_;
}
else
{
lean_object* v_reuseFailAlloc_6251_; 
v_reuseFailAlloc_6251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6251_, 0, v___x_6248_);
v___x_6250_ = v_reuseFailAlloc_6251_;
goto v_reusejp_6249_;
}
v_reusejp_6249_:
{
return v___x_6250_;
}
}
}
}
else
{
lean_object* v___f_6254_; lean_object* v_mergedRefs_6255_; lean_object* v_mergedDecls_6256_; lean_object* v___x_6258_; 
v___f_6254_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6255_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6234_, v_refs_6221_);
v_mergedDecls_6256_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6222_, v_decls_6235_, v___f_6254_);
lean_dec(v_decls_6222_);
if (v_isShared_6238_ == 0)
{
lean_ctor_set(v___x_6237_, 5, v_mergedDecls_6256_);
lean_ctor_set(v___x_6237_, 4, v_mergedRefs_6255_);
lean_ctor_set(v___x_6237_, 1, v_version_6220_);
lean_ctor_set(v___x_6237_, 0, v_moduleUri_6219_);
v___x_6258_ = v___x_6237_;
goto v_reusejp_6257_;
}
else
{
lean_object* v_reuseFailAlloc_6266_; 
v_reuseFailAlloc_6266_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6266_, 0, v_moduleUri_6219_);
lean_ctor_set(v_reuseFailAlloc_6266_, 1, v_version_6220_);
lean_ctor_set(v_reuseFailAlloc_6266_, 2, v_directImports_6232_);
lean_ctor_set(v_reuseFailAlloc_6266_, 3, v_isSetupFailure_x3f_6233_);
lean_ctor_set(v_reuseFailAlloc_6266_, 4, v_mergedRefs_6255_);
lean_ctor_set(v_reuseFailAlloc_6266_, 5, v_mergedDecls_6256_);
v___x_6258_ = v_reuseFailAlloc_6266_;
goto v_reusejp_6257_;
}
v_reusejp_6257_:
{
lean_object* v___x_6259_; lean_object* v___x_6261_; 
v___x_6259_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6218_, v___x_6258_, v_workers_6225_);
if (v_isShared_6242_ == 0)
{
lean_ctor_set(v___x_6241_, 1, v___x_6259_);
v___x_6261_ = v___x_6241_;
goto v_reusejp_6260_;
}
else
{
lean_object* v_reuseFailAlloc_6265_; 
v_reuseFailAlloc_6265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_ileans_6224_);
lean_ctor_set(v_reuseFailAlloc_6265_, 1, v___x_6259_);
v___x_6261_ = v_reuseFailAlloc_6265_;
goto v_reusejp_6260_;
}
v_reusejp_6260_:
{
lean_object* v___x_6263_; 
if (v_isShared_6230_ == 0)
{
lean_ctor_set_tag(v___x_6229_, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6261_);
v___x_6263_ = v___x_6229_;
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
}
}
else
{
lean_object* v___x_6271_; 
lean_del_object(v___x_6237_);
lean_dec(v_decls_6235_);
lean_dec(v_refs_6234_);
lean_dec(v_isSetupFailure_x3f_6233_);
lean_dec_ref(v_directImports_6232_);
lean_dec(v_version_6231_);
lean_dec(v_decls_6222_);
lean_dec(v_refs_6221_);
lean_dec(v_version_6220_);
lean_dec_ref(v_moduleUri_6219_);
lean_dec(v_name_6218_);
if (v_isShared_6230_ == 0)
{
lean_ctor_set_tag(v___x_6229_, 0);
lean_ctor_set(v___x_6229_, 0, v_self_6217_);
v___x_6271_ = v___x_6229_;
goto v_reusejp_6270_;
}
else
{
lean_object* v_reuseFailAlloc_6272_; 
v_reuseFailAlloc_6272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6272_, 0, v_self_6217_);
v___x_6271_ = v_reuseFailAlloc_6272_;
goto v_reusejp_6270_;
}
v_reusejp_6270_:
{
return v___x_6271_;
}
}
}
}
}
else
{
lean_object* v___x_6277_; uint8_t v_isShared_6278_; uint8_t v_isSharedCheck_6287_; 
lean_inc(v_workers_6225_);
lean_inc(v_ileans_6224_);
lean_dec(v___x_6226_);
v_isSharedCheck_6287_ = !lean_is_exclusive(v_self_6217_);
if (v_isSharedCheck_6287_ == 0)
{
lean_object* v_unused_6288_; lean_object* v_unused_6289_; 
v_unused_6288_ = lean_ctor_get(v_self_6217_, 1);
lean_dec(v_unused_6288_);
v_unused_6289_ = lean_ctor_get(v_self_6217_, 0);
lean_dec(v_unused_6289_);
v___x_6277_ = v_self_6217_;
v_isShared_6278_ = v_isSharedCheck_6287_;
goto v_resetjp_6276_;
}
else
{
lean_dec(v_self_6217_);
v___x_6277_ = lean_box(0);
v_isShared_6278_ = v_isSharedCheck_6287_;
goto v_resetjp_6276_;
}
v_resetjp_6276_:
{
lean_object* v___x_6279_; lean_object* v___x_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___x_6284_; 
v___x_6279_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6280_ = lean_box(0);
v___x_6281_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6281_, 0, v_moduleUri_6219_);
lean_ctor_set(v___x_6281_, 1, v_version_6220_);
lean_ctor_set(v___x_6281_, 2, v___x_6279_);
lean_ctor_set(v___x_6281_, 3, v___x_6280_);
lean_ctor_set(v___x_6281_, 4, v_refs_6221_);
lean_ctor_set(v___x_6281_, 5, v_decls_6222_);
v___x_6282_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6218_, v___x_6281_, v_workers_6225_);
if (v_isShared_6278_ == 0)
{
lean_ctor_set(v___x_6277_, 1, v___x_6282_);
v___x_6284_ = v___x_6277_;
goto v_reusejp_6283_;
}
else
{
lean_object* v_reuseFailAlloc_6286_; 
v_reuseFailAlloc_6286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6286_, 0, v_ileans_6224_);
lean_ctor_set(v_reuseFailAlloc_6286_, 1, v___x_6282_);
v___x_6284_ = v_reuseFailAlloc_6286_;
goto v_reusejp_6283_;
}
v_reusejp_6283_:
{
lean_object* v___x_6285_; 
v___x_6285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6285_, 0, v___x_6284_);
return v___x_6285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6290_, lean_object* v_name_6291_, lean_object* v_moduleUri_6292_, lean_object* v_version_6293_, lean_object* v_refs_6294_, lean_object* v_decls_6295_, lean_object* v_a_6296_){
_start:
{
lean_object* v_res_6297_; 
v_res_6297_ = l_Lean_Server_References_updateWorkerRefs(v_self_6290_, v_name_6291_, v_moduleUri_6292_, v_version_6293_, v_refs_6294_, v_decls_6295_);
return v_res_6297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6298_, lean_object* v_t_6299_, lean_object* v_k_6300_, lean_object* v_fallback_6301_){
_start:
{
lean_object* v___x_6302_; 
v___x_6302_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6299_, v_k_6300_, v_fallback_6301_);
return v___x_6302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6303_, lean_object* v_t_6304_, lean_object* v_k_6305_, lean_object* v_fallback_6306_){
_start:
{
lean_object* v_res_6307_; 
v_res_6307_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6303_, v_t_6304_, v_k_6305_, v_fallback_6306_);
lean_dec(v_fallback_6306_);
lean_dec_ref(v_k_6305_);
lean_dec(v_t_6304_);
return v_res_6307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6308_, lean_object* v_t_6309_){
_start:
{
lean_object* v___x_6310_; 
v___x_6310_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6308_, v_t_6309_);
return v___x_6310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6311_, lean_object* v_name_6312_, lean_object* v_moduleUri_6313_, lean_object* v_version_6314_, lean_object* v_refs_6315_, lean_object* v_decls_6316_){
_start:
{
lean_object* v_ileans_6318_; lean_object* v_workers_6319_; lean_object* v___x_6320_; 
v_ileans_6318_ = lean_ctor_get(v_self_6311_, 0);
v_workers_6319_ = lean_ctor_get(v_self_6311_, 1);
v___x_6320_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6319_, v_name_6312_);
if (lean_obj_tag(v___x_6320_) == 1)
{
lean_object* v_val_6321_; lean_object* v___x_6323_; uint8_t v_isShared_6324_; uint8_t v_isSharedCheck_6355_; 
v_val_6321_ = lean_ctor_get(v___x_6320_, 0);
v_isSharedCheck_6355_ = !lean_is_exclusive(v___x_6320_);
if (v_isSharedCheck_6355_ == 0)
{
v___x_6323_ = v___x_6320_;
v_isShared_6324_ = v_isSharedCheck_6355_;
goto v_resetjp_6322_;
}
else
{
lean_inc(v_val_6321_);
lean_dec(v___x_6320_);
v___x_6323_ = lean_box(0);
v_isShared_6324_ = v_isSharedCheck_6355_;
goto v_resetjp_6322_;
}
v_resetjp_6322_:
{
lean_object* v_version_6325_; lean_object* v_directImports_6326_; lean_object* v_isSetupFailure_x3f_6327_; lean_object* v___x_6329_; uint8_t v_isShared_6330_; uint8_t v_isSharedCheck_6351_; 
v_version_6325_ = lean_ctor_get(v_val_6321_, 1);
v_directImports_6326_ = lean_ctor_get(v_val_6321_, 2);
v_isSetupFailure_x3f_6327_ = lean_ctor_get(v_val_6321_, 3);
v_isSharedCheck_6351_ = !lean_is_exclusive(v_val_6321_);
if (v_isSharedCheck_6351_ == 0)
{
lean_object* v_unused_6352_; lean_object* v_unused_6353_; lean_object* v_unused_6354_; 
v_unused_6352_ = lean_ctor_get(v_val_6321_, 5);
lean_dec(v_unused_6352_);
v_unused_6353_ = lean_ctor_get(v_val_6321_, 4);
lean_dec(v_unused_6353_);
v_unused_6354_ = lean_ctor_get(v_val_6321_, 0);
lean_dec(v_unused_6354_);
v___x_6329_ = v_val_6321_;
v_isShared_6330_ = v_isSharedCheck_6351_;
goto v_resetjp_6328_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6327_);
lean_inc(v_directImports_6326_);
lean_inc(v_version_6325_);
lean_dec(v_val_6321_);
v___x_6329_ = lean_box(0);
v_isShared_6330_ = v_isSharedCheck_6351_;
goto v_resetjp_6328_;
}
v_resetjp_6328_:
{
uint8_t v___x_6331_; 
v___x_6331_ = lean_nat_dec_lt(v_version_6314_, v_version_6325_);
lean_dec(v_version_6325_);
if (v___x_6331_ == 0)
{
lean_object* v___x_6333_; uint8_t v_isShared_6334_; uint8_t v_isSharedCheck_6345_; 
lean_inc(v_workers_6319_);
lean_inc(v_ileans_6318_);
v_isSharedCheck_6345_ = !lean_is_exclusive(v_self_6311_);
if (v_isSharedCheck_6345_ == 0)
{
lean_object* v_unused_6346_; lean_object* v_unused_6347_; 
v_unused_6346_ = lean_ctor_get(v_self_6311_, 1);
lean_dec(v_unused_6346_);
v_unused_6347_ = lean_ctor_get(v_self_6311_, 0);
lean_dec(v_unused_6347_);
v___x_6333_ = v_self_6311_;
v_isShared_6334_ = v_isSharedCheck_6345_;
goto v_resetjp_6332_;
}
else
{
lean_dec(v_self_6311_);
v___x_6333_ = lean_box(0);
v_isShared_6334_ = v_isSharedCheck_6345_;
goto v_resetjp_6332_;
}
v_resetjp_6332_:
{
lean_object* v___x_6336_; 
if (v_isShared_6330_ == 0)
{
lean_ctor_set(v___x_6329_, 5, v_decls_6316_);
lean_ctor_set(v___x_6329_, 4, v_refs_6315_);
lean_ctor_set(v___x_6329_, 1, v_version_6314_);
lean_ctor_set(v___x_6329_, 0, v_moduleUri_6313_);
v___x_6336_ = v___x_6329_;
goto v_reusejp_6335_;
}
else
{
lean_object* v_reuseFailAlloc_6344_; 
v_reuseFailAlloc_6344_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6344_, 0, v_moduleUri_6313_);
lean_ctor_set(v_reuseFailAlloc_6344_, 1, v_version_6314_);
lean_ctor_set(v_reuseFailAlloc_6344_, 2, v_directImports_6326_);
lean_ctor_set(v_reuseFailAlloc_6344_, 3, v_isSetupFailure_x3f_6327_);
lean_ctor_set(v_reuseFailAlloc_6344_, 4, v_refs_6315_);
lean_ctor_set(v_reuseFailAlloc_6344_, 5, v_decls_6316_);
v___x_6336_ = v_reuseFailAlloc_6344_;
goto v_reusejp_6335_;
}
v_reusejp_6335_:
{
lean_object* v___x_6337_; lean_object* v___x_6339_; 
v___x_6337_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6312_, v___x_6336_, v_workers_6319_);
if (v_isShared_6334_ == 0)
{
lean_ctor_set(v___x_6333_, 1, v___x_6337_);
v___x_6339_ = v___x_6333_;
goto v_reusejp_6338_;
}
else
{
lean_object* v_reuseFailAlloc_6343_; 
v_reuseFailAlloc_6343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6343_, 0, v_ileans_6318_);
lean_ctor_set(v_reuseFailAlloc_6343_, 1, v___x_6337_);
v___x_6339_ = v_reuseFailAlloc_6343_;
goto v_reusejp_6338_;
}
v_reusejp_6338_:
{
lean_object* v___x_6341_; 
if (v_isShared_6324_ == 0)
{
lean_ctor_set_tag(v___x_6323_, 0);
lean_ctor_set(v___x_6323_, 0, v___x_6339_);
v___x_6341_ = v___x_6323_;
goto v_reusejp_6340_;
}
else
{
lean_object* v_reuseFailAlloc_6342_; 
v_reuseFailAlloc_6342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6342_, 0, v___x_6339_);
v___x_6341_ = v_reuseFailAlloc_6342_;
goto v_reusejp_6340_;
}
v_reusejp_6340_:
{
return v___x_6341_;
}
}
}
}
}
else
{
lean_object* v___x_6349_; 
lean_del_object(v___x_6329_);
lean_dec(v_isSetupFailure_x3f_6327_);
lean_dec_ref(v_directImports_6326_);
lean_dec(v_decls_6316_);
lean_dec(v_refs_6315_);
lean_dec(v_version_6314_);
lean_dec_ref(v_moduleUri_6313_);
lean_dec(v_name_6312_);
if (v_isShared_6324_ == 0)
{
lean_ctor_set_tag(v___x_6323_, 0);
lean_ctor_set(v___x_6323_, 0, v_self_6311_);
v___x_6349_ = v___x_6323_;
goto v_reusejp_6348_;
}
else
{
lean_object* v_reuseFailAlloc_6350_; 
v_reuseFailAlloc_6350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6350_, 0, v_self_6311_);
v___x_6349_ = v_reuseFailAlloc_6350_;
goto v_reusejp_6348_;
}
v_reusejp_6348_:
{
return v___x_6349_;
}
}
}
}
}
else
{
lean_object* v___x_6357_; uint8_t v_isShared_6358_; uint8_t v_isSharedCheck_6367_; 
lean_inc(v_workers_6319_);
lean_inc(v_ileans_6318_);
lean_dec(v___x_6320_);
v_isSharedCheck_6367_ = !lean_is_exclusive(v_self_6311_);
if (v_isSharedCheck_6367_ == 0)
{
lean_object* v_unused_6368_; lean_object* v_unused_6369_; 
v_unused_6368_ = lean_ctor_get(v_self_6311_, 1);
lean_dec(v_unused_6368_);
v_unused_6369_ = lean_ctor_get(v_self_6311_, 0);
lean_dec(v_unused_6369_);
v___x_6357_ = v_self_6311_;
v_isShared_6358_ = v_isSharedCheck_6367_;
goto v_resetjp_6356_;
}
else
{
lean_dec(v_self_6311_);
v___x_6357_ = lean_box(0);
v_isShared_6358_ = v_isSharedCheck_6367_;
goto v_resetjp_6356_;
}
v_resetjp_6356_:
{
lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6364_; 
v___x_6359_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6360_ = lean_box(0);
v___x_6361_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6361_, 0, v_moduleUri_6313_);
lean_ctor_set(v___x_6361_, 1, v_version_6314_);
lean_ctor_set(v___x_6361_, 2, v___x_6359_);
lean_ctor_set(v___x_6361_, 3, v___x_6360_);
lean_ctor_set(v___x_6361_, 4, v_refs_6315_);
lean_ctor_set(v___x_6361_, 5, v_decls_6316_);
v___x_6362_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6312_, v___x_6361_, v_workers_6319_);
if (v_isShared_6358_ == 0)
{
lean_ctor_set(v___x_6357_, 1, v___x_6362_);
v___x_6364_ = v___x_6357_;
goto v_reusejp_6363_;
}
else
{
lean_object* v_reuseFailAlloc_6366_; 
v_reuseFailAlloc_6366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6366_, 0, v_ileans_6318_);
lean_ctor_set(v_reuseFailAlloc_6366_, 1, v___x_6362_);
v___x_6364_ = v_reuseFailAlloc_6366_;
goto v_reusejp_6363_;
}
v_reusejp_6363_:
{
lean_object* v___x_6365_; 
v___x_6365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6365_, 0, v___x_6364_);
return v___x_6365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6370_, lean_object* v_name_6371_, lean_object* v_moduleUri_6372_, lean_object* v_version_6373_, lean_object* v_refs_6374_, lean_object* v_decls_6375_, lean_object* v_a_6376_){
_start:
{
lean_object* v_res_6377_; 
v_res_6377_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6370_, v_name_6371_, v_moduleUri_6372_, v_version_6373_, v_refs_6374_, v_decls_6375_);
return v_res_6377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6378_, lean_object* v_name_6379_){
_start:
{
lean_object* v_ileans_6380_; lean_object* v_workers_6381_; lean_object* v___x_6383_; uint8_t v_isShared_6384_; uint8_t v_isSharedCheck_6389_; 
v_ileans_6380_ = lean_ctor_get(v_self_6378_, 0);
v_workers_6381_ = lean_ctor_get(v_self_6378_, 1);
v_isSharedCheck_6389_ = !lean_is_exclusive(v_self_6378_);
if (v_isSharedCheck_6389_ == 0)
{
v___x_6383_ = v_self_6378_;
v_isShared_6384_ = v_isSharedCheck_6389_;
goto v_resetjp_6382_;
}
else
{
lean_inc(v_workers_6381_);
lean_inc(v_ileans_6380_);
lean_dec(v_self_6378_);
v___x_6383_ = lean_box(0);
v_isShared_6384_ = v_isSharedCheck_6389_;
goto v_resetjp_6382_;
}
v_resetjp_6382_:
{
lean_object* v___x_6385_; lean_object* v___x_6387_; 
v___x_6385_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6379_, v_workers_6381_);
if (v_isShared_6384_ == 0)
{
lean_ctor_set(v___x_6383_, 1, v___x_6385_);
v___x_6387_ = v___x_6383_;
goto v_reusejp_6386_;
}
else
{
lean_object* v_reuseFailAlloc_6388_; 
v_reuseFailAlloc_6388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6388_, 0, v_ileans_6380_);
lean_ctor_set(v_reuseFailAlloc_6388_, 1, v___x_6385_);
v___x_6387_ = v_reuseFailAlloc_6388_;
goto v_reusejp_6386_;
}
v_reusejp_6386_:
{
return v___x_6387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6390_, lean_object* v_name_6391_){
_start:
{
lean_object* v_res_6392_; 
v_res_6392_ = l_Lean_Server_References_removeWorkerRefs(v_self_6390_, v_name_6391_);
lean_dec(v_name_6391_);
return v_res_6392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6393_, lean_object* v_x_6394_){
_start:
{
if (lean_obj_tag(v_x_6394_) == 0)
{
lean_object* v_v_6395_; lean_object* v_k_6396_; lean_object* v_l_6397_; lean_object* v_r_6398_; lean_object* v_moduleUri_6399_; lean_object* v_refs_6400_; lean_object* v_decls_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; 
v_v_6395_ = lean_ctor_get(v_x_6394_, 2);
lean_inc(v_v_6395_);
v_k_6396_ = lean_ctor_get(v_x_6394_, 1);
lean_inc(v_k_6396_);
v_l_6397_ = lean_ctor_get(v_x_6394_, 3);
lean_inc(v_l_6397_);
v_r_6398_ = lean_ctor_get(v_x_6394_, 4);
lean_inc(v_r_6398_);
lean_dec_ref_known(v_x_6394_, 5);
v_moduleUri_6399_ = lean_ctor_get(v_v_6395_, 0);
lean_inc_ref(v_moduleUri_6399_);
v_refs_6400_ = lean_ctor_get(v_v_6395_, 3);
lean_inc(v_refs_6400_);
v_decls_6401_ = lean_ctor_get(v_v_6395_, 4);
lean_inc(v_decls_6401_);
lean_dec(v_v_6395_);
v___x_6402_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6393_, v_l_6397_);
v___x_6403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6403_, 0, v_refs_6400_);
lean_ctor_set(v___x_6403_, 1, v_decls_6401_);
v___x_6404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6404_, 0, v_moduleUri_6399_);
lean_ctor_set(v___x_6404_, 1, v___x_6403_);
v___x_6405_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6396_, v___x_6404_, v___x_6402_);
v_init_6393_ = v___x_6405_;
v_x_6394_ = v_r_6398_;
goto _start;
}
else
{
return v_init_6393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6407_, lean_object* v_x_6408_){
_start:
{
if (lean_obj_tag(v_x_6408_) == 0)
{
lean_object* v_v_6409_; lean_object* v_k_6410_; lean_object* v_l_6411_; lean_object* v_r_6412_; lean_object* v_moduleUri_6413_; lean_object* v_refs_6414_; lean_object* v_decls_6415_; lean_object* v___x_6416_; uint8_t v___x_6417_; 
v_v_6409_ = lean_ctor_get(v_x_6408_, 2);
lean_inc(v_v_6409_);
v_k_6410_ = lean_ctor_get(v_x_6408_, 1);
lean_inc(v_k_6410_);
v_l_6411_ = lean_ctor_get(v_x_6408_, 3);
lean_inc(v_l_6411_);
v_r_6412_ = lean_ctor_get(v_x_6408_, 4);
lean_inc(v_r_6412_);
lean_dec_ref_known(v_x_6408_, 5);
v_moduleUri_6413_ = lean_ctor_get(v_v_6409_, 0);
lean_inc_ref(v_moduleUri_6413_);
v_refs_6414_ = lean_ctor_get(v_v_6409_, 4);
lean_inc(v_refs_6414_);
v_decls_6415_ = lean_ctor_get(v_v_6409_, 5);
lean_inc(v_decls_6415_);
v___x_6416_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6407_, v_l_6411_);
v___x_6417_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6409_);
lean_dec(v_v_6409_);
if (v___x_6417_ == 0)
{
lean_dec(v_decls_6415_);
lean_dec(v_refs_6414_);
lean_dec_ref(v_moduleUri_6413_);
lean_dec(v_k_6410_);
v_init_6407_ = v___x_6416_;
v_x_6408_ = v_r_6412_;
goto _start;
}
else
{
lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; 
v___x_6419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6419_, 0, v_refs_6414_);
lean_ctor_set(v___x_6419_, 1, v_decls_6415_);
v___x_6420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6420_, 0, v_moduleUri_6413_);
lean_ctor_set(v___x_6420_, 1, v___x_6419_);
v___x_6421_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6410_, v___x_6420_, v___x_6416_);
v_init_6407_ = v___x_6421_;
v_x_6408_ = v_r_6412_;
goto _start;
}
}
else
{
return v_init_6407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6423_){
_start:
{
lean_object* v_ileans_6424_; lean_object* v_workers_6425_; lean_object* v___x_6426_; lean_object* v_ileanRefs_6427_; lean_object* v___x_6428_; 
v_ileans_6424_ = lean_ctor_get(v_self_6423_, 0);
lean_inc(v_ileans_6424_);
v_workers_6425_ = lean_ctor_get(v_self_6423_, 1);
lean_inc(v_workers_6425_);
lean_dec_ref(v_self_6423_);
v___x_6426_ = lean_box(1);
v_ileanRefs_6427_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6426_, v_ileans_6424_);
v___x_6428_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6427_, v_workers_6425_);
return v___x_6428_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6429_, lean_object* v_t_6430_){
_start:
{
lean_object* v___x_6431_; 
v___x_6431_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6429_, v_t_6430_);
return v___x_6431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6432_, lean_object* v_t_6433_){
_start:
{
lean_object* v___x_6434_; 
v___x_6434_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6432_, v_t_6433_);
return v___x_6434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6435_, lean_object* v_x_6436_){
_start:
{
if (lean_obj_tag(v_x_6436_) == 0)
{
lean_object* v_k_6437_; lean_object* v_v_6438_; lean_object* v_l_6439_; lean_object* v_r_6440_; lean_object* v___x_6441_; lean_object* v_a_6442_; uint8_t v___x_6443_; 
v_k_6437_ = lean_ctor_get(v_x_6436_, 1);
lean_inc(v_k_6437_);
v_v_6438_ = lean_ctor_get(v_x_6436_, 2);
lean_inc(v_v_6438_);
v_l_6439_ = lean_ctor_get(v_x_6436_, 3);
lean_inc(v_l_6439_);
v_r_6440_ = lean_ctor_get(v_x_6436_, 4);
lean_inc(v_r_6440_);
lean_dec_ref_known(v_x_6436_, 5);
v___x_6441_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6435_, v_l_6439_);
v_a_6442_ = lean_ctor_get(v___x_6441_, 0);
lean_inc(v_a_6442_);
v___x_6443_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6438_);
if (v___x_6443_ == 0)
{
lean_object* v_a_6444_; 
lean_dec(v_a_6442_);
lean_dec(v_v_6438_);
lean_dec(v_k_6437_);
v_a_6444_ = lean_ctor_get(v___x_6441_, 0);
lean_inc(v_a_6444_);
lean_dec_ref(v___x_6441_);
v_init_6435_ = v_a_6444_;
v_x_6436_ = v_r_6440_;
goto _start;
}
else
{
lean_object* v_moduleUri_6446_; lean_object* v_directImports_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; 
lean_dec_ref(v___x_6441_);
v_moduleUri_6446_ = lean_ctor_get(v_v_6438_, 0);
lean_inc_ref(v_moduleUri_6446_);
v_directImports_6447_ = lean_ctor_get(v_v_6438_, 2);
lean_inc_ref(v_directImports_6447_);
lean_dec(v_v_6438_);
v___x_6448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6448_, 0, v_moduleUri_6446_);
lean_ctor_set(v___x_6448_, 1, v_directImports_6447_);
v___x_6449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6437_, v___x_6448_, v_a_6442_);
v_init_6435_ = v___x_6449_;
v_x_6436_ = v_r_6440_;
goto _start;
}
}
else
{
lean_object* v___x_6451_; 
v___x_6451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6451_, 0, v_init_6435_);
return v___x_6451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6452_, lean_object* v_x_6453_){
_start:
{
if (lean_obj_tag(v_x_6453_) == 0)
{
lean_object* v_k_6454_; lean_object* v_v_6455_; lean_object* v_l_6456_; lean_object* v_r_6457_; lean_object* v___x_6458_; lean_object* v_a_6459_; lean_object* v_moduleUri_6460_; lean_object* v_directImports_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; 
v_k_6454_ = lean_ctor_get(v_x_6453_, 1);
lean_inc(v_k_6454_);
v_v_6455_ = lean_ctor_get(v_x_6453_, 2);
lean_inc(v_v_6455_);
v_l_6456_ = lean_ctor_get(v_x_6453_, 3);
lean_inc(v_l_6456_);
v_r_6457_ = lean_ctor_get(v_x_6453_, 4);
lean_inc(v_r_6457_);
lean_dec_ref_known(v_x_6453_, 5);
v___x_6458_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6452_, v_l_6456_);
v_a_6459_ = lean_ctor_get(v___x_6458_, 0);
lean_inc(v_a_6459_);
lean_dec_ref(v___x_6458_);
v_moduleUri_6460_ = lean_ctor_get(v_v_6455_, 0);
lean_inc_ref(v_moduleUri_6460_);
v_directImports_6461_ = lean_ctor_get(v_v_6455_, 2);
lean_inc_ref(v_directImports_6461_);
lean_dec(v_v_6455_);
v___x_6462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6462_, 0, v_moduleUri_6460_);
lean_ctor_set(v___x_6462_, 1, v_directImports_6461_);
v___x_6463_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6454_, v___x_6462_, v_a_6459_);
v_init_6452_ = v___x_6463_;
v_x_6453_ = v_r_6457_;
goto _start;
}
else
{
lean_object* v___x_6465_; 
v___x_6465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6465_, 0, v_init_6452_);
return v___x_6465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6466_){
_start:
{
lean_object* v_ileans_6467_; lean_object* v_workers_6468_; lean_object* v___y_6470_; lean_object* v_allDirectImports_6473_; lean_object* v___x_6474_; lean_object* v_a_6475_; 
v_ileans_6467_ = lean_ctor_get(v_self_6466_, 0);
lean_inc(v_ileans_6467_);
v_workers_6468_ = lean_ctor_get(v_self_6466_, 1);
lean_inc(v_workers_6468_);
lean_dec_ref(v_self_6466_);
v_allDirectImports_6473_ = lean_box(1);
v___x_6474_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6473_, v_ileans_6467_);
v_a_6475_ = lean_ctor_get(v___x_6474_, 0);
lean_inc(v_a_6475_);
lean_dec_ref(v___x_6474_);
v___y_6470_ = v_a_6475_;
goto v___jp_6469_;
v___jp_6469_:
{
lean_object* v___x_6471_; lean_object* v_a_6472_; 
v___x_6471_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6470_, v_workers_6468_);
v_a_6472_ = lean_ctor_get(v___x_6471_, 0);
lean_inc(v_a_6472_);
lean_dec_ref(v___x_6471_);
return v_a_6472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6476_, lean_object* v_mod_6477_){
_start:
{
lean_object* v_ileans_6478_; lean_object* v_workers_6479_; lean_object* v___x_6481_; uint8_t v_isShared_6482_; uint8_t v_isSharedCheck_6516_; 
v_ileans_6478_ = lean_ctor_get(v_self_6476_, 0);
v_workers_6479_ = lean_ctor_get(v_self_6476_, 1);
v_isSharedCheck_6516_ = !lean_is_exclusive(v_self_6476_);
if (v_isSharedCheck_6516_ == 0)
{
v___x_6481_ = v_self_6476_;
v_isShared_6482_ = v_isSharedCheck_6516_;
goto v_resetjp_6480_;
}
else
{
lean_inc(v_workers_6479_);
lean_inc(v_ileans_6478_);
lean_dec(v_self_6476_);
v___x_6481_ = lean_box(0);
v_isShared_6482_ = v_isSharedCheck_6516_;
goto v_resetjp_6480_;
}
v_resetjp_6480_:
{
lean_object* v___x_6501_; 
v___x_6501_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6479_, v_mod_6477_);
lean_dec(v_workers_6479_);
if (lean_obj_tag(v___x_6501_) == 1)
{
lean_object* v_val_6502_; lean_object* v___x_6504_; uint8_t v_isShared_6505_; uint8_t v_isSharedCheck_6515_; 
v_val_6502_ = lean_ctor_get(v___x_6501_, 0);
v_isSharedCheck_6515_ = !lean_is_exclusive(v___x_6501_);
if (v_isSharedCheck_6515_ == 0)
{
v___x_6504_ = v___x_6501_;
v_isShared_6505_ = v_isSharedCheck_6515_;
goto v_resetjp_6503_;
}
else
{
lean_inc(v_val_6502_);
lean_dec(v___x_6501_);
v___x_6504_ = lean_box(0);
v_isShared_6505_ = v_isSharedCheck_6515_;
goto v_resetjp_6503_;
}
v_resetjp_6503_:
{
uint8_t v___x_6506_; 
v___x_6506_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6502_);
if (v___x_6506_ == 0)
{
lean_del_object(v___x_6504_);
lean_dec(v_val_6502_);
goto v___jp_6483_;
}
else
{
lean_object* v_moduleUri_6507_; lean_object* v_refs_6508_; lean_object* v_decls_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___x_6513_; 
lean_del_object(v___x_6481_);
lean_dec(v_ileans_6478_);
v_moduleUri_6507_ = lean_ctor_get(v_val_6502_, 0);
lean_inc_ref(v_moduleUri_6507_);
v_refs_6508_ = lean_ctor_get(v_val_6502_, 4);
lean_inc(v_refs_6508_);
v_decls_6509_ = lean_ctor_get(v_val_6502_, 5);
lean_inc(v_decls_6509_);
lean_dec(v_val_6502_);
v___x_6510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6510_, 0, v_refs_6508_);
lean_ctor_set(v___x_6510_, 1, v_decls_6509_);
v___x_6511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6511_, 0, v_moduleUri_6507_);
lean_ctor_set(v___x_6511_, 1, v___x_6510_);
if (v_isShared_6505_ == 0)
{
lean_ctor_set(v___x_6504_, 0, v___x_6511_);
v___x_6513_ = v___x_6504_;
goto v_reusejp_6512_;
}
else
{
lean_object* v_reuseFailAlloc_6514_; 
v_reuseFailAlloc_6514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6514_, 0, v___x_6511_);
v___x_6513_ = v_reuseFailAlloc_6514_;
goto v_reusejp_6512_;
}
v_reusejp_6512_:
{
return v___x_6513_;
}
}
}
}
else
{
lean_dec(v___x_6501_);
goto v___jp_6483_;
}
v___jp_6483_:
{
lean_object* v___x_6484_; 
v___x_6484_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6478_, v_mod_6477_);
lean_dec(v_ileans_6478_);
if (lean_obj_tag(v___x_6484_) == 1)
{
lean_object* v_val_6485_; lean_object* v___x_6487_; uint8_t v_isShared_6488_; uint8_t v_isSharedCheck_6499_; 
v_val_6485_ = lean_ctor_get(v___x_6484_, 0);
v_isSharedCheck_6499_ = !lean_is_exclusive(v___x_6484_);
if (v_isSharedCheck_6499_ == 0)
{
v___x_6487_ = v___x_6484_;
v_isShared_6488_ = v_isSharedCheck_6499_;
goto v_resetjp_6486_;
}
else
{
lean_inc(v_val_6485_);
lean_dec(v___x_6484_);
v___x_6487_ = lean_box(0);
v_isShared_6488_ = v_isSharedCheck_6499_;
goto v_resetjp_6486_;
}
v_resetjp_6486_:
{
lean_object* v_moduleUri_6489_; lean_object* v_refs_6490_; lean_object* v_decls_6491_; lean_object* v___x_6493_; 
v_moduleUri_6489_ = lean_ctor_get(v_val_6485_, 0);
lean_inc_ref(v_moduleUri_6489_);
v_refs_6490_ = lean_ctor_get(v_val_6485_, 3);
lean_inc(v_refs_6490_);
v_decls_6491_ = lean_ctor_get(v_val_6485_, 4);
lean_inc(v_decls_6491_);
lean_dec(v_val_6485_);
if (v_isShared_6482_ == 0)
{
lean_ctor_set(v___x_6481_, 1, v_decls_6491_);
lean_ctor_set(v___x_6481_, 0, v_refs_6490_);
v___x_6493_ = v___x_6481_;
goto v_reusejp_6492_;
}
else
{
lean_object* v_reuseFailAlloc_6498_; 
v_reuseFailAlloc_6498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6498_, 0, v_refs_6490_);
lean_ctor_set(v_reuseFailAlloc_6498_, 1, v_decls_6491_);
v___x_6493_ = v_reuseFailAlloc_6498_;
goto v_reusejp_6492_;
}
v_reusejp_6492_:
{
lean_object* v___x_6494_; lean_object* v___x_6496_; 
v___x_6494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6494_, 0, v_moduleUri_6489_);
lean_ctor_set(v___x_6494_, 1, v___x_6493_);
if (v_isShared_6488_ == 0)
{
lean_ctor_set(v___x_6487_, 0, v___x_6494_);
v___x_6496_ = v___x_6487_;
goto v_reusejp_6495_;
}
else
{
lean_object* v_reuseFailAlloc_6497_; 
v_reuseFailAlloc_6497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6497_, 0, v___x_6494_);
v___x_6496_ = v_reuseFailAlloc_6497_;
goto v_reusejp_6495_;
}
v_reusejp_6495_:
{
return v___x_6496_;
}
}
}
}
else
{
lean_object* v___x_6500_; 
lean_dec(v___x_6484_);
lean_del_object(v___x_6481_);
v___x_6500_ = lean_box(0);
return v___x_6500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6517_, lean_object* v_mod_6518_){
_start:
{
lean_object* v_res_6519_; 
v_res_6519_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6517_, v_mod_6518_);
lean_dec(v_mod_6518_);
return v_res_6519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6520_, lean_object* v_mod_6521_){
_start:
{
lean_object* v_ileans_6522_; lean_object* v_workers_6523_; lean_object* v___x_6536_; 
v_ileans_6522_ = lean_ctor_get(v_self_6520_, 0);
v_workers_6523_ = lean_ctor_get(v_self_6520_, 1);
v___x_6536_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6523_, v_mod_6521_);
if (lean_obj_tag(v___x_6536_) == 1)
{
lean_object* v_val_6537_; lean_object* v___x_6539_; uint8_t v_isShared_6540_; uint8_t v_isSharedCheck_6546_; 
v_val_6537_ = lean_ctor_get(v___x_6536_, 0);
v_isSharedCheck_6546_ = !lean_is_exclusive(v___x_6536_);
if (v_isSharedCheck_6546_ == 0)
{
v___x_6539_ = v___x_6536_;
v_isShared_6540_ = v_isSharedCheck_6546_;
goto v_resetjp_6538_;
}
else
{
lean_inc(v_val_6537_);
lean_dec(v___x_6536_);
v___x_6539_ = lean_box(0);
v_isShared_6540_ = v_isSharedCheck_6546_;
goto v_resetjp_6538_;
}
v_resetjp_6538_:
{
uint8_t v___x_6541_; 
v___x_6541_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6537_);
if (v___x_6541_ == 0)
{
lean_del_object(v___x_6539_);
lean_dec(v_val_6537_);
goto v___jp_6524_;
}
else
{
lean_object* v_directImports_6542_; lean_object* v___x_6544_; 
v_directImports_6542_ = lean_ctor_get(v_val_6537_, 2);
lean_inc_ref(v_directImports_6542_);
lean_dec(v_val_6537_);
if (v_isShared_6540_ == 0)
{
lean_ctor_set(v___x_6539_, 0, v_directImports_6542_);
v___x_6544_ = v___x_6539_;
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
}
else
{
lean_dec(v___x_6536_);
goto v___jp_6524_;
}
v___jp_6524_:
{
lean_object* v___x_6525_; 
v___x_6525_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6522_, v_mod_6521_);
if (lean_obj_tag(v___x_6525_) == 1)
{
lean_object* v_val_6526_; lean_object* v___x_6528_; uint8_t v_isShared_6529_; uint8_t v_isSharedCheck_6534_; 
v_val_6526_ = lean_ctor_get(v___x_6525_, 0);
v_isSharedCheck_6534_ = !lean_is_exclusive(v___x_6525_);
if (v_isSharedCheck_6534_ == 0)
{
v___x_6528_ = v___x_6525_;
v_isShared_6529_ = v_isSharedCheck_6534_;
goto v_resetjp_6527_;
}
else
{
lean_inc(v_val_6526_);
lean_dec(v___x_6525_);
v___x_6528_ = lean_box(0);
v_isShared_6529_ = v_isSharedCheck_6534_;
goto v_resetjp_6527_;
}
v_resetjp_6527_:
{
lean_object* v_directImports_6530_; lean_object* v___x_6532_; 
v_directImports_6530_ = lean_ctor_get(v_val_6526_, 2);
lean_inc_ref(v_directImports_6530_);
lean_dec(v_val_6526_);
if (v_isShared_6529_ == 0)
{
lean_ctor_set(v___x_6528_, 0, v_directImports_6530_);
v___x_6532_ = v___x_6528_;
goto v_reusejp_6531_;
}
else
{
lean_object* v_reuseFailAlloc_6533_; 
v_reuseFailAlloc_6533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6533_, 0, v_directImports_6530_);
v___x_6532_ = v_reuseFailAlloc_6533_;
goto v_reusejp_6531_;
}
v_reusejp_6531_:
{
return v___x_6532_;
}
}
}
else
{
lean_object* v___x_6535_; 
lean_dec(v___x_6525_);
v___x_6535_ = lean_box(0);
return v___x_6535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6547_, lean_object* v_mod_6548_){
_start:
{
lean_object* v_res_6549_; 
v_res_6549_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6547_, v_mod_6548_);
lean_dec(v_mod_6548_);
lean_dec_ref(v_self_6547_);
return v_res_6549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6550_, lean_object* v_mod_6551_){
_start:
{
lean_object* v_ileans_6552_; lean_object* v_workers_6553_; lean_object* v___x_6566_; 
v_ileans_6552_ = lean_ctor_get(v_self_6550_, 0);
v_workers_6553_ = lean_ctor_get(v_self_6550_, 1);
v___x_6566_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6553_, v_mod_6551_);
if (lean_obj_tag(v___x_6566_) == 1)
{
lean_object* v_val_6567_; lean_object* v___x_6569_; uint8_t v_isShared_6570_; uint8_t v_isSharedCheck_6576_; 
v_val_6567_ = lean_ctor_get(v___x_6566_, 0);
v_isSharedCheck_6576_ = !lean_is_exclusive(v___x_6566_);
if (v_isSharedCheck_6576_ == 0)
{
v___x_6569_ = v___x_6566_;
v_isShared_6570_ = v_isSharedCheck_6576_;
goto v_resetjp_6568_;
}
else
{
lean_inc(v_val_6567_);
lean_dec(v___x_6566_);
v___x_6569_ = lean_box(0);
v_isShared_6570_ = v_isSharedCheck_6576_;
goto v_resetjp_6568_;
}
v_resetjp_6568_:
{
uint8_t v___x_6571_; 
v___x_6571_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6567_);
if (v___x_6571_ == 0)
{
lean_del_object(v___x_6569_);
lean_dec(v_val_6567_);
goto v___jp_6554_;
}
else
{
lean_object* v_decls_6572_; lean_object* v___x_6574_; 
v_decls_6572_ = lean_ctor_get(v_val_6567_, 5);
lean_inc(v_decls_6572_);
lean_dec(v_val_6567_);
if (v_isShared_6570_ == 0)
{
lean_ctor_set(v___x_6569_, 0, v_decls_6572_);
v___x_6574_ = v___x_6569_;
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
}
else
{
lean_dec(v___x_6566_);
goto v___jp_6554_;
}
v___jp_6554_:
{
lean_object* v___x_6555_; 
v___x_6555_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6552_, v_mod_6551_);
if (lean_obj_tag(v___x_6555_) == 1)
{
lean_object* v_val_6556_; lean_object* v___x_6558_; uint8_t v_isShared_6559_; uint8_t v_isSharedCheck_6564_; 
v_val_6556_ = lean_ctor_get(v___x_6555_, 0);
v_isSharedCheck_6564_ = !lean_is_exclusive(v___x_6555_);
if (v_isSharedCheck_6564_ == 0)
{
v___x_6558_ = v___x_6555_;
v_isShared_6559_ = v_isSharedCheck_6564_;
goto v_resetjp_6557_;
}
else
{
lean_inc(v_val_6556_);
lean_dec(v___x_6555_);
v___x_6558_ = lean_box(0);
v_isShared_6559_ = v_isSharedCheck_6564_;
goto v_resetjp_6557_;
}
v_resetjp_6557_:
{
lean_object* v_decls_6560_; lean_object* v___x_6562_; 
v_decls_6560_ = lean_ctor_get(v_val_6556_, 4);
lean_inc(v_decls_6560_);
lean_dec(v_val_6556_);
if (v_isShared_6559_ == 0)
{
lean_ctor_set(v___x_6558_, 0, v_decls_6560_);
v___x_6562_ = v___x_6558_;
goto v_reusejp_6561_;
}
else
{
lean_object* v_reuseFailAlloc_6563_; 
v_reuseFailAlloc_6563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6563_, 0, v_decls_6560_);
v___x_6562_ = v_reuseFailAlloc_6563_;
goto v_reusejp_6561_;
}
v_reusejp_6561_:
{
return v___x_6562_;
}
}
}
else
{
lean_object* v___x_6565_; 
lean_dec(v___x_6555_);
v___x_6565_ = lean_box(0);
return v___x_6565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6577_, lean_object* v_mod_6578_){
_start:
{
lean_object* v_res_6579_; 
v_res_6579_ = l_Lean_Server_References_getDecls_x3f(v_self_6577_, v_mod_6578_);
lean_dec(v_mod_6578_);
lean_dec_ref(v_self_6577_);
return v_res_6579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6580_, lean_object* v_x_6581_){
_start:
{
if (lean_obj_tag(v_x_6581_) == 0)
{
lean_object* v_k_6582_; lean_object* v_v_6583_; lean_object* v_l_6584_; lean_object* v_r_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; 
v_k_6582_ = lean_ctor_get(v_x_6581_, 1);
v_v_6583_ = lean_ctor_get(v_x_6581_, 2);
v_l_6584_ = lean_ctor_get(v_x_6581_, 3);
v_r_6585_ = lean_ctor_get(v_x_6581_, 4);
v___x_6586_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6580_, v_l_6584_);
lean_inc(v_v_6583_);
lean_inc(v_k_6582_);
v___x_6587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6587_, 0, v_k_6582_);
lean_ctor_set(v___x_6587_, 1, v_v_6583_);
v___x_6588_ = lean_array_push(v___x_6586_, v___x_6587_);
v_init_6580_ = v___x_6588_;
v_x_6581_ = v_r_6585_;
goto _start;
}
else
{
return v_init_6580_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6590_, lean_object* v_x_6591_){
_start:
{
lean_object* v_res_6592_; 
v_res_6592_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6590_, v_x_6591_);
lean_dec(v_x_6591_);
return v_res_6592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6593_, lean_object* v_k_6594_){
_start:
{
if (lean_obj_tag(v_t_6593_) == 0)
{
lean_object* v_k_6595_; lean_object* v_v_6596_; lean_object* v_l_6597_; lean_object* v_r_6598_; uint8_t v___x_6599_; 
v_k_6595_ = lean_ctor_get(v_t_6593_, 1);
v_v_6596_ = lean_ctor_get(v_t_6593_, 2);
v_l_6597_ = lean_ctor_get(v_t_6593_, 3);
v_r_6598_ = lean_ctor_get(v_t_6593_, 4);
v___x_6599_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6594_, v_k_6595_);
switch(v___x_6599_)
{
case 0:
{
v_t_6593_ = v_l_6597_;
goto _start;
}
case 1:
{
lean_object* v___x_6601_; 
lean_inc(v_v_6596_);
v___x_6601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6601_, 0, v_v_6596_);
return v___x_6601_;
}
default: 
{
v_t_6593_ = v_r_6598_;
goto _start;
}
}
}
else
{
lean_object* v___x_6603_; 
v___x_6603_ = lean_box(0);
return v___x_6603_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6604_, lean_object* v_k_6605_){
_start:
{
lean_object* v_res_6606_; 
v_res_6606_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6604_, v_k_6605_);
lean_dec_ref(v_k_6605_);
lean_dec(v_t_6604_);
return v_res_6606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6607_, lean_object* v_as_6608_, size_t v_sz_6609_, size_t v_i_6610_, lean_object* v_b_6611_){
_start:
{
lean_object* v_a_6613_; uint8_t v___x_6617_; 
v___x_6617_ = lean_usize_dec_lt(v_i_6610_, v_sz_6609_);
if (v___x_6617_ == 0)
{
return v_b_6611_;
}
else
{
lean_object* v_a_6618_; lean_object* v_snd_6619_; lean_object* v_snd_6620_; lean_object* v_fst_6621_; lean_object* v___x_6623_; uint8_t v_isShared_6624_; uint8_t v_isSharedCheck_6649_; 
v_a_6618_ = lean_array_uget(v_as_6608_, v_i_6610_);
v_snd_6619_ = lean_ctor_get(v_a_6618_, 1);
lean_inc(v_snd_6619_);
v_snd_6620_ = lean_ctor_get(v_snd_6619_, 1);
lean_inc(v_snd_6620_);
v_fst_6621_ = lean_ctor_get(v_a_6618_, 0);
v_isSharedCheck_6649_ = !lean_is_exclusive(v_a_6618_);
if (v_isSharedCheck_6649_ == 0)
{
lean_object* v_unused_6650_; 
v_unused_6650_ = lean_ctor_get(v_a_6618_, 1);
lean_dec(v_unused_6650_);
v___x_6623_ = v_a_6618_;
v_isShared_6624_ = v_isSharedCheck_6649_;
goto v_resetjp_6622_;
}
else
{
lean_inc(v_fst_6621_);
lean_dec(v_a_6618_);
v___x_6623_ = lean_box(0);
v_isShared_6624_ = v_isSharedCheck_6649_;
goto v_resetjp_6622_;
}
v_resetjp_6622_:
{
lean_object* v_fst_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6647_; 
v_fst_6625_ = lean_ctor_get(v_snd_6619_, 0);
v_isSharedCheck_6647_ = !lean_is_exclusive(v_snd_6619_);
if (v_isSharedCheck_6647_ == 0)
{
lean_object* v_unused_6648_; 
v_unused_6648_ = lean_ctor_get(v_snd_6619_, 1);
lean_dec(v_unused_6648_);
v___x_6627_ = v_snd_6619_;
v_isShared_6628_ = v_isSharedCheck_6647_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_fst_6625_);
lean_dec(v_snd_6619_);
v___x_6627_ = lean_box(0);
v_isShared_6628_ = v_isSharedCheck_6647_;
goto v_resetjp_6626_;
}
v_resetjp_6626_:
{
lean_object* v_fst_6629_; lean_object* v_snd_6630_; lean_object* v___x_6632_; uint8_t v_isShared_6633_; uint8_t v_isSharedCheck_6646_; 
v_fst_6629_ = lean_ctor_get(v_snd_6620_, 0);
v_snd_6630_ = lean_ctor_get(v_snd_6620_, 1);
v_isSharedCheck_6646_ = !lean_is_exclusive(v_snd_6620_);
if (v_isSharedCheck_6646_ == 0)
{
v___x_6632_ = v_snd_6620_;
v_isShared_6633_ = v_isSharedCheck_6646_;
goto v_resetjp_6631_;
}
else
{
lean_inc(v_snd_6630_);
lean_inc(v_fst_6629_);
lean_dec(v_snd_6620_);
v___x_6632_ = lean_box(0);
v_isShared_6633_ = v_isSharedCheck_6646_;
goto v_resetjp_6631_;
}
v_resetjp_6631_:
{
lean_object* v___x_6634_; 
v___x_6634_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6629_, v_ident_6607_);
lean_dec(v_fst_6629_);
if (lean_obj_tag(v___x_6634_) == 1)
{
lean_object* v_val_6635_; lean_object* v___x_6637_; 
v_val_6635_ = lean_ctor_get(v___x_6634_, 0);
lean_inc(v_val_6635_);
lean_dec_ref_known(v___x_6634_, 1);
if (v_isShared_6633_ == 0)
{
lean_ctor_set(v___x_6632_, 0, v_val_6635_);
v___x_6637_ = v___x_6632_;
goto v_reusejp_6636_;
}
else
{
lean_object* v_reuseFailAlloc_6645_; 
v_reuseFailAlloc_6645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6645_, 0, v_val_6635_);
lean_ctor_set(v_reuseFailAlloc_6645_, 1, v_snd_6630_);
v___x_6637_ = v_reuseFailAlloc_6645_;
goto v_reusejp_6636_;
}
v_reusejp_6636_:
{
lean_object* v___x_6639_; 
if (v_isShared_6628_ == 0)
{
lean_ctor_set(v___x_6627_, 1, v___x_6637_);
lean_ctor_set(v___x_6627_, 0, v_fst_6621_);
v___x_6639_ = v___x_6627_;
goto v_reusejp_6638_;
}
else
{
lean_object* v_reuseFailAlloc_6644_; 
v_reuseFailAlloc_6644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6644_, 0, v_fst_6621_);
lean_ctor_set(v_reuseFailAlloc_6644_, 1, v___x_6637_);
v___x_6639_ = v_reuseFailAlloc_6644_;
goto v_reusejp_6638_;
}
v_reusejp_6638_:
{
lean_object* v___x_6641_; 
if (v_isShared_6624_ == 0)
{
lean_ctor_set(v___x_6623_, 1, v___x_6639_);
lean_ctor_set(v___x_6623_, 0, v_fst_6625_);
v___x_6641_ = v___x_6623_;
goto v_reusejp_6640_;
}
else
{
lean_object* v_reuseFailAlloc_6643_; 
v_reuseFailAlloc_6643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6643_, 0, v_fst_6625_);
lean_ctor_set(v_reuseFailAlloc_6643_, 1, v___x_6639_);
v___x_6641_ = v_reuseFailAlloc_6643_;
goto v_reusejp_6640_;
}
v_reusejp_6640_:
{
lean_object* v___x_6642_; 
v___x_6642_ = lean_array_push(v_b_6611_, v___x_6641_);
v_a_6613_ = v___x_6642_;
goto v___jp_6612_;
}
}
}
}
else
{
lean_dec(v___x_6634_);
lean_del_object(v___x_6632_);
lean_dec(v_snd_6630_);
lean_del_object(v___x_6627_);
lean_dec(v_fst_6625_);
lean_del_object(v___x_6623_);
lean_dec(v_fst_6621_);
v_a_6613_ = v_b_6611_;
goto v___jp_6612_;
}
}
}
}
}
v___jp_6612_:
{
size_t v___x_6614_; size_t v___x_6615_; 
v___x_6614_ = ((size_t)1ULL);
v___x_6615_ = lean_usize_add(v_i_6610_, v___x_6614_);
v_i_6610_ = v___x_6615_;
v_b_6611_ = v_a_6613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6651_, lean_object* v_as_6652_, lean_object* v_sz_6653_, lean_object* v_i_6654_, lean_object* v_b_6655_){
_start:
{
size_t v_sz_boxed_6656_; size_t v_i_boxed_6657_; lean_object* v_res_6658_; 
v_sz_boxed_6656_ = lean_unbox_usize(v_sz_6653_);
lean_dec(v_sz_6653_);
v_i_boxed_6657_ = lean_unbox_usize(v_i_6654_);
lean_dec(v_i_6654_);
v_res_6658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6651_, v_as_6652_, v_sz_boxed_6656_, v_i_boxed_6657_, v_b_6655_);
lean_dec_ref(v_as_6652_);
lean_dec_ref(v_ident_6651_);
return v_res_6658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6665_, lean_object* v_ident_6666_){
_start:
{
lean_object* v___y_6668_; 
if (lean_obj_tag(v_ident_6666_) == 0)
{
lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; 
v___x_6673_ = l_Lean_Server_References_allRefs(v_self_6665_);
v___x_6674_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6675_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6674_, v___x_6673_);
lean_dec(v___x_6673_);
v___y_6668_ = v___x_6675_;
goto v___jp_6667_;
}
else
{
lean_object* v_moduleName_6676_; lean_object* v_identModuleName_6677_; lean_object* v___x_6678_; 
v_moduleName_6676_ = lean_ctor_get(v_ident_6666_, 0);
lean_inc_ref(v_moduleName_6676_);
v_identModuleName_6677_ = l_String_toName(v_moduleName_6676_);
v___x_6678_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6665_, v_identModuleName_6677_);
if (lean_obj_tag(v___x_6678_) == 0)
{
lean_object* v___x_6679_; 
lean_dec(v_identModuleName_6677_);
v___x_6679_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6668_ = v___x_6679_;
goto v___jp_6667_;
}
else
{
lean_object* v_val_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; 
v_val_6680_ = lean_ctor_get(v___x_6678_, 0);
lean_inc(v_val_6680_);
lean_dec_ref_known(v___x_6678_, 1);
v___x_6681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6681_, 0, v_identModuleName_6677_);
lean_ctor_set(v___x_6681_, 1, v_val_6680_);
v___x_6682_ = lean_unsigned_to_nat(1u);
v___x_6683_ = lean_mk_empty_array_with_capacity(v___x_6682_);
v___x_6684_ = lean_array_push(v___x_6683_, v___x_6681_);
v___y_6668_ = v___x_6684_;
goto v___jp_6667_;
}
}
v___jp_6667_:
{
lean_object* v_result_6669_; size_t v_sz_6670_; size_t v___x_6671_; lean_object* v___x_6672_; 
v_result_6669_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6670_ = lean_array_size(v___y_6668_);
v___x_6671_ = ((size_t)0ULL);
v___x_6672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6666_, v___y_6668_, v_sz_6670_, v___x_6671_, v_result_6669_);
lean_dec_ref(v___y_6668_);
lean_dec_ref(v_ident_6666_);
return v___x_6672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6685_, lean_object* v_t_6686_, lean_object* v_k_6687_){
_start:
{
lean_object* v___x_6688_; 
v___x_6688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6686_, v_k_6687_);
return v___x_6688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6689_, lean_object* v_t_6690_, lean_object* v_k_6691_){
_start:
{
lean_object* v_res_6692_; 
v_res_6692_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6689_, v_t_6690_, v_k_6691_);
lean_dec_ref(v_k_6691_);
lean_dec(v_t_6690_);
return v_res_6692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6693_, lean_object* v_t_6694_){
_start:
{
lean_object* v___x_6695_; 
v___x_6695_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6693_, v_t_6694_);
return v___x_6695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6696_, lean_object* v_t_6697_){
_start:
{
lean_object* v_res_6698_; 
v_res_6698_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6696_, v_t_6697_);
lean_dec(v_t_6697_);
return v_res_6698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6699_, lean_object* v_module_6700_, lean_object* v_pos_6701_, uint8_t v_includeStop_6702_){
_start:
{
lean_object* v___x_6703_; 
v___x_6703_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6699_, v_module_6700_);
if (lean_obj_tag(v___x_6703_) == 1)
{
lean_object* v_val_6704_; lean_object* v_snd_6705_; lean_object* v_fst_6706_; lean_object* v___x_6707_; 
v_val_6704_ = lean_ctor_get(v___x_6703_, 0);
lean_inc(v_val_6704_);
lean_dec_ref_known(v___x_6703_, 1);
v_snd_6705_ = lean_ctor_get(v_val_6704_, 1);
lean_inc(v_snd_6705_);
lean_dec(v_val_6704_);
v_fst_6706_ = lean_ctor_get(v_snd_6705_, 0);
lean_inc(v_fst_6706_);
lean_dec(v_snd_6705_);
v___x_6707_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6706_, v_pos_6701_, v_includeStop_6702_);
return v___x_6707_;
}
else
{
lean_object* v___x_6708_; 
lean_dec(v___x_6703_);
v___x_6708_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6709_, lean_object* v_module_6710_, lean_object* v_pos_6711_, lean_object* v_includeStop_6712_){
_start:
{
uint8_t v_includeStop_boxed_6713_; lean_object* v_res_6714_; 
v_includeStop_boxed_6713_ = lean_unbox(v_includeStop_6712_);
v_res_6714_ = l_Lean_Server_References_findAt(v_self_6709_, v_module_6710_, v_pos_6711_, v_includeStop_boxed_6713_);
lean_dec_ref(v_pos_6711_);
lean_dec(v_module_6710_);
return v_res_6714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6715_, lean_object* v_module_6716_, lean_object* v_pos_6717_, uint8_t v_includeStop_6718_){
_start:
{
lean_object* v___x_6719_; 
v___x_6719_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6715_, v_module_6716_);
if (lean_obj_tag(v___x_6719_) == 0)
{
lean_object* v___x_6720_; 
v___x_6720_ = lean_box(0);
return v___x_6720_;
}
else
{
lean_object* v_val_6721_; lean_object* v_snd_6722_; lean_object* v_fst_6723_; lean_object* v___x_6724_; 
v_val_6721_ = lean_ctor_get(v___x_6719_, 0);
lean_inc(v_val_6721_);
lean_dec_ref_known(v___x_6719_, 1);
v_snd_6722_ = lean_ctor_get(v_val_6721_, 1);
lean_inc(v_snd_6722_);
lean_dec(v_val_6721_);
v_fst_6723_ = lean_ctor_get(v_snd_6722_, 0);
lean_inc(v_fst_6723_);
lean_dec(v_snd_6722_);
v___x_6724_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6723_, v_pos_6717_, v_includeStop_6718_);
lean_dec(v_fst_6723_);
return v___x_6724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6725_, lean_object* v_module_6726_, lean_object* v_pos_6727_, lean_object* v_includeStop_6728_){
_start:
{
uint8_t v_includeStop_boxed_6729_; lean_object* v_res_6730_; 
v_includeStop_boxed_6729_ = lean_unbox(v_includeStop_6728_);
v_res_6730_ = l_Lean_Server_References_findRange_x3f(v_self_6725_, v_module_6726_, v_pos_6727_, v_includeStop_boxed_6729_);
lean_dec_ref(v_pos_6727_);
lean_dec(v_module_6726_);
return v_res_6730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6731_, lean_object* v_k_6732_){
_start:
{
if (lean_obj_tag(v_t_6731_) == 0)
{
lean_object* v_k_6733_; lean_object* v_v_6734_; lean_object* v_l_6735_; lean_object* v_r_6736_; uint8_t v___x_6737_; 
v_k_6733_ = lean_ctor_get(v_t_6731_, 1);
v_v_6734_ = lean_ctor_get(v_t_6731_, 2);
v_l_6735_ = lean_ctor_get(v_t_6731_, 3);
v_r_6736_ = lean_ctor_get(v_t_6731_, 4);
v___x_6737_ = lean_string_compare(v_k_6732_, v_k_6733_);
switch(v___x_6737_)
{
case 0:
{
v_t_6731_ = v_l_6735_;
goto _start;
}
case 1:
{
lean_object* v___x_6739_; 
lean_inc(v_v_6734_);
v___x_6739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6739_, 0, v_v_6734_);
return v___x_6739_;
}
default: 
{
v_t_6731_ = v_r_6736_;
goto _start;
}
}
}
else
{
lean_object* v___x_6741_; 
v___x_6741_ = lean_box(0);
return v___x_6741_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6742_, lean_object* v_k_6743_){
_start:
{
lean_object* v_res_6744_; 
v_res_6744_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6742_, v_k_6743_);
lean_dec_ref(v_k_6743_);
lean_dec(v_t_6742_);
return v_res_6744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6745_, lean_object* v_name_6746_){
_start:
{
lean_object* v___x_6747_; 
v___x_6747_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6745_, v_name_6746_);
if (lean_obj_tag(v___x_6747_) == 0)
{
lean_object* v___x_6748_; 
lean_dec_ref(v_name_6746_);
v___x_6748_ = lean_box(0);
return v___x_6748_;
}
else
{
lean_object* v_val_6749_; lean_object* v___x_6751_; uint8_t v_isShared_6752_; uint8_t v_isSharedCheck_6759_; 
v_val_6749_ = lean_ctor_get(v___x_6747_, 0);
v_isSharedCheck_6759_ = !lean_is_exclusive(v___x_6747_);
if (v_isSharedCheck_6759_ == 0)
{
v___x_6751_ = v___x_6747_;
v_isShared_6752_ = v_isSharedCheck_6759_;
goto v_resetjp_6750_;
}
else
{
lean_inc(v_val_6749_);
lean_dec(v___x_6747_);
v___x_6751_ = lean_box(0);
v_isShared_6752_ = v_isSharedCheck_6759_;
goto v_resetjp_6750_;
}
v_resetjp_6750_:
{
lean_object* v___x_6753_; lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6757_; 
v___x_6753_ = l_Lean_Lsp_DeclInfo_range(v_val_6749_);
v___x_6754_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6749_);
lean_dec(v_val_6749_);
v___x_6755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6755_, 0, v_name_6746_);
lean_ctor_set(v___x_6755_, 1, v___x_6753_);
lean_ctor_set(v___x_6755_, 2, v___x_6754_);
if (v_isShared_6752_ == 0)
{
lean_ctor_set(v___x_6751_, 0, v___x_6755_);
v___x_6757_ = v___x_6751_;
goto v_reusejp_6756_;
}
else
{
lean_object* v_reuseFailAlloc_6758_; 
v_reuseFailAlloc_6758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6758_, 0, v___x_6755_);
v___x_6757_ = v_reuseFailAlloc_6758_;
goto v_reusejp_6756_;
}
v_reusejp_6756_:
{
return v___x_6757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6760_, lean_object* v_name_6761_){
_start:
{
lean_object* v_res_6762_; 
v_res_6762_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6760_, v_name_6761_);
lean_dec(v_ds_6760_);
return v_res_6762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6763_, lean_object* v_t_6764_, lean_object* v_k_6765_){
_start:
{
lean_object* v___x_6766_; 
v___x_6766_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6764_, v_k_6765_);
return v___x_6766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6767_, lean_object* v_t_6768_, lean_object* v_k_6769_){
_start:
{
lean_object* v_res_6770_; 
v_res_6770_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6767_, v_t_6768_, v_k_6769_);
lean_dec_ref(v_k_6769_);
lean_dec(v_t_6768_);
return v_res_6770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6771_, lean_object* v_fst_6772_, lean_object* v_snd_6773_, lean_object* v_as_6774_, size_t v_sz_6775_, size_t v_i_6776_, lean_object* v_b_6777_){
_start:
{
uint8_t v___x_6778_; 
v___x_6778_ = lean_usize_dec_lt(v_i_6776_, v_sz_6775_);
if (v___x_6778_ == 0)
{
lean_dec(v_fst_6772_);
lean_dec_ref(v_fst_6771_);
return v_b_6777_;
}
else
{
lean_object* v_a_6779_; lean_object* v___y_6781_; lean_object* v___x_6789_; 
v_a_6779_ = lean_array_uget_borrowed(v_as_6774_, v_i_6776_);
v___x_6789_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6779_);
if (lean_obj_tag(v___x_6789_) == 0)
{
lean_object* v___x_6790_; 
v___x_6790_ = lean_box(0);
v___y_6781_ = v___x_6790_;
goto v___jp_6780_;
}
else
{
lean_object* v_val_6791_; lean_object* v___x_6792_; 
v_val_6791_ = lean_ctor_get(v___x_6789_, 0);
lean_inc(v_val_6791_);
lean_dec_ref_known(v___x_6789_, 1);
v___x_6792_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6773_, v_val_6791_);
v___y_6781_ = v___x_6792_;
goto v___jp_6780_;
}
v___jp_6780_:
{
lean_object* v___x_6782_; lean_object* v___x_6783_; lean_object* v___x_6784_; lean_object* v___x_6785_; size_t v___x_6786_; size_t v___x_6787_; 
v___x_6782_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6779_);
lean_inc_ref(v_fst_6771_);
v___x_6783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6783_, 0, v_fst_6771_);
lean_ctor_set(v___x_6783_, 1, v___x_6782_);
lean_inc(v_fst_6772_);
v___x_6784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6784_, 0, v___x_6783_);
lean_ctor_set(v___x_6784_, 1, v_fst_6772_);
lean_ctor_set(v___x_6784_, 2, v___y_6781_);
v___x_6785_ = lean_array_push(v_b_6777_, v___x_6784_);
v___x_6786_ = ((size_t)1ULL);
v___x_6787_ = lean_usize_add(v_i_6776_, v___x_6786_);
v_i_6776_ = v___x_6787_;
v_b_6777_ = v___x_6785_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6793_, lean_object* v_fst_6794_, lean_object* v_snd_6795_, lean_object* v_as_6796_, lean_object* v_sz_6797_, lean_object* v_i_6798_, lean_object* v_b_6799_){
_start:
{
size_t v_sz_boxed_6800_; size_t v_i_boxed_6801_; lean_object* v_res_6802_; 
v_sz_boxed_6800_ = lean_unbox_usize(v_sz_6797_);
lean_dec(v_sz_6797_);
v_i_boxed_6801_ = lean_unbox_usize(v_i_6798_);
lean_dec(v_i_6798_);
v_res_6802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6793_, v_fst_6794_, v_snd_6795_, v_as_6796_, v_sz_boxed_6800_, v_i_boxed_6801_, v_b_6799_);
lean_dec_ref(v_as_6796_);
lean_dec(v_snd_6795_);
return v_res_6802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6803_, lean_object* v_as_6804_, size_t v_sz_6805_, size_t v_i_6806_, lean_object* v_b_6807_){
_start:
{
uint8_t v___x_6808_; 
v___x_6808_ = lean_usize_dec_lt(v_i_6806_, v_sz_6805_);
if (v___x_6808_ == 0)
{
return v_b_6807_;
}
else
{
lean_object* v_a_6809_; lean_object* v_snd_6810_; lean_object* v_snd_6811_; lean_object* v_fst_6812_; lean_object* v_fst_6813_; lean_object* v_fst_6814_; lean_object* v_snd_6815_; lean_object* v___x_6817_; uint8_t v_isShared_6818_; uint8_t v_isSharedCheck_6842_; 
v_a_6809_ = lean_array_uget_borrowed(v_as_6804_, v_i_6806_);
v_snd_6810_ = lean_ctor_get(v_a_6809_, 1);
v_snd_6811_ = lean_ctor_get(v_snd_6810_, 1);
lean_inc(v_snd_6811_);
v_fst_6812_ = lean_ctor_get(v_a_6809_, 0);
v_fst_6813_ = lean_ctor_get(v_snd_6810_, 0);
v_fst_6814_ = lean_ctor_get(v_snd_6811_, 0);
v_snd_6815_ = lean_ctor_get(v_snd_6811_, 1);
v_isSharedCheck_6842_ = !lean_is_exclusive(v_snd_6811_);
if (v_isSharedCheck_6842_ == 0)
{
v___x_6817_ = v_snd_6811_;
v_isShared_6818_ = v_isSharedCheck_6842_;
goto v_resetjp_6816_;
}
else
{
lean_inc(v_snd_6815_);
lean_inc(v_fst_6814_);
lean_dec(v_snd_6811_);
v___x_6817_ = lean_box(0);
v_isShared_6818_ = v_isSharedCheck_6842_;
goto v_resetjp_6816_;
}
v_resetjp_6816_:
{
lean_object* v_result_6820_; 
if (v_includeDefinition_6803_ == 0)
{
lean_del_object(v___x_6817_);
v_result_6820_ = v_b_6807_;
goto v___jp_6819_;
}
else
{
lean_object* v_definition_x3f_6828_; 
v_definition_x3f_6828_ = lean_ctor_get(v_fst_6814_, 0);
if (lean_obj_tag(v_definition_x3f_6828_) == 1)
{
lean_object* v_val_6829_; lean_object* v___y_6831_; lean_object* v___x_6838_; 
v_val_6829_ = lean_ctor_get(v_definition_x3f_6828_, 0);
v___x_6838_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6829_);
if (lean_obj_tag(v___x_6838_) == 0)
{
lean_object* v___x_6839_; 
v___x_6839_ = lean_box(0);
v___y_6831_ = v___x_6839_;
goto v___jp_6830_;
}
else
{
lean_object* v_val_6840_; lean_object* v___x_6841_; 
v_val_6840_ = lean_ctor_get(v___x_6838_, 0);
lean_inc(v_val_6840_);
lean_dec_ref_known(v___x_6838_, 1);
v___x_6841_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6815_, v_val_6840_);
v___y_6831_ = v___x_6841_;
goto v___jp_6830_;
}
v___jp_6830_:
{
lean_object* v___x_6832_; lean_object* v___x_6834_; 
v___x_6832_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6829_);
lean_inc(v_fst_6812_);
if (v_isShared_6818_ == 0)
{
lean_ctor_set(v___x_6817_, 1, v___x_6832_);
lean_ctor_set(v___x_6817_, 0, v_fst_6812_);
v___x_6834_ = v___x_6817_;
goto v_reusejp_6833_;
}
else
{
lean_object* v_reuseFailAlloc_6837_; 
v_reuseFailAlloc_6837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6837_, 0, v_fst_6812_);
lean_ctor_set(v_reuseFailAlloc_6837_, 1, v___x_6832_);
v___x_6834_ = v_reuseFailAlloc_6837_;
goto v_reusejp_6833_;
}
v_reusejp_6833_:
{
lean_object* v___x_6835_; lean_object* v___x_6836_; 
lean_inc(v_fst_6813_);
v___x_6835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6835_, 0, v___x_6834_);
lean_ctor_set(v___x_6835_, 1, v_fst_6813_);
lean_ctor_set(v___x_6835_, 2, v___y_6831_);
v___x_6836_ = lean_array_push(v_b_6807_, v___x_6835_);
v_result_6820_ = v___x_6836_;
goto v___jp_6819_;
}
}
}
else
{
lean_del_object(v___x_6817_);
v_result_6820_ = v_b_6807_;
goto v___jp_6819_;
}
}
v___jp_6819_:
{
lean_object* v_usages_6821_; size_t v_sz_6822_; size_t v___x_6823_; lean_object* v___x_6824_; size_t v___x_6825_; size_t v___x_6826_; 
v_usages_6821_ = lean_ctor_get(v_fst_6814_, 1);
lean_inc_ref(v_usages_6821_);
lean_dec(v_fst_6814_);
v_sz_6822_ = lean_array_size(v_usages_6821_);
v___x_6823_ = ((size_t)0ULL);
lean_inc(v_fst_6813_);
lean_inc(v_fst_6812_);
v___x_6824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6812_, v_fst_6813_, v_snd_6815_, v_usages_6821_, v_sz_6822_, v___x_6823_, v_result_6820_);
lean_dec_ref(v_usages_6821_);
lean_dec(v_snd_6815_);
v___x_6825_ = ((size_t)1ULL);
v___x_6826_ = lean_usize_add(v_i_6806_, v___x_6825_);
v_i_6806_ = v___x_6826_;
v_b_6807_ = v___x_6824_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6843_, lean_object* v_as_6844_, lean_object* v_sz_6845_, lean_object* v_i_6846_, lean_object* v_b_6847_){
_start:
{
uint8_t v_includeDefinition_boxed_6848_; size_t v_sz_boxed_6849_; size_t v_i_boxed_6850_; lean_object* v_res_6851_; 
v_includeDefinition_boxed_6848_ = lean_unbox(v_includeDefinition_6843_);
v_sz_boxed_6849_ = lean_unbox_usize(v_sz_6845_);
lean_dec(v_sz_6845_);
v_i_boxed_6850_ = lean_unbox_usize(v_i_6846_);
lean_dec(v_i_6846_);
v_res_6851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6848_, v_as_6844_, v_sz_boxed_6849_, v_i_boxed_6850_, v_b_6847_);
lean_dec_ref(v_as_6844_);
return v_res_6851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6854_, lean_object* v_ident_6855_, uint8_t v_includeDefinition_6856_){
_start:
{
lean_object* v_result_6857_; lean_object* v___x_6858_; size_t v_sz_6859_; size_t v___x_6860_; lean_object* v___x_6861_; 
v_result_6857_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6858_ = l_Lean_Server_References_allRefsFor(v_self_6854_, v_ident_6855_);
v_sz_6859_ = lean_array_size(v___x_6858_);
v___x_6860_ = ((size_t)0ULL);
v___x_6861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6856_, v___x_6858_, v_sz_6859_, v___x_6860_, v_result_6857_);
lean_dec_ref(v___x_6858_);
return v___x_6861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6862_, lean_object* v_ident_6863_, lean_object* v_includeDefinition_6864_){
_start:
{
uint8_t v_includeDefinition_boxed_6865_; lean_object* v_res_6866_; 
v_includeDefinition_boxed_6865_ = lean_unbox(v_includeDefinition_6864_);
v_res_6866_ = l_Lean_Server_References_referringTo(v_self_6862_, v_ident_6863_, v_includeDefinition_boxed_6865_);
return v_res_6866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6870_, size_t v_sz_6871_, size_t v_i_6872_, lean_object* v_b_6873_){
_start:
{
uint8_t v___x_6874_; 
v___x_6874_ = lean_usize_dec_lt(v_i_6872_, v_sz_6871_);
if (v___x_6874_ == 0)
{
lean_inc_ref(v_b_6873_);
return v_b_6873_;
}
else
{
lean_object* v_a_6875_; lean_object* v_snd_6876_; lean_object* v_snd_6877_; lean_object* v_fst_6878_; lean_object* v_fst_6879_; lean_object* v_fst_6880_; lean_object* v_snd_6881_; lean_object* v___x_6883_; uint8_t v_isShared_6884_; uint8_t v_isSharedCheck_6919_; 
v_a_6875_ = lean_array_uget_borrowed(v_as_6870_, v_i_6872_);
v_snd_6876_ = lean_ctor_get(v_a_6875_, 1);
v_snd_6877_ = lean_ctor_get(v_snd_6876_, 1);
lean_inc(v_snd_6877_);
v_fst_6878_ = lean_ctor_get(v_snd_6877_, 0);
lean_inc(v_fst_6878_);
v_fst_6879_ = lean_ctor_get(v_a_6875_, 0);
v_fst_6880_ = lean_ctor_get(v_snd_6876_, 0);
v_snd_6881_ = lean_ctor_get(v_snd_6877_, 1);
v_isSharedCheck_6919_ = !lean_is_exclusive(v_snd_6877_);
if (v_isSharedCheck_6919_ == 0)
{
lean_object* v_unused_6920_; 
v_unused_6920_ = lean_ctor_get(v_snd_6877_, 0);
lean_dec(v_unused_6920_);
v___x_6883_ = v_snd_6877_;
v_isShared_6884_ = v_isSharedCheck_6919_;
goto v_resetjp_6882_;
}
else
{
lean_inc(v_snd_6881_);
lean_dec(v_snd_6877_);
v___x_6883_ = lean_box(0);
v_isShared_6884_ = v_isSharedCheck_6919_;
goto v_resetjp_6882_;
}
v_resetjp_6882_:
{
lean_object* v_definition_x3f_6885_; lean_object* v___x_6887_; uint8_t v_isShared_6888_; uint8_t v_isSharedCheck_6917_; 
v_definition_x3f_6885_ = lean_ctor_get(v_fst_6878_, 0);
v_isSharedCheck_6917_ = !lean_is_exclusive(v_fst_6878_);
if (v_isSharedCheck_6917_ == 0)
{
lean_object* v_unused_6918_; 
v_unused_6918_ = lean_ctor_get(v_fst_6878_, 1);
lean_dec(v_unused_6918_);
v___x_6887_ = v_fst_6878_;
v_isShared_6888_ = v_isSharedCheck_6917_;
goto v_resetjp_6886_;
}
else
{
lean_inc(v_definition_x3f_6885_);
lean_dec(v_fst_6878_);
v___x_6887_ = lean_box(0);
v_isShared_6888_ = v_isSharedCheck_6917_;
goto v_resetjp_6886_;
}
v_resetjp_6886_:
{
lean_object* v___x_6889_; 
v___x_6889_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6885_) == 1)
{
lean_object* v_val_6890_; lean_object* v___x_6892_; uint8_t v_isShared_6893_; uint8_t v_isSharedCheck_6912_; 
v_val_6890_ = lean_ctor_get(v_definition_x3f_6885_, 0);
v_isSharedCheck_6912_ = !lean_is_exclusive(v_definition_x3f_6885_);
if (v_isSharedCheck_6912_ == 0)
{
v___x_6892_ = v_definition_x3f_6885_;
v_isShared_6893_ = v_isSharedCheck_6912_;
goto v_resetjp_6891_;
}
else
{
lean_inc(v_val_6890_);
lean_dec(v_definition_x3f_6885_);
v___x_6892_ = lean_box(0);
v_isShared_6893_ = v_isSharedCheck_6912_;
goto v_resetjp_6891_;
}
v_resetjp_6891_:
{
lean_object* v___y_6895_; lean_object* v___x_6908_; 
v___x_6908_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6890_);
if (lean_obj_tag(v___x_6908_) == 0)
{
lean_object* v___x_6909_; 
lean_dec(v_snd_6881_);
v___x_6909_ = lean_box(0);
v___y_6895_ = v___x_6909_;
goto v___jp_6894_;
}
else
{
lean_object* v_val_6910_; lean_object* v___x_6911_; 
v_val_6910_ = lean_ctor_get(v___x_6908_, 0);
lean_inc(v_val_6910_);
lean_dec_ref_known(v___x_6908_, 1);
v___x_6911_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6881_, v_val_6910_);
lean_dec(v_snd_6881_);
v___y_6895_ = v___x_6911_;
goto v___jp_6894_;
}
v___jp_6894_:
{
lean_object* v___x_6896_; lean_object* v___x_6898_; 
v___x_6896_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6890_);
lean_dec(v_val_6890_);
lean_inc(v_fst_6879_);
if (v_isShared_6888_ == 0)
{
lean_ctor_set(v___x_6887_, 1, v___x_6896_);
lean_ctor_set(v___x_6887_, 0, v_fst_6879_);
v___x_6898_ = v___x_6887_;
goto v_reusejp_6897_;
}
else
{
lean_object* v_reuseFailAlloc_6907_; 
v_reuseFailAlloc_6907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6907_, 0, v_fst_6879_);
lean_ctor_set(v_reuseFailAlloc_6907_, 1, v___x_6896_);
v___x_6898_ = v_reuseFailAlloc_6907_;
goto v_reusejp_6897_;
}
v_reusejp_6897_:
{
lean_object* v___x_6899_; lean_object* v___x_6901_; 
lean_inc(v_fst_6880_);
v___x_6899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6899_, 0, v___x_6898_);
lean_ctor_set(v___x_6899_, 1, v_fst_6880_);
lean_ctor_set(v___x_6899_, 2, v___y_6895_);
if (v_isShared_6893_ == 0)
{
lean_ctor_set(v___x_6892_, 0, v___x_6899_);
v___x_6901_ = v___x_6892_;
goto v_reusejp_6900_;
}
else
{
lean_object* v_reuseFailAlloc_6906_; 
v_reuseFailAlloc_6906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6906_, 0, v___x_6899_);
v___x_6901_ = v_reuseFailAlloc_6906_;
goto v_reusejp_6900_;
}
v_reusejp_6900_:
{
lean_object* v___x_6902_; lean_object* v___x_6904_; 
v___x_6902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6902_, 0, v___x_6901_);
if (v_isShared_6884_ == 0)
{
lean_ctor_set(v___x_6883_, 1, v___x_6889_);
lean_ctor_set(v___x_6883_, 0, v___x_6902_);
v___x_6904_ = v___x_6883_;
goto v_reusejp_6903_;
}
else
{
lean_object* v_reuseFailAlloc_6905_; 
v_reuseFailAlloc_6905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6905_, 0, v___x_6902_);
lean_ctor_set(v_reuseFailAlloc_6905_, 1, v___x_6889_);
v___x_6904_ = v_reuseFailAlloc_6905_;
goto v_reusejp_6903_;
}
v_reusejp_6903_:
{
return v___x_6904_;
}
}
}
}
}
}
else
{
lean_object* v___x_6913_; size_t v___x_6914_; size_t v___x_6915_; 
lean_del_object(v___x_6887_);
lean_dec(v_definition_x3f_6885_);
lean_del_object(v___x_6883_);
lean_dec(v_snd_6881_);
v___x_6913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6914_ = ((size_t)1ULL);
v___x_6915_ = lean_usize_add(v_i_6872_, v___x_6914_);
v_i_6872_ = v___x_6915_;
v_b_6873_ = v___x_6913_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6921_, lean_object* v_sz_6922_, lean_object* v_i_6923_, lean_object* v_b_6924_){
_start:
{
size_t v_sz_boxed_6925_; size_t v_i_boxed_6926_; lean_object* v_res_6927_; 
v_sz_boxed_6925_ = lean_unbox_usize(v_sz_6922_);
lean_dec(v_sz_6922_);
v_i_boxed_6926_ = lean_unbox_usize(v_i_6923_);
lean_dec(v_i_6923_);
v_res_6927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6921_, v_sz_boxed_6925_, v_i_boxed_6926_, v_b_6924_);
lean_dec_ref(v_b_6924_);
lean_dec_ref(v_as_6921_);
return v_res_6927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6928_, lean_object* v_ident_6929_){
_start:
{
lean_object* v___x_6930_; lean_object* v___x_6931_; lean_object* v___x_6932_; size_t v_sz_6933_; size_t v___x_6934_; lean_object* v___x_6935_; lean_object* v_fst_6936_; 
v___x_6930_ = l_Lean_Server_References_allRefsFor(v_self_6928_, v_ident_6929_);
v___x_6931_ = lean_box(0);
v___x_6932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6933_ = lean_array_size(v___x_6930_);
v___x_6934_ = ((size_t)0ULL);
v___x_6935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6930_, v_sz_6933_, v___x_6934_, v___x_6932_);
lean_dec_ref(v___x_6930_);
v_fst_6936_ = lean_ctor_get(v___x_6935_, 0);
lean_inc(v_fst_6936_);
lean_dec_ref(v___x_6935_);
if (lean_obj_tag(v_fst_6936_) == 0)
{
return v___x_6931_;
}
else
{
lean_object* v_val_6937_; 
v_val_6937_ = lean_ctor_get(v_fst_6936_, 0);
lean_inc(v_val_6937_);
lean_dec_ref_known(v_fst_6936_, 1);
return v_val_6937_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6938_, lean_object* v_a_6939_, lean_object* v_fst_6940_, lean_object* v_init_6941_, lean_object* v_x_6942_){
_start:
{
lean_object* v_d_6945_; 
if (lean_obj_tag(v_x_6942_) == 0)
{
lean_object* v_k_6947_; lean_object* v_v_6948_; lean_object* v_l_6949_; lean_object* v_r_6950_; lean_object* v___y_6952_; lean_object* v___x_6956_; 
v_k_6947_ = lean_ctor_get(v_x_6942_, 1);
lean_inc(v_k_6947_);
v_v_6948_ = lean_ctor_get(v_x_6942_, 2);
lean_inc(v_v_6948_);
v_l_6949_ = lean_ctor_get(v_x_6942_, 3);
lean_inc(v_l_6949_);
v_r_6950_ = lean_ctor_get(v_x_6942_, 4);
lean_inc(v_r_6950_);
lean_dec_ref_known(v_x_6942_, 5);
lean_inc_ref(v_fst_6940_);
lean_inc(v_a_6939_);
lean_inc_ref(v_filterMapIdent_6938_);
v___x_6956_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6938_, v_a_6939_, v_fst_6940_, v_init_6941_, v_l_6949_);
if (lean_obj_tag(v___x_6956_) == 0)
{
lean_object* v_a_6957_; 
lean_dec(v_r_6950_);
lean_dec(v_v_6948_);
lean_dec(v_k_6947_);
lean_dec_ref(v_fst_6940_);
lean_dec(v_a_6939_);
lean_dec_ref(v_filterMapIdent_6938_);
v_a_6957_ = lean_ctor_get(v___x_6956_, 0);
lean_inc(v_a_6957_);
lean_dec_ref_known(v___x_6956_, 1);
v_d_6945_ = v_a_6957_;
goto v___jp_6944_;
}
else
{
if (lean_obj_tag(v_k_6947_) == 0)
{
lean_object* v_definition_x3f_6958_; 
v_definition_x3f_6958_ = lean_ctor_get(v_v_6948_, 0);
lean_inc(v_definition_x3f_6958_);
lean_dec(v_v_6948_);
if (lean_obj_tag(v_definition_x3f_6958_) == 1)
{
lean_object* v_a_6959_; lean_object* v_identName_6960_; lean_object* v_val_6961_; lean_object* v___x_6962_; lean_object* v___x_6963_; 
v_a_6959_ = lean_ctor_get(v___x_6956_, 0);
lean_inc(v_a_6959_);
v_identName_6960_ = lean_ctor_get(v_k_6947_, 1);
lean_inc_ref(v_identName_6960_);
lean_dec_ref_known(v_k_6947_, 2);
v_val_6961_ = lean_ctor_get(v_definition_x3f_6958_, 0);
lean_inc(v_val_6961_);
lean_dec_ref_known(v_definition_x3f_6958_, 1);
v___x_6962_ = l_String_toName(v_identName_6960_);
lean_inc_ref(v_filterMapIdent_6938_);
v___x_6963_ = lean_apply_1(v_filterMapIdent_6938_, v___x_6962_);
if (lean_obj_tag(v___x_6963_) == 1)
{
lean_object* v_val_6964_; lean_object* v___x_6965_; lean_object* v___x_6966_; lean_object* v___x_6967_; 
lean_dec_ref_known(v___x_6956_, 1);
v_val_6964_ = lean_ctor_get(v___x_6963_, 0);
lean_inc(v_val_6964_);
lean_dec_ref_known(v___x_6963_, 1);
v___x_6965_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6961_);
lean_dec(v_val_6961_);
lean_inc_ref(v_fst_6940_);
lean_inc(v_a_6939_);
v___x_6966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6966_, 0, v_a_6939_);
lean_ctor_set(v___x_6966_, 1, v_fst_6940_);
lean_ctor_set(v___x_6966_, 2, v_val_6964_);
lean_ctor_set(v___x_6966_, 3, v___x_6965_);
v___x_6967_ = lean_array_push(v_a_6959_, v___x_6966_);
v_init_6941_ = v___x_6967_;
v_x_6942_ = v_r_6950_;
goto _start;
}
else
{
lean_dec(v___x_6963_);
lean_dec(v_val_6961_);
lean_dec(v_a_6959_);
v___y_6952_ = v___x_6956_;
goto v___jp_6951_;
}
}
else
{
lean_dec_ref_known(v_k_6947_, 2);
lean_dec(v_definition_x3f_6958_);
v___y_6952_ = v___x_6956_;
goto v___jp_6951_;
}
}
else
{
lean_dec(v_v_6948_);
lean_dec(v_k_6947_);
v___y_6952_ = v___x_6956_;
goto v___jp_6951_;
}
}
v___jp_6951_:
{
if (lean_obj_tag(v___y_6952_) == 0)
{
lean_object* v_a_6953_; 
lean_dec(v_r_6950_);
lean_dec_ref(v_fst_6940_);
lean_dec(v_a_6939_);
lean_dec_ref(v_filterMapIdent_6938_);
v_a_6953_ = lean_ctor_get(v___y_6952_, 0);
lean_inc(v_a_6953_);
lean_dec_ref_known(v___y_6952_, 1);
v_d_6945_ = v_a_6953_;
goto v___jp_6944_;
}
else
{
lean_object* v_a_6954_; 
v_a_6954_ = lean_ctor_get(v___y_6952_, 0);
lean_inc(v_a_6954_);
lean_dec_ref_known(v___y_6952_, 1);
v_init_6941_ = v_a_6954_;
v_x_6942_ = v_r_6950_;
goto _start;
}
}
}
else
{
lean_object* v___x_6969_; 
lean_dec_ref(v_fst_6940_);
lean_dec(v_a_6939_);
lean_dec_ref(v_filterMapIdent_6938_);
v___x_6969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6969_, 0, v_init_6941_);
return v___x_6969_;
}
v___jp_6944_:
{
lean_object* v___x_6946_; 
v___x_6946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6946_, 0, v_d_6945_);
return v___x_6946_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6970_, lean_object* v_a_6971_, lean_object* v_fst_6972_, lean_object* v_init_6973_, lean_object* v_x_6974_, lean_object* v___y_6975_){
_start:
{
lean_object* v_res_6976_; 
v_res_6976_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6970_, v_a_6971_, v_fst_6972_, v_init_6973_, v_x_6974_);
return v_res_6976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6977_, lean_object* v_cancelTk_x3f_6978_, lean_object* v_init_6979_, lean_object* v_x_6980_){
_start:
{
lean_object* v_d_6983_; 
if (lean_obj_tag(v_x_6980_) == 0)
{
lean_object* v_k_6985_; lean_object* v_v_6986_; lean_object* v_l_6987_; lean_object* v_r_6988_; lean_object* v___x_6989_; 
v_k_6985_ = lean_ctor_get(v_x_6980_, 1);
lean_inc(v_k_6985_);
v_v_6986_ = lean_ctor_get(v_x_6980_, 2);
lean_inc(v_v_6986_);
v_l_6987_ = lean_ctor_get(v_x_6980_, 3);
lean_inc(v_l_6987_);
v_r_6988_ = lean_ctor_get(v_x_6980_, 4);
lean_inc(v_r_6988_);
lean_dec_ref_known(v_x_6980_, 5);
lean_inc(v_cancelTk_x3f_6978_);
lean_inc_ref(v_filterMapIdent_6977_);
v___x_6989_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6977_, v_cancelTk_x3f_6978_, v_init_6979_, v_l_6987_);
if (lean_obj_tag(v___x_6989_) == 0)
{
lean_object* v_a_6990_; 
lean_dec(v_r_6988_);
lean_dec(v_v_6986_);
lean_dec(v_k_6985_);
lean_dec(v_cancelTk_x3f_6978_);
lean_dec_ref(v_filterMapIdent_6977_);
v_a_6990_ = lean_ctor_get(v___x_6989_, 0);
lean_inc(v_a_6990_);
lean_dec_ref_known(v___x_6989_, 1);
v_d_6983_ = v_a_6990_;
goto v___jp_6982_;
}
else
{
lean_object* v_snd_6991_; lean_object* v_a_6992_; lean_object* v_fst_6993_; lean_object* v_fst_6994_; lean_object* v___x_6996_; uint8_t v_isShared_6997_; uint8_t v_isSharedCheck_7027_; 
v_snd_6991_ = lean_ctor_get(v_v_6986_, 1);
lean_inc(v_snd_6991_);
v_a_6992_ = lean_ctor_get(v___x_6989_, 0);
lean_inc(v_a_6992_);
lean_dec_ref_known(v___x_6989_, 1);
v_fst_6993_ = lean_ctor_get(v_v_6986_, 0);
lean_inc(v_fst_6993_);
lean_dec(v_v_6986_);
v_fst_6994_ = lean_ctor_get(v_snd_6991_, 0);
v_isSharedCheck_7027_ = !lean_is_exclusive(v_snd_6991_);
if (v_isSharedCheck_7027_ == 0)
{
lean_object* v_unused_7028_; 
v_unused_7028_ = lean_ctor_get(v_snd_6991_, 1);
lean_dec(v_unused_7028_);
v___x_6996_ = v_snd_6991_;
v_isShared_6997_ = v_isSharedCheck_7027_;
goto v_resetjp_6995_;
}
else
{
lean_inc(v_fst_6994_);
lean_dec(v_snd_6991_);
v___x_6996_ = lean_box(0);
v_isShared_6997_ = v_isSharedCheck_7027_;
goto v_resetjp_6995_;
}
v_resetjp_6995_:
{
lean_object* v_snd_6998_; lean_object* v___x_7000_; uint8_t v_isShared_7001_; uint8_t v_isSharedCheck_7025_; 
v_snd_6998_ = lean_ctor_get(v_a_6992_, 1);
v_isSharedCheck_7025_ = !lean_is_exclusive(v_a_6992_);
if (v_isSharedCheck_7025_ == 0)
{
lean_object* v_unused_7026_; 
v_unused_7026_ = lean_ctor_get(v_a_6992_, 0);
lean_dec(v_unused_7026_);
v___x_7000_ = v_a_6992_;
v_isShared_7001_ = v_isSharedCheck_7025_;
goto v_resetjp_6999_;
}
else
{
lean_inc(v_snd_6998_);
lean_dec(v_a_6992_);
v___x_7000_ = lean_box(0);
v_isShared_7001_ = v_isSharedCheck_7025_;
goto v_resetjp_6999_;
}
v_resetjp_6999_:
{
lean_object* v___x_7002_; lean_object* v_val_7004_; 
v___x_7002_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_6978_) == 1)
{
lean_object* v_val_7012_; uint8_t v___x_7013_; 
v_val_7012_ = lean_ctor_get(v_cancelTk_x3f_6978_, 0);
v___x_7013_ = l_IO_CancelToken_isSet(v_val_7012_);
if (v___x_7013_ == 0)
{
lean_del_object(v___x_6996_);
goto v___jp_7009_;
}
else
{
lean_object* v___x_7015_; uint8_t v_isShared_7016_; uint8_t v_isSharedCheck_7023_; 
lean_del_object(v___x_7000_);
lean_dec(v_fst_6994_);
lean_dec(v_fst_6993_);
lean_dec(v_r_6988_);
lean_dec(v_k_6985_);
lean_dec_ref(v_filterMapIdent_6977_);
v_isSharedCheck_7023_ = !lean_is_exclusive(v_cancelTk_x3f_6978_);
if (v_isSharedCheck_7023_ == 0)
{
lean_object* v_unused_7024_; 
v_unused_7024_ = lean_ctor_get(v_cancelTk_x3f_6978_, 0);
lean_dec(v_unused_7024_);
v___x_7015_ = v_cancelTk_x3f_6978_;
v_isShared_7016_ = v_isSharedCheck_7023_;
goto v_resetjp_7014_;
}
else
{
lean_dec(v_cancelTk_x3f_6978_);
v___x_7015_ = lean_box(0);
v_isShared_7016_ = v_isSharedCheck_7023_;
goto v_resetjp_7014_;
}
v_resetjp_7014_:
{
lean_object* v___x_7018_; 
lean_inc(v_snd_6998_);
if (v_isShared_7016_ == 0)
{
lean_ctor_set(v___x_7015_, 0, v_snd_6998_);
v___x_7018_ = v___x_7015_;
goto v_reusejp_7017_;
}
else
{
lean_object* v_reuseFailAlloc_7022_; 
v_reuseFailAlloc_7022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7022_, 0, v_snd_6998_);
v___x_7018_ = v_reuseFailAlloc_7022_;
goto v_reusejp_7017_;
}
v_reusejp_7017_:
{
lean_object* v___x_7020_; 
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 1, v_snd_6998_);
lean_ctor_set(v___x_6996_, 0, v___x_7018_);
v___x_7020_ = v___x_6996_;
goto v_reusejp_7019_;
}
else
{
lean_object* v_reuseFailAlloc_7021_; 
v_reuseFailAlloc_7021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7021_, 0, v___x_7018_);
lean_ctor_set(v_reuseFailAlloc_7021_, 1, v_snd_6998_);
v___x_7020_ = v_reuseFailAlloc_7021_;
goto v_reusejp_7019_;
}
v_reusejp_7019_:
{
v_d_6983_ = v___x_7020_;
goto v___jp_6982_;
}
}
}
}
}
else
{
lean_del_object(v___x_6996_);
goto v___jp_7009_;
}
v___jp_7003_:
{
lean_object* v___x_7006_; 
if (v_isShared_7001_ == 0)
{
lean_ctor_set(v___x_7000_, 1, v_val_7004_);
lean_ctor_set(v___x_7000_, 0, v___x_7002_);
v___x_7006_ = v___x_7000_;
goto v_reusejp_7005_;
}
else
{
lean_object* v_reuseFailAlloc_7008_; 
v_reuseFailAlloc_7008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7008_, 0, v___x_7002_);
lean_ctor_set(v_reuseFailAlloc_7008_, 1, v_val_7004_);
v___x_7006_ = v_reuseFailAlloc_7008_;
goto v_reusejp_7005_;
}
v_reusejp_7005_:
{
v_init_6979_ = v___x_7006_;
v_x_6980_ = v_r_6988_;
goto _start;
}
}
v___jp_7009_:
{
lean_object* v___x_7010_; lean_object* v_a_7011_; 
lean_inc_ref(v_filterMapIdent_6977_);
v___x_7010_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6977_, v_k_6985_, v_fst_6993_, v_snd_6998_, v_fst_6994_);
v_a_7011_ = lean_ctor_get(v___x_7010_, 0);
lean_inc(v_a_7011_);
lean_dec_ref(v___x_7010_);
v_val_7004_ = v_a_7011_;
goto v___jp_7003_;
}
}
}
}
}
else
{
lean_object* v___x_7029_; 
lean_dec(v_cancelTk_x3f_6978_);
lean_dec_ref(v_filterMapIdent_6977_);
v___x_7029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7029_, 0, v_init_6979_);
return v___x_7029_;
}
v___jp_6982_:
{
lean_object* v___x_6984_; 
v___x_6984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6984_, 0, v_d_6983_);
return v___x_6984_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_7030_, lean_object* v_cancelTk_x3f_7031_, lean_object* v_init_7032_, lean_object* v_x_7033_, lean_object* v___y_7034_){
_start:
{
lean_object* v_res_7035_; 
v_res_7035_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7030_, v_cancelTk_x3f_7031_, v_init_7032_, v_x_7033_);
return v_res_7035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_7041_, lean_object* v_filterMapIdent_7042_, lean_object* v_cancelTk_x3f_7043_){
_start:
{
lean_object* v___x_7045_; lean_object* v___x_7046_; lean_object* v___x_7047_; lean_object* v_val_7049_; lean_object* v_a_7053_; 
v___x_7045_ = l_Lean_Server_References_allRefs(v_self_7041_);
v___x_7046_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_7047_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7042_, v_cancelTk_x3f_7043_, v___x_7046_, v___x_7045_);
v_a_7053_ = lean_ctor_get(v___x_7047_, 0);
lean_inc(v_a_7053_);
lean_dec_ref(v___x_7047_);
v_val_7049_ = v_a_7053_;
goto v___jp_7048_;
v___jp_7048_:
{
lean_object* v_fst_7050_; 
v_fst_7050_ = lean_ctor_get(v_val_7049_, 0);
if (lean_obj_tag(v_fst_7050_) == 0)
{
lean_object* v_snd_7051_; 
v_snd_7051_ = lean_ctor_get(v_val_7049_, 1);
lean_inc(v_snd_7051_);
lean_dec_ref(v_val_7049_);
return v_snd_7051_;
}
else
{
lean_object* v_val_7052_; 
lean_inc_ref(v_fst_7050_);
lean_dec_ref(v_val_7049_);
v_val_7052_ = lean_ctor_get(v_fst_7050_, 0);
lean_inc(v_val_7052_);
lean_dec_ref_known(v_fst_7050_, 1);
return v_val_7052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_7054_, lean_object* v_filterMapIdent_7055_, lean_object* v_cancelTk_x3f_7056_, lean_object* v_a_7057_){
_start:
{
lean_object* v_res_7058_; 
v_res_7058_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7054_, v_filterMapIdent_7055_, v_cancelTk_x3f_7056_);
return v_res_7058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_7059_, lean_object* v_self_7060_, lean_object* v_filterMapIdent_7061_, lean_object* v_cancelTk_x3f_7062_){
_start:
{
lean_object* v___x_7064_; 
v___x_7064_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7060_, v_filterMapIdent_7061_, v_cancelTk_x3f_7062_);
return v___x_7064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_7065_, lean_object* v_self_7066_, lean_object* v_filterMapIdent_7067_, lean_object* v_cancelTk_x3f_7068_, lean_object* v_a_7069_){
_start:
{
lean_object* v_res_7070_; 
v_res_7070_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_7065_, v_self_7066_, v_filterMapIdent_7067_, v_cancelTk_x3f_7068_);
return v_res_7070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_7071_, lean_object* v_filterMapIdent_7072_, lean_object* v_a_7073_, lean_object* v_fst_7074_, lean_object* v_init_7075_, lean_object* v_x_7076_){
_start:
{
lean_object* v___x_7078_; 
v___x_7078_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_7072_, v_a_7073_, v_fst_7074_, v_init_7075_, v_x_7076_);
return v___x_7078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_7079_, lean_object* v_filterMapIdent_7080_, lean_object* v_a_7081_, lean_object* v_fst_7082_, lean_object* v_init_7083_, lean_object* v_x_7084_, lean_object* v___y_7085_){
_start:
{
lean_object* v_res_7086_; 
v_res_7086_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_7079_, v_filterMapIdent_7080_, v_a_7081_, v_fst_7082_, v_init_7083_, v_x_7084_);
return v_res_7086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_7087_, lean_object* v_filterMapIdent_7088_, lean_object* v_cancelTk_x3f_7089_, lean_object* v_init_7090_, lean_object* v_x_7091_){
_start:
{
lean_object* v___x_7093_; 
v___x_7093_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7088_, v_cancelTk_x3f_7089_, v_init_7090_, v_x_7091_);
return v___x_7093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7094_, lean_object* v_filterMapIdent_7095_, lean_object* v_cancelTk_x3f_7096_, lean_object* v_init_7097_, lean_object* v_x_7098_, lean_object* v___y_7099_){
_start:
{
lean_object* v_res_7100_; 
v_res_7100_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7094_, v_filterMapIdent_7095_, v_cancelTk_x3f_7096_, v_init_7097_, v_x_7098_);
return v_res_7100_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7101_){
_start:
{
lean_object* v___x_7102_; lean_object* v___x_7103_; 
v___x_7102_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7103_ = lean_panic_fn_borrowed(v___x_7102_, v_msg_7101_);
return v___x_7103_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7107_; lean_object* v___x_7108_; lean_object* v___x_7109_; lean_object* v___x_7110_; lean_object* v___x_7111_; lean_object* v___x_7112_; 
v___x_7107_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7108_ = lean_unsigned_to_nat(14u);
v___x_7109_ = lean_unsigned_to_nat(22u);
v___x_7110_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7111_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7112_ = l_mkPanicMessageWithDecl(v___x_7111_, v___x_7110_, v___x_7109_, v___x_7108_, v___x_7107_);
return v___x_7112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7113_, lean_object* v_init_7114_, lean_object* v_x_7115_){
_start:
{
if (lean_obj_tag(v_x_7115_) == 0)
{
lean_object* v_k_7116_; lean_object* v_v_7117_; lean_object* v_l_7118_; lean_object* v_r_7119_; lean_object* v___x_7120_; lean_object* v_a_7121_; lean_object* v_fst_7122_; lean_object* v_snd_7123_; lean_object* v___y_7125_; lean_object* v_index_7140_; lean_object* v___x_7141_; 
v_k_7116_ = lean_ctor_get(v_x_7115_, 1);
v_v_7117_ = lean_ctor_get(v_x_7115_, 2);
v_l_7118_ = lean_ctor_get(v_x_7115_, 3);
v_r_7119_ = lean_ctor_get(v_x_7115_, 4);
v___x_7120_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7113_, v_init_7114_, v_l_7118_);
v_a_7121_ = lean_ctor_get(v___x_7120_, 0);
lean_inc(v_a_7121_);
v_fst_7122_ = lean_ctor_get(v_v_7117_, 0);
v_snd_7123_ = lean_ctor_get(v_v_7117_, 1);
v_index_7140_ = lean_ctor_get(v_snd_7123_, 1);
v___x_7141_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7140_, v_requestedMod_7113_);
if (lean_obj_tag(v___x_7141_) == 1)
{
lean_object* v_val_7142_; lean_object* v___x_7143_; 
lean_dec_ref(v___x_7120_);
v_val_7142_ = lean_ctor_get(v___x_7141_, 0);
lean_inc(v_val_7142_);
lean_dec_ref_known(v___x_7141_, 1);
v___x_7143_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7142_);
lean_dec(v_val_7142_);
if (lean_obj_tag(v___x_7143_) == 0)
{
lean_object* v___x_7144_; lean_object* v___x_7145_; 
v___x_7144_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7145_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7144_);
v___y_7125_ = v___x_7145_;
goto v___jp_7124_;
}
else
{
lean_object* v_val_7146_; 
v_val_7146_ = lean_ctor_get(v___x_7143_, 0);
lean_inc(v_val_7146_);
lean_dec_ref_known(v___x_7143_, 1);
v___y_7125_ = v_val_7146_;
goto v___jp_7124_;
}
}
else
{
lean_object* v_a_7147_; 
lean_dec(v___x_7141_);
lean_dec(v_a_7121_);
v_a_7147_ = lean_ctor_get(v___x_7120_, 0);
lean_inc(v_a_7147_);
lean_dec_ref(v___x_7120_);
v_init_7114_ = v_a_7147_;
v_x_7115_ = v_r_7119_;
goto _start;
}
v___jp_7124_:
{
uint8_t v_isAll_7126_; uint8_t v_isPrivate_7127_; uint8_t v_metaKind_7128_; lean_object* v___x_7130_; uint8_t v_isShared_7131_; uint8_t v_isSharedCheck_7137_; 
v_isAll_7126_ = lean_ctor_get_uint8(v___y_7125_, sizeof(void*)*2);
v_isPrivate_7127_ = lean_ctor_get_uint8(v___y_7125_, sizeof(void*)*2 + 1);
v_metaKind_7128_ = lean_ctor_get_uint8(v___y_7125_, sizeof(void*)*2 + 2);
v_isSharedCheck_7137_ = !lean_is_exclusive(v___y_7125_);
if (v_isSharedCheck_7137_ == 0)
{
lean_object* v_unused_7138_; lean_object* v_unused_7139_; 
v_unused_7138_ = lean_ctor_get(v___y_7125_, 1);
lean_dec(v_unused_7138_);
v_unused_7139_ = lean_ctor_get(v___y_7125_, 0);
lean_dec(v_unused_7139_);
v___x_7130_ = v___y_7125_;
v_isShared_7131_ = v_isSharedCheck_7137_;
goto v_resetjp_7129_;
}
else
{
lean_dec(v___y_7125_);
v___x_7130_ = lean_box(0);
v_isShared_7131_ = v_isSharedCheck_7137_;
goto v_resetjp_7129_;
}
v_resetjp_7129_:
{
lean_object* v___x_7133_; 
lean_inc(v_fst_7122_);
lean_inc(v_k_7116_);
if (v_isShared_7131_ == 0)
{
lean_ctor_set(v___x_7130_, 1, v_fst_7122_);
lean_ctor_set(v___x_7130_, 0, v_k_7116_);
v___x_7133_ = v___x_7130_;
goto v_reusejp_7132_;
}
else
{
lean_object* v_reuseFailAlloc_7136_; 
v_reuseFailAlloc_7136_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7136_, 0, v_k_7116_);
lean_ctor_set(v_reuseFailAlloc_7136_, 1, v_fst_7122_);
lean_ctor_set_uint8(v_reuseFailAlloc_7136_, sizeof(void*)*2, v_isAll_7126_);
lean_ctor_set_uint8(v_reuseFailAlloc_7136_, sizeof(void*)*2 + 1, v_isPrivate_7127_);
lean_ctor_set_uint8(v_reuseFailAlloc_7136_, sizeof(void*)*2 + 2, v_metaKind_7128_);
v___x_7133_ = v_reuseFailAlloc_7136_;
goto v_reusejp_7132_;
}
v_reusejp_7132_:
{
lean_object* v___x_7134_; 
v___x_7134_ = lean_array_push(v_a_7121_, v___x_7133_);
v_init_7114_ = v___x_7134_;
v_x_7115_ = v_r_7119_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7149_; 
v___x_7149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7149_, 0, v_init_7114_);
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

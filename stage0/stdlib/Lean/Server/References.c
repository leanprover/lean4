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
v___x_607_ = lean_nat_add(v___y_604_, v___y_606_);
lean_dec(v___y_606_);
lean_dec(v___y_604_);
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
lean_ctor_set(v___x_587_, 3, v___y_605_);
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
lean_ctor_set(v_reuseFailAlloc_612_, 3, v___y_605_);
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
v___y_604_ = v___x_620_;
v___y_605_ = v___x_619_;
v___y_606_ = v_size_621_;
goto v___jp_603_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___y_604_ = v___x_620_;
v___y_605_ = v___x_619_;
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
lean_object* v_v_1338_; lean_object* v___x_1339_; lean_object* v_bs_x27_1340_; lean_object* v_a_1342_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1413_; 
v_v_1338_ = lean_array_uget(v_bs_1335_, v_i_1334_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v_bs_x27_1340_ = lean_array_uset(v_bs_1335_, v_i_1334_, v___x_1339_);
v___x_1347_ = lean_array_get_size(v_v_1338_);
v___x_1348_ = lean_unsigned_to_nat(4u);
v___x_1413_ = lean_nat_dec_eq(v___x_1347_, v___x_1348_);
if (v___x_1413_ == 0)
{
if (v___x_1336_ == 0)
{
goto v___jp_1349_;
}
else
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = lean_unsigned_to_nat(5u);
v___x_1415_ = lean_nat_dec_eq(v___x_1347_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v___x_1416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1417_ = l_Nat_reprFast(v___x_1347_);
v___x_1418_ = lean_string_append(v___x_1416_, v___x_1417_);
lean_dec_ref(v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
else
{
goto v___jp_1349_;
}
}
}
else
{
goto v___jp_1349_;
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
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_array_fget_borrowed(v_v_1338_, v___x_1339_);
lean_inc(v___x_1350_);
v___x_1351_ = l_Lean_Json_getNat_x3f(v___x_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_a_1360_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1361_ = lean_unsigned_to_nat(1u);
v___x_1362_ = lean_array_fget_borrowed(v_v_1338_, v___x_1361_);
lean_inc(v___x_1362_);
v___x_1363_ = l_Lean_Json_getNat_x3f(v___x_1362_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_a_1360_);
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_a_1372_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1373_ = lean_unsigned_to_nat(2u);
v___x_1374_ = lean_array_fget_borrowed(v_v_1338_, v___x_1373_);
lean_inc(v___x_1374_);
v___x_1375_ = l_Lean_Json_getNat_x3f(v___x_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_a_1372_);
lean_dec(v_a_1360_);
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1384_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1385_ = lean_unsigned_to_nat(3u);
v___x_1386_ = lean_array_fget_borrowed(v_v_1338_, v___x_1385_);
lean_inc(v___x_1386_);
v___x_1387_ = l_Lean_Json_getNat_x3f(v___x_1386_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_a_1384_);
lean_dec(v_a_1372_);
lean_dec(v_a_1360_);
lean_dec_ref(v_bs_x27_1340_);
lean_dec(v_v_1338_);
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_a_1396_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1397_ = lean_unsigned_to_nat(5u);
v___x_1398_ = lean_nat_dec_eq(v___x_1347_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec(v_v_1338_);
v___x_1399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
v___x_1400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1400_, 0, v_a_1360_);
lean_ctor_set(v___x_1400_, 1, v_a_1372_);
lean_ctor_set(v___x_1400_, 2, v_a_1384_);
lean_ctor_set(v___x_1400_, 3, v_a_1396_);
lean_ctor_set(v___x_1400_, 4, v___x_1399_);
v_a_1342_ = v___x_1400_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_array_fget(v_v_1338_, v___x_1348_);
lean_dec(v_v_1338_);
v___x_1402_ = l_Lean_Json_getStr_x3f(v___x_1401_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_a_1396_);
lean_dec(v_a_1384_);
lean_dec(v_a_1372_);
lean_dec(v_a_1360_);
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
lean_ctor_set(v___x_1412_, 0, v_a_1360_);
lean_ctor_set(v___x_1412_, 1, v_a_1372_);
lean_ctor_set(v___x_1412_, 2, v_a_1384_);
lean_ctor_set(v___x_1412_, 3, v_a_1396_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___boxed(lean_object* v_sz_1420_, lean_object* v_i_1421_, lean_object* v_bs_1422_){
_start:
{
size_t v_sz_boxed_1423_; size_t v_i_boxed_1424_; lean_object* v_res_1425_; 
v_sz_boxed_1423_ = lean_unbox_usize(v_sz_1420_);
lean_dec(v_sz_1420_);
v_i_boxed_1424_ = lean_unbox_usize(v_i_1421_);
lean_dec(v_i_1421_);
v_res_1425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_boxed_1423_, v_i_boxed_1424_, v_bs_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(lean_object* v_x_1428_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
lean_object* v___x_1429_; 
v___x_1429_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0));
return v___x_1429_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(v_x_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1447_; 
v_a_1439_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1441_ = v___x_1430_;
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1430_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_a_1439_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(lean_object* v_j_1448_, lean_object* v_k_1449_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = l_Lean_Json_getObjValD(v_j_1448_, v_k_1449_);
v___x_1451_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6___boxed(lean_object* v_j_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_j_1452_, v_k_1453_);
lean_dec_ref(v_k_1453_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(lean_object* v_init_1457_, lean_object* v_x_1458_){
_start:
{
if (lean_obj_tag(v_x_1458_) == 0)
{
lean_object* v_k_1459_; lean_object* v_v_1460_; lean_object* v_l_1461_; lean_object* v_r_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1622_; 
v_k_1459_ = lean_ctor_get(v_x_1458_, 1);
v_v_1460_ = lean_ctor_get(v_x_1458_, 2);
v_l_1461_ = lean_ctor_get(v_x_1458_, 3);
v_r_1462_ = lean_ctor_get(v_x_1458_, 4);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1458_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v_x_1458_, 0);
lean_dec(v_unused_1623_);
v___x_1464_ = v_x_1458_;
v_isShared_1465_ = v_isSharedCheck_1622_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_r_1462_);
lean_inc(v_l_1461_);
lean_inc(v_v_1460_);
lean_inc(v_k_1459_);
lean_dec(v_x_1458_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1622_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v_init_1457_, v_l_1461_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
lean_dec(v_k_1459_);
return v___x_1466_;
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1621_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1621_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1621_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Json_parse(v_k_1459_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_del_object(v___x_1469_);
lean_dec(v_a_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1481_; 
v_a_1480_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1481_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1480_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_del_object(v___x_1469_);
lean_dec(v_a_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v_definition_x3f_1492_; lean_object* v_a_1520_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_a_1490_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1524_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
lean_inc(v_v_1460_);
v___x_1525_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_v_1460_, v___x_1524_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_a_1490_);
lean_del_object(v___x_1469_);
lean_dec(v_a_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1620_; 
v_a_1534_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1536_ = v___x_1525_;
v_isShared_1537_ = v_isSharedCheck_1620_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1525_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1620_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
if (lean_obj_tag(v_a_1534_) == 0)
{
lean_object* v___x_1538_; 
lean_del_object(v___x_1536_);
lean_del_object(v___x_1469_);
lean_del_object(v___x_1464_);
v___x_1538_ = lean_box(0);
v_definition_x3f_1492_ = v___x_1538_;
goto v___jp_1491_;
}
else
{
lean_object* v_val_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1611_; 
v_val_1539_ = lean_ctor_get(v_a_1534_, 0);
lean_inc(v_val_1539_);
lean_dec_ref_known(v_a_1534_, 1);
v___x_1540_ = lean_array_get_size(v_val_1539_);
v___x_1541_ = lean_unsigned_to_nat(4u);
v___x_1611_ = lean_nat_dec_eq(v___x_1540_, v___x_1541_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = lean_unsigned_to_nat(5u);
v___x_1613_ = lean_nat_dec_eq(v___x_1540_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
lean_dec(v_val_1539_);
lean_dec(v_a_1490_);
lean_del_object(v___x_1469_);
lean_dec(v_a_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
v___x_1614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1615_ = l_Nat_reprFast(v___x_1540_);
v___x_1616_ = lean_string_append(v___x_1614_, v___x_1615_);
lean_dec_ref(v___x_1615_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1616_);
v___x_1618_ = v___x_1536_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
else
{
lean_del_object(v___x_1536_);
goto v___jp_1542_;
}
}
else
{
lean_del_object(v___x_1536_);
goto v___jp_1542_;
}
v___jp_1542_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = lean_array_fget_borrowed(v_val_1539_, v___x_1543_);
lean_inc(v___x_1544_);
v___x_1545_ = l_Lean_Json_getNat_x3f(v___x_1544_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_val_1539_);
lean_dec(v_a_1490_);
lean_del_object(v___x_1469_);
lean_dec(v_a_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_a_1554_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_array_fget_borrowed(v_val_1539_, v___x_1555_);
lean_inc(v___x_1556_);
v___x_1557_ = l_Lean_Json_getNat_x3f(v___x_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_a_1554_);
lean_dec(v_val_1539_);
lean_dec(v_a_1490_);
lean_del_object(v___x_1469_);
lean_dec(v_a_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_a_1566_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1567_ = lean_unsigned_to_nat(2u);
v___x_1568_ = lean_array_fget_borrowed(v_val_1539_, v___x_1567_);
lean_inc(v___x_1568_);
v___x_1569_ = l_Lean_Json_getNat_x3f(v___x_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_a_1566_);
lean_dec(v_a_1554_);
lean_dec(v_val_1539_);
lean_dec(v_a_1490_);
lean_del_object(v___x_1469_);
lean_dec(v_a_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_a_1578_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1579_ = lean_unsigned_to_nat(3u);
v___x_1580_ = lean_array_fget_borrowed(v_val_1539_, v___x_1579_);
lean_inc(v___x_1580_);
v___x_1581_ = l_Lean_Json_getNat_x3f(v___x_1580_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1578_);
lean_dec(v_a_1566_);
lean_dec(v_a_1554_);
lean_dec(v_val_1539_);
lean_dec(v_a_1490_);
lean_del_object(v___x_1469_);
lean_dec(v_a_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v_a_1590_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1591_ = lean_unsigned_to_nat(5u);
v___x_1592_ = lean_nat_dec_eq(v___x_1540_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_dec(v_val_1539_);
v___x_1593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v___x_1593_);
lean_ctor_set(v___x_1464_, 3, v_a_1590_);
lean_ctor_set(v___x_1464_, 2, v_a_1578_);
lean_ctor_set(v___x_1464_, 1, v_a_1566_);
lean_ctor_set(v___x_1464_, 0, v_a_1554_);
v___x_1595_ = v___x_1464_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1554_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_a_1566_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_a_1578_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_a_1590_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
v_a_1520_ = v___x_1595_;
goto v___jp_1519_;
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_array_fget(v_val_1539_, v___x_1541_);
lean_dec(v_val_1539_);
v___x_1598_ = l_Lean_Json_getStr_x3f(v___x_1597_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1578_);
lean_dec(v_a_1566_);
lean_dec(v_a_1554_);
lean_dec(v_a_1490_);
lean_del_object(v___x_1469_);
lean_dec(v_a_1467_);
lean_del_object(v___x_1464_);
lean_dec(v_r_1462_);
lean_dec(v_v_1460_);
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; 
v_a_1607_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1598_, 1);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v_a_1607_);
lean_ctor_set(v___x_1464_, 3, v_a_1590_);
lean_ctor_set(v___x_1464_, 2, v_a_1578_);
lean_ctor_set(v___x_1464_, 1, v_a_1566_);
lean_ctor_set(v___x_1464_, 0, v_a_1554_);
v___x_1609_ = v___x_1464_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1554_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_a_1566_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_a_1578_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_a_1590_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_a_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
v_a_1520_ = v___x_1609_;
goto v___jp_1519_;
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
v___jp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v___x_1494_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(v_v_1460_, v___x_1493_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_definition_x3f_1492_);
lean_dec(v_a_1490_);
lean_dec(v_a_1467_);
lean_dec(v_r_1462_);
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_object* v_a_1503_; size_t v_sz_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v_a_1503_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1494_, 1);
v_sz_1504_ = lean_array_size(v_a_1503_);
v___x_1505_ = ((size_t)0ULL);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_1504_, v___x_1505_, v_a_1503_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_definition_x3f_1492_);
lean_dec(v_a_1490_);
lean_dec(v_a_1467_);
lean_dec(v_r_1462_);
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v_a_1515_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v_definition_x3f_1492_);
lean_ctor_set(v___x_1516_, 1, v_a_1515_);
v___x_1517_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_a_1490_, v___x_1516_, v_a_1467_);
v_init_1457_ = v___x_1517_;
v_x_1458_ = v_r_1462_;
goto _start;
}
}
}
v___jp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v_a_1520_);
v___x_1522_ = v___x_1469_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
v_definition_x3f_1492_ = v___x_1522_;
goto v___jp_1491_;
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
lean_object* v___x_1624_; 
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v_init_1457_);
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(lean_object* v_j_1625_, lean_object* v_k_1626_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = l_Lean_Json_getObjValD(v_j_1625_, v_k_1626_);
v___x_1628_ = l_Lean_Json_getObj_x3f(v___x_1627_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1638_ = lean_box(1);
v___x_1639_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v___x_1638_, v_a_1637_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3___boxed(lean_object* v_j_1640_, lean_object* v_k_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_j_1640_, v_k_1641_);
lean_dec_ref(v_k_1641_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1646_, size_t v_i_1647_, lean_object* v_bs_1648_){
_start:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_usize_dec_lt(v_i_1647_, v_sz_1646_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v_bs_1648_);
return v___x_1652_;
}
else
{
lean_object* v_v_1653_; 
v_v_1653_ = lean_array_uget_borrowed(v_bs_1648_, v_i_1647_);
if (lean_obj_tag(v_v_1653_) == 4)
{
lean_object* v_elems_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v_elems_1654_ = lean_ctor_get(v_v_1653_, 0);
v___x_1655_ = lean_array_get_size(v_elems_1654_);
v___x_1656_ = lean_unsigned_to_nat(4u);
v___x_1657_ = lean_nat_dec_eq(v___x_1655_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_dec_ref(v_bs_1648_);
goto v___jp_1649_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_array_fget_borrowed(v_elems_1654_, v___x_1658_);
lean_inc(v___x_1659_);
v___x_1660_ = l_Lean_Json_getStr_x3f(v___x_1659_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v_bs_1648_);
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_a_1669_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_array_fget_borrowed(v_elems_1654_, v___x_1670_);
v___x_1672_ = l_Lean_Json_getBool_x3f(v___x_1671_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_a_1669_);
lean_dec_ref(v_bs_1648_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_a_1681_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1682_ = lean_unsigned_to_nat(2u);
v___x_1683_ = lean_array_fget_borrowed(v_elems_1654_, v___x_1682_);
v___x_1684_ = l_Lean_Json_getBool_x3f(v___x_1683_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_a_1681_);
lean_dec(v_a_1669_);
lean_dec_ref(v_bs_1648_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_a_1693_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1684_, 1);
v___x_1694_ = lean_unsigned_to_nat(3u);
v___x_1695_ = lean_array_fget_borrowed(v_elems_1654_, v___x_1694_);
v___x_1696_ = l_Lean_Json_getBool_x3f(v___x_1695_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_a_1693_);
lean_dec(v_a_1681_);
lean_dec(v_a_1669_);
lean_dec_ref(v_bs_1648_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v_bs_x27_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; uint8_t v___x_1709_; uint8_t v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v_a_1705_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1696_, 1);
v_bs_x27_1706_ = lean_array_uset(v_bs_1648_, v_i_1647_, v___x_1658_);
v___x_1707_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1707_, 0, v_a_1669_);
v___x_1708_ = lean_unbox(v_a_1681_);
lean_dec(v_a_1681_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*1, v___x_1708_);
v___x_1709_ = lean_unbox(v_a_1693_);
lean_dec(v_a_1693_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*1 + 1, v___x_1709_);
v___x_1710_ = lean_unbox(v_a_1705_);
lean_dec(v_a_1705_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*1 + 2, v___x_1710_);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1647_, v___x_1711_);
v___x_1713_ = lean_array_uset(v_bs_x27_1706_, v_i_1647_, v___x_1707_);
v_i_1647_ = v___x_1712_;
v_bs_1648_ = v___x_1713_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1648_);
goto v___jp_1649_;
}
}
v___jp_1649_:
{
lean_object* v___x_1650_; 
v___x_1650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1));
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1715_, lean_object* v_i_1716_, lean_object* v_bs_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1715_);
lean_dec(v_sz_1715_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1721_) == 4)
{
lean_object* v_elems_1722_; size_t v_sz_1723_; size_t v___x_1724_; lean_object* v___x_1725_; 
v_elems_1722_ = lean_ctor_get(v_x_1721_, 0);
lean_inc_ref(v_elems_1722_);
lean_dec_ref_known(v_x_1721_, 1);
v_sz_1723_ = lean_array_size(v_elems_1722_);
v___x_1724_ = ((size_t)0ULL);
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_1723_, v___x_1724_, v_elems_1722_);
return v___x_1725_;
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1726_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1727_ = lean_unsigned_to_nat(80u);
v___x_1728_ = l_Lean_Json_pretty(v_x_1721_, v___x_1727_);
v___x_1729_ = lean_string_append(v___x_1726_, v___x_1728_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1731_ = lean_string_append(v___x_1729_, v___x_1730_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(lean_object* v_j_1733_, lean_object* v_k_1734_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = l_Lean_Json_getObjValD(v_j_1733_, v_k_1734_);
v___x_1736_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(v___x_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2___boxed(lean_object* v_j_1737_, lean_object* v_k_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_j_1737_, v_k_1738_);
lean_dec_ref(v_k_1738_);
return v_res_1739_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = 1;
v___x_1749_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__4));
v___x_1750_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1749_, v___x_1748_);
return v___x_1750_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__6));
v___x_1753_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__5, &l_Lean_Server_instFromJsonIlean_fromJson___closed__5_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5);
v___x_1754_ = lean_string_append(v___x_1753_, v___x_1752_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = 1;
v___x_1758_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__8));
v___x_1759_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1758_, v___x_1757_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__9, &l_Lean_Server_instFromJsonIlean_fromJson___closed__9_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9);
v___x_1761_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1762_ = lean_string_append(v___x_1761_, v___x_1760_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1765_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__10, &l_Lean_Server_instFromJsonIlean_fromJson___closed__10_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10);
v___x_1766_ = lean_string_append(v___x_1765_, v___x_1764_);
return v___x_1766_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = 1;
v___x_1771_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__14));
v___x_1772_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1771_, v___x_1770_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__15, &l_Lean_Server_instFromJsonIlean_fromJson___closed__15_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15);
v___x_1774_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1775_ = lean_string_append(v___x_1774_, v___x_1773_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1777_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__16, &l_Lean_Server_instFromJsonIlean_fromJson___closed__16_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16);
v___x_1778_ = lean_string_append(v___x_1777_, v___x_1776_);
return v___x_1778_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = 1;
v___x_1783_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__19));
v___x_1784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1783_, v___x_1782_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__20, &l_Lean_Server_instFromJsonIlean_fromJson___closed__20_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20);
v___x_1786_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1787_ = lean_string_append(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1789_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__21, &l_Lean_Server_instFromJsonIlean_fromJson___closed__21_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21);
v___x_1790_ = lean_string_append(v___x_1789_, v___x_1788_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = 1;
v___x_1795_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__24));
v___x_1796_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1795_, v___x_1794_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__25, &l_Lean_Server_instFromJsonIlean_fromJson___closed__25_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25);
v___x_1798_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1799_ = lean_string_append(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1801_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__26, &l_Lean_Server_instFromJsonIlean_fromJson___closed__26_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26);
v___x_1802_ = lean_string_append(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30(void){
_start:
{
uint8_t v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = 1;
v___x_1807_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__29));
v___x_1808_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1807_, v___x_1806_);
return v___x_1808_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__30, &l_Lean_Server_instFromJsonIlean_fromJson___closed__30_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30);
v___x_1810_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1811_ = lean_string_append(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1813_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__31, &l_Lean_Server_instFromJsonIlean_fromJson___closed__31_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31);
v___x_1814_ = lean_string_append(v___x_1813_, v___x_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonIlean_fromJson(lean_object* v_json_1815_){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
lean_inc(v_json_1815_);
v___x_1817_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(v_json_1815_, v___x_1816_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_json_1815_);
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1827_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1827_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1822_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__12, &l_Lean_Server_instFromJsonIlean_fromJson___closed__12_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12);
v___x_1823_ = lean_string_append(v___x_1822_, v_a_1818_);
lean_dec(v_a_1818_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1823_);
v___x_1825_ = v___x_1820_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_json_1815_);
v_a_1828_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1817_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1817_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 0);
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_a_1836_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1817_, 1);
v___x_1837_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
lean_inc(v_json_1815_);
v___x_1838_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(v_json_1815_, v___x_1837_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1836_);
lean_dec(v_json_1815_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1848_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1848_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1843_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__17, &l_Lean_Server_instFromJsonIlean_fromJson___closed__17_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17);
v___x_1844_ = lean_string_append(v___x_1843_, v_a_1839_);
lean_dec(v_a_1839_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1844_);
v___x_1846_ = v___x_1841_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_a_1836_);
lean_dec(v_json_1815_);
v_a_1849_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1838_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1838_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 0);
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_a_1857_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1838_, 1);
v___x_1858_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
lean_inc(v_json_1815_);
v___x_1859_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_json_1815_, v___x_1858_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_a_1857_);
lean_dec(v_a_1836_);
lean_dec(v_json_1815_);
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1869_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1869_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1864_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__22, &l_Lean_Server_instFromJsonIlean_fromJson___closed__22_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22);
v___x_1865_ = lean_string_append(v___x_1864_, v_a_1860_);
lean_dec(v_a_1860_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1865_);
v___x_1867_ = v___x_1862_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_a_1857_);
lean_dec(v_a_1836_);
lean_dec(v_json_1815_);
v_a_1870_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1859_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1859_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 0);
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_a_1878_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1859_, 1);
v___x_1879_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
lean_inc(v_json_1815_);
v___x_1880_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_json_1815_, v___x_1879_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_a_1878_);
lean_dec(v_a_1857_);
lean_dec(v_a_1836_);
lean_dec(v_json_1815_);
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1885_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__27, &l_Lean_Server_instFromJsonIlean_fromJson___closed__27_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27);
v___x_1886_ = lean_string_append(v___x_1885_, v_a_1881_);
lean_dec(v_a_1881_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
else
{
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_a_1878_);
lean_dec(v_a_1857_);
lean_dec(v_a_1836_);
lean_dec(v_json_1815_);
v_a_1891_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1880_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1880_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set_tag(v___x_1893_, 0);
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_a_1899_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1880_, 1);
v___x_1900_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_1901_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(v_json_1815_, v___x_1900_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1899_);
lean_dec(v_a_1878_);
lean_dec(v_a_1857_);
lean_dec(v_a_1836_);
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1906_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__32, &l_Lean_Server_instFromJsonIlean_fromJson___closed__32_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32);
v___x_1907_ = lean_string_append(v___x_1906_, v_a_1902_);
lean_dec(v_a_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1907_);
v___x_1909_ = v___x_1904_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_a_1899_);
lean_dec(v_a_1878_);
lean_dec(v_a_1857_);
lean_dec(v_a_1836_);
v_a_1912_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1901_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1901_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set_tag(v___x_1914_, 0);
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
v_a_1920_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v___x_1901_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1901_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1924_, 0, v_a_1836_);
lean_ctor_set(v___x_1924_, 1, v_a_1857_);
lean_ctor_set(v___x_1924_, 2, v_a_1878_);
lean_ctor_set(v___x_1924_, 3, v_a_1899_);
lean_ctor_set(v___x_1924_, 4, v_a_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(size_t v_sz_1931_, size_t v_i_1932_, lean_object* v_bs_1933_){
_start:
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_usize_dec_lt(v_i_1932_, v_sz_1931_);
if (v___x_1934_ == 0)
{
return v_bs_1933_;
}
else
{
lean_object* v_v_1935_; lean_object* v_module_1936_; uint8_t v_isPrivate_1937_; uint8_t v_isAll_1938_; uint8_t v_isMeta_1939_; lean_object* v___x_1940_; lean_object* v_bs_x27_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; size_t v___x_1953_; size_t v___x_1954_; lean_object* v___x_1955_; 
v_v_1935_ = lean_array_uget_borrowed(v_bs_1933_, v_i_1932_);
v_module_1936_ = lean_ctor_get(v_v_1935_, 0);
lean_inc_ref(v_module_1936_);
v_isPrivate_1937_ = lean_ctor_get_uint8(v_v_1935_, sizeof(void*)*1);
v_isAll_1938_ = lean_ctor_get_uint8(v_v_1935_, sizeof(void*)*1 + 1);
v_isMeta_1939_ = lean_ctor_get_uint8(v_v_1935_, sizeof(void*)*1 + 2);
v___x_1940_ = lean_unsigned_to_nat(0u);
v_bs_x27_1941_ = lean_array_uset(v_bs_1933_, v_i_1932_, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_module_1936_);
v___x_1943_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1943_, 0, v_isPrivate_1937_);
v___x_1944_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1944_, 0, v_isAll_1938_);
v___x_1945_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1945_, 0, v_isMeta_1939_);
v___x_1946_ = lean_unsigned_to_nat(4u);
v___x_1947_ = lean_mk_empty_array_with_capacity(v___x_1946_);
v___x_1948_ = lean_array_push(v___x_1947_, v___x_1942_);
v___x_1949_ = lean_array_push(v___x_1948_, v___x_1943_);
v___x_1950_ = lean_array_push(v___x_1949_, v___x_1944_);
v___x_1951_ = lean_array_push(v___x_1950_, v___x_1945_);
v___x_1952_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___x_1953_ = ((size_t)1ULL);
v___x_1954_ = lean_usize_add(v_i_1932_, v___x_1953_);
v___x_1955_ = lean_array_uset(v_bs_x27_1941_, v_i_1932_, v___x_1952_);
v_i_1932_ = v___x_1954_;
v_bs_1933_ = v___x_1955_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6___boxed(lean_object* v_sz_1957_, lean_object* v_i_1958_, lean_object* v_bs_1959_){
_start:
{
size_t v_sz_boxed_1960_; size_t v_i_boxed_1961_; lean_object* v_res_1962_; 
v_sz_boxed_1960_ = lean_unbox_usize(v_sz_1957_);
lean_dec(v_sz_1957_);
v_i_boxed_1961_ = lean_unbox_usize(v_i_1958_);
lean_dec(v_i_1958_);
v_res_1962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_boxed_1960_, v_i_boxed_1961_, v_bs_1959_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(lean_object* v_a_1963_){
_start:
{
size_t v_sz_1964_; size_t v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_sz_1964_ = lean_array_size(v_a_1963_);
v___x_1965_ = ((size_t)0ULL);
v___x_1966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_1964_, v___x_1965_, v_a_1963_);
v___x_1967_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
if (lean_obj_tag(v_a_1968_) == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = l_List_reverse___redArg(v_a_1969_);
return v___x_1970_;
}
else
{
lean_object* v_head_1971_; lean_object* v_tail_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1982_; 
v_head_1971_ = lean_ctor_get(v_a_1968_, 0);
v_tail_1972_ = lean_ctor_get(v_a_1968_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1974_ = v_a_1968_;
v_isShared_1975_ = v_isSharedCheck_1982_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_tail_1972_);
lean_inc(v_head_1971_);
lean_dec(v_a_1968_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1982_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1976_ = l_Lean_JsonNumber_fromNat(v_head_1971_);
v___x_1977_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v_a_1969_);
lean_ctor_set(v___x_1974_, 0, v___x_1977_);
v___x_1979_ = v___x_1974_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_a_1969_);
v___x_1979_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
v_a_1968_ = v_tail_1972_;
v_a_1969_ = v___x_1979_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(size_t v_sz_1983_, size_t v_i_1984_, lean_object* v_bs_1985_){
_start:
{
uint8_t v___x_1986_; 
v___x_1986_ = lean_usize_dec_lt(v_i_1984_, v_sz_1983_);
if (v___x_1986_ == 0)
{
return v_bs_1985_;
}
else
{
lean_object* v_v_1987_; lean_object* v___x_1988_; lean_object* v_bs_x27_1989_; size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v_v_1987_ = lean_array_uget(v_bs_1985_, v_i_1984_);
v___x_1988_ = lean_unsigned_to_nat(0u);
v_bs_x27_1989_ = lean_array_uset(v_bs_1985_, v_i_1984_, v___x_1988_);
v___x_1990_ = ((size_t)1ULL);
v___x_1991_ = lean_usize_add(v_i_1984_, v___x_1990_);
v___x_1992_ = lean_array_uset(v_bs_x27_1989_, v_i_1984_, v_v_1987_);
v_i_1984_ = v___x_1991_;
v_bs_1985_ = v___x_1992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11___boxed(lean_object* v_sz_1994_, lean_object* v_i_1995_, lean_object* v_bs_1996_){
_start:
{
size_t v_sz_boxed_1997_; size_t v_i_boxed_1998_; lean_object* v_res_1999_; 
v_sz_boxed_1997_ = lean_unbox_usize(v_sz_1994_);
lean_dec(v_sz_1994_);
v_i_boxed_1998_ = lean_unbox_usize(v_i_1995_);
lean_dec(v_i_1995_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_boxed_1997_, v_i_boxed_1998_, v_bs_1996_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(lean_object* v_a_2000_){
_start:
{
size_t v_sz_2001_; size_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_sz_2001_ = lean_array_size(v_a_2000_);
v___x_2002_ = ((size_t)0ULL);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_2001_, v___x_2002_, v_a_2000_);
v___x_2004_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(lean_object* v_a_2005_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_array_mk(v_a_2005_);
v___x_2007_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_box(0);
return v___x_2009_;
}
else
{
lean_object* v_val_2010_; lean_object* v___x_2011_; 
v_val_2010_ = lean_ctor_get(v_x_2008_, 0);
lean_inc(v_val_2010_);
lean_dec_ref_known(v_x_2008_, 1);
v___x_2011_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_val_2010_);
return v___x_2011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(size_t v_sz_2012_, size_t v_i_2013_, lean_object* v_bs_2014_){
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
lean_object* v_v_2016_; lean_object* v_startPosLine_2017_; lean_object* v_startPosCharacter_2018_; lean_object* v_endPosLine_2019_; lean_object* v_endPosCharacter_2020_; lean_object* v___x_2021_; lean_object* v_bs_x27_2022_; lean_object* v___y_2024_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v_range_2034_; lean_object* v___x_2035_; 
v_v_2016_ = lean_array_uget(v_bs_2014_, v_i_2013_);
v_startPosLine_2017_ = lean_ctor_get(v_v_2016_, 0);
v_startPosCharacter_2018_ = lean_ctor_get(v_v_2016_, 1);
v_endPosLine_2019_ = lean_ctor_get(v_v_2016_, 2);
v_endPosCharacter_2020_ = lean_ctor_get(v_v_2016_, 3);
v___x_2021_ = lean_unsigned_to_nat(0u);
v_bs_x27_2022_ = lean_array_uset(v_bs_2014_, v_i_2013_, v___x_2021_);
v___x_2029_ = lean_box(0);
lean_inc(v_endPosCharacter_2020_);
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_endPosCharacter_2020_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
lean_inc(v_endPosLine_2019_);
v___x_2031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_endPosLine_2019_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
lean_inc(v_startPosCharacter_2018_);
v___x_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_startPosCharacter_2018_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
lean_inc(v_startPosLine_2017_);
v___x_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_startPosLine_2017_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v_range_2034_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_2033_, v___x_2029_);
v___x_2035_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_2016_);
lean_dec(v_v_2016_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = l_List_appendTR___redArg(v_range_2034_, v___x_2029_);
v___y_2024_ = v___x_2036_;
goto v___jp_2023_;
}
else
{
lean_object* v_val_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2046_; 
v_val_2037_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2039_ = v___x_2035_;
v_isShared_2040_ = v_isSharedCheck_2046_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_val_2037_);
lean_dec(v___x_2035_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2046_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set_tag(v___x_2039_, 3);
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_val_2037_);
v___x_2042_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
lean_ctor_set(v___x_2043_, 1, v___x_2029_);
v___x_2044_ = l_List_appendTR___redArg(v_range_2034_, v___x_2043_);
v___y_2024_ = v___x_2044_;
goto v___jp_2023_;
}
}
}
v___jp_2023_:
{
size_t v___x_2025_; size_t v___x_2026_; lean_object* v___x_2027_; 
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2013_, v___x_2025_);
v___x_2027_ = lean_array_uset(v_bs_x27_2022_, v_i_2013_, v___y_2024_);
v_i_2013_ = v___x_2026_;
v_bs_2014_ = v___x_2027_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2___boxed(lean_object* v_sz_2047_, lean_object* v_i_2048_, lean_object* v_bs_2049_){
_start:
{
size_t v_sz_boxed_2050_; size_t v_i_boxed_2051_; lean_object* v_res_2052_; 
v_sz_boxed_2050_ = lean_unbox_usize(v_sz_2047_);
lean_dec(v_sz_2047_);
v_i_boxed_2051_ = lean_unbox_usize(v_i_2048_);
lean_dec(v_i_2048_);
v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_boxed_2050_, v_i_boxed_2051_, v_bs_2049_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(size_t v_sz_2053_, size_t v_i_2054_, lean_object* v_bs_2055_){
_start:
{
uint8_t v___x_2056_; 
v___x_2056_ = lean_usize_dec_lt(v_i_2054_, v_sz_2053_);
if (v___x_2056_ == 0)
{
return v_bs_2055_;
}
else
{
lean_object* v_v_2057_; lean_object* v___x_2058_; lean_object* v_bs_x27_2059_; lean_object* v___x_2060_; size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v_v_2057_ = lean_array_uget(v_bs_2055_, v_i_2054_);
v___x_2058_ = lean_unsigned_to_nat(0u);
v_bs_x27_2059_ = lean_array_uset(v_bs_2055_, v_i_2054_, v___x_2058_);
v___x_2060_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_v_2057_);
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = lean_usize_add(v_i_2054_, v___x_2061_);
v___x_2063_ = lean_array_uset(v_bs_x27_2059_, v_i_2054_, v___x_2060_);
v_i_2054_ = v___x_2062_;
v_bs_2055_ = v___x_2063_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4___boxed(lean_object* v_sz_2065_, lean_object* v_i_2066_, lean_object* v_bs_2067_){
_start:
{
size_t v_sz_boxed_2068_; size_t v_i_boxed_2069_; lean_object* v_res_2070_; 
v_sz_boxed_2068_ = lean_unbox_usize(v_sz_2065_);
lean_dec(v_sz_2065_);
v_i_boxed_2069_ = lean_unbox_usize(v_i_2066_);
lean_dec(v_i_2066_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_boxed_2068_, v_i_boxed_2069_, v_bs_2067_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(lean_object* v_a_2071_){
_start:
{
size_t v_sz_2072_; size_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_sz_2072_ = lean_array_size(v_a_2071_);
v___x_2073_ = ((size_t)0ULL);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_2072_, v___x_2073_, v_a_2071_);
v___x_2075_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
if (lean_obj_tag(v_a_2076_) == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = l_List_reverse___redArg(v_a_2077_);
return v___x_2078_;
}
else
{
lean_object* v_head_2079_; lean_object* v_snd_2080_; lean_object* v_tail_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2150_; 
v_head_2079_ = lean_ctor_get(v_a_2076_, 0);
lean_inc(v_head_2079_);
v_snd_2080_ = lean_ctor_get(v_head_2079_, 1);
lean_inc(v_snd_2080_);
v_tail_2081_ = lean_ctor_get(v_a_2076_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_a_2076_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v_a_2076_, 0);
lean_dec(v_unused_2151_);
v___x_2083_ = v_a_2076_;
v_isShared_2084_ = v_isSharedCheck_2150_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_tail_2081_);
lean_dec(v_a_2076_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2150_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_fst_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2148_; 
v_fst_2085_ = lean_ctor_get(v_head_2079_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_head_2079_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v_head_2079_, 1);
lean_dec(v_unused_2149_);
v___x_2087_ = v_head_2079_;
v_isShared_2088_ = v_isSharedCheck_2148_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_fst_2085_);
lean_dec(v_head_2079_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2148_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_definition_x3f_2089_; lean_object* v_usages_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2147_; 
v_definition_x3f_2089_ = lean_ctor_get(v_snd_2080_, 0);
v_usages_2090_ = lean_ctor_get(v_snd_2080_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_snd_2080_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2092_ = v_snd_2080_;
v_isShared_2093_ = v_isSharedCheck_2147_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_usages_2090_);
lean_inc(v_definition_x3f_2089_);
lean_dec(v_snd_2080_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2147_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___y_2098_; lean_object* v___y_2121_; 
v___x_2094_ = l_Lean_Lsp_RefIdent_toJson(v_fst_2085_);
v___x_2095_ = l_Lean_Json_compress(v___x_2094_);
v___x_2096_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
if (lean_obj_tag(v_definition_x3f_2089_) == 0)
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_box(0);
v___y_2098_ = v___x_2123_;
goto v___jp_2097_;
}
else
{
lean_object* v_val_2124_; lean_object* v_startPosLine_2125_; lean_object* v_startPosCharacter_2126_; lean_object* v_endPosLine_2127_; lean_object* v_endPosCharacter_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v_range_2134_; lean_object* v___x_2135_; 
v_val_2124_ = lean_ctor_get(v_definition_x3f_2089_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v_definition_x3f_2089_, 1);
v_startPosLine_2125_ = lean_ctor_get(v_val_2124_, 0);
v_startPosCharacter_2126_ = lean_ctor_get(v_val_2124_, 1);
v_endPosLine_2127_ = lean_ctor_get(v_val_2124_, 2);
v_endPosCharacter_2128_ = lean_ctor_get(v_val_2124_, 3);
v___x_2129_ = lean_box(0);
lean_inc(v_endPosCharacter_2128_);
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_endPosCharacter_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
lean_inc(v_endPosLine_2127_);
v___x_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2131_, 0, v_endPosLine_2127_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
lean_inc(v_startPosCharacter_2126_);
v___x_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2132_, 0, v_startPosCharacter_2126_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
lean_inc(v_startPosLine_2125_);
v___x_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2133_, 0, v_startPosLine_2125_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v_range_2134_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_2133_, v___x_2129_);
v___x_2135_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_2124_);
lean_dec(v_val_2124_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2136_; 
v___x_2136_ = l_List_appendTR___redArg(v_range_2134_, v___x_2129_);
v___y_2121_ = v___x_2136_;
goto v___jp_2120_;
}
else
{
lean_object* v_val_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2146_; 
v_val_2137_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2139_ = v___x_2135_;
v_isShared_2140_ = v_isSharedCheck_2146_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_val_2137_);
lean_dec(v___x_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2146_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set_tag(v___x_2139_, 3);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_val_2137_);
v___x_2142_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v___x_2129_);
v___x_2144_ = l_List_appendTR___redArg(v_range_2134_, v___x_2143_);
v___y_2121_ = v___x_2144_;
goto v___jp_2120_;
}
}
}
}
v___jp_2097_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = l_Lean_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(v___y_2098_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2099_);
lean_ctor_set(v___x_2087_, 0, v___x_2096_);
v___x_2101_ = v___x_2087_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; size_t v_sz_2103_; size_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2102_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v_sz_2103_ = lean_array_size(v_usages_2090_);
v___x_2104_ = ((size_t)0ULL);
v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_2103_, v___x_2104_, v_usages_2090_);
v___x_2106_ = l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(v___x_2105_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2106_);
lean_ctor_set(v___x_2092_, 0, v___x_2102_);
v___x_2108_ = v___x_2092_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_box(0);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v___x_2109_);
lean_ctor_set(v___x_2083_, 0, v___x_2108_);
v___x_2111_ = v___x_2083_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2101_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = l_Lean_Json_mkObj(v___x_2112_);
lean_dec_ref_known(v___x_2112_, 2);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2095_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v_a_2077_);
v_a_2076_ = v_tail_2081_;
v_a_2077_ = v___x_2115_;
goto _start;
}
}
}
}
v___jp_2120_:
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___y_2121_);
v___y_2098_ = v___x_2122_;
goto v___jp_2097_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(lean_object* v_init_2152_, lean_object* v_x_2153_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 0)
{
lean_object* v_k_2154_; lean_object* v_v_2155_; lean_object* v_l_2156_; lean_object* v_r_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_k_2154_ = lean_ctor_get(v_x_2153_, 1);
v_v_2155_ = lean_ctor_get(v_x_2153_, 2);
v_l_2156_ = lean_ctor_get(v_x_2153_, 3);
v_r_2157_ = lean_ctor_get(v_x_2153_, 4);
v___x_2158_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2152_, v_r_2157_);
lean_inc(v_v_2155_);
lean_inc(v_k_2154_);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v_k_2154_);
lean_ctor_set(v___x_2159_, 1, v_v_2155_);
v___x_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v___x_2158_);
v_init_2152_ = v___x_2160_;
v_x_2153_ = v_l_2156_;
goto _start;
}
else
{
return v_init_2152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5___boxed(lean_object* v_init_2162_, lean_object* v_x_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2162_, v_x_2163_);
lean_dec(v_x_2163_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
if (lean_obj_tag(v_a_2165_) == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = l_List_reverse___redArg(v_a_2166_);
return v___x_2167_;
}
else
{
lean_object* v_head_2168_; lean_object* v_snd_2169_; lean_object* v_tail_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2222_; 
v_head_2168_ = lean_ctor_get(v_a_2165_, 0);
lean_inc(v_head_2168_);
v_snd_2169_ = lean_ctor_get(v_head_2168_, 1);
lean_inc(v_snd_2169_);
v_tail_2170_ = lean_ctor_get(v_a_2165_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v_a_2165_, 0);
lean_dec(v_unused_2223_);
v___x_2172_ = v_a_2165_;
v_isShared_2173_ = v_isSharedCheck_2222_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_tail_2170_);
lean_dec(v_a_2165_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2222_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_fst_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2220_; 
v_fst_2174_ = lean_ctor_get(v_head_2168_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_head_2168_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v_head_2168_, 1);
lean_dec(v_unused_2221_);
v___x_2176_ = v_head_2168_;
v_isShared_2177_ = v_isSharedCheck_2220_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_fst_2174_);
lean_dec(v_head_2168_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2220_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_rangeStartPosLine_2178_; lean_object* v_rangeStartPosCharacter_2179_; lean_object* v_rangeEndPosLine_2180_; lean_object* v_rangeEndPosCharacter_2181_; lean_object* v_selectionRangeStartPosLine_2182_; lean_object* v_selectionRangeStartPosCharacter_2183_; lean_object* v_selectionRangeEndPosLine_2184_; lean_object* v_selectionRangeEndPosCharacter_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v_rangeStartPosLine_2178_ = lean_ctor_get(v_snd_2169_, 0);
lean_inc(v_rangeStartPosLine_2178_);
v_rangeStartPosCharacter_2179_ = lean_ctor_get(v_snd_2169_, 1);
lean_inc(v_rangeStartPosCharacter_2179_);
v_rangeEndPosLine_2180_ = lean_ctor_get(v_snd_2169_, 2);
lean_inc(v_rangeEndPosLine_2180_);
v_rangeEndPosCharacter_2181_ = lean_ctor_get(v_snd_2169_, 3);
lean_inc(v_rangeEndPosCharacter_2181_);
v_selectionRangeStartPosLine_2182_ = lean_ctor_get(v_snd_2169_, 4);
lean_inc(v_selectionRangeStartPosLine_2182_);
v_selectionRangeStartPosCharacter_2183_ = lean_ctor_get(v_snd_2169_, 5);
lean_inc(v_selectionRangeStartPosCharacter_2183_);
v_selectionRangeEndPosLine_2184_ = lean_ctor_get(v_snd_2169_, 6);
lean_inc(v_selectionRangeEndPosLine_2184_);
v_selectionRangeEndPosCharacter_2185_ = lean_ctor_get(v_snd_2169_, 7);
lean_inc(v_selectionRangeEndPosCharacter_2185_);
lean_dec(v_snd_2169_);
v___x_2186_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_2178_);
v___x_2187_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
v___x_2188_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_2179_);
v___x_2189_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
v___x_2190_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_2180_);
v___x_2191_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
v___x_2192_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_2181_);
v___x_2193_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
v___x_2194_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_2182_);
v___x_2195_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
v___x_2196_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_2183_);
v___x_2197_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
v___x_2198_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_2184_);
v___x_2199_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
v___x_2200_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_2185_);
v___x_2201_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
v___x_2202_ = lean_unsigned_to_nat(8u);
v___x_2203_ = lean_mk_empty_array_with_capacity(v___x_2202_);
v___x_2204_ = lean_array_push(v___x_2203_, v___x_2187_);
v___x_2205_ = lean_array_push(v___x_2204_, v___x_2189_);
v___x_2206_ = lean_array_push(v___x_2205_, v___x_2191_);
v___x_2207_ = lean_array_push(v___x_2206_, v___x_2193_);
v___x_2208_ = lean_array_push(v___x_2207_, v___x_2195_);
v___x_2209_ = lean_array_push(v___x_2208_, v___x_2197_);
v___x_2210_ = lean_array_push(v___x_2209_, v___x_2199_);
v___x_2211_ = lean_array_push(v___x_2210_, v___x_2201_);
v___x_2212_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v___x_2212_);
v___x_2214_ = v___x_2176_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_fst_2174_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2216_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v_a_2166_);
lean_ctor_set(v___x_2172_, 0, v___x_2214_);
v___x_2216_ = v___x_2172_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_a_2166_);
v___x_2216_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
v_a_2165_ = v_tail_2170_;
v_a_2166_ = v___x_2216_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
if (lean_obj_tag(v_a_2224_) == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_array_to_list(v_a_2225_);
return v___x_2226_;
}
else
{
lean_object* v_head_2227_; lean_object* v_tail_2228_; lean_object* v___x_2229_; 
v_head_2227_ = lean_ctor_get(v_a_2224_, 0);
lean_inc(v_head_2227_);
v_tail_2228_ = lean_ctor_get(v_a_2224_, 1);
lean_inc(v_tail_2228_);
lean_dec_ref_known(v_a_2224_, 2);
v___x_2229_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2225_, v_head_2227_);
v_a_2224_ = v_tail_2228_;
v_a_2225_ = v___x_2229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(lean_object* v_init_2231_, lean_object* v_x_2232_){
_start:
{
if (lean_obj_tag(v_x_2232_) == 0)
{
lean_object* v_k_2233_; lean_object* v_v_2234_; lean_object* v_l_2235_; lean_object* v_r_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_k_2233_ = lean_ctor_get(v_x_2232_, 1);
v_v_2234_ = lean_ctor_get(v_x_2232_, 2);
v_l_2235_ = lean_ctor_get(v_x_2232_, 3);
v_r_2236_ = lean_ctor_get(v_x_2232_, 4);
v___x_2237_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2231_, v_r_2236_);
lean_inc(v_v_2234_);
lean_inc(v_k_2233_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_k_2233_);
lean_ctor_set(v___x_2238_, 1, v_v_2234_);
v___x_2239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___x_2237_);
v_init_2231_ = v___x_2239_;
v_x_2232_ = v_l_2235_;
goto _start;
}
else
{
return v_init_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7___boxed(lean_object* v_init_2241_, lean_object* v_x_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2241_, v_x_2242_);
lean_dec(v_x_2242_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonIlean_toJson(lean_object* v_x_2246_){
_start:
{
lean_object* v_version_2247_; lean_object* v_module_2248_; lean_object* v_directImports_2249_; lean_object* v_references_2250_; lean_object* v_decls_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v_version_2247_ = lean_ctor_get(v_x_2246_, 0);
lean_inc(v_version_2247_);
v_module_2248_ = lean_ctor_get(v_x_2246_, 1);
lean_inc(v_module_2248_);
v_directImports_2249_ = lean_ctor_get(v_x_2246_, 2);
lean_inc_ref(v_directImports_2249_);
v_references_2250_ = lean_ctor_get(v_x_2246_, 3);
lean_inc(v_references_2250_);
v_decls_2251_ = lean_ctor_get(v_x_2246_, 4);
lean_inc(v_decls_2251_);
lean_dec_ref(v_x_2246_);
v___x_2252_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
v___x_2253_ = l_Lean_JsonNumber_fromNat(v_version_2247_);
v___x_2254_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2252_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = lean_box(0);
v___x_2257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
v___x_2259_ = 1;
v___x_2260_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_2248_, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2258_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___x_2256_);
v___x_2264_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
v___x_2265_ = l_Lean_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(v_directImports_2249_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v___x_2256_);
v___x_2268_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
v___x_2269_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v___x_2256_, v_references_2250_);
lean_dec(v_references_2250_);
v___x_2270_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(v___x_2269_, v___x_2256_);
v___x_2271_ = l_Lean_Json_mkObj(v___x_2270_);
lean_dec(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2268_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___x_2256_);
v___x_2274_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_2275_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v___x_2256_, v_decls_2251_);
lean_dec(v_decls_2251_);
v___x_2276_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(v___x_2275_, v___x_2256_);
v___x_2277_ = l_Lean_Json_mkObj(v___x_2276_);
lean_dec(v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2274_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v___x_2256_);
v___x_2280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___x_2256_);
v___x_2281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2273_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2267_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2263_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2257_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = ((lean_object*)(l_Lean_Server_instToJsonIlean_toJson___closed__0));
v___x_2286_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(v___x_2284_, v___x_2285_);
v___x_2287_ = l_Lean_Json_mkObj(v___x_2286_);
lean_dec(v___x_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load(lean_object* v_path_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_IO_FS_readFile(v_path_2291_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2315_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2315_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2315_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_a_2299_; lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Json_parse(v_a_2294_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; 
lean_del_object(v___x_2296_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v_a_2299_ = v_a_2307_;
goto v___jp_2298_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2309_; 
v_a_2308_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2309_ = l_Lean_Server_instFromJsonIlean_fromJson(v_a_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; 
lean_del_object(v___x_2296_);
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v_a_2299_ = v_a_2310_;
goto v___jp_2298_;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; 
v_a_2311_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2309_, 1);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_a_2311_);
v___x_2313_ = v___x_2296_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
v___jp_2298_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2300_ = ((lean_object*)(l_Lean_Server_Ilean_load___closed__0));
v___x_2301_ = lean_string_append(v___x_2300_, v_path_2291_);
v___x_2302_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_2303_ = lean_string_append(v___x_2301_, v___x_2302_);
v___x_2304_ = lean_string_append(v___x_2303_, v_a_2299_);
lean_dec_ref(v_a_2299_);
v___x_2305_ = l_Lean_IO_throwServerError___redArg(v___x_2304_);
return v___x_2305_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
v_a_2316_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2293_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2293_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load___boxed(lean_object* v_path_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Server_Ilean_load(v_path_2324_);
lean_dec_ref(v_path_2324_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f(lean_object* v_env_2327_, lean_object* v_declName_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2327_, v_declName_2328_);
if (lean_obj_tag(v___x_2329_) == 1)
{
lean_object* v_val_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2342_; 
v_val_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2342_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_val_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2342_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2334_ = l_Lean_Environment_allImportedModuleNames(v_env_2327_);
v___x_2335_ = lean_array_get_size(v___x_2334_);
v___x_2336_ = lean_nat_dec_lt(v_val_2330_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; 
lean_dec_ref(v___x_2334_);
lean_del_object(v___x_2332_);
lean_dec(v_val_2330_);
v___x_2337_ = lean_box(0);
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2338_ = lean_array_fget(v___x_2334_, v_val_2330_);
lean_dec(v_val_2330_);
lean_dec_ref(v___x_2334_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2338_);
v___x_2340_ = v___x_2332_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v___x_2343_; lean_object* v_mainModule_2344_; lean_object* v___x_2345_; 
lean_dec(v___x_2329_);
v___x_2343_ = l_Lean_Environment_header(v_env_2327_);
v_mainModule_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_mainModule_2344_);
lean_dec_ref(v___x_2343_);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v_mainModule_2344_);
return v___x_2345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f___boxed(lean_object* v_env_2346_, lean_object* v_declName_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2346_, v_declName_2347_);
lean_dec(v_declName_2347_);
lean_dec_ref(v_env_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf(lean_object* v_ci_2349_, lean_object* v_i_2350_){
_start:
{
switch(lean_obj_tag(v_i_2350_))
{
case 1:
{
lean_object* v_i_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2392_; 
v_i_2351_ = lean_ctor_get(v_i_2350_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_i_2350_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2353_ = v_i_2350_;
v_isShared_2354_ = v_isSharedCheck_2392_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_i_2351_);
lean_dec(v_i_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2392_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_expr_2355_; 
v_expr_2355_ = lean_ctor_get(v_i_2351_, 3);
lean_inc_ref(v_expr_2355_);
switch(lean_obj_tag(v_expr_2355_))
{
case 4:
{
lean_object* v_toCommandContextInfo_2356_; uint8_t v_isBinder_2357_; lean_object* v_declName_2358_; lean_object* v_env_2359_; lean_object* v___x_2360_; 
lean_del_object(v___x_2353_);
v_toCommandContextInfo_2356_ = lean_ctor_get(v_ci_2349_, 0);
v_isBinder_2357_ = lean_ctor_get_uint8(v_i_2351_, sizeof(void*)*4);
lean_dec_ref(v_i_2351_);
v_declName_2358_ = lean_ctor_get(v_expr_2355_, 0);
lean_inc(v_declName_2358_);
lean_dec_ref_known(v_expr_2355_, 2);
v_env_2359_ = lean_ctor_get(v_toCommandContextInfo_2356_, 0);
v___x_2360_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2359_, v_declName_2358_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v___x_2361_; 
lean_dec(v_declName_2358_);
v___x_2361_ = lean_box(0);
return v___x_2361_;
}
else
{
lean_object* v_val_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2375_; 
v_val_2362_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2364_ = v___x_2360_;
v_isShared_2365_ = v_isSharedCheck_2375_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_val_2362_);
lean_dec(v___x_2360_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2375_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2366_ = 1;
v___x_2367_ = l_Lean_Name_toString(v_val_2362_, v___x_2366_);
v___x_2368_ = l_Lean_Name_toString(v_declName_2358_, v___x_2366_);
v___x_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_box(v_isBinder_2357_);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2371_);
v___x_2373_ = v___x_2364_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
case 1:
{
lean_object* v_toCommandContextInfo_2376_; uint8_t v_isBinder_2377_; lean_object* v_fvarId_2378_; lean_object* v_env_2379_; lean_object* v___x_2380_; lean_object* v_mainModule_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v_toCommandContextInfo_2376_ = lean_ctor_get(v_ci_2349_, 0);
v_isBinder_2377_ = lean_ctor_get_uint8(v_i_2351_, sizeof(void*)*4);
lean_dec_ref(v_i_2351_);
v_fvarId_2378_ = lean_ctor_get(v_expr_2355_, 0);
lean_inc(v_fvarId_2378_);
lean_dec_ref_known(v_expr_2355_, 1);
v_env_2379_ = lean_ctor_get(v_toCommandContextInfo_2376_, 0);
v___x_2380_ = l_Lean_Environment_header(v_env_2379_);
v_mainModule_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_mainModule_2381_);
lean_dec_ref(v___x_2380_);
v___x_2382_ = 1;
v___x_2383_ = l_Lean_Name_toString(v_mainModule_2381_, v___x_2382_);
v___x_2384_ = l_Lean_Name_toString(v_fvarId_2378_, v___x_2382_);
v___x_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_box(v_isBinder_2377_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2387_);
v___x_2389_ = v___x_2353_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
default: 
{
lean_object* v___x_2391_; 
lean_dec_ref(v_expr_2355_);
lean_del_object(v___x_2353_);
lean_dec_ref(v_i_2351_);
v___x_2391_ = lean_box(0);
return v___x_2391_;
}
}
}
}
case 7:
{
lean_object* v_toCommandContextInfo_2393_; lean_object* v_i_2394_; lean_object* v_env_2395_; lean_object* v_projName_2396_; lean_object* v___x_2397_; 
v_toCommandContextInfo_2393_ = lean_ctor_get(v_ci_2349_, 0);
v_i_2394_ = lean_ctor_get(v_i_2350_, 0);
lean_inc_ref(v_i_2394_);
lean_dec_ref_known(v_i_2350_, 1);
v_env_2395_ = lean_ctor_get(v_toCommandContextInfo_2393_, 0);
v_projName_2396_ = lean_ctor_get(v_i_2394_, 0);
lean_inc(v_projName_2396_);
lean_dec_ref(v_i_2394_);
v___x_2397_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2395_, v_projName_2396_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v___x_2398_; 
lean_dec(v_projName_2396_);
v___x_2398_ = lean_box(0);
return v___x_2398_;
}
else
{
lean_object* v_val_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2413_; 
v_val_2399_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2401_ = v___x_2397_;
v_isShared_2402_ = v_isSharedCheck_2413_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_val_2399_);
lean_dec(v___x_2397_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2413_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2403_ = 1;
v___x_2404_ = l_Lean_Name_toString(v_val_2399_, v___x_2403_);
v___x_2405_ = l_Lean_Name_toString(v_projName_2396_, v___x_2403_);
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = 0;
v___x_2408_ = lean_box(v___x_2407_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2406_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2409_);
v___x_2411_ = v___x_2401_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
case 5:
{
lean_object* v_toCommandContextInfo_2414_; lean_object* v_i_2415_; lean_object* v_env_2416_; lean_object* v_declName_2417_; lean_object* v___x_2418_; 
v_toCommandContextInfo_2414_ = lean_ctor_get(v_ci_2349_, 0);
v_i_2415_ = lean_ctor_get(v_i_2350_, 0);
lean_inc_ref(v_i_2415_);
lean_dec_ref_known(v_i_2350_, 1);
v_env_2416_ = lean_ctor_get(v_toCommandContextInfo_2414_, 0);
v_declName_2417_ = lean_ctor_get(v_i_2415_, 2);
lean_inc(v_declName_2417_);
lean_dec_ref(v_i_2415_);
v___x_2418_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2416_, v_declName_2417_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v___x_2419_; 
lean_dec(v_declName_2417_);
v___x_2419_ = lean_box(0);
return v___x_2419_;
}
else
{
lean_object* v_val_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2434_; 
v_val_2420_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2422_ = v___x_2418_;
v_isShared_2423_ = v_isSharedCheck_2434_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_val_2420_);
lean_dec(v___x_2418_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2434_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2424_ = 1;
v___x_2425_ = l_Lean_Name_toString(v_val_2420_, v___x_2424_);
v___x_2426_ = l_Lean_Name_toString(v_declName_2417_, v___x_2424_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = 0;
v___x_2429_ = lean_box(v___x_2428_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2427_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2430_);
v___x_2432_ = v___x_2422_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
case 16:
{
lean_object* v_toCommandContextInfo_2435_; lean_object* v_i_2436_; lean_object* v_env_2437_; lean_object* v_name_2438_; lean_object* v___x_2439_; 
v_toCommandContextInfo_2435_ = lean_ctor_get(v_ci_2349_, 0);
v_i_2436_ = lean_ctor_get(v_i_2350_, 0);
lean_inc_ref(v_i_2436_);
lean_dec_ref_known(v_i_2350_, 1);
v_env_2437_ = lean_ctor_get(v_toCommandContextInfo_2435_, 0);
v_name_2438_ = lean_ctor_get(v_i_2436_, 1);
lean_inc(v_name_2438_);
lean_dec_ref(v_i_2436_);
v___x_2439_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2437_, v_name_2438_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v___x_2440_; 
lean_dec(v_name_2438_);
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
v___x_2447_ = l_Lean_Name_toString(v_name_2438_, v___x_2445_);
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
default: 
{
lean_object* v___x_2456_; 
lean_dec_ref(v_i_2350_);
v___x_2456_ = lean_box(0);
return v___x_2456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf___boxed(lean_object* v_ci_2457_, lean_object* v_i_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Server_identOf(v_ci_2457_, v_i_2458_);
lean_dec_ref(v_ci_2457_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(uint8_t v___x_2460_, lean_object* v_x_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_box(v___x_2460_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v___y_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed(lean_object* v___x_2467_, lean_object* v_x_2468_, lean_object* v_x_2469_, lean_object* v_x_2470_, lean_object* v___y_2471_){
_start:
{
uint8_t v___x_3593__boxed_2472_; lean_object* v_res_2473_; 
v___x_3593__boxed_2472_ = lean_unbox(v___x_2467_);
v_res_2473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(v___x_3593__boxed_2472_, v_x_2468_, v_x_2469_, v_x_2470_, v___y_2471_);
lean_dec_ref(v_x_2470_);
lean_dec_ref(v_x_2469_);
lean_dec_ref(v_x_2468_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(lean_object* v_text_2474_, lean_object* v_ci_2475_, lean_object* v_info_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2479_; 
lean_inc_ref(v_info_2476_);
v___x_2479_ = l_Lean_Server_identOf(v_ci_2475_, v_info_2476_);
if (lean_obj_tag(v___x_2479_) == 1)
{
lean_object* v_val_2480_; lean_object* v_fst_2481_; lean_object* v_snd_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2507_; 
v_val_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v_fst_2481_ = lean_ctor_get(v_val_2480_, 0);
v_snd_2482_ = lean_ctor_get(v_val_2480_, 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_val_2480_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2484_ = v_val_2480_;
v_isShared_2485_ = v_isSharedCheck_2507_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_snd_2482_);
lean_inc(v_fst_2481_);
lean_dec(v_val_2480_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2507_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_Elab_Info_range_x3f(v_info_2476_);
if (lean_obj_tag(v___x_2486_) == 1)
{
lean_object* v_val_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v_val_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_val_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2488_ = l_Lean_Elab_Info_stx(v_info_2476_);
v___x_2489_ = l_Lean_Syntax_getHeadInfo(v___x_2488_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
lean_dec_ref_known(v___x_2489_, 4);
v___x_2490_ = lean_box(0);
v___x_2491_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_2492_ = l_Lean_Syntax_Range_toLspRange(v_text_2474_, v_val_2487_);
v___x_2493_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2493_, 0, v_fst_2481_);
lean_ctor_set(v___x_2493_, 1, v___x_2491_);
lean_ctor_set(v___x_2493_, 2, v___x_2492_);
lean_ctor_set(v___x_2493_, 3, v___x_2488_);
lean_ctor_set(v___x_2493_, 4, v_ci_2475_);
lean_ctor_set(v___x_2493_, 5, v_info_2476_);
v___x_2494_ = lean_unbox(v_snd_2482_);
lean_dec(v_snd_2482_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*6, v___x_2494_);
v___x_2495_ = lean_array_push(v___y_2478_, v___x_2493_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___x_2495_);
lean_ctor_set(v___x_2484_, 0, v___x_2490_);
v___x_2497_ = v___x_2484_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
lean_dec(v___x_2489_);
lean_dec(v___x_2488_);
lean_dec(v_val_2487_);
lean_dec(v_snd_2482_);
lean_dec(v_fst_2481_);
lean_dec_ref(v_info_2476_);
lean_dec_ref(v_ci_2475_);
lean_dec_ref(v_text_2474_);
v___x_2499_ = lean_box(0);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___y_2478_);
lean_ctor_set(v___x_2484_, 0, v___x_2499_);
v___x_2501_ = v___x_2484_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___y_2478_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
lean_dec(v___x_2486_);
lean_dec(v_snd_2482_);
lean_dec(v_fst_2481_);
lean_dec_ref(v_info_2476_);
lean_dec_ref(v_ci_2475_);
lean_dec_ref(v_text_2474_);
v___x_2503_ = lean_box(0);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___y_2478_);
lean_ctor_set(v___x_2484_, 0, v___x_2503_);
v___x_2505_ = v___x_2484_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v___y_2478_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec(v___x_2479_);
lean_dec_ref(v_info_2476_);
lean_dec_ref(v_ci_2475_);
lean_dec_ref(v_text_2474_);
v___x_2508_ = lean_box(0);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___y_2478_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed(lean_object* v_text_2510_, lean_object* v_ci_2511_, lean_object* v_info_2512_, lean_object* v_x_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(v_text_2510_, v_ci_2511_, v_info_2512_, v_x_2513_, v___y_2514_);
lean_dec_ref(v_x_2513_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object* v_postNode_2516_, lean_object* v_ci_2517_, lean_object* v_i_2518_, lean_object* v_cs_2519_, lean_object* v_x_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_apply_4(v_postNode_2516_, v_ci_2517_, v_i_2518_, v_cs_2519_, v___y_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object* v_postNode_2523_, lean_object* v_ci_2524_, lean_object* v_i_2525_, lean_object* v_cs_2526_, lean_object* v_x_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(v_postNode_2523_, v_ci_2524_, v_i_2525_, v_cs_2526_, v_x_2527_, v___y_2528_);
lean_dec(v_x_2527_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___f_2539_; lean_object* v___f_2540_; lean_object* v___f_2541_; lean_object* v___f_2542_; lean_object* v___f_2543_; lean_object* v___f_2544_; lean_object* v___f_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___f_2549_; lean_object* v___f_2550_; lean_object* v___f_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_3187__overap_2561_; lean_object* v___x_2562_; 
v___f_2539_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_2540_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_2541_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_2542_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_2543_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_2544_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_2545_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___f_2539_);
lean_ctor_set(v___x_2546_, 1, v___f_2540_);
v___x_2547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
lean_ctor_set(v___x_2547_, 1, v___f_2541_);
lean_ctor_set(v___x_2547_, 2, v___f_2542_);
lean_ctor_set(v___x_2547_, 3, v___f_2543_);
lean_ctor_set(v___x_2547_, 4, v___f_2544_);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v___f_2545_);
lean_inc_ref_n(v___x_2548_, 6);
v___f_2549_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2549_, 0, v___x_2548_);
v___f_2550_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2550_, 0, v___x_2548_);
v___f_2551_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2551_, 0, v___x_2548_);
v___f_2552_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2552_, 0, v___x_2548_);
v___x_2553_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2553_, 0, lean_box(0));
lean_closure_set(v___x_2553_, 1, lean_box(0));
lean_closure_set(v___x_2553_, 2, v___x_2548_);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v___f_2549_);
v___x_2555_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2555_, 0, lean_box(0));
lean_closure_set(v___x_2555_, 1, lean_box(0));
lean_closure_set(v___x_2555_, 2, v___x_2548_);
v___x_2556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
lean_ctor_set(v___x_2556_, 2, v___f_2550_);
lean_ctor_set(v___x_2556_, 3, v___f_2551_);
lean_ctor_set(v___x_2556_, 4, v___f_2552_);
v___x_2557_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2557_, 0, lean_box(0));
lean_closure_set(v___x_2557_, 1, lean_box(0));
lean_closure_set(v___x_2557_, 2, v___x_2548_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = lean_box(0);
v___x_2560_ = l_instInhabitedOfMonad___redArg(v___x_2558_, v___x_2559_);
v___x_3187__overap_2561_ = lean_panic_fn_borrowed(v___x_2560_, v_msg_2537_);
lean_dec(v___x_2560_);
v___x_2562_ = lean_apply_1(v___x_3187__overap_2561_, v___y_2538_);
return v___x_2562_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2566_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2));
v___x_2567_ = lean_unsigned_to_nat(21u);
v___x_2568_ = lean_unsigned_to_nat(65u);
v___x_2569_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1));
v___x_2570_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0));
v___x_2571_ = l_mkPanicMessageWithDecl(v___x_2570_, v___x_2569_, v___x_2568_, v___x_2567_, v___x_2566_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object* v_preNode_2572_, lean_object* v_postNode_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_, lean_object* v___y_2576_){
_start:
{
switch(lean_obj_tag(v_x_2575_))
{
case 0:
{
lean_object* v_i_2577_; lean_object* v_t_2578_; lean_object* v___x_2579_; 
v_i_2577_ = lean_ctor_get(v_x_2575_, 0);
lean_inc_ref(v_i_2577_);
v_t_2578_ = lean_ctor_get(v_x_2575_, 1);
lean_inc_ref(v_t_2578_);
lean_dec_ref_known(v_x_2575_, 2);
v___x_2579_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2577_, v_x_2574_);
v_x_2574_ = v___x_2579_;
v_x_2575_ = v_t_2578_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_2574_) == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_dec_ref_known(v_x_2575_, 2);
lean_dec_ref(v_postNode_2573_);
lean_dec_ref(v_preNode_2572_);
v___x_2581_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_2582_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v___x_2581_, v___y_2576_);
return v___x_2582_;
}
else
{
lean_object* v_i_2583_; lean_object* v_children_2584_; lean_object* v_val_2585_; lean_object* v___x_2586_; lean_object* v_fst_2587_; uint8_t v___x_2588_; 
v_i_2583_ = lean_ctor_get(v_x_2575_, 0);
lean_inc_ref_n(v_i_2583_, 2);
v_children_2584_ = lean_ctor_get(v_x_2575_, 1);
lean_inc_ref_n(v_children_2584_, 2);
lean_dec_ref_known(v_x_2575_, 2);
v_val_2585_ = lean_ctor_get(v_x_2574_, 0);
lean_inc_n(v_val_2585_, 2);
lean_inc_ref(v_preNode_2572_);
v___x_2586_ = lean_apply_4(v_preNode_2572_, v_val_2585_, v_i_2583_, v_children_2584_, v___y_2576_);
v_fst_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_fst_2587_);
v___x_2588_ = lean_unbox(v_fst_2587_);
lean_dec(v_fst_2587_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2607_; 
lean_dec_ref(v_preNode_2572_);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_x_2574_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; 
v_unused_2608_ = lean_ctor_get(v_x_2574_, 0);
lean_dec(v_unused_2608_);
v___x_2590_ = v_x_2574_;
v_isShared_2591_ = v_isSharedCheck_2607_;
goto v_resetjp_2589_;
}
else
{
lean_dec(v_x_2574_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2607_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v_snd_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v_fst_2595_; lean_object* v_snd_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2606_; 
v_snd_2592_ = lean_ctor_get(v___x_2586_, 1);
lean_inc(v_snd_2592_);
lean_dec_ref(v___x_2586_);
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_apply_5(v_postNode_2573_, v_val_2585_, v_i_2583_, v_children_2584_, v___x_2593_, v_snd_2592_);
v_fst_2595_ = lean_ctor_get(v___x_2594_, 0);
v_snd_2596_ = lean_ctor_get(v___x_2594_, 1);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2598_ = v___x_2594_;
v_isShared_2599_ = v_isSharedCheck_2606_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_snd_2596_);
lean_inc(v_fst_2595_);
lean_dec(v___x_2594_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2606_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v_fst_2595_);
v___x_2601_ = v___x_2590_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_fst_2595_);
v___x_2601_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2601_);
v___x_2603_ = v___x_2598_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_snd_2596_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
else
{
lean_object* v_snd_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_fst_2614_; lean_object* v_snd_2615_; lean_object* v___x_2616_; lean_object* v_fst_2617_; lean_object* v_snd_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2626_; 
v_snd_2609_ = lean_ctor_get(v___x_2586_, 1);
lean_inc(v_snd_2609_);
lean_dec_ref(v___x_2586_);
v___x_2610_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2574_, v_i_2583_);
v___x_2611_ = l_Lean_PersistentArray_toList___redArg(v_children_2584_);
v___x_2612_ = lean_box(0);
lean_inc_ref(v_postNode_2573_);
v___x_2613_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2572_, v_postNode_2573_, v___x_2610_, v___x_2611_, v___x_2612_, v_snd_2609_);
v_fst_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_fst_2614_);
v_snd_2615_ = lean_ctor_get(v___x_2613_, 1);
lean_inc(v_snd_2615_);
lean_dec_ref(v___x_2613_);
v___x_2616_ = lean_apply_5(v_postNode_2573_, v_val_2585_, v_i_2583_, v_children_2584_, v_fst_2614_, v_snd_2615_);
v_fst_2617_ = lean_ctor_get(v___x_2616_, 0);
v_snd_2618_ = lean_ctor_get(v___x_2616_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2620_ = v___x_2616_;
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_snd_2618_);
lean_inc(v_fst_2617_);
lean_dec(v___x_2616_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2626_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2622_, 0, v_fst_2617_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2622_);
v___x_2624_ = v___x_2620_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_snd_2618_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
default: 
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec_ref_known(v_x_2575_, 1);
lean_dec(v_x_2574_);
lean_dec_ref(v_postNode_2573_);
lean_dec_ref(v_preNode_2572_);
v___x_2627_ = lean_box(0);
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
lean_ctor_set(v___x_2628_, 1, v___y_2576_);
return v___x_2628_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_2629_, lean_object* v_postNode_2630_, lean_object* v___x_2631_, lean_object* v_x_2632_, lean_object* v_x_2633_, lean_object* v___y_2634_){
_start:
{
if (lean_obj_tag(v_x_2632_) == 0)
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_dec(v___x_2631_);
lean_dec_ref(v_postNode_2630_);
lean_dec_ref(v_preNode_2629_);
v___x_2635_ = l_List_reverse___redArg(v_x_2633_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___y_2634_);
return v___x_2636_;
}
else
{
lean_object* v_head_2637_; lean_object* v_tail_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2649_; 
v_head_2637_ = lean_ctor_get(v_x_2632_, 0);
v_tail_2638_ = lean_ctor_get(v_x_2632_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_x_2632_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2640_ = v_x_2632_;
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_tail_2638_);
lean_inc(v_head_2637_);
lean_dec(v_x_2632_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v_fst_2643_; lean_object* v_snd_2644_; lean_object* v___x_2646_; 
lean_inc(v___x_2631_);
lean_inc_ref(v_postNode_2630_);
lean_inc_ref(v_preNode_2629_);
v___x_2642_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2629_, v_postNode_2630_, v___x_2631_, v_head_2637_, v___y_2634_);
v_fst_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_fst_2643_);
v_snd_2644_ = lean_ctor_get(v___x_2642_, 1);
lean_inc(v_snd_2644_);
lean_dec_ref(v___x_2642_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 1, v_x_2633_);
lean_ctor_set(v___x_2640_, 0, v_fst_2643_);
v___x_2646_ = v___x_2640_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_fst_2643_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_x_2633_);
v___x_2646_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
v_x_2632_ = v_tail_2638_;
v_x_2633_ = v___x_2646_;
v___y_2634_ = v_snd_2644_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object* v_preNode_2650_, lean_object* v_postNode_2651_, lean_object* v_ctx_x3f_2652_, lean_object* v_t_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___f_2655_; lean_object* v___x_2656_; lean_object* v_snd_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2665_; 
v___f_2655_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2655_, 0, v_postNode_2651_);
v___x_2656_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2650_, v___f_2655_, v_ctx_x3f_2652_, v_t_2653_, v___y_2654_);
v_snd_2657_ = lean_ctor_get(v___x_2656_, 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2665_ == 0)
{
lean_object* v_unused_2666_; 
v_unused_2666_ = lean_ctor_get(v___x_2656_, 0);
lean_dec(v_unused_2666_);
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2665_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_snd_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2665_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2661_ = lean_box(0);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2661_);
v___x_2663_ = v___x_2659_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_snd_2657_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(lean_object* v_text_2667_, lean_object* v_as_2668_, size_t v_sz_2669_, size_t v_i_2670_, lean_object* v_b_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v___x_2673_; 
v___x_2673_ = lean_usize_dec_lt(v_i_2670_, v_sz_2669_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; 
lean_dec_ref(v_text_2667_);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v_b_2671_);
lean_ctor_set(v___x_2674_, 1, v___y_2672_);
return v___x_2674_;
}
else
{
lean_object* v___x_2675_; lean_object* v___f_2676_; lean_object* v___f_2677_; lean_object* v_a_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v_snd_2681_; lean_object* v___x_2682_; size_t v___x_2683_; size_t v___x_2684_; 
v___x_2675_ = lean_box(v___x_2673_);
v___f_2676_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2676_, 0, v___x_2675_);
lean_inc_ref(v_text_2667_);
v___f_2677_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2677_, 0, v_text_2667_);
v_a_2678_ = lean_array_uget_borrowed(v_as_2668_, v_i_2670_);
v___x_2679_ = lean_box(0);
lean_inc(v_a_2678_);
v___x_2680_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(v___f_2676_, v___f_2677_, v___x_2679_, v_a_2678_, v___y_2672_);
v_snd_2681_ = lean_ctor_get(v___x_2680_, 1);
lean_inc(v_snd_2681_);
lean_dec_ref(v___x_2680_);
v___x_2682_ = lean_box(0);
v___x_2683_ = ((size_t)1ULL);
v___x_2684_ = lean_usize_add(v_i_2670_, v___x_2683_);
v_i_2670_ = v___x_2684_;
v_b_2671_ = v___x_2682_;
v___y_2672_ = v_snd_2681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___boxed(lean_object* v_text_2686_, lean_object* v_as_2687_, lean_object* v_sz_2688_, lean_object* v_i_2689_, lean_object* v_b_2690_, lean_object* v___y_2691_){
_start:
{
size_t v_sz_boxed_2692_; size_t v_i_boxed_2693_; lean_object* v_res_2694_; 
v_sz_boxed_2692_ = lean_unbox_usize(v_sz_2688_);
lean_dec(v_sz_2688_);
v_i_boxed_2693_ = lean_unbox_usize(v_i_2689_);
lean_dec(v_i_2689_);
v_res_2694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2686_, v_as_2687_, v_sz_boxed_2692_, v_i_boxed_2693_, v_b_2690_, v___y_2691_);
lean_dec_ref(v_as_2687_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences(lean_object* v_text_2695_, lean_object* v_trees_2696_){
_start:
{
lean_object* v___x_2697_; size_t v_sz_2698_; size_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v_snd_2702_; 
v___x_2697_ = lean_box(0);
v_sz_2698_ = lean_array_size(v_trees_2696_);
v___x_2699_ = ((size_t)0ULL);
v___x_2700_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2695_, v_trees_2696_, v_sz_2698_, v___x_2699_, v___x_2697_, v___x_2700_);
v_snd_2702_ = lean_ctor_get(v___x_2701_, 1);
lean_inc(v_snd_2702_);
lean_dec_ref(v___x_2701_);
return v_snd_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences___boxed(lean_object* v_text_2703_, lean_object* v_trees_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Server_findReferences(v_text_2703_, v_trees_2704_);
lean_dec_ref(v_trees_2704_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2706_, lean_object* v_msg_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v_msg_2707_, v___y_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object* v_00_u03b1_2710_, lean_object* v_preNode_2711_, lean_object* v_postNode_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2711_, v_postNode_2712_, v_x_2713_, v_x_2714_, v___y_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2717_, lean_object* v_preNode_2718_, lean_object* v_postNode_2719_, lean_object* v___x_2720_, lean_object* v_x_2721_, lean_object* v_x_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2718_, v_postNode_2719_, v___x_2720_, v_x_2721_, v_x_2722_, v___y_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(lean_object* v_a_2725_, lean_object* v_x_2726_){
_start:
{
lean_object* v_key_2727_; lean_object* v_value_2728_; lean_object* v_tail_2729_; uint8_t v___x_2730_; 
v_key_2727_ = lean_ctor_get(v_x_2726_, 0);
v_value_2728_ = lean_ctor_get(v_x_2726_, 1);
v_tail_2729_ = lean_ctor_get(v_x_2726_, 2);
v___x_2730_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2727_, v_a_2725_);
if (v___x_2730_ == 0)
{
v_x_2726_ = v_tail_2729_;
goto _start;
}
else
{
lean_inc(v_value_2728_);
return v_value_2728_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg___boxed(lean_object* v_a_2732_, lean_object* v_x_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2732_, v_x_2733_);
lean_dec(v_x_2733_);
lean_dec_ref(v_a_2732_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(lean_object* v_m_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v_buckets_2737_; lean_object* v___x_2738_; uint64_t v___x_2739_; uint64_t v___x_2740_; uint64_t v___x_2741_; uint64_t v_fold_2742_; uint64_t v___x_2743_; uint64_t v___x_2744_; uint64_t v___x_2745_; size_t v___x_2746_; size_t v___x_2747_; size_t v___x_2748_; size_t v___x_2749_; size_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_buckets_2737_ = lean_ctor_get(v_m_2735_, 1);
v___x_2738_ = lean_array_get_size(v_buckets_2737_);
v___x_2739_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2736_);
v___x_2740_ = 32ULL;
v___x_2741_ = lean_uint64_shift_right(v___x_2739_, v___x_2740_);
v_fold_2742_ = lean_uint64_xor(v___x_2739_, v___x_2741_);
v___x_2743_ = 16ULL;
v___x_2744_ = lean_uint64_shift_right(v_fold_2742_, v___x_2743_);
v___x_2745_ = lean_uint64_xor(v_fold_2742_, v___x_2744_);
v___x_2746_ = lean_uint64_to_usize(v___x_2745_);
v___x_2747_ = lean_usize_of_nat(v___x_2738_);
v___x_2748_ = ((size_t)1ULL);
v___x_2749_ = lean_usize_sub(v___x_2747_, v___x_2748_);
v___x_2750_ = lean_usize_land(v___x_2746_, v___x_2749_);
v___x_2751_ = lean_array_uget_borrowed(v_buckets_2737_, v___x_2750_);
v___x_2752_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2736_, v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg___boxed(lean_object* v_m_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2753_, v_a_2754_);
lean_dec_ref(v_a_2754_);
lean_dec_ref(v_m_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(lean_object* v_a_2756_, lean_object* v_x_2757_){
_start:
{
if (lean_obj_tag(v_x_2757_) == 0)
{
uint8_t v___x_2758_; 
v___x_2758_ = 0;
return v___x_2758_;
}
else
{
lean_object* v_key_2759_; lean_object* v_tail_2760_; uint8_t v___x_2761_; 
v_key_2759_ = lean_ctor_get(v_x_2757_, 0);
v_tail_2760_ = lean_ctor_get(v_x_2757_, 2);
v___x_2761_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2759_, v_a_2756_);
if (v___x_2761_ == 0)
{
v_x_2757_ = v_tail_2760_;
goto _start;
}
else
{
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg___boxed(lean_object* v_a_2763_, lean_object* v_x_2764_){
_start:
{
uint8_t v_res_2765_; lean_object* v_r_2766_; 
v_res_2765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2763_, v_x_2764_);
lean_dec(v_x_2764_);
lean_dec_ref(v_a_2763_);
v_r_2766_ = lean_box(v_res_2765_);
return v_r_2766_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(lean_object* v_m_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v_buckets_2769_; lean_object* v___x_2770_; uint64_t v___x_2771_; uint64_t v___x_2772_; uint64_t v___x_2773_; uint64_t v_fold_2774_; uint64_t v___x_2775_; uint64_t v___x_2776_; uint64_t v___x_2777_; size_t v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; size_t v___x_2781_; size_t v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_buckets_2769_ = lean_ctor_get(v_m_2767_, 1);
v___x_2770_ = lean_array_get_size(v_buckets_2769_);
v___x_2771_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2768_);
v___x_2772_ = 32ULL;
v___x_2773_ = lean_uint64_shift_right(v___x_2771_, v___x_2772_);
v_fold_2774_ = lean_uint64_xor(v___x_2771_, v___x_2773_);
v___x_2775_ = 16ULL;
v___x_2776_ = lean_uint64_shift_right(v_fold_2774_, v___x_2775_);
v___x_2777_ = lean_uint64_xor(v_fold_2774_, v___x_2776_);
v___x_2778_ = lean_uint64_to_usize(v___x_2777_);
v___x_2779_ = lean_usize_of_nat(v___x_2770_);
v___x_2780_ = ((size_t)1ULL);
v___x_2781_ = lean_usize_sub(v___x_2779_, v___x_2780_);
v___x_2782_ = lean_usize_land(v___x_2778_, v___x_2781_);
v___x_2783_ = lean_array_uget_borrowed(v_buckets_2769_, v___x_2782_);
v___x_2784_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2768_, v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg___boxed(lean_object* v_m_2785_, lean_object* v_a_2786_){
_start:
{
uint8_t v_res_2787_; lean_object* v_r_2788_; 
v_res_2787_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2785_, v_a_2786_);
lean_dec_ref(v_a_2786_);
lean_dec_ref(v_m_2785_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(lean_object* v_idMap_2789_, lean_object* v_a_2790_){
_start:
{
uint8_t v___x_2791_; 
v___x_2791_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_idMap_2789_, v_a_2790_);
if (v___x_2791_ == 0)
{
return v_a_2790_;
}
else
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_idMap_2789_, v_a_2790_);
lean_dec_ref(v_a_2790_);
v_a_2790_ = v___x_2792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg___boxed(lean_object* v_idMap_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2794_, v_a_2795_);
lean_dec_ref(v_idMap_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object* v_idMap_2797_, lean_object* v_id_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2797_, v_id_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object* v_idMap_2800_, lean_object* v_id_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(v_idMap_2800_, v_id_2801_);
lean_dec_ref(v_idMap_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object* v_00_u03b2_2803_, lean_object* v_m_2804_, lean_object* v_a_2805_){
_start:
{
uint8_t v___x_2806_; 
v___x_2806_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2804_, v_a_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object* v_00_u03b2_2807_, lean_object* v_m_2808_, lean_object* v_a_2809_){
_start:
{
uint8_t v_res_2810_; lean_object* v_r_2811_; 
v_res_2810_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(v_00_u03b2_2807_, v_m_2808_, v_a_2809_);
lean_dec_ref(v_a_2809_);
lean_dec_ref(v_m_2808_);
v_r_2811_ = lean_box(v_res_2810_);
return v_r_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object* v_00_u03b2_2812_, lean_object* v_m_2813_, lean_object* v_a_2814_, lean_object* v_hma_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2813_, v_a_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object* v_00_u03b2_2817_, lean_object* v_m_2818_, lean_object* v_a_2819_, lean_object* v_hma_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(v_00_u03b2_2817_, v_m_2818_, v_a_2819_, v_hma_2820_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_m_2818_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object* v_idMap_2822_, lean_object* v_inst_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2822_, v_a_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object* v_idMap_2826_, lean_object* v_inst_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2826_, v_inst_2827_, v_a_2828_);
lean_dec_ref(v_idMap_2826_);
return v_res_2829_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(lean_object* v_00_u03b2_2830_, lean_object* v_a_2831_, lean_object* v_x_2832_){
_start:
{
uint8_t v___x_2833_; 
v___x_2833_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2831_, v_x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2834_, lean_object* v_a_2835_, lean_object* v_x_2836_){
_start:
{
uint8_t v_res_2837_; lean_object* v_r_2838_; 
v_res_2837_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(v_00_u03b2_2834_, v_a_2835_, v_x_2836_);
lean_dec(v_x_2836_);
lean_dec_ref(v_a_2835_);
v_r_2838_ = lean_box(v_res_2837_);
return v_r_2838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(lean_object* v_00_u03b2_2839_, lean_object* v_a_2840_, lean_object* v_x_2841_, lean_object* v_x_2842_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2840_, v_x_2841_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2844_, lean_object* v_a_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(v_00_u03b2_2844_, v_a_2845_, v_x_2846_, v_x_2847_);
lean_dec(v_x_2846_);
lean_dec_ref(v_a_2845_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
if (lean_obj_tag(v_a_2849_) == 0)
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v_a_2850_);
return v___x_2851_;
}
else
{
if (lean_obj_tag(v_a_2850_) == 0)
{
lean_object* v_tail_2852_; 
v_tail_2852_ = lean_ctor_get(v_a_2849_, 2);
lean_inc(v_tail_2852_);
lean_dec_ref_known(v_a_2849_, 3);
v_a_2849_ = v_tail_2852_;
goto _start;
}
else
{
lean_object* v_key_2854_; 
v_key_2854_ = lean_ctor_get(v_a_2849_, 0);
if (lean_obj_tag(v_key_2854_) == 0)
{
lean_object* v_tail_2855_; 
lean_inc_ref(v_key_2854_);
lean_dec_ref_known(v_a_2850_, 2);
v_tail_2855_ = lean_ctor_get(v_a_2849_, 2);
lean_inc(v_tail_2855_);
lean_dec_ref_known(v_a_2849_, 3);
v_a_2849_ = v_tail_2855_;
v_a_2850_ = v_key_2854_;
goto _start;
}
else
{
lean_object* v_tail_2857_; 
v_tail_2857_ = lean_ctor_get(v_a_2849_, 2);
lean_inc(v_tail_2857_);
lean_dec_ref_known(v_a_2849_, 3);
v_a_2849_ = v_tail_2857_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(lean_object* v_as_2859_, size_t v_sz_2860_, size_t v_i_2861_, lean_object* v_b_2862_){
_start:
{
uint8_t v___x_2863_; 
v___x_2863_ = lean_usize_dec_lt(v_i_2861_, v_sz_2860_);
if (v___x_2863_ == 0)
{
return v_b_2862_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2865_; 
v_a_2864_ = lean_array_uget_borrowed(v_as_2859_, v_i_2861_);
lean_inc(v_a_2864_);
v___x_2865_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(v_a_2864_, v_b_2862_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
return v_a_2866_;
}
else
{
lean_object* v_a_2867_; size_t v___x_2868_; size_t v___x_2869_; 
v_a_2867_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2868_ = ((size_t)1ULL);
v___x_2869_ = lean_usize_add(v_i_2861_, v___x_2868_);
v_i_2861_ = v___x_2869_;
v_b_2862_ = v_a_2867_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5___boxed(lean_object* v_as_2871_, lean_object* v_sz_2872_, lean_object* v_i_2873_, lean_object* v_b_2874_){
_start:
{
size_t v_sz_boxed_2875_; size_t v_i_boxed_2876_; lean_object* v_res_2877_; 
v_sz_boxed_2875_ = lean_unbox_usize(v_sz_2872_);
lean_dec(v_sz_2872_);
v_i_boxed_2876_ = lean_unbox_usize(v_i_2873_);
lean_dec(v_i_2873_);
v_res_2877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_as_2871_, v_sz_boxed_2875_, v_i_boxed_2876_, v_b_2874_);
lean_dec_ref(v_as_2871_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(lean_object* v_a_2878_, lean_object* v_b_2879_, lean_object* v_x_2880_){
_start:
{
if (lean_obj_tag(v_x_2880_) == 0)
{
lean_dec(v_b_2879_);
lean_dec_ref(v_a_2878_);
return v_x_2880_;
}
else
{
lean_object* v_key_2881_; lean_object* v_value_2882_; lean_object* v_tail_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2895_; 
v_key_2881_ = lean_ctor_get(v_x_2880_, 0);
v_value_2882_ = lean_ctor_get(v_x_2880_, 1);
v_tail_2883_ = lean_ctor_get(v_x_2880_, 2);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_x_2880_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2885_ = v_x_2880_;
v_isShared_2886_ = v_isSharedCheck_2895_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_tail_2883_);
lean_inc(v_value_2882_);
lean_inc(v_key_2881_);
lean_dec(v_x_2880_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2895_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
uint8_t v___x_2887_; 
v___x_2887_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2881_, v_a_2878_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2878_, v_b_2879_, v_tail_2883_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 2, v___x_2888_);
v___x_2890_ = v___x_2885_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_key_2881_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_value_2882_);
lean_ctor_set(v_reuseFailAlloc_2891_, 2, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
else
{
lean_object* v___x_2893_; 
lean_dec(v_value_2882_);
lean_dec(v_key_2881_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v_b_2879_);
lean_ctor_set(v___x_2885_, 0, v_a_2878_);
v___x_2893_ = v___x_2885_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2878_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_b_2879_);
lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_tail_2883_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(lean_object* v_x_2896_, lean_object* v_x_2897_){
_start:
{
if (lean_obj_tag(v_x_2897_) == 0)
{
return v_x_2896_;
}
else
{
lean_object* v_key_2898_; lean_object* v_value_2899_; lean_object* v_tail_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2923_; 
v_key_2898_ = lean_ctor_get(v_x_2897_, 0);
v_value_2899_ = lean_ctor_get(v_x_2897_, 1);
v_tail_2900_ = lean_ctor_get(v_x_2897_, 2);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_x_2897_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2902_ = v_x_2897_;
v_isShared_2903_ = v_isSharedCheck_2923_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_tail_2900_);
lean_inc(v_value_2899_);
lean_inc(v_key_2898_);
lean_dec(v_x_2897_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2923_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; uint64_t v___x_2905_; uint64_t v___x_2906_; uint64_t v___x_2907_; uint64_t v_fold_2908_; uint64_t v___x_2909_; uint64_t v___x_2910_; uint64_t v___x_2911_; size_t v___x_2912_; size_t v___x_2913_; size_t v___x_2914_; size_t v___x_2915_; size_t v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2919_; 
v___x_2904_ = lean_array_get_size(v_x_2896_);
v___x_2905_ = l_Lean_Lsp_instHashableRefIdent_hash(v_key_2898_);
v___x_2906_ = 32ULL;
v___x_2907_ = lean_uint64_shift_right(v___x_2905_, v___x_2906_);
v_fold_2908_ = lean_uint64_xor(v___x_2905_, v___x_2907_);
v___x_2909_ = 16ULL;
v___x_2910_ = lean_uint64_shift_right(v_fold_2908_, v___x_2909_);
v___x_2911_ = lean_uint64_xor(v_fold_2908_, v___x_2910_);
v___x_2912_ = lean_uint64_to_usize(v___x_2911_);
v___x_2913_ = lean_usize_of_nat(v___x_2904_);
v___x_2914_ = ((size_t)1ULL);
v___x_2915_ = lean_usize_sub(v___x_2913_, v___x_2914_);
v___x_2916_ = lean_usize_land(v___x_2912_, v___x_2915_);
v___x_2917_ = lean_array_uget_borrowed(v_x_2896_, v___x_2916_);
lean_inc(v___x_2917_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 2, v___x_2917_);
v___x_2919_ = v___x_2902_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_key_2898_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_value_2899_);
lean_ctor_set(v_reuseFailAlloc_2922_, 2, v___x_2917_);
v___x_2919_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_array_uset(v_x_2896_, v___x_2916_, v___x_2919_);
v_x_2896_ = v___x_2920_;
v_x_2897_ = v_tail_2900_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(lean_object* v_i_2924_, lean_object* v_source_2925_, lean_object* v_target_2926_){
_start:
{
lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2927_ = lean_array_get_size(v_source_2925_);
v___x_2928_ = lean_nat_dec_lt(v_i_2924_, v___x_2927_);
if (v___x_2928_ == 0)
{
lean_dec_ref(v_source_2925_);
lean_dec(v_i_2924_);
return v_target_2926_;
}
else
{
lean_object* v_es_2929_; lean_object* v___x_2930_; lean_object* v_source_2931_; lean_object* v_target_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_es_2929_ = lean_array_fget(v_source_2925_, v_i_2924_);
v___x_2930_ = lean_box(0);
v_source_2931_ = lean_array_fset(v_source_2925_, v_i_2924_, v___x_2930_);
v_target_2932_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_target_2926_, v_es_2929_);
v___x_2933_ = lean_unsigned_to_nat(1u);
v___x_2934_ = lean_nat_add(v_i_2924_, v___x_2933_);
lean_dec(v_i_2924_);
v_i_2924_ = v___x_2934_;
v_source_2925_ = v_source_2931_;
v_target_2926_ = v_target_2932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(lean_object* v_data_2936_){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v_nbuckets_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2937_ = lean_array_get_size(v_data_2936_);
v___x_2938_ = lean_unsigned_to_nat(2u);
v_nbuckets_2939_ = lean_nat_mul(v___x_2937_, v___x_2938_);
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_mk_array(v_nbuckets_2939_, v___x_2941_);
v___x_2943_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2940_, v_data_2936_, v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object* v_m_2944_, lean_object* v_a_2945_, lean_object* v_b_2946_){
_start:
{
lean_object* v_size_2947_; lean_object* v_buckets_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2991_; 
v_size_2947_ = lean_ctor_get(v_m_2944_, 0);
v_buckets_2948_ = lean_ctor_get(v_m_2944_, 1);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_m_2944_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2950_ = v_m_2944_;
v_isShared_2951_ = v_isSharedCheck_2991_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_buckets_2948_);
lean_inc(v_size_2947_);
lean_dec(v_m_2944_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2991_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; uint64_t v___x_2953_; uint64_t v___x_2954_; uint64_t v___x_2955_; uint64_t v_fold_2956_; uint64_t v___x_2957_; uint64_t v___x_2958_; uint64_t v___x_2959_; size_t v___x_2960_; size_t v___x_2961_; size_t v___x_2962_; size_t v___x_2963_; size_t v___x_2964_; lean_object* v_bkt_2965_; uint8_t v___x_2966_; 
v___x_2952_ = lean_array_get_size(v_buckets_2948_);
v___x_2953_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2945_);
v___x_2954_ = 32ULL;
v___x_2955_ = lean_uint64_shift_right(v___x_2953_, v___x_2954_);
v_fold_2956_ = lean_uint64_xor(v___x_2953_, v___x_2955_);
v___x_2957_ = 16ULL;
v___x_2958_ = lean_uint64_shift_right(v_fold_2956_, v___x_2957_);
v___x_2959_ = lean_uint64_xor(v_fold_2956_, v___x_2958_);
v___x_2960_ = lean_uint64_to_usize(v___x_2959_);
v___x_2961_ = lean_usize_of_nat(v___x_2952_);
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_sub(v___x_2961_, v___x_2962_);
v___x_2964_ = lean_usize_land(v___x_2960_, v___x_2963_);
v_bkt_2965_ = lean_array_uget_borrowed(v_buckets_2948_, v___x_2964_);
v___x_2966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2945_, v_bkt_2965_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; lean_object* v_size_x27_2968_; lean_object* v___x_2969_; lean_object* v_buckets_x27_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v___x_2967_ = lean_unsigned_to_nat(1u);
v_size_x27_2968_ = lean_nat_add(v_size_2947_, v___x_2967_);
lean_dec(v_size_2947_);
lean_inc(v_bkt_2965_);
v___x_2969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2969_, 0, v_a_2945_);
lean_ctor_set(v___x_2969_, 1, v_b_2946_);
lean_ctor_set(v___x_2969_, 2, v_bkt_2965_);
v_buckets_x27_2970_ = lean_array_uset(v_buckets_2948_, v___x_2964_, v___x_2969_);
v___x_2971_ = lean_unsigned_to_nat(4u);
v___x_2972_ = lean_nat_mul(v_size_x27_2968_, v___x_2971_);
v___x_2973_ = lean_unsigned_to_nat(3u);
v___x_2974_ = lean_nat_div(v___x_2972_, v___x_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_array_get_size(v_buckets_x27_2970_);
v___x_2976_ = lean_nat_dec_le(v___x_2974_, v___x_2975_);
lean_dec(v___x_2974_);
if (v___x_2976_ == 0)
{
lean_object* v_val_2977_; lean_object* v___x_2979_; 
v_val_2977_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_2970_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v_val_2977_);
lean_ctor_set(v___x_2950_, 0, v_size_x27_2968_);
v___x_2979_ = v___x_2950_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_size_x27_2968_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_val_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
else
{
lean_object* v___x_2982_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v_buckets_x27_2970_);
lean_ctor_set(v___x_2950_, 0, v_size_x27_2968_);
v___x_2982_ = v___x_2950_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_size_x27_2968_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_buckets_x27_2970_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
else
{
lean_object* v___x_2984_; lean_object* v_buckets_x27_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
lean_inc(v_bkt_2965_);
v___x_2984_ = lean_box(0);
v_buckets_x27_2985_ = lean_array_uset(v_buckets_2948_, v___x_2964_, v___x_2984_);
v___x_2986_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2945_, v_b_2946_, v_bkt_2965_);
v___x_2987_ = lean_array_uset(v_buckets_x27_2985_, v___x_2964_, v___x_2986_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v___x_2987_);
v___x_2989_ = v___x_2950_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_size_2947_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object* v___x_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
if (lean_obj_tag(v_a_2993_) == 0)
{
lean_object* v___x_2995_; 
lean_dec_ref(v___x_2992_);
v___x_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2995_, 0, v_a_2994_);
return v___x_2995_;
}
else
{
lean_object* v_key_2996_; lean_object* v_tail_2997_; uint8_t v___x_2998_; 
v_key_2996_ = lean_ctor_get(v_a_2993_, 0);
lean_inc(v_key_2996_);
v_tail_2997_ = lean_ctor_get(v_a_2993_, 2);
lean_inc(v_tail_2997_);
lean_dec_ref_known(v_a_2993_, 3);
v___x_2998_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2996_, v___x_2992_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; 
lean_inc_ref(v___x_2992_);
v___x_2999_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_2994_, v_key_2996_, v___x_2992_);
v_a_2993_ = v_tail_2997_;
v_a_2994_ = v___x_2999_;
goto _start;
}
else
{
lean_dec(v_key_2996_);
v_a_2993_ = v_tail_2997_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object* v___x_3002_, lean_object* v_as_3003_, size_t v_sz_3004_, size_t v_i_3005_, lean_object* v_b_3006_){
_start:
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_usize_dec_lt(v_i_3005_, v_sz_3004_);
if (v___x_3007_ == 0)
{
lean_dec_ref(v___x_3002_);
return v_b_3006_;
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3009_; 
v_a_3008_ = lean_array_uget_borrowed(v_as_3003_, v_i_3005_);
lean_inc(v_a_3008_);
lean_inc_ref(v___x_3002_);
v___x_3009_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(v___x_3002_, v_a_3008_, v_b_3006_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; 
lean_dec_ref(v___x_3002_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
return v_a_3010_;
}
else
{
lean_object* v_a_3011_; size_t v___x_3012_; size_t v___x_3013_; 
v_a_3011_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3012_ = ((size_t)1ULL);
v___x_3013_ = lean_usize_add(v_i_3005_, v___x_3012_);
v_i_3005_ = v___x_3013_;
v_b_3006_ = v_a_3011_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object* v___x_3015_, lean_object* v_as_3016_, lean_object* v_sz_3017_, lean_object* v_i_3018_, lean_object* v_b_3019_){
_start:
{
size_t v_sz_boxed_3020_; size_t v_i_boxed_3021_; lean_object* v_res_3022_; 
v_sz_boxed_3020_ = lean_unbox_usize(v_sz_3017_);
lean_dec(v_sz_3017_);
v_i_boxed_3021_ = lean_unbox_usize(v_i_3018_);
lean_dec(v_i_3018_);
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3015_, v_as_3016_, v_sz_boxed_3020_, v_i_boxed_3021_, v_b_3019_);
lean_dec_ref(v_as_3016_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
if (lean_obj_tag(v_a_3023_) == 0)
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_a_3024_);
return v___x_3025_;
}
else
{
lean_object* v_value_3026_; lean_object* v_key_3027_; lean_object* v_tail_3028_; lean_object* v_buckets_3029_; size_t v_sz_3030_; size_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_value_3026_ = lean_ctor_get(v_a_3023_, 1);
lean_inc(v_value_3026_);
v_key_3027_ = lean_ctor_get(v_a_3023_, 0);
lean_inc(v_key_3027_);
v_tail_3028_ = lean_ctor_get(v_a_3023_, 2);
lean_inc(v_tail_3028_);
lean_dec_ref_known(v_a_3023_, 3);
v_buckets_3029_ = lean_ctor_get(v_value_3026_, 1);
lean_inc_ref(v_buckets_3029_);
lean_dec(v_value_3026_);
v_sz_3030_ = lean_array_size(v_buckets_3029_);
v___x_3031_ = ((size_t)0ULL);
v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_buckets_3029_, v_sz_3030_, v___x_3031_, v_key_3027_);
v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3032_, v_buckets_3029_, v_sz_3030_, v___x_3031_, v_a_3024_);
lean_dec_ref(v_buckets_3029_);
v_a_3023_ = v_tail_3028_;
v_a_3024_ = v___x_3033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object* v_as_3035_, size_t v_sz_3036_, size_t v_i_3037_, lean_object* v_b_3038_){
_start:
{
uint8_t v___x_3039_; 
v___x_3039_ = lean_usize_dec_lt(v_i_3037_, v_sz_3036_);
if (v___x_3039_ == 0)
{
return v_b_3038_;
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3041_; 
v_a_3040_ = lean_array_uget_borrowed(v_as_3035_, v_i_3037_);
lean_inc(v_a_3040_);
v___x_3041_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(v_a_3040_, v_b_3038_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3041_, 1);
return v_a_3042_;
}
else
{
lean_object* v_a_3043_; size_t v___x_3044_; size_t v___x_3045_; 
v_a_3043_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3044_ = ((size_t)1ULL);
v___x_3045_ = lean_usize_add(v_i_3037_, v___x_3044_);
v_i_3037_ = v___x_3045_;
v_b_3038_ = v_a_3043_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object* v_as_3047_, lean_object* v_sz_3048_, lean_object* v_i_3049_, lean_object* v_b_3050_){
_start:
{
size_t v_sz_boxed_3051_; size_t v_i_boxed_3052_; lean_object* v_res_3053_; 
v_sz_boxed_3051_ = lean_unbox_usize(v_sz_3048_);
lean_dec(v_sz_3048_);
v_i_boxed_3052_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_res_3053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_as_3047_, v_sz_boxed_3051_, v_i_boxed_3052_, v_b_3050_);
lean_dec_ref(v_as_3047_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object* v_a_3054_, lean_object* v_x_3055_){
_start:
{
if (lean_obj_tag(v_x_3055_) == 0)
{
return v_x_3055_;
}
else
{
lean_object* v_key_3056_; lean_object* v_value_3057_; lean_object* v_tail_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3067_; 
v_key_3056_ = lean_ctor_get(v_x_3055_, 0);
v_value_3057_ = lean_ctor_get(v_x_3055_, 1);
v_tail_3058_ = lean_ctor_get(v_x_3055_, 2);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_x_3055_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3060_ = v_x_3055_;
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_tail_3058_);
lean_inc(v_value_3057_);
lean_inc(v_key_3056_);
lean_dec(v_x_3055_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3056_, v_a_3054_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3054_, v_tail_3058_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 2, v___x_3063_);
v___x_3065_ = v___x_3060_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_key_3056_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_value_3057_);
lean_ctor_set(v_reuseFailAlloc_3066_, 2, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
else
{
lean_del_object(v___x_3060_);
lean_dec(v_value_3057_);
lean_dec(v_key_3056_);
return v_tail_3058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object* v_a_3068_, lean_object* v_x_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3068_, v_x_3069_);
lean_dec_ref(v_a_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object* v_m_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_size_3073_; lean_object* v_buckets_3074_; lean_object* v___x_3075_; uint64_t v___x_3076_; uint64_t v___x_3077_; uint64_t v___x_3078_; uint64_t v_fold_3079_; uint64_t v___x_3080_; uint64_t v___x_3081_; uint64_t v___x_3082_; size_t v___x_3083_; size_t v___x_3084_; size_t v___x_3085_; size_t v___x_3086_; size_t v___x_3087_; lean_object* v_bkt_3088_; uint8_t v___x_3089_; 
v_size_3073_ = lean_ctor_get(v_m_3071_, 0);
v_buckets_3074_ = lean_ctor_get(v_m_3071_, 1);
v___x_3075_ = lean_array_get_size(v_buckets_3074_);
v___x_3076_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3072_);
v___x_3077_ = 32ULL;
v___x_3078_ = lean_uint64_shift_right(v___x_3076_, v___x_3077_);
v_fold_3079_ = lean_uint64_xor(v___x_3076_, v___x_3078_);
v___x_3080_ = 16ULL;
v___x_3081_ = lean_uint64_shift_right(v_fold_3079_, v___x_3080_);
v___x_3082_ = lean_uint64_xor(v_fold_3079_, v___x_3081_);
v___x_3083_ = lean_uint64_to_usize(v___x_3082_);
v___x_3084_ = lean_usize_of_nat(v___x_3075_);
v___x_3085_ = ((size_t)1ULL);
v___x_3086_ = lean_usize_sub(v___x_3084_, v___x_3085_);
v___x_3087_ = lean_usize_land(v___x_3083_, v___x_3086_);
v_bkt_3088_ = lean_array_uget_borrowed(v_buckets_3074_, v___x_3087_);
v___x_3089_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3072_, v_bkt_3088_);
if (v___x_3089_ == 0)
{
return v_m_3071_;
}
else
{
lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3102_; 
lean_inc(v_bkt_3088_);
lean_inc_ref(v_buckets_3074_);
lean_inc(v_size_3073_);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_m_3071_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; lean_object* v_unused_3104_; 
v_unused_3103_ = lean_ctor_get(v_m_3071_, 1);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v_m_3071_, 0);
lean_dec(v_unused_3104_);
v___x_3091_ = v_m_3071_;
v_isShared_3092_ = v_isSharedCheck_3102_;
goto v_resetjp_3090_;
}
else
{
lean_dec(v_m_3071_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3102_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v_buckets_x27_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3093_ = lean_box(0);
v_buckets_x27_3094_ = lean_array_uset(v_buckets_3074_, v___x_3087_, v___x_3093_);
v___x_3095_ = lean_unsigned_to_nat(1u);
v___x_3096_ = lean_nat_sub(v_size_3073_, v___x_3095_);
lean_dec(v_size_3073_);
v___x_3097_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3072_, v_bkt_3088_);
v___x_3098_ = lean_array_uset(v_buckets_x27_3094_, v___x_3087_, v___x_3097_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 1, v___x_3098_);
lean_ctor_set(v___x_3091_, 0, v___x_3096_);
v___x_3100_ = v___x_3091_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object* v_m_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3105_, v_a_3106_);
lean_dec_ref(v_a_3106_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object* v_m_3108_, lean_object* v_a_3109_, lean_object* v_b_3110_){
_start:
{
lean_object* v_size_3111_; lean_object* v_buckets_3112_; lean_object* v___x_3113_; uint64_t v___x_3114_; uint64_t v___x_3115_; uint64_t v___x_3116_; uint64_t v_fold_3117_; uint64_t v___x_3118_; uint64_t v___x_3119_; uint64_t v___x_3120_; size_t v___x_3121_; size_t v___x_3122_; size_t v___x_3123_; size_t v___x_3124_; size_t v___x_3125_; lean_object* v_bkt_3126_; uint8_t v___x_3127_; 
v_size_3111_ = lean_ctor_get(v_m_3108_, 0);
v_buckets_3112_ = lean_ctor_get(v_m_3108_, 1);
v___x_3113_ = lean_array_get_size(v_buckets_3112_);
v___x_3114_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3109_);
v___x_3115_ = 32ULL;
v___x_3116_ = lean_uint64_shift_right(v___x_3114_, v___x_3115_);
v_fold_3117_ = lean_uint64_xor(v___x_3114_, v___x_3116_);
v___x_3118_ = 16ULL;
v___x_3119_ = lean_uint64_shift_right(v_fold_3117_, v___x_3118_);
v___x_3120_ = lean_uint64_xor(v_fold_3117_, v___x_3119_);
v___x_3121_ = lean_uint64_to_usize(v___x_3120_);
v___x_3122_ = lean_usize_of_nat(v___x_3113_);
v___x_3123_ = ((size_t)1ULL);
v___x_3124_ = lean_usize_sub(v___x_3122_, v___x_3123_);
v___x_3125_ = lean_usize_land(v___x_3121_, v___x_3124_);
v_bkt_3126_ = lean_array_uget_borrowed(v_buckets_3112_, v___x_3125_);
v___x_3127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3109_, v_bkt_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3148_; 
lean_inc_ref(v_buckets_3112_);
lean_inc(v_size_3111_);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_m_3108_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; lean_object* v_unused_3150_; 
v_unused_3149_ = lean_ctor_get(v_m_3108_, 1);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_m_3108_, 0);
lean_dec(v_unused_3150_);
v___x_3129_ = v_m_3108_;
v_isShared_3130_ = v_isSharedCheck_3148_;
goto v_resetjp_3128_;
}
else
{
lean_dec(v_m_3108_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3148_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; lean_object* v_size_x27_3132_; lean_object* v___x_3133_; lean_object* v_buckets_x27_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; uint8_t v___x_3140_; 
v___x_3131_ = lean_unsigned_to_nat(1u);
v_size_x27_3132_ = lean_nat_add(v_size_3111_, v___x_3131_);
lean_dec(v_size_3111_);
lean_inc(v_bkt_3126_);
v___x_3133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3133_, 0, v_a_3109_);
lean_ctor_set(v___x_3133_, 1, v_b_3110_);
lean_ctor_set(v___x_3133_, 2, v_bkt_3126_);
v_buckets_x27_3134_ = lean_array_uset(v_buckets_3112_, v___x_3125_, v___x_3133_);
v___x_3135_ = lean_unsigned_to_nat(4u);
v___x_3136_ = lean_nat_mul(v_size_x27_3132_, v___x_3135_);
v___x_3137_ = lean_unsigned_to_nat(3u);
v___x_3138_ = lean_nat_div(v___x_3136_, v___x_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_array_get_size(v_buckets_x27_3134_);
v___x_3140_ = lean_nat_dec_le(v___x_3138_, v___x_3139_);
lean_dec(v___x_3138_);
if (v___x_3140_ == 0)
{
lean_object* v_val_3141_; lean_object* v___x_3143_; 
v_val_3141_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3134_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 1, v_val_3141_);
lean_ctor_set(v___x_3129_, 0, v_size_x27_3132_);
v___x_3143_ = v___x_3129_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_size_x27_3132_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_val_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
else
{
lean_object* v___x_3146_; 
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 1, v_buckets_x27_3134_);
lean_ctor_set(v___x_3129_, 0, v_size_x27_3132_);
v___x_3146_ = v___x_3129_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_size_x27_3132_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_buckets_x27_3134_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_dec(v_b_3110_);
lean_dec_ref(v_a_3109_);
return v_m_3108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object* v_a_3151_, lean_object* v_fallback_3152_, lean_object* v_x_3153_){
_start:
{
if (lean_obj_tag(v_x_3153_) == 0)
{
lean_inc(v_fallback_3152_);
return v_fallback_3152_;
}
else
{
lean_object* v_key_3154_; lean_object* v_value_3155_; lean_object* v_tail_3156_; uint8_t v___x_3157_; 
v_key_3154_ = lean_ctor_get(v_x_3153_, 0);
v_value_3155_ = lean_ctor_get(v_x_3153_, 1);
v_tail_3156_ = lean_ctor_get(v_x_3153_, 2);
v___x_3157_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3154_, v_a_3151_);
if (v___x_3157_ == 0)
{
v_x_3153_ = v_tail_3156_;
goto _start;
}
else
{
lean_inc(v_value_3155_);
return v_value_3155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object* v_a_3159_, lean_object* v_fallback_3160_, lean_object* v_x_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3159_, v_fallback_3160_, v_x_3161_);
lean_dec(v_x_3161_);
lean_dec(v_fallback_3160_);
lean_dec_ref(v_a_3159_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object* v_m_3163_, lean_object* v_a_3164_, lean_object* v_fallback_3165_){
_start:
{
lean_object* v_buckets_3166_; lean_object* v___x_3167_; uint64_t v___x_3168_; uint64_t v___x_3169_; uint64_t v___x_3170_; uint64_t v_fold_3171_; uint64_t v___x_3172_; uint64_t v___x_3173_; uint64_t v___x_3174_; size_t v___x_3175_; size_t v___x_3176_; size_t v___x_3177_; size_t v___x_3178_; size_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_buckets_3166_ = lean_ctor_get(v_m_3163_, 1);
v___x_3167_ = lean_array_get_size(v_buckets_3166_);
v___x_3168_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3164_);
v___x_3169_ = 32ULL;
v___x_3170_ = lean_uint64_shift_right(v___x_3168_, v___x_3169_);
v_fold_3171_ = lean_uint64_xor(v___x_3168_, v___x_3170_);
v___x_3172_ = 16ULL;
v___x_3173_ = lean_uint64_shift_right(v_fold_3171_, v___x_3172_);
v___x_3174_ = lean_uint64_xor(v_fold_3171_, v___x_3173_);
v___x_3175_ = lean_uint64_to_usize(v___x_3174_);
v___x_3176_ = lean_usize_of_nat(v___x_3167_);
v___x_3177_ = ((size_t)1ULL);
v___x_3178_ = lean_usize_sub(v___x_3176_, v___x_3177_);
v___x_3179_ = lean_usize_land(v___x_3175_, v___x_3178_);
v___x_3180_ = lean_array_uget_borrowed(v_buckets_3166_, v___x_3179_);
v___x_3181_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3164_, v_fallback_3165_, v___x_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object* v_m_3182_, lean_object* v_a_3183_, lean_object* v_fallback_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3182_, v_a_3183_, v_fallback_3184_);
lean_dec(v_fallback_3184_);
lean_dec_ref(v_a_3183_);
lean_dec_ref(v_m_3182_);
return v_res_3185_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = lean_box(0);
v___x_3187_ = lean_unsigned_to_nat(16u);
v___x_3188_ = lean_mk_array(v___x_3187_, v___x_3186_);
return v___x_3188_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0);
v___x_3190_ = lean_unsigned_to_nat(0u);
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v___x_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object* v_idMap_3192_, lean_object* v_classesById_3193_, lean_object* v_id_3194_){
_start:
{
lean_object* v_representative_3195_; lean_object* v___x_3196_; lean_object* v_class_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v_class_3200_; lean_object* v___x_3201_; 
lean_inc_ref(v_id_3194_);
v_representative_3195_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_3192_, v_id_3194_);
v___x_3196_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_class_3197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_classesById_3193_, v_representative_3195_, v___x_3196_);
v___x_3198_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_classesById_3193_, v_representative_3195_);
v___x_3199_ = lean_box(0);
v_class_3200_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_class_3197_, v_id_3194_, v___x_3199_);
v___x_3201_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v___x_3198_, v_representative_3195_, v_class_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object* v_idMap_3202_, lean_object* v_classesById_3203_, lean_object* v_id_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3202_, v_classesById_3203_, v_id_3204_);
lean_dec_ref(v_idMap_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object* v_idMap_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_){
_start:
{
if (lean_obj_tag(v_a_3207_) == 0)
{
lean_object* v___x_3209_; 
v___x_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3209_, 0, v_a_3208_);
return v___x_3209_;
}
else
{
lean_object* v_key_3210_; lean_object* v_value_3211_; lean_object* v_tail_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_key_3210_ = lean_ctor_get(v_a_3207_, 0);
lean_inc(v_key_3210_);
v_value_3211_ = lean_ctor_get(v_a_3207_, 1);
lean_inc(v_value_3211_);
v_tail_3212_ = lean_ctor_get(v_a_3207_, 2);
lean_inc(v_tail_3212_);
lean_dec_ref_known(v_a_3207_, 3);
v___x_3213_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3206_, v_a_3208_, v_key_3210_);
v___x_3214_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3206_, v___x_3213_, v_value_3211_);
v_a_3207_ = v_tail_3212_;
v_a_3208_ = v___x_3214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object* v_idMap_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3216_, v_a_3217_, v_a_3218_);
lean_dec_ref(v_idMap_3216_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object* v_idMap_3220_, lean_object* v_as_3221_, size_t v_sz_3222_, size_t v_i_3223_, lean_object* v_b_3224_){
_start:
{
uint8_t v___x_3225_; 
v___x_3225_ = lean_usize_dec_lt(v_i_3223_, v_sz_3222_);
if (v___x_3225_ == 0)
{
return v_b_3224_;
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3227_; 
v_a_3226_ = lean_array_uget_borrowed(v_as_3221_, v_i_3223_);
lean_inc(v_a_3226_);
v___x_3227_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3220_, v_a_3226_, v_b_3224_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3227_, 1);
return v_a_3228_;
}
else
{
lean_object* v_a_3229_; size_t v___x_3230_; size_t v___x_3231_; 
v_a_3229_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3227_, 1);
v___x_3230_ = ((size_t)1ULL);
v___x_3231_ = lean_usize_add(v_i_3223_, v___x_3230_);
v_i_3223_ = v___x_3231_;
v_b_3224_ = v_a_3229_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object* v_idMap_3233_, lean_object* v_as_3234_, lean_object* v_sz_3235_, lean_object* v_i_3236_, lean_object* v_b_3237_){
_start:
{
size_t v_sz_boxed_3238_; size_t v_i_boxed_3239_; lean_object* v_res_3240_; 
v_sz_boxed_3238_ = lean_unbox_usize(v_sz_3235_);
lean_dec(v_sz_3235_);
v_i_boxed_3239_ = lean_unbox_usize(v_i_3236_);
lean_dec(v_i_3236_);
v_res_3240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3233_, v_as_3234_, v_sz_boxed_3238_, v_i_boxed_3239_, v_b_3237_);
lean_dec_ref(v_as_3234_);
lean_dec_ref(v_idMap_3233_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object* v_idMap_3241_){
_start:
{
lean_object* v_buckets_3242_; lean_object* v_classesById_3243_; size_t v_sz_3244_; size_t v___x_3245_; lean_object* v___x_3246_; lean_object* v_buckets_3247_; size_t v_sz_3248_; lean_object* v___x_3249_; 
v_buckets_3242_ = lean_ctor_get(v_idMap_3241_, 1);
v_classesById_3243_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_sz_3244_ = lean_array_size(v_buckets_3242_);
v___x_3245_ = ((size_t)0ULL);
v___x_3246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3241_, v_buckets_3242_, v_sz_3244_, v___x_3245_, v_classesById_3243_);
v_buckets_3247_ = lean_ctor_get(v___x_3246_, 1);
lean_inc_ref(v_buckets_3247_);
lean_dec_ref(v___x_3246_);
v_sz_3248_ = lean_array_size(v_buckets_3247_);
v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_buckets_3247_, v_sz_3248_, v___x_3245_, v_classesById_3243_);
lean_dec_ref(v_buckets_3247_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object* v_idMap_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v_idMap_3250_);
lean_dec_ref(v_idMap_3250_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object* v_00_u03b2_3252_, lean_object* v_m_3253_, lean_object* v_a_3254_, lean_object* v_fallback_3255_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3253_, v_a_3254_, v_fallback_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object* v_00_u03b2_3257_, lean_object* v_m_3258_, lean_object* v_a_3259_, lean_object* v_fallback_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(v_00_u03b2_3257_, v_m_3258_, v_a_3259_, v_fallback_3260_);
lean_dec(v_fallback_3260_);
lean_dec_ref(v_a_3259_);
lean_dec_ref(v_m_3258_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object* v_00_u03b2_3262_, lean_object* v_m_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3263_, v_a_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object* v_00_u03b2_3266_, lean_object* v_m_3267_, lean_object* v_a_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(v_00_u03b2_3266_, v_m_3267_, v_a_3268_);
lean_dec_ref(v_a_3268_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object* v_00_u03b2_3270_, lean_object* v_m_3271_, lean_object* v_a_3272_, lean_object* v_b_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_m_3271_, v_a_3272_, v_b_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object* v_00_u03b2_3275_, lean_object* v_m_3276_, lean_object* v_a_3277_, lean_object* v_b_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_m_3276_, v_a_3277_, v_b_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object* v_00_u03b2_3280_, lean_object* v_a_3281_, lean_object* v_fallback_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3281_, v_fallback_3282_, v_x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3285_, lean_object* v_a_3286_, lean_object* v_fallback_3287_, lean_object* v_x_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(v_00_u03b2_3285_, v_a_3286_, v_fallback_3287_, v_x_3288_);
lean_dec(v_x_3288_);
lean_dec(v_fallback_3287_);
lean_dec_ref(v_a_3286_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object* v_00_u03b2_3290_, lean_object* v_a_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3291_, v_x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3294_, lean_object* v_a_3295_, lean_object* v_x_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(v_00_u03b2_3294_, v_a_3295_, v_x_3296_);
lean_dec_ref(v_a_3295_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object* v_00_u03b2_3298_, lean_object* v_data_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_data_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object* v_00_u03b2_3301_, lean_object* v_a_3302_, lean_object* v_b_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_3302_, v_b_3303_, v_x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3306_, lean_object* v_i_3307_, lean_object* v_source_3308_, lean_object* v_target_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v_i_3307_, v_source_3308_, v_target_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object* v_00_u03b2_3311_, lean_object* v_x_3312_, lean_object* v_x_3313_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_x_3312_, v_x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object* v_id_3315_, lean_object* v_baseId_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3318_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3317_, v_id_3315_);
v___x_3319_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3317_, v_baseId_3316_);
v___x_3320_ = l_Lean_Lsp_instBEqRefIdent_beq(v___x_3319_, v___x_3318_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_box(0);
v___x_3322_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3317_, v___x_3318_, v___x_3319_);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3321_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3318_);
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v_a_3317_);
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object* v_ci_3326_, lean_object* v_info_3327_, lean_object* v_x_3328_, lean_object* v___y_3329_){
_start:
{
if (lean_obj_tag(v_info_3327_) == 11)
{
lean_object* v_toCommandContextInfo_3330_; lean_object* v_i_3331_; lean_object* v_env_3332_; lean_object* v___x_3333_; lean_object* v_mainModule_3334_; lean_object* v_id_3335_; lean_object* v_baseId_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v_toCommandContextInfo_3330_ = lean_ctor_get(v_ci_3326_, 0);
v_i_3331_ = lean_ctor_get(v_info_3327_, 0);
lean_inc_ref(v_i_3331_);
lean_dec_ref_known(v_info_3327_, 1);
v_env_3332_ = lean_ctor_get(v_toCommandContextInfo_3330_, 0);
v___x_3333_ = l_Lean_Environment_header(v_env_3332_);
v_mainModule_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_mainModule_3334_);
lean_dec_ref(v___x_3333_);
v_id_3335_ = lean_ctor_get(v_i_3331_, 1);
lean_inc(v_id_3335_);
v_baseId_3336_ = lean_ctor_get(v_i_3331_, 2);
lean_inc(v_baseId_3336_);
lean_dec_ref(v_i_3331_);
v___x_3337_ = 1;
v___x_3338_ = l_Lean_Name_toString(v_mainModule_3334_, v___x_3337_);
v___x_3339_ = l_Lean_Name_toString(v_id_3335_, v___x_3337_);
lean_inc_ref(v___x_3338_);
v___x_3340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = l_Lean_Name_toString(v_baseId_3336_, v___x_3337_);
v___x_3342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3338_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v___x_3340_, v___x_3342_, v___y_3329_);
return v___x_3343_;
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
lean_dec_ref(v_info_3327_);
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
lean_ctor_set(v___x_3345_, 1, v___y_3329_);
return v___x_3345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object* v_ci_3346_, lean_object* v_info_3347_, lean_object* v_x_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(v_ci_3346_, v_info_3347_, v_x_3348_, v___y_3349_);
lean_dec_ref(v_x_3348_);
lean_dec_ref(v_ci_3346_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v___y_3354_){
_start:
{
uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = 1;
v___x_3356_ = lean_box(v___x_3355_);
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
lean_ctor_set(v___x_3357_, 1, v___y_3354_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object* v_x_3358_, lean_object* v_x_3359_, lean_object* v_x_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(v_x_3358_, v_x_3359_, v_x_3360_, v___y_3361_);
lean_dec_ref(v_x_3360_);
lean_dec_ref(v_x_3359_);
lean_dec_ref(v_x_3358_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3363_, lean_object* v_ci_3364_, lean_object* v_i_3365_, lean_object* v_cs_3366_, lean_object* v_x_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_apply_4(v_postNode_3363_, v_ci_3364_, v_i_3365_, v_cs_3366_, v___y_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3370_, lean_object* v_ci_3371_, lean_object* v_i_3372_, lean_object* v_cs_3373_, lean_object* v_x_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3370_, v_ci_3371_, v_i_3372_, v_cs_3373_, v_x_3374_, v___y_3375_);
lean_dec(v_x_3374_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___f_3379_; lean_object* v___f_3380_; lean_object* v___f_3381_; lean_object* v___f_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___f_3389_; lean_object* v___f_3390_; lean_object* v___f_3391_; lean_object* v___f_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3784__overap_3401_; lean_object* v___x_3402_; 
v___f_3379_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3380_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3381_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3382_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3383_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3384_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3385_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___f_3379_);
lean_ctor_set(v___x_3386_, 1, v___f_3380_);
v___x_3387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v___f_3381_);
lean_ctor_set(v___x_3387_, 2, v___f_3382_);
lean_ctor_set(v___x_3387_, 3, v___f_3383_);
lean_ctor_set(v___x_3387_, 4, v___f_3384_);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___f_3385_);
lean_inc_ref_n(v___x_3388_, 6);
v___f_3389_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3389_, 0, v___x_3388_);
v___f_3390_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3390_, 0, v___x_3388_);
v___f_3391_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3391_, 0, v___x_3388_);
v___f_3392_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3392_, 0, v___x_3388_);
v___x_3393_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3393_, 0, lean_box(0));
lean_closure_set(v___x_3393_, 1, lean_box(0));
lean_closure_set(v___x_3393_, 2, v___x_3388_);
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v___f_3389_);
v___x_3395_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3395_, 0, lean_box(0));
lean_closure_set(v___x_3395_, 1, lean_box(0));
lean_closure_set(v___x_3395_, 2, v___x_3388_);
v___x_3396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
lean_ctor_set(v___x_3396_, 2, v___f_3390_);
lean_ctor_set(v___x_3396_, 3, v___f_3391_);
lean_ctor_set(v___x_3396_, 4, v___f_3392_);
v___x_3397_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3397_, 0, lean_box(0));
lean_closure_set(v___x_3397_, 1, lean_box(0));
lean_closure_set(v___x_3397_, 2, v___x_3388_);
v___x_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = lean_box(0);
v___x_3400_ = l_instInhabitedOfMonad___redArg(v___x_3398_, v___x_3399_);
v___x_3784__overap_3401_ = lean_panic_fn_borrowed(v___x_3400_, v_msg_3377_);
lean_dec(v___x_3400_);
v___x_3402_ = lean_apply_1(v___x_3784__overap_3401_, v___y_3378_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3403_, lean_object* v_postNode_3404_, lean_object* v_x_3405_, lean_object* v_x_3406_, lean_object* v___y_3407_){
_start:
{
switch(lean_obj_tag(v_x_3406_))
{
case 0:
{
lean_object* v_i_3408_; lean_object* v_t_3409_; lean_object* v___x_3410_; 
v_i_3408_ = lean_ctor_get(v_x_3406_, 0);
lean_inc_ref(v_i_3408_);
v_t_3409_ = lean_ctor_get(v_x_3406_, 1);
lean_inc_ref(v_t_3409_);
lean_dec_ref_known(v_x_3406_, 2);
v___x_3410_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3408_, v_x_3405_);
v_x_3405_ = v___x_3410_;
v_x_3406_ = v_t_3409_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3405_) == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec_ref_known(v_x_3406_, 2);
lean_dec_ref(v_postNode_3404_);
lean_dec_ref(v_preNode_3403_);
v___x_3412_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3413_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3412_, v___y_3407_);
return v___x_3413_;
}
else
{
lean_object* v_i_3414_; lean_object* v_children_3415_; lean_object* v_val_3416_; lean_object* v___x_3417_; lean_object* v_fst_3418_; uint8_t v___x_3419_; 
v_i_3414_ = lean_ctor_get(v_x_3406_, 0);
lean_inc_ref_n(v_i_3414_, 2);
v_children_3415_ = lean_ctor_get(v_x_3406_, 1);
lean_inc_ref_n(v_children_3415_, 2);
lean_dec_ref_known(v_x_3406_, 2);
v_val_3416_ = lean_ctor_get(v_x_3405_, 0);
lean_inc_n(v_val_3416_, 2);
lean_inc_ref(v_preNode_3403_);
v___x_3417_ = lean_apply_4(v_preNode_3403_, v_val_3416_, v_i_3414_, v_children_3415_, v___y_3407_);
v_fst_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_fst_3418_);
v___x_3419_ = lean_unbox(v_fst_3418_);
lean_dec(v_fst_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3438_; 
lean_dec_ref(v_preNode_3403_);
v_isSharedCheck_3438_ = !lean_is_exclusive(v_x_3405_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; 
v_unused_3439_ = lean_ctor_get(v_x_3405_, 0);
lean_dec(v_unused_3439_);
v___x_3421_ = v_x_3405_;
v_isShared_3422_ = v_isSharedCheck_3438_;
goto v_resetjp_3420_;
}
else
{
lean_dec(v_x_3405_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3438_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v_snd_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v_fst_3426_; lean_object* v_snd_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3437_; 
v_snd_3423_ = lean_ctor_get(v___x_3417_, 1);
lean_inc(v_snd_3423_);
lean_dec_ref(v___x_3417_);
v___x_3424_ = lean_box(0);
v___x_3425_ = lean_apply_5(v_postNode_3404_, v_val_3416_, v_i_3414_, v_children_3415_, v___x_3424_, v_snd_3423_);
v_fst_3426_ = lean_ctor_get(v___x_3425_, 0);
v_snd_3427_ = lean_ctor_get(v___x_3425_, 1);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3429_ = v___x_3425_;
v_isShared_3430_ = v_isSharedCheck_3437_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_snd_3427_);
lean_inc(v_fst_3426_);
lean_dec(v___x_3425_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3437_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v_fst_3426_);
v___x_3432_ = v___x_3421_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_fst_3426_);
v___x_3432_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
lean_object* v___x_3434_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3432_);
v___x_3434_ = v___x_3429_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v_snd_3427_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
else
{
lean_object* v_snd_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v_fst_3445_; lean_object* v_snd_3446_; lean_object* v___x_3447_; lean_object* v_fst_3448_; lean_object* v_snd_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3457_; 
v_snd_3440_ = lean_ctor_get(v___x_3417_, 1);
lean_inc(v_snd_3440_);
lean_dec_ref(v___x_3417_);
v___x_3441_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3405_, v_i_3414_);
v___x_3442_ = l_Lean_PersistentArray_toList___redArg(v_children_3415_);
v___x_3443_ = lean_box(0);
lean_inc_ref(v_postNode_3404_);
v___x_3444_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3403_, v_postNode_3404_, v___x_3441_, v___x_3442_, v___x_3443_, v_snd_3440_);
v_fst_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_fst_3445_);
v_snd_3446_ = lean_ctor_get(v___x_3444_, 1);
lean_inc(v_snd_3446_);
lean_dec_ref(v___x_3444_);
v___x_3447_ = lean_apply_5(v_postNode_3404_, v_val_3416_, v_i_3414_, v_children_3415_, v_fst_3445_, v_snd_3446_);
v_fst_3448_ = lean_ctor_get(v___x_3447_, 0);
v_snd_3449_ = lean_ctor_get(v___x_3447_, 1);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3451_ = v___x_3447_;
v_isShared_3452_ = v_isSharedCheck_3457_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_snd_3449_);
lean_inc(v_fst_3448_);
lean_dec(v___x_3447_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3457_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
v___x_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3453_, 0, v_fst_3448_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3453_);
v___x_3455_ = v___x_3451_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_snd_3449_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
default: 
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_dec_ref_known(v_x_3406_, 1);
lean_dec(v_x_3405_);
lean_dec_ref(v_postNode_3404_);
lean_dec_ref(v_preNode_3403_);
v___x_3458_ = lean_box(0);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v___y_3407_);
return v___x_3459_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3460_, lean_object* v_postNode_3461_, lean_object* v___x_3462_, lean_object* v_x_3463_, lean_object* v_x_3464_, lean_object* v___y_3465_){
_start:
{
if (lean_obj_tag(v_x_3463_) == 0)
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec(v___x_3462_);
lean_dec_ref(v_postNode_3461_);
lean_dec_ref(v_preNode_3460_);
v___x_3466_ = l_List_reverse___redArg(v_x_3464_);
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
lean_ctor_set(v___x_3467_, 1, v___y_3465_);
return v___x_3467_;
}
else
{
lean_object* v_head_3468_; lean_object* v_tail_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3480_; 
v_head_3468_ = lean_ctor_get(v_x_3463_, 0);
v_tail_3469_ = lean_ctor_get(v_x_3463_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_x_3463_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3471_ = v_x_3463_;
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_tail_3469_);
lean_inc(v_head_3468_);
lean_dec(v_x_3463_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v_fst_3474_; lean_object* v_snd_3475_; lean_object* v___x_3477_; 
lean_inc(v___x_3462_);
lean_inc_ref(v_postNode_3461_);
lean_inc_ref(v_preNode_3460_);
v___x_3473_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3460_, v_postNode_3461_, v___x_3462_, v_head_3468_, v___y_3465_);
v_fst_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_fst_3474_);
v_snd_3475_ = lean_ctor_get(v___x_3473_, 1);
lean_inc(v_snd_3475_);
lean_dec_ref(v___x_3473_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v_x_3464_);
lean_ctor_set(v___x_3471_, 0, v_fst_3474_);
v___x_3477_ = v___x_3471_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_fst_3474_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_x_3464_);
v___x_3477_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
v_x_3463_ = v_tail_3469_;
v_x_3464_ = v___x_3477_;
v___y_3465_ = v_snd_3475_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3481_, lean_object* v_postNode_3482_, lean_object* v_ctx_x3f_3483_, lean_object* v_t_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___f_3486_; lean_object* v___x_3487_; lean_object* v_snd_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3496_; 
v___f_3486_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3486_, 0, v_postNode_3482_);
v___x_3487_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3481_, v___f_3486_, v_ctx_x3f_3483_, v_t_3484_, v___y_3485_);
v_snd_3488_ = lean_ctor_get(v___x_3487_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; 
v_unused_3497_ = lean_ctor_get(v___x_3487_, 0);
lean_dec(v_unused_3497_);
v___x_3490_ = v___x_3487_;
v_isShared_3491_ = v_isSharedCheck_3496_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_snd_3488_);
lean_dec(v___x_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3496_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3492_ = lean_box(0);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3492_);
v___x_3494_ = v___x_3490_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_snd_3488_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(lean_object* v_as_3500_, size_t v_i_3501_, size_t v_stop_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_){
_start:
{
uint8_t v___x_3505_; 
v___x_3505_ = lean_usize_dec_eq(v_i_3501_, v_stop_3502_);
if (v___x_3505_ == 0)
{
lean_object* v___f_3506_; lean_object* v___f_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v_fst_3511_; lean_object* v_snd_3512_; size_t v___x_3513_; size_t v___x_3514_; 
v___f_3506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0));
v___f_3507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1));
v___x_3508_ = lean_array_uget_borrowed(v_as_3500_, v_i_3501_);
v___x_3509_ = lean_box(0);
lean_inc(v___x_3508_);
v___x_3510_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(v___f_3506_, v___f_3507_, v___x_3509_, v___x_3508_, v___y_3504_);
v_fst_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_fst_3511_);
v_snd_3512_ = lean_ctor_get(v___x_3510_, 1);
lean_inc(v_snd_3512_);
lean_dec_ref(v___x_3510_);
v___x_3513_ = ((size_t)1ULL);
v___x_3514_ = lean_usize_add(v_i_3501_, v___x_3513_);
v_i_3501_ = v___x_3514_;
v_b_3503_ = v_fst_3511_;
v___y_3504_ = v_snd_3512_;
goto _start;
}
else
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v_b_3503_);
lean_ctor_set(v___x_3516_, 1, v___y_3504_);
return v___x_3516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___boxed(lean_object* v_as_3517_, lean_object* v_i_3518_, lean_object* v_stop_3519_, lean_object* v_b_3520_, lean_object* v___y_3521_){
_start:
{
size_t v_i_boxed_3522_; size_t v_stop_boxed_3523_; lean_object* v_res_3524_; 
v_i_boxed_3522_ = lean_unbox_usize(v_i_3518_);
lean_dec(v_i_3518_);
v_stop_boxed_3523_ = lean_unbox_usize(v_stop_3519_);
lean_dec(v_stop_3519_);
v_res_3524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_as_3517_, v_i_boxed_3522_, v_stop_boxed_3523_, v_b_3520_, v___y_3521_);
lean_dec_ref(v_as_3517_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(lean_object* v_a_3525_, lean_object* v_x_3526_){
_start:
{
if (lean_obj_tag(v_x_3526_) == 0)
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_box(0);
return v___x_3527_;
}
else
{
lean_object* v_key_3528_; lean_object* v_value_3529_; lean_object* v_tail_3530_; uint8_t v___x_3531_; 
v_key_3528_ = lean_ctor_get(v_x_3526_, 0);
v_value_3529_ = lean_ctor_get(v_x_3526_, 1);
v_tail_3530_ = lean_ctor_get(v_x_3526_, 2);
v___x_3531_ = l_Lean_Lsp_instBEqRange_beq(v_key_3528_, v_a_3525_);
if (v___x_3531_ == 0)
{
v_x_3526_ = v_tail_3530_;
goto _start;
}
else
{
lean_object* v___x_3533_; 
lean_inc(v_value_3529_);
v___x_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3533_, 0, v_value_3529_);
return v___x_3533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_3534_, lean_object* v_x_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3534_, v_x_3535_);
lean_dec(v_x_3535_);
lean_dec_ref(v_a_3534_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(lean_object* v_m_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v_buckets_3539_; lean_object* v___x_3540_; uint64_t v___x_3541_; uint64_t v___x_3542_; uint64_t v___x_3543_; uint64_t v_fold_3544_; uint64_t v___x_3545_; uint64_t v___x_3546_; uint64_t v___x_3547_; size_t v___x_3548_; size_t v___x_3549_; size_t v___x_3550_; size_t v___x_3551_; size_t v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v_buckets_3539_ = lean_ctor_get(v_m_3537_, 1);
v___x_3540_ = lean_array_get_size(v_buckets_3539_);
v___x_3541_ = l_Lean_Lsp_instHashableRange_hash(v_a_3538_);
v___x_3542_ = 32ULL;
v___x_3543_ = lean_uint64_shift_right(v___x_3541_, v___x_3542_);
v_fold_3544_ = lean_uint64_xor(v___x_3541_, v___x_3543_);
v___x_3545_ = 16ULL;
v___x_3546_ = lean_uint64_shift_right(v_fold_3544_, v___x_3545_);
v___x_3547_ = lean_uint64_xor(v_fold_3544_, v___x_3546_);
v___x_3548_ = lean_uint64_to_usize(v___x_3547_);
v___x_3549_ = lean_usize_of_nat(v___x_3540_);
v___x_3550_ = ((size_t)1ULL);
v___x_3551_ = lean_usize_sub(v___x_3549_, v___x_3550_);
v___x_3552_ = lean_usize_land(v___x_3548_, v___x_3551_);
v___x_3553_ = lean_array_uget_borrowed(v_buckets_3539_, v___x_3552_);
v___x_3554_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3538_, v___x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg___boxed(lean_object* v_m_3555_, lean_object* v_a_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3555_, v_a_3556_);
lean_dec_ref(v_a_3556_);
lean_dec_ref(v_m_3555_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(lean_object* v_posMap_3558_, lean_object* v_as_3559_, size_t v_sz_3560_, size_t v_i_3561_, lean_object* v_b_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v_a_3565_; lean_object* v_snd_3566_; uint8_t v___x_3570_; 
v___x_3570_ = lean_usize_dec_lt(v_i_3561_, v_sz_3560_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v_b_3562_);
lean_ctor_set(v___x_3571_, 1, v___y_3563_);
return v___x_3571_;
}
else
{
lean_object* v_a_3572_; lean_object* v_ident_3573_; lean_object* v_range_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_a_3572_ = lean_array_uget_borrowed(v_as_3559_, v_i_3561_);
v_ident_3573_ = lean_ctor_get(v_a_3572_, 0);
v_range_3574_ = lean_ctor_get(v_a_3572_, 2);
v___x_3575_ = lean_box(0);
v___x_3576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_posMap_3558_, v_range_3574_);
if (lean_obj_tag(v___x_3576_) == 1)
{
lean_object* v_val_3577_; lean_object* v___x_3578_; lean_object* v_snd_3579_; 
v_val_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_val_3577_);
lean_dec_ref_known(v___x_3576_, 1);
lean_inc_ref(v_ident_3573_);
v___x_3578_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v_val_3577_, v_ident_3573_, v___y_3563_);
v_snd_3579_ = lean_ctor_get(v___x_3578_, 1);
lean_inc(v_snd_3579_);
lean_dec_ref(v___x_3578_);
v_a_3565_ = v___x_3575_;
v_snd_3566_ = v_snd_3579_;
goto v___jp_3564_;
}
else
{
lean_dec(v___x_3576_);
v_a_3565_ = v___x_3575_;
v_snd_3566_ = v___y_3563_;
goto v___jp_3564_;
}
}
v___jp_3564_:
{
size_t v___x_3567_; size_t v___x_3568_; 
v___x_3567_ = ((size_t)1ULL);
v___x_3568_ = lean_usize_add(v_i_3561_, v___x_3567_);
v_i_3561_ = v___x_3568_;
v_b_3562_ = v_a_3565_;
v___y_3563_ = v_snd_3566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2___boxed(lean_object* v_posMap_3580_, lean_object* v_as_3581_, lean_object* v_sz_3582_, lean_object* v_i_3583_, lean_object* v_b_3584_, lean_object* v___y_3585_){
_start:
{
size_t v_sz_boxed_3586_; size_t v_i_boxed_3587_; lean_object* v_res_3588_; 
v_sz_boxed_3586_ = lean_unbox_usize(v_sz_3582_);
lean_dec(v_sz_3582_);
v_i_boxed_3587_ = lean_unbox_usize(v_i_3583_);
lean_dec(v_i_3583_);
v_res_3588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3580_, v_as_3581_, v_sz_boxed_3586_, v_i_boxed_3587_, v_b_3584_, v___y_3585_);
lean_dec_ref(v_as_3581_);
lean_dec_ref(v_posMap_3580_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(lean_object* v_trees_3589_, lean_object* v_refs_3590_, lean_object* v_posMap_3591_){
_start:
{
lean_object* v___x_3592_; size_t v_sz_3593_; size_t v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v_snd_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v___x_3592_ = lean_box(0);
v_sz_3593_ = lean_array_size(v_refs_3590_);
v___x_3594_ = ((size_t)0ULL);
v___x_3595_ = lean_unsigned_to_nat(0u);
v___x_3596_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3591_, v_refs_3590_, v_sz_3593_, v___x_3594_, v___x_3592_, v___x_3596_);
v_snd_3598_ = lean_ctor_get(v___x_3597_, 1);
lean_inc(v_snd_3598_);
lean_dec_ref(v___x_3597_);
v___x_3599_ = lean_array_get_size(v_trees_3589_);
v___x_3600_ = lean_nat_dec_lt(v___x_3595_, v___x_3599_);
if (v___x_3600_ == 0)
{
return v_snd_3598_;
}
else
{
uint8_t v___x_3601_; 
v___x_3601_ = lean_nat_dec_le(v___x_3599_, v___x_3599_);
if (v___x_3601_ == 0)
{
if (v___x_3600_ == 0)
{
return v_snd_3598_;
}
else
{
size_t v___x_3602_; lean_object* v___x_3603_; lean_object* v_snd_3604_; 
v___x_3602_ = lean_usize_of_nat(v___x_3599_);
v___x_3603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3589_, v___x_3594_, v___x_3602_, v___x_3592_, v_snd_3598_);
v_snd_3604_ = lean_ctor_get(v___x_3603_, 1);
lean_inc(v_snd_3604_);
lean_dec_ref(v___x_3603_);
return v_snd_3604_;
}
}
else
{
size_t v___x_3605_; lean_object* v___x_3606_; lean_object* v_snd_3607_; 
v___x_3605_ = lean_usize_of_nat(v___x_3599_);
v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3589_, v___x_3594_, v___x_3605_, v___x_3592_, v_snd_3598_);
v_snd_3607_ = lean_ctor_get(v___x_3606_, 1);
lean_inc(v_snd_3607_);
lean_dec_ref(v___x_3606_);
return v_snd_3607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap___boxed(lean_object* v_trees_3608_, lean_object* v_refs_3609_, lean_object* v_posMap_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3608_, v_refs_3609_, v_posMap_3610_);
lean_dec_ref(v_posMap_3610_);
lean_dec_ref(v_refs_3609_);
lean_dec_ref(v_trees_3608_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(lean_object* v_00_u03b2_3612_, lean_object* v_m_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3613_, v_a_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___boxed(lean_object* v_00_u03b2_3616_, lean_object* v_m_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(v_00_u03b2_3616_, v_m_3617_, v_a_3618_);
lean_dec_ref(v_a_3618_);
lean_dec_ref(v_m_3617_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3620_, lean_object* v_msg_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v_msg_3621_, v___y_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object* v_00_u03b1_3624_, lean_object* v_preNode_3625_, lean_object* v_postNode_3626_, lean_object* v_x_3627_, lean_object* v_x_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3625_, v_postNode_3626_, v_x_3627_, v_x_3628_, v___y_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object* v_00_u03b2_3631_, lean_object* v_a_3632_, lean_object* v_x_3633_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3632_, v_x_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3635_, lean_object* v_a_3636_, lean_object* v_x_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(v_00_u03b2_3635_, v_a_3636_, v_x_3637_);
lean_dec(v_x_3637_);
lean_dec_ref(v_a_3636_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3639_, lean_object* v_preNode_3640_, lean_object* v_postNode_3641_, lean_object* v___x_3642_, lean_object* v_x_3643_, lean_object* v_x_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3640_, v_postNode_3641_, v___x_3642_, v_x_3643_, v_x_3644_, v___y_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(lean_object* v_a_3647_, lean_object* v_b_3648_, lean_object* v_x_3649_){
_start:
{
if (lean_obj_tag(v_x_3649_) == 0)
{
lean_dec(v_b_3648_);
lean_dec_ref(v_a_3647_);
return v_x_3649_;
}
else
{
lean_object* v_key_3650_; lean_object* v_value_3651_; lean_object* v_tail_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3664_; 
v_key_3650_ = lean_ctor_get(v_x_3649_, 0);
v_value_3651_ = lean_ctor_get(v_x_3649_, 1);
v_tail_3652_ = lean_ctor_get(v_x_3649_, 2);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_x_3649_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3654_ = v_x_3649_;
v_isShared_3655_ = v_isSharedCheck_3664_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_tail_3652_);
lean_inc(v_value_3651_);
lean_inc(v_key_3650_);
lean_dec(v_x_3649_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3664_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
uint8_t v___x_3656_; 
v___x_3656_ = l_Lean_Lsp_instBEqRange_beq(v_key_3650_, v_a_3647_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
v___x_3657_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3647_, v_b_3648_, v_tail_3652_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 2, v___x_3657_);
v___x_3659_ = v___x_3654_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_key_3650_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_value_3651_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
else
{
lean_object* v___x_3662_; 
lean_dec(v_value_3651_);
lean_dec(v_key_3650_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 1, v_b_3648_);
lean_ctor_set(v___x_3654_, 0, v_a_3647_);
v___x_3662_ = v___x_3654_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3647_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_b_3648_);
lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_tail_3652_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_3665_, lean_object* v_x_3666_){
_start:
{
if (lean_obj_tag(v_x_3666_) == 0)
{
return v_x_3665_;
}
else
{
lean_object* v_key_3667_; lean_object* v_value_3668_; lean_object* v_tail_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3692_; 
v_key_3667_ = lean_ctor_get(v_x_3666_, 0);
v_value_3668_ = lean_ctor_get(v_x_3666_, 1);
v_tail_3669_ = lean_ctor_get(v_x_3666_, 2);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_x_3666_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3671_ = v_x_3666_;
v_isShared_3672_ = v_isSharedCheck_3692_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_tail_3669_);
lean_inc(v_value_3668_);
lean_inc(v_key_3667_);
lean_dec(v_x_3666_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3692_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; uint64_t v___x_3674_; uint64_t v___x_3675_; uint64_t v___x_3676_; uint64_t v_fold_3677_; uint64_t v___x_3678_; uint64_t v___x_3679_; uint64_t v___x_3680_; size_t v___x_3681_; size_t v___x_3682_; size_t v___x_3683_; size_t v___x_3684_; size_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3673_ = lean_array_get_size(v_x_3665_);
v___x_3674_ = l_Lean_Lsp_instHashableRange_hash(v_key_3667_);
v___x_3675_ = 32ULL;
v___x_3676_ = lean_uint64_shift_right(v___x_3674_, v___x_3675_);
v_fold_3677_ = lean_uint64_xor(v___x_3674_, v___x_3676_);
v___x_3678_ = 16ULL;
v___x_3679_ = lean_uint64_shift_right(v_fold_3677_, v___x_3678_);
v___x_3680_ = lean_uint64_xor(v_fold_3677_, v___x_3679_);
v___x_3681_ = lean_uint64_to_usize(v___x_3680_);
v___x_3682_ = lean_usize_of_nat(v___x_3673_);
v___x_3683_ = ((size_t)1ULL);
v___x_3684_ = lean_usize_sub(v___x_3682_, v___x_3683_);
v___x_3685_ = lean_usize_land(v___x_3681_, v___x_3684_);
v___x_3686_ = lean_array_uget_borrowed(v_x_3665_, v___x_3685_);
lean_inc(v___x_3686_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 2, v___x_3686_);
v___x_3688_ = v___x_3671_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_key_3667_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_value_3668_);
lean_ctor_set(v_reuseFailAlloc_3691_, 2, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_array_uset(v_x_3665_, v___x_3685_, v___x_3688_);
v_x_3665_ = v___x_3689_;
v_x_3666_ = v_tail_3669_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3693_, lean_object* v_source_3694_, lean_object* v_target_3695_){
_start:
{
lean_object* v___x_3696_; uint8_t v___x_3697_; 
v___x_3696_ = lean_array_get_size(v_source_3694_);
v___x_3697_ = lean_nat_dec_lt(v_i_3693_, v___x_3696_);
if (v___x_3697_ == 0)
{
lean_dec_ref(v_source_3694_);
lean_dec(v_i_3693_);
return v_target_3695_;
}
else
{
lean_object* v_es_3698_; lean_object* v___x_3699_; lean_object* v_source_3700_; lean_object* v_target_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_es_3698_ = lean_array_fget(v_source_3694_, v_i_3693_);
v___x_3699_ = lean_box(0);
v_source_3700_ = lean_array_fset(v_source_3694_, v_i_3693_, v___x_3699_);
v_target_3701_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3695_, v_es_3698_);
v___x_3702_ = lean_unsigned_to_nat(1u);
v___x_3703_ = lean_nat_add(v_i_3693_, v___x_3702_);
lean_dec(v_i_3693_);
v_i_3693_ = v___x_3703_;
v_source_3694_ = v_source_3700_;
v_target_3695_ = v_target_3701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(lean_object* v_data_3705_){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v_nbuckets_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3706_ = lean_array_get_size(v_data_3705_);
v___x_3707_ = lean_unsigned_to_nat(2u);
v_nbuckets_3708_ = lean_nat_mul(v___x_3706_, v___x_3707_);
v___x_3709_ = lean_unsigned_to_nat(0u);
v___x_3710_ = lean_box(0);
v___x_3711_ = lean_mk_array(v_nbuckets_3708_, v___x_3710_);
v___x_3712_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v___x_3709_, v_data_3705_, v___x_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object* v_a_3713_, lean_object* v_x_3714_){
_start:
{
if (lean_obj_tag(v_x_3714_) == 0)
{
uint8_t v___x_3715_; 
v___x_3715_ = 0;
return v___x_3715_;
}
else
{
lean_object* v_key_3716_; lean_object* v_tail_3717_; uint8_t v___x_3718_; 
v_key_3716_ = lean_ctor_get(v_x_3714_, 0);
v_tail_3717_ = lean_ctor_get(v_x_3714_, 2);
v___x_3718_ = l_Lean_Lsp_instBEqRange_beq(v_key_3716_, v_a_3713_);
if (v___x_3718_ == 0)
{
v_x_3714_ = v_tail_3717_;
goto _start;
}
else
{
return v___x_3718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object* v_a_3720_, lean_object* v_x_3721_){
_start:
{
uint8_t v_res_3722_; lean_object* v_r_3723_; 
v_res_3722_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3720_, v_x_3721_);
lean_dec(v_x_3721_);
lean_dec_ref(v_a_3720_);
v_r_3723_ = lean_box(v_res_3722_);
return v_r_3723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object* v_m_3724_, lean_object* v_a_3725_, lean_object* v_b_3726_){
_start:
{
lean_object* v_size_3727_; lean_object* v_buckets_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3771_; 
v_size_3727_ = lean_ctor_get(v_m_3724_, 0);
v_buckets_3728_ = lean_ctor_get(v_m_3724_, 1);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_m_3724_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3730_ = v_m_3724_;
v_isShared_3731_ = v_isSharedCheck_3771_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_buckets_3728_);
lean_inc(v_size_3727_);
lean_dec(v_m_3724_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3771_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3732_; uint64_t v___x_3733_; uint64_t v___x_3734_; uint64_t v___x_3735_; uint64_t v_fold_3736_; uint64_t v___x_3737_; uint64_t v___x_3738_; uint64_t v___x_3739_; size_t v___x_3740_; size_t v___x_3741_; size_t v___x_3742_; size_t v___x_3743_; size_t v___x_3744_; lean_object* v_bkt_3745_; uint8_t v___x_3746_; 
v___x_3732_ = lean_array_get_size(v_buckets_3728_);
v___x_3733_ = l_Lean_Lsp_instHashableRange_hash(v_a_3725_);
v___x_3734_ = 32ULL;
v___x_3735_ = lean_uint64_shift_right(v___x_3733_, v___x_3734_);
v_fold_3736_ = lean_uint64_xor(v___x_3733_, v___x_3735_);
v___x_3737_ = 16ULL;
v___x_3738_ = lean_uint64_shift_right(v_fold_3736_, v___x_3737_);
v___x_3739_ = lean_uint64_xor(v_fold_3736_, v___x_3738_);
v___x_3740_ = lean_uint64_to_usize(v___x_3739_);
v___x_3741_ = lean_usize_of_nat(v___x_3732_);
v___x_3742_ = ((size_t)1ULL);
v___x_3743_ = lean_usize_sub(v___x_3741_, v___x_3742_);
v___x_3744_ = lean_usize_land(v___x_3740_, v___x_3743_);
v_bkt_3745_ = lean_array_uget_borrowed(v_buckets_3728_, v___x_3744_);
v___x_3746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3725_, v_bkt_3745_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; lean_object* v_size_x27_3748_; lean_object* v___x_3749_; lean_object* v_buckets_x27_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; 
v___x_3747_ = lean_unsigned_to_nat(1u);
v_size_x27_3748_ = lean_nat_add(v_size_3727_, v___x_3747_);
lean_dec(v_size_3727_);
lean_inc(v_bkt_3745_);
v___x_3749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3749_, 0, v_a_3725_);
lean_ctor_set(v___x_3749_, 1, v_b_3726_);
lean_ctor_set(v___x_3749_, 2, v_bkt_3745_);
v_buckets_x27_3750_ = lean_array_uset(v_buckets_3728_, v___x_3744_, v___x_3749_);
v___x_3751_ = lean_unsigned_to_nat(4u);
v___x_3752_ = lean_nat_mul(v_size_x27_3748_, v___x_3751_);
v___x_3753_ = lean_unsigned_to_nat(3u);
v___x_3754_ = lean_nat_div(v___x_3752_, v___x_3753_);
lean_dec(v___x_3752_);
v___x_3755_ = lean_array_get_size(v_buckets_x27_3750_);
v___x_3756_ = lean_nat_dec_le(v___x_3754_, v___x_3755_);
lean_dec(v___x_3754_);
if (v___x_3756_ == 0)
{
lean_object* v_val_3757_; lean_object* v___x_3759_; 
v_val_3757_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_buckets_x27_3750_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 1, v_val_3757_);
lean_ctor_set(v___x_3730_, 0, v_size_x27_3748_);
v___x_3759_ = v___x_3730_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_size_x27_3748_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_val_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
else
{
lean_object* v___x_3762_; 
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 1, v_buckets_x27_3750_);
lean_ctor_set(v___x_3730_, 0, v_size_x27_3748_);
v___x_3762_ = v___x_3730_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_size_x27_3748_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_buckets_x27_3750_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
else
{
lean_object* v___x_3764_; lean_object* v_buckets_x27_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
lean_inc(v_bkt_3745_);
v___x_3764_ = lean_box(0);
v_buckets_x27_3765_ = lean_array_uset(v_buckets_3728_, v___x_3744_, v___x_3764_);
v___x_3766_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3725_, v_b_3726_, v_bkt_3745_);
v___x_3767_ = lean_array_uset(v_buckets_x27_3765_, v___x_3744_, v___x_3766_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 1, v___x_3767_);
v___x_3769_ = v___x_3730_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_size_3727_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object* v_as_3772_, size_t v_sz_3773_, size_t v_i_3774_, lean_object* v_b_3775_){
_start:
{
lean_object* v_a_3777_; uint8_t v___x_3781_; 
v___x_3781_ = lean_usize_dec_lt(v_i_3774_, v_sz_3773_);
if (v___x_3781_ == 0)
{
return v_b_3775_;
}
else
{
lean_object* v_a_3782_; uint8_t v_isBinder_3783_; 
v_a_3782_ = lean_array_uget_borrowed(v_as_3772_, v_i_3774_);
v_isBinder_3783_ = lean_ctor_get_uint8(v_a_3782_, sizeof(void*)*6);
if (v_isBinder_3783_ == 1)
{
lean_object* v_ident_3784_; lean_object* v_range_3785_; lean_object* v___x_3786_; 
v_ident_3784_ = lean_ctor_get(v_a_3782_, 0);
v_range_3785_ = lean_ctor_get(v_a_3782_, 2);
lean_inc_ref(v_ident_3784_);
lean_inc_ref(v_range_3785_);
v___x_3786_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_b_3775_, v_range_3785_, v_ident_3784_);
v_a_3777_ = v___x_3786_;
goto v___jp_3776_;
}
else
{
v_a_3777_ = v_b_3775_;
goto v___jp_3776_;
}
}
v___jp_3776_:
{
size_t v___x_3778_; size_t v___x_3779_; 
v___x_3778_ = ((size_t)1ULL);
v___x_3779_ = lean_usize_add(v_i_3774_, v___x_3778_);
v_i_3774_ = v___x_3779_;
v_b_3775_ = v_a_3777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object* v_as_3787_, lean_object* v_sz_3788_, lean_object* v_i_3789_, lean_object* v_b_3790_){
_start:
{
size_t v_sz_boxed_3791_; size_t v_i_boxed_3792_; lean_object* v_res_3793_; 
v_sz_boxed_3791_ = lean_unbox_usize(v_sz_3788_);
lean_dec(v_sz_3788_);
v_i_boxed_3792_ = lean_unbox_usize(v_i_3789_);
lean_dec(v_i_3789_);
v_res_3793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_as_3787_, v_sz_boxed_3791_, v_i_boxed_3792_, v_b_3790_);
lean_dec_ref(v_as_3787_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object* v___x_3794_, lean_object* v_as_3795_, size_t v_sz_3796_, size_t v_i_3797_, lean_object* v_b_3798_){
_start:
{
lean_object* v_a_3800_; uint8_t v___x_3804_; 
v___x_3804_ = lean_usize_dec_lt(v_i_3797_, v_sz_3796_);
if (v___x_3804_ == 0)
{
return v_b_3798_;
}
else
{
lean_object* v_a_3805_; lean_object* v_ident_3808_; lean_object* v_range_3809_; lean_object* v_stx_3810_; lean_object* v_ci_3811_; lean_object* v_info_3812_; uint8_t v_isBinder_3813_; uint8_t v___x_3814_; 
v_a_3805_ = lean_array_uget(v_as_3795_, v_i_3797_);
v_ident_3808_ = lean_ctor_get(v_a_3805_, 0);
v_range_3809_ = lean_ctor_get(v_a_3805_, 2);
v_stx_3810_ = lean_ctor_get(v_a_3805_, 3);
v_ci_3811_ = lean_ctor_get(v_a_3805_, 4);
v_info_3812_ = lean_ctor_get(v_a_3805_, 5);
v_isBinder_3813_ = lean_ctor_get_uint8(v_a_3805_, sizeof(void*)*6);
v___x_3814_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v___x_3794_, v_ident_3808_);
if (v___x_3814_ == 0)
{
if (v___x_3814_ == 0)
{
goto v___jp_3806_;
}
else
{
if (v___x_3814_ == 0)
{
lean_dec(v_a_3805_);
v_a_3800_ = v_b_3798_;
goto v___jp_3799_;
}
else
{
goto v___jp_3806_;
}
}
}
else
{
lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3826_; 
lean_inc_ref(v_info_3812_);
lean_inc_ref(v_ci_3811_);
lean_inc(v_stx_3810_);
lean_inc_ref(v_range_3809_);
lean_inc_ref(v_ident_3808_);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_a_3805_);
if (v_isSharedCheck_3826_ == 0)
{
lean_object* v_unused_3827_; lean_object* v_unused_3828_; lean_object* v_unused_3829_; lean_object* v_unused_3830_; lean_object* v_unused_3831_; lean_object* v_unused_3832_; 
v_unused_3827_ = lean_ctor_get(v_a_3805_, 5);
lean_dec(v_unused_3827_);
v_unused_3828_ = lean_ctor_get(v_a_3805_, 4);
lean_dec(v_unused_3828_);
v_unused_3829_ = lean_ctor_get(v_a_3805_, 3);
lean_dec(v_unused_3829_);
v_unused_3830_ = lean_ctor_get(v_a_3805_, 2);
lean_dec(v_unused_3830_);
v_unused_3831_ = lean_ctor_get(v_a_3805_, 1);
lean_dec(v_unused_3831_);
v_unused_3832_ = lean_ctor_get(v_a_3805_, 0);
lean_dec(v_unused_3832_);
v___x_3816_ = v_a_3805_;
v_isShared_3817_ = v_isSharedCheck_3826_;
goto v_resetjp_3815_;
}
else
{
lean_dec(v_a_3805_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3826_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
lean_inc_ref(v_ident_3808_);
v___x_3818_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v___x_3794_, v_ident_3808_);
v___x_3819_ = lean_unsigned_to_nat(1u);
v___x_3820_ = lean_mk_empty_array_with_capacity(v___x_3819_);
v___x_3821_ = lean_array_push(v___x_3820_, v_ident_3808_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 1, v___x_3821_);
lean_ctor_set(v___x_3816_, 0, v___x_3818_);
v___x_3823_ = v___x_3816_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3825_, 2, v_range_3809_);
lean_ctor_set(v_reuseFailAlloc_3825_, 3, v_stx_3810_);
lean_ctor_set(v_reuseFailAlloc_3825_, 4, v_ci_3811_);
lean_ctor_set(v_reuseFailAlloc_3825_, 5, v_info_3812_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*6, v_isBinder_3813_);
v___x_3823_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_array_push(v_b_3798_, v___x_3823_);
v_a_3800_ = v___x_3824_;
goto v___jp_3799_;
}
}
}
v___jp_3806_:
{
lean_object* v___x_3807_; 
v___x_3807_ = lean_array_push(v_b_3798_, v_a_3805_);
v_a_3800_ = v___x_3807_;
goto v___jp_3799_;
}
}
v___jp_3799_:
{
size_t v___x_3801_; size_t v___x_3802_; 
v___x_3801_ = ((size_t)1ULL);
v___x_3802_ = lean_usize_add(v_i_3797_, v___x_3801_);
v_i_3797_ = v___x_3802_;
v_b_3798_ = v_a_3800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object* v___x_3833_, lean_object* v_as_3834_, lean_object* v_sz_3835_, lean_object* v_i_3836_, lean_object* v_b_3837_){
_start:
{
size_t v_sz_boxed_3838_; size_t v_i_boxed_3839_; lean_object* v_res_3840_; 
v_sz_boxed_3838_ = lean_unbox_usize(v_sz_3835_);
lean_dec(v_sz_3835_);
v_i_boxed_3839_ = lean_unbox_usize(v_i_3836_);
lean_dec(v_i_3836_);
v_res_3840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3833_, v_as_3834_, v_sz_boxed_3838_, v_i_boxed_3839_, v_b_3837_);
lean_dec_ref(v_as_3834_);
lean_dec_ref(v___x_3833_);
return v_res_3840_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__0(void){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = lean_box(0);
v___x_3842_ = lean_unsigned_to_nat(16u);
v___x_3843_ = lean_mk_array(v___x_3842_, v___x_3841_);
return v___x_3843_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__1(void){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v_posMap_3846_; 
v___x_3844_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__0, &l_Lean_Server_combineIdents___closed__0_once, _init_l_Lean_Server_combineIdents___closed__0);
v___x_3845_ = lean_unsigned_to_nat(0u);
v_posMap_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_posMap_3846_, 0, v___x_3845_);
lean_ctor_set(v_posMap_3846_, 1, v___x_3844_);
return v_posMap_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object* v_trees_3847_, lean_object* v_refs_3848_){
_start:
{
lean_object* v_posMap_3849_; size_t v_sz_3850_; size_t v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_posMap_3849_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__1, &l_Lean_Server_combineIdents___closed__1_once, _init_l_Lean_Server_combineIdents___closed__1);
v_sz_3850_ = lean_array_size(v_refs_3848_);
v___x_3851_ = ((size_t)0ULL);
v___x_3852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_refs_3848_, v_sz_3850_, v___x_3851_, v_posMap_3849_);
v___x_3853_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3847_, v_refs_3848_, v___x_3852_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v___x_3853_);
lean_dec_ref(v___x_3853_);
v___x_3855_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_3856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3854_, v_refs_3848_, v_sz_3850_, v___x_3851_, v___x_3855_);
lean_dec_ref(v___x_3854_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object* v_trees_3857_, lean_object* v_refs_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_Server_combineIdents(v_trees_3857_, v_refs_3858_);
lean_dec_ref(v_refs_3858_);
lean_dec_ref(v_trees_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object* v_00_u03b2_3860_, lean_object* v_m_3861_, lean_object* v_a_3862_, lean_object* v_b_3863_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_m_3861_, v_a_3862_, v_b_3863_);
return v___x_3864_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object* v_00_u03b2_3865_, lean_object* v_a_3866_, lean_object* v_x_3867_){
_start:
{
uint8_t v___x_3868_; 
v___x_3868_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3866_, v_x_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3869_, lean_object* v_a_3870_, lean_object* v_x_3871_){
_start:
{
uint8_t v_res_3872_; lean_object* v_r_3873_; 
v_res_3872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(v_00_u03b2_3869_, v_a_3870_, v_x_3871_);
lean_dec(v_x_3871_);
lean_dec_ref(v_a_3870_);
v_r_3873_ = lean_box(v_res_3872_);
return v_r_3873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object* v_00_u03b2_3874_, lean_object* v_data_3875_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_data_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object* v_00_u03b2_3877_, lean_object* v_a_3878_, lean_object* v_b_3879_, lean_object* v_x_3880_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3878_, v_b_3879_, v_x_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3882_, lean_object* v_i_3883_, lean_object* v_source_3884_, lean_object* v_target_3885_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v_i_3883_, v_source_3884_, v_target_3885_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3887_, lean_object* v_x_3888_, lean_object* v_x_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3888_, v_x_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object* v_hi_3891_, lean_object* v_pivot_3892_, lean_object* v_as_3893_, lean_object* v_i_3894_, lean_object* v_k_3895_){
_start:
{
uint8_t v___x_3900_; 
v___x_3900_ = lean_nat_dec_lt(v_k_3895_, v_hi_3891_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
lean_dec(v_k_3895_);
v___x_3901_ = lean_array_fswap(v_as_3893_, v_i_3894_, v_hi_3891_);
v___x_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3902_, 0, v_i_3894_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
return v___x_3902_;
}
else
{
lean_object* v___x_3903_; lean_object* v_range_3904_; lean_object* v_range_3905_; uint8_t v___x_3906_; 
v___x_3903_ = lean_array_fget_borrowed(v_as_3893_, v_k_3895_);
v_range_3904_ = lean_ctor_get(v___x_3903_, 2);
v_range_3905_ = lean_ctor_get(v_pivot_3892_, 2);
v___x_3906_ = l_Lean_Lsp_instOrdRange_ord(v_range_3904_, v_range_3905_);
if (v___x_3906_ == 0)
{
if (v___x_3900_ == 0)
{
goto v___jp_3896_;
}
else
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3907_ = lean_array_fswap(v_as_3893_, v_i_3894_, v_k_3895_);
v___x_3908_ = lean_unsigned_to_nat(1u);
v___x_3909_ = lean_nat_add(v_i_3894_, v___x_3908_);
lean_dec(v_i_3894_);
v___x_3910_ = lean_nat_add(v_k_3895_, v___x_3908_);
lean_dec(v_k_3895_);
v_as_3893_ = v___x_3907_;
v_i_3894_ = v___x_3909_;
v_k_3895_ = v___x_3910_;
goto _start;
}
}
else
{
goto v___jp_3896_;
}
}
v___jp_3896_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_unsigned_to_nat(1u);
v___x_3898_ = lean_nat_add(v_k_3895_, v___x_3897_);
lean_dec(v_k_3895_);
v_k_3895_ = v___x_3898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object* v_hi_3912_, lean_object* v_pivot_3913_, lean_object* v_as_3914_, lean_object* v_i_3915_, lean_object* v_k_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3912_, v_pivot_3913_, v_as_3914_, v_i_3915_, v_k_3916_);
lean_dec_ref(v_pivot_3913_);
lean_dec(v_hi_3912_);
return v_res_3917_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3918_, lean_object* v_x1_3919_, lean_object* v_x2_3920_){
_start:
{
lean_object* v_range_3921_; lean_object* v_range_3922_; uint8_t v___x_3923_; 
v_range_3921_ = lean_ctor_get(v_x1_3919_, 2);
v_range_3922_ = lean_ctor_get(v_x2_3920_, 2);
v___x_3923_ = l_Lean_Lsp_instOrdRange_ord(v_range_3921_, v_range_3922_);
if (v___x_3923_ == 0)
{
return v___x_3918_;
}
else
{
uint8_t v___x_3924_; 
v___x_3924_ = 0;
return v___x_3924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3925_, lean_object* v_x1_3926_, lean_object* v_x2_3927_){
_start:
{
uint8_t v___x_2063__boxed_3928_; uint8_t v_res_3929_; lean_object* v_r_3930_; 
v___x_2063__boxed_3928_ = lean_unbox(v___x_3925_);
v_res_3929_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_2063__boxed_3928_, v_x1_3926_, v_x2_3927_);
lean_dec_ref(v_x2_3927_);
lean_dec_ref(v_x1_3926_);
v_r_3930_ = lean_box(v_res_3929_);
return v_r_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_n_3931_, lean_object* v_as_3932_, lean_object* v_lo_3933_, lean_object* v_hi_3934_){
_start:
{
lean_object* v___y_3936_; uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_lt(v_lo_3933_, v_hi_3934_);
if (v___x_3946_ == 0)
{
lean_dec(v_lo_3933_);
return v_as_3932_;
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v_mid_3949_; lean_object* v___y_3951_; lean_object* v___y_3957_; lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v___x_3947_ = lean_nat_add(v_lo_3933_, v_hi_3934_);
v___x_3948_ = lean_unsigned_to_nat(1u);
v_mid_3949_ = lean_nat_shiftr(v___x_3947_, v___x_3948_);
lean_dec(v___x_3947_);
v___x_3962_ = lean_array_fget_borrowed(v_as_3932_, v_mid_3949_);
v___x_3963_ = lean_array_fget_borrowed(v_as_3932_, v_lo_3933_);
v___x_3964_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3946_, v___x_3962_, v___x_3963_);
if (v___x_3964_ == 0)
{
v___y_3957_ = v_as_3932_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_3965_; 
v___x_3965_ = lean_array_fswap(v_as_3932_, v_lo_3933_, v_mid_3949_);
v___y_3957_ = v___x_3965_;
goto v___jp_3956_;
}
v___jp_3950_:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v___x_3952_ = lean_array_fget_borrowed(v___y_3951_, v_mid_3949_);
v___x_3953_ = lean_array_fget_borrowed(v___y_3951_, v_hi_3934_);
v___x_3954_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3946_, v___x_3952_, v___x_3953_);
if (v___x_3954_ == 0)
{
lean_dec(v_mid_3949_);
v___y_3936_ = v___y_3951_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_array_fswap(v___y_3951_, v_mid_3949_, v_hi_3934_);
lean_dec(v_mid_3949_);
v___y_3936_ = v___x_3955_;
goto v___jp_3935_;
}
}
v___jp_3956_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3958_ = lean_array_fget_borrowed(v___y_3957_, v_hi_3934_);
v___x_3959_ = lean_array_fget_borrowed(v___y_3957_, v_lo_3933_);
v___x_3960_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3946_, v___x_3958_, v___x_3959_);
if (v___x_3960_ == 0)
{
v___y_3951_ = v___y_3957_;
goto v___jp_3950_;
}
else
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_array_fswap(v___y_3957_, v_lo_3933_, v_hi_3934_);
v___y_3951_ = v___x_3961_;
goto v___jp_3950_;
}
}
}
v___jp_3935_:
{
lean_object* v_pivot_3937_; lean_object* v___x_3938_; lean_object* v_fst_3939_; lean_object* v_snd_3940_; uint8_t v___x_3941_; 
v_pivot_3937_ = lean_array_fget(v___y_3936_, v_hi_3934_);
lean_inc_n(v_lo_3933_, 2);
v___x_3938_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3934_, v_pivot_3937_, v___y_3936_, v_lo_3933_, v_lo_3933_);
lean_dec(v_pivot_3937_);
v_fst_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_fst_3939_);
v_snd_3940_ = lean_ctor_get(v___x_3938_, 1);
lean_inc(v_snd_3940_);
lean_dec_ref(v___x_3938_);
v___x_3941_ = lean_nat_dec_le(v_hi_3934_, v_fst_3939_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3931_, v_snd_3940_, v_lo_3933_, v_fst_3939_);
v___x_3943_ = lean_unsigned_to_nat(1u);
v___x_3944_ = lean_nat_add(v_fst_3939_, v___x_3943_);
lean_dec(v_fst_3939_);
v_as_3932_ = v___x_3942_;
v_lo_3933_ = v___x_3944_;
goto _start;
}
else
{
lean_dec(v_fst_3939_);
lean_dec(v_lo_3933_);
return v_snd_3940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_n_3966_, lean_object* v_as_3967_, lean_object* v_lo_3968_, lean_object* v_hi_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3966_, v_as_3967_, v_lo_3968_, v_hi_3969_);
lean_dec(v_hi_3969_);
lean_dec(v_n_3966_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object* v_x_3971_, lean_object* v_x_3972_){
_start:
{
if (lean_obj_tag(v_x_3972_) == 0)
{
return v_x_3971_;
}
else
{
lean_object* v_key_3973_; lean_object* v_snd_3974_; lean_object* v_value_3975_; lean_object* v_tail_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_4016_; 
v_key_3973_ = lean_ctor_get(v_x_3972_, 0);
lean_inc(v_key_3973_);
v_snd_3974_ = lean_ctor_get(v_key_3973_, 1);
v_value_3975_ = lean_ctor_get(v_x_3972_, 1);
v_tail_3976_ = lean_ctor_get(v_x_3972_, 2);
v_isSharedCheck_4016_ = !lean_is_exclusive(v_x_3972_);
if (v_isSharedCheck_4016_ == 0)
{
lean_object* v_unused_4017_; 
v_unused_4017_ = lean_ctor_get(v_x_3972_, 0);
lean_dec(v_unused_4017_);
v___x_3978_ = v_x_3972_;
v_isShared_3979_ = v_isSharedCheck_4016_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_tail_3976_);
lean_inc(v_value_3975_);
lean_dec(v_x_3972_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_4016_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v_fst_3980_; lean_object* v_fst_3981_; lean_object* v_snd_3982_; lean_object* v___x_3983_; uint64_t v___x_3984_; uint64_t v___y_3986_; uint64_t v___y_4008_; 
v_fst_3980_ = lean_ctor_get(v_key_3973_, 0);
v_fst_3981_ = lean_ctor_get(v_snd_3974_, 0);
v_snd_3982_ = lean_ctor_get(v_snd_3974_, 1);
v___x_3983_ = lean_array_get_size(v_x_3971_);
v___x_3984_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_3980_);
if (lean_obj_tag(v_fst_3981_) == 0)
{
uint64_t v___x_4011_; 
v___x_4011_ = 11ULL;
v___y_3986_ = v___x_4011_;
goto v___jp_3985_;
}
else
{
lean_object* v_val_4012_; uint8_t v___x_4013_; 
v_val_4012_ = lean_ctor_get(v_fst_3981_, 0);
v___x_4013_ = lean_unbox(v_val_4012_);
if (v___x_4013_ == 0)
{
uint64_t v___x_4014_; 
v___x_4014_ = 13ULL;
v___y_4008_ = v___x_4014_;
goto v___jp_4007_;
}
else
{
uint64_t v___x_4015_; 
v___x_4015_ = 11ULL;
v___y_4008_ = v___x_4015_;
goto v___jp_4007_;
}
}
v___jp_3985_:
{
uint64_t v___x_3987_; uint64_t v___x_3988_; uint64_t v___x_3989_; uint64_t v___x_3990_; uint64_t v___x_3991_; uint64_t v_fold_3992_; uint64_t v___x_3993_; uint64_t v___x_3994_; uint64_t v___x_3995_; size_t v___x_3996_; size_t v___x_3997_; size_t v___x_3998_; size_t v___x_3999_; size_t v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_3987_ = l_Lean_Lsp_instHashableRange_hash(v_snd_3982_);
v___x_3988_ = lean_uint64_mix_hash(v___y_3986_, v___x_3987_);
v___x_3989_ = lean_uint64_mix_hash(v___x_3984_, v___x_3988_);
v___x_3990_ = 32ULL;
v___x_3991_ = lean_uint64_shift_right(v___x_3989_, v___x_3990_);
v_fold_3992_ = lean_uint64_xor(v___x_3989_, v___x_3991_);
v___x_3993_ = 16ULL;
v___x_3994_ = lean_uint64_shift_right(v_fold_3992_, v___x_3993_);
v___x_3995_ = lean_uint64_xor(v_fold_3992_, v___x_3994_);
v___x_3996_ = lean_uint64_to_usize(v___x_3995_);
v___x_3997_ = lean_usize_of_nat(v___x_3983_);
v___x_3998_ = ((size_t)1ULL);
v___x_3999_ = lean_usize_sub(v___x_3997_, v___x_3998_);
v___x_4000_ = lean_usize_land(v___x_3996_, v___x_3999_);
v___x_4001_ = lean_array_uget_borrowed(v_x_3971_, v___x_4000_);
lean_inc(v___x_4001_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 2, v___x_4001_);
v___x_4003_ = v___x_3978_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_key_3973_);
lean_ctor_set(v_reuseFailAlloc_4006_, 1, v_value_3975_);
lean_ctor_set(v_reuseFailAlloc_4006_, 2, v___x_4001_);
v___x_4003_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_array_uset(v_x_3971_, v___x_4000_, v___x_4003_);
v_x_3971_ = v___x_4004_;
v_x_3972_ = v_tail_3976_;
goto _start;
}
}
v___jp_4007_:
{
uint64_t v___x_4009_; uint64_t v___x_4010_; 
v___x_4009_ = 13ULL;
v___x_4010_ = lean_uint64_mix_hash(v___y_4008_, v___x_4009_);
v___y_3986_ = v___x_4010_;
goto v___jp_3985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object* v_i_4018_, lean_object* v_source_4019_, lean_object* v_target_4020_){
_start:
{
lean_object* v___x_4021_; uint8_t v___x_4022_; 
v___x_4021_ = lean_array_get_size(v_source_4019_);
v___x_4022_ = lean_nat_dec_lt(v_i_4018_, v___x_4021_);
if (v___x_4022_ == 0)
{
lean_dec_ref(v_source_4019_);
lean_dec(v_i_4018_);
return v_target_4020_;
}
else
{
lean_object* v_es_4023_; lean_object* v___x_4024_; lean_object* v_source_4025_; lean_object* v_target_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v_es_4023_ = lean_array_fget(v_source_4019_, v_i_4018_);
v___x_4024_ = lean_box(0);
v_source_4025_ = lean_array_fset(v_source_4019_, v_i_4018_, v___x_4024_);
v_target_4026_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_target_4020_, v_es_4023_);
v___x_4027_ = lean_unsigned_to_nat(1u);
v___x_4028_ = lean_nat_add(v_i_4018_, v___x_4027_);
lean_dec(v_i_4018_);
v_i_4018_ = v___x_4028_;
v_source_4019_ = v_source_4025_;
v_target_4020_ = v_target_4026_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object* v_data_4030_){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v_nbuckets_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4031_ = lean_array_get_size(v_data_4030_);
v___x_4032_ = lean_unsigned_to_nat(2u);
v_nbuckets_4033_ = lean_nat_mul(v___x_4031_, v___x_4032_);
v___x_4034_ = lean_unsigned_to_nat(0u);
v___x_4035_ = lean_box(0);
v___x_4036_ = lean_mk_array(v_nbuckets_4033_, v___x_4035_);
v___x_4037_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v___x_4034_, v_data_4030_, v___x_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object* v_x_4038_, lean_object* v_x_4039_){
_start:
{
if (lean_obj_tag(v_x_4038_) == 0)
{
if (lean_obj_tag(v_x_4039_) == 0)
{
uint8_t v___x_4040_; 
v___x_4040_ = 1;
return v___x_4040_;
}
else
{
uint8_t v___x_4041_; 
v___x_4041_ = 0;
return v___x_4041_;
}
}
else
{
if (lean_obj_tag(v_x_4039_) == 0)
{
uint8_t v___x_4042_; 
v___x_4042_ = 0;
return v___x_4042_;
}
else
{
lean_object* v_val_4043_; uint8_t v___x_4044_; 
v_val_4043_ = lean_ctor_get(v_x_4038_, 0);
v___x_4044_ = lean_unbox(v_val_4043_);
if (v___x_4044_ == 0)
{
lean_object* v_val_4045_; uint8_t v___x_4046_; 
v_val_4045_ = lean_ctor_get(v_x_4039_, 0);
v___x_4046_ = lean_unbox(v_val_4045_);
if (v___x_4046_ == 0)
{
uint8_t v___x_4047_; 
v___x_4047_ = 1;
return v___x_4047_;
}
else
{
uint8_t v___x_4048_; 
v___x_4048_ = lean_unbox(v_val_4043_);
return v___x_4048_;
}
}
else
{
lean_object* v_val_4049_; uint8_t v___x_4050_; 
v_val_4049_ = lean_ctor_get(v_x_4039_, 0);
v___x_4050_ = lean_unbox(v_val_4049_);
return v___x_4050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object* v_x_4051_, lean_object* v_x_4052_){
_start:
{
uint8_t v_res_4053_; lean_object* v_r_4054_; 
v_res_4053_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_x_4051_, v_x_4052_);
lean_dec(v_x_4052_);
lean_dec(v_x_4051_);
v_r_4054_ = lean_box(v_res_4053_);
return v_r_4054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object* v_a_4055_, lean_object* v_x_4056_){
_start:
{
if (lean_obj_tag(v_x_4056_) == 0)
{
lean_object* v___x_4057_; 
v___x_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4057_, 0, v_a_4055_);
return v___x_4057_;
}
else
{
lean_object* v_val_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4086_; 
v_val_4058_ = lean_ctor_get(v_x_4056_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_x_4056_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4060_ = v_x_4056_;
v_isShared_4061_ = v_isSharedCheck_4086_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_val_4058_);
lean_dec(v_x_4056_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4086_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v_ident_4062_; lean_object* v_aliases_4063_; lean_object* v_range_4064_; lean_object* v_stx_4065_; lean_object* v_ci_4066_; lean_object* v_info_4067_; uint8_t v_isBinder_4068_; lean_object* v_aliases_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4080_; 
v_ident_4062_ = lean_ctor_get(v_val_4058_, 0);
lean_inc_ref(v_ident_4062_);
v_aliases_4063_ = lean_ctor_get(v_val_4058_, 1);
lean_inc_ref(v_aliases_4063_);
v_range_4064_ = lean_ctor_get(v_val_4058_, 2);
lean_inc_ref(v_range_4064_);
v_stx_4065_ = lean_ctor_get(v_val_4058_, 3);
lean_inc(v_stx_4065_);
v_ci_4066_ = lean_ctor_get(v_val_4058_, 4);
lean_inc_ref(v_ci_4066_);
v_info_4067_ = lean_ctor_get(v_val_4058_, 5);
lean_inc_ref(v_info_4067_);
v_isBinder_4068_ = lean_ctor_get_uint8(v_val_4058_, sizeof(void*)*6);
lean_dec(v_val_4058_);
v_aliases_4069_ = lean_ctor_get(v_a_4055_, 1);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_a_4055_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; lean_object* v_unused_4082_; lean_object* v_unused_4083_; lean_object* v_unused_4084_; lean_object* v_unused_4085_; 
v_unused_4081_ = lean_ctor_get(v_a_4055_, 5);
lean_dec(v_unused_4081_);
v_unused_4082_ = lean_ctor_get(v_a_4055_, 4);
lean_dec(v_unused_4082_);
v_unused_4083_ = lean_ctor_get(v_a_4055_, 3);
lean_dec(v_unused_4083_);
v_unused_4084_ = lean_ctor_get(v_a_4055_, 2);
lean_dec(v_unused_4084_);
v_unused_4085_ = lean_ctor_get(v_a_4055_, 0);
lean_dec(v_unused_4085_);
v___x_4071_ = v_a_4055_;
v_isShared_4072_ = v_isSharedCheck_4080_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_aliases_4069_);
lean_dec(v_a_4055_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4080_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4073_ = l_Array_append___redArg(v_aliases_4063_, v_aliases_4069_);
lean_dec_ref(v_aliases_4069_);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 5, v_info_4067_);
lean_ctor_set(v___x_4071_, 4, v_ci_4066_);
lean_ctor_set(v___x_4071_, 3, v_stx_4065_);
lean_ctor_set(v___x_4071_, 2, v_range_4064_);
lean_ctor_set(v___x_4071_, 1, v___x_4073_);
lean_ctor_set(v___x_4071_, 0, v_ident_4062_);
v___x_4075_ = v___x_4071_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_ident_4062_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_range_4064_);
lean_ctor_set(v_reuseFailAlloc_4079_, 3, v_stx_4065_);
lean_ctor_set(v_reuseFailAlloc_4079_, 4, v_ci_4066_);
lean_ctor_set(v_reuseFailAlloc_4079_, 5, v_info_4067_);
v___x_4075_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4077_; 
lean_ctor_set_uint8(v___x_4075_, sizeof(void*)*6, v_isBinder_4068_);
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 0, v___x_4075_);
v___x_4077_ = v___x_4060_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_x_4089_){
_start:
{
if (lean_obj_tag(v_x_4089_) == 0)
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v_val_4092_; lean_object* v___x_4093_; 
v___x_4090_ = lean_box(0);
v___x_4091_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4087_, v___x_4090_);
v_val_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_val_4092_);
lean_dec(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4093_, 0, v_a_4088_);
lean_ctor_set(v___x_4093_, 1, v_val_4092_);
lean_ctor_set(v___x_4093_, 2, v_x_4089_);
return v___x_4093_;
}
else
{
lean_object* v_key_4094_; lean_object* v_value_4095_; lean_object* v_tail_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4123_; 
v_key_4094_ = lean_ctor_get(v_x_4089_, 0);
v_value_4095_ = lean_ctor_get(v_x_4089_, 1);
v_tail_4096_ = lean_ctor_get(v_x_4089_, 2);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_x_4089_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4098_ = v_x_4089_;
v_isShared_4099_ = v_isSharedCheck_4123_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_tail_4096_);
lean_inc(v_value_4095_);
lean_inc(v_key_4094_);
lean_dec(v_x_4089_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4123_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
uint8_t v___y_4101_; lean_object* v_fst_4112_; lean_object* v_snd_4113_; lean_object* v_fst_4114_; lean_object* v_snd_4115_; uint8_t v___x_4116_; 
v_fst_4112_ = lean_ctor_get(v_key_4094_, 0);
v_snd_4113_ = lean_ctor_get(v_key_4094_, 1);
v_fst_4114_ = lean_ctor_get(v_a_4088_, 0);
v_snd_4115_ = lean_ctor_get(v_a_4088_, 1);
v___x_4116_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4112_, v_fst_4114_);
if (v___x_4116_ == 0)
{
v___y_4101_ = v___x_4116_;
goto v___jp_4100_;
}
else
{
lean_object* v_fst_4117_; lean_object* v_snd_4118_; lean_object* v_fst_4119_; lean_object* v_snd_4120_; uint8_t v___x_4121_; 
v_fst_4117_ = lean_ctor_get(v_snd_4113_, 0);
v_snd_4118_ = lean_ctor_get(v_snd_4113_, 1);
v_fst_4119_ = lean_ctor_get(v_snd_4115_, 0);
v_snd_4120_ = lean_ctor_get(v_snd_4115_, 1);
v___x_4121_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4117_, v_fst_4119_);
if (v___x_4121_ == 0)
{
v___y_4101_ = v___x_4121_;
goto v___jp_4100_;
}
else
{
uint8_t v___x_4122_; 
v___x_4122_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4118_, v_snd_4120_);
v___y_4101_ = v___x_4122_;
goto v___jp_4100_;
}
}
v___jp_4100_:
{
if (v___y_4101_ == 0)
{
lean_object* v_tail_4102_; lean_object* v___x_4104_; 
v_tail_4102_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4087_, v_a_4088_, v_tail_4096_);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 2, v_tail_4102_);
v___x_4104_ = v___x_4098_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_key_4094_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v_value_4095_);
lean_ctor_set(v_reuseFailAlloc_4105_, 2, v_tail_4102_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
else
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v_val_4108_; lean_object* v___x_4110_; 
lean_dec(v_key_4094_);
v___x_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4106_, 0, v_value_4095_);
v___x_4107_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4087_, v___x_4106_);
v_val_4108_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_val_4108_);
lean_dec(v___x_4107_);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 1, v_val_4108_);
lean_ctor_set(v___x_4098_, 0, v_a_4088_);
v___x_4110_ = v___x_4098_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4088_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v_val_4108_);
lean_ctor_set(v_reuseFailAlloc_4111_, 2, v_tail_4096_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_a_4124_, lean_object* v_x_4125_){
_start:
{
if (lean_obj_tag(v_x_4125_) == 0)
{
uint8_t v___x_4126_; 
v___x_4126_ = 0;
return v___x_4126_;
}
else
{
lean_object* v_key_4127_; lean_object* v_tail_4128_; uint8_t v___y_4130_; lean_object* v_fst_4132_; lean_object* v_snd_4133_; lean_object* v_fst_4134_; lean_object* v_snd_4135_; uint8_t v___x_4136_; 
v_key_4127_ = lean_ctor_get(v_x_4125_, 0);
v_tail_4128_ = lean_ctor_get(v_x_4125_, 2);
v_fst_4132_ = lean_ctor_get(v_key_4127_, 0);
v_snd_4133_ = lean_ctor_get(v_key_4127_, 1);
v_fst_4134_ = lean_ctor_get(v_a_4124_, 0);
v_snd_4135_ = lean_ctor_get(v_a_4124_, 1);
v___x_4136_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4132_, v_fst_4134_);
if (v___x_4136_ == 0)
{
v___y_4130_ = v___x_4136_;
goto v___jp_4129_;
}
else
{
lean_object* v_fst_4137_; lean_object* v_snd_4138_; lean_object* v_fst_4139_; lean_object* v_snd_4140_; uint8_t v___x_4141_; 
v_fst_4137_ = lean_ctor_get(v_snd_4133_, 0);
v_snd_4138_ = lean_ctor_get(v_snd_4133_, 1);
v_fst_4139_ = lean_ctor_get(v_snd_4135_, 0);
v_snd_4140_ = lean_ctor_get(v_snd_4135_, 1);
v___x_4141_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4137_, v_fst_4139_);
if (v___x_4141_ == 0)
{
v___y_4130_ = v___x_4141_;
goto v___jp_4129_;
}
else
{
uint8_t v___x_4142_; 
v___x_4142_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4138_, v_snd_4140_);
v___y_4130_ = v___x_4142_;
goto v___jp_4129_;
}
}
v___jp_4129_:
{
if (v___y_4130_ == 0)
{
v_x_4125_ = v_tail_4128_;
goto _start;
}
else
{
return v___y_4130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object* v_a_4143_, lean_object* v_x_4144_){
_start:
{
uint8_t v_res_4145_; lean_object* v_r_4146_; 
v_res_4145_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4143_, v_x_4144_);
lean_dec(v_x_4144_);
lean_dec_ref(v_a_4143_);
v_r_4146_ = lean_box(v_res_4145_);
return v_r_4146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4147_, lean_object* v_m_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v___y_4151_; lean_object* v___y_4152_; size_t v___y_4153_; lean_object* v___y_4154_; lean_object* v_snd_4157_; lean_object* v_size_4158_; lean_object* v_buckets_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4218_; 
v_snd_4157_ = lean_ctor_get(v_a_4149_, 1);
v_size_4158_ = lean_ctor_get(v_m_4148_, 0);
v_buckets_4159_ = lean_ctor_get(v_m_4148_, 1);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_m_4148_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4161_ = v_m_4148_;
v_isShared_4162_ = v_isSharedCheck_4218_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_buckets_4159_);
lean_inc(v_size_4158_);
lean_dec(v_m_4148_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4218_;
goto v_resetjp_4160_;
}
v___jp_4150_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = lean_array_uset(v___y_4151_, v___y_4153_, v___y_4152_);
v___x_4156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___y_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
return v___x_4156_;
}
v_resetjp_4160_:
{
lean_object* v_fst_4163_; lean_object* v_fst_4164_; lean_object* v_snd_4165_; lean_object* v___x_4166_; uint64_t v___x_4167_; uint64_t v___y_4169_; uint64_t v___y_4210_; 
v_fst_4163_ = lean_ctor_get(v_a_4149_, 0);
v_fst_4164_ = lean_ctor_get(v_snd_4157_, 0);
v_snd_4165_ = lean_ctor_get(v_snd_4157_, 1);
v___x_4166_ = lean_array_get_size(v_buckets_4159_);
v___x_4167_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4163_);
if (lean_obj_tag(v_fst_4164_) == 0)
{
uint64_t v___x_4213_; 
v___x_4213_ = 11ULL;
v___y_4169_ = v___x_4213_;
goto v___jp_4168_;
}
else
{
lean_object* v_val_4214_; uint8_t v___x_4215_; 
v_val_4214_ = lean_ctor_get(v_fst_4164_, 0);
v___x_4215_ = lean_unbox(v_val_4214_);
if (v___x_4215_ == 0)
{
uint64_t v___x_4216_; 
v___x_4216_ = 13ULL;
v___y_4210_ = v___x_4216_;
goto v___jp_4209_;
}
else
{
uint64_t v___x_4217_; 
v___x_4217_ = 11ULL;
v___y_4210_ = v___x_4217_;
goto v___jp_4209_;
}
}
v___jp_4168_:
{
uint64_t v___x_4170_; uint64_t v___x_4171_; uint64_t v___x_4172_; uint64_t v___x_4173_; uint64_t v___x_4174_; uint64_t v_fold_4175_; uint64_t v___x_4176_; uint64_t v___x_4177_; uint64_t v___x_4178_; size_t v___x_4179_; size_t v___x_4180_; size_t v___x_4181_; size_t v___x_4182_; size_t v___x_4183_; lean_object* v_bkt_4184_; uint8_t v___x_4185_; 
v___x_4170_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4165_);
v___x_4171_ = lean_uint64_mix_hash(v___y_4169_, v___x_4170_);
v___x_4172_ = lean_uint64_mix_hash(v___x_4167_, v___x_4171_);
v___x_4173_ = 32ULL;
v___x_4174_ = lean_uint64_shift_right(v___x_4172_, v___x_4173_);
v_fold_4175_ = lean_uint64_xor(v___x_4172_, v___x_4174_);
v___x_4176_ = 16ULL;
v___x_4177_ = lean_uint64_shift_right(v_fold_4175_, v___x_4176_);
v___x_4178_ = lean_uint64_xor(v_fold_4175_, v___x_4177_);
v___x_4179_ = lean_uint64_to_usize(v___x_4178_);
v___x_4180_ = lean_usize_of_nat(v___x_4166_);
v___x_4181_ = ((size_t)1ULL);
v___x_4182_ = lean_usize_sub(v___x_4180_, v___x_4181_);
v___x_4183_ = lean_usize_land(v___x_4179_, v___x_4182_);
v_bkt_4184_ = lean_array_uget_borrowed(v_buckets_4159_, v___x_4183_);
v___x_4185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4149_, v_bkt_4184_);
if (v___x_4185_ == 0)
{
lean_object* v___x_4186_; lean_object* v_size_x27_4187_; lean_object* v___x_4188_; lean_object* v_buckets_x27_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4186_ = lean_unsigned_to_nat(1u);
v_size_x27_4187_ = lean_nat_add(v_size_4158_, v___x_4186_);
lean_dec(v_size_4158_);
lean_inc(v_bkt_4184_);
v___x_4188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4188_, 0, v_a_4149_);
lean_ctor_set(v___x_4188_, 1, v_a_4147_);
lean_ctor_set(v___x_4188_, 2, v_bkt_4184_);
v_buckets_x27_4189_ = lean_array_uset(v_buckets_4159_, v___x_4183_, v___x_4188_);
v___x_4190_ = lean_unsigned_to_nat(4u);
v___x_4191_ = lean_nat_mul(v_size_x27_4187_, v___x_4190_);
v___x_4192_ = lean_unsigned_to_nat(3u);
v___x_4193_ = lean_nat_div(v___x_4191_, v___x_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = lean_array_get_size(v_buckets_x27_4189_);
v___x_4195_ = lean_nat_dec_le(v___x_4193_, v___x_4194_);
lean_dec(v___x_4193_);
if (v___x_4195_ == 0)
{
lean_object* v_val_4196_; lean_object* v___x_4198_; 
v_val_4196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_buckets_x27_4189_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 1, v_val_4196_);
lean_ctor_set(v___x_4161_, 0, v_size_x27_4187_);
v___x_4198_ = v___x_4161_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_size_x27_4187_);
lean_ctor_set(v_reuseFailAlloc_4199_, 1, v_val_4196_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
else
{
lean_object* v___x_4201_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 1, v_buckets_x27_4189_);
lean_ctor_set(v___x_4161_, 0, v_size_x27_4187_);
v___x_4201_ = v___x_4161_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_size_x27_4187_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v_buckets_x27_4189_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
else
{
lean_object* v___x_4203_; lean_object* v_buckets_x27_4204_; lean_object* v_bkt_x27_4205_; uint8_t v___x_4206_; 
lean_inc(v_bkt_4184_);
lean_del_object(v___x_4161_);
v___x_4203_ = lean_box(0);
v_buckets_x27_4204_ = lean_array_uset(v_buckets_4159_, v___x_4183_, v___x_4203_);
lean_inc_ref(v_a_4149_);
v_bkt_x27_4205_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4147_, v_a_4149_, v_bkt_4184_);
v___x_4206_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4149_, v_bkt_x27_4205_);
lean_dec_ref(v_a_4149_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = lean_unsigned_to_nat(1u);
v___x_4208_ = lean_nat_sub(v_size_4158_, v___x_4207_);
lean_dec(v_size_4158_);
v___y_4151_ = v_buckets_x27_4204_;
v___y_4152_ = v_bkt_x27_4205_;
v___y_4153_ = v___x_4183_;
v___y_4154_ = v___x_4208_;
goto v___jp_4150_;
}
else
{
v___y_4151_ = v_buckets_x27_4204_;
v___y_4152_ = v_bkt_x27_4205_;
v___y_4153_ = v___x_4183_;
v___y_4154_ = v_size_4158_;
goto v___jp_4150_;
}
}
}
v___jp_4209_:
{
uint64_t v___x_4211_; uint64_t v___x_4212_; 
v___x_4211_ = 13ULL;
v___x_4212_ = lean_uint64_mix_hash(v___y_4210_, v___x_4211_);
v___y_4169_ = v___x_4212_;
goto v___jp_4168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4219_, lean_object* v_as_4220_, size_t v_sz_4221_, size_t v_i_4222_, lean_object* v_b_4223_){
_start:
{
uint8_t v___x_4224_; 
v___x_4224_ = lean_usize_dec_lt(v_i_4222_, v_sz_4221_);
if (v___x_4224_ == 0)
{
return v_b_4223_;
}
else
{
lean_object* v_a_4225_; lean_object* v___y_4227_; 
v_a_4225_ = lean_array_uget_borrowed(v_as_4220_, v_i_4222_);
if (v_allowSimultaneousBinderUse_4219_ == 0)
{
lean_object* v___x_4236_; 
v___x_4236_ = lean_box(0);
v___y_4227_ = v___x_4236_;
goto v___jp_4226_;
}
else
{
uint8_t v_isBinder_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v_isBinder_4237_ = lean_ctor_get_uint8(v_a_4225_, sizeof(void*)*6);
v___x_4238_ = lean_box(v_isBinder_4237_);
v___x_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
v___y_4227_ = v___x_4239_;
goto v___jp_4226_;
}
v___jp_4226_:
{
lean_object* v_ident_4228_; lean_object* v_range_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; size_t v___x_4233_; size_t v___x_4234_; 
v_ident_4228_ = lean_ctor_get(v_a_4225_, 0);
v_range_4229_ = lean_ctor_get(v_a_4225_, 2);
lean_inc_ref(v_range_4229_);
v___x_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___y_4227_);
lean_ctor_set(v___x_4230_, 1, v_range_4229_);
lean_inc_ref(v_ident_4228_);
v___x_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4231_, 0, v_ident_4228_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
lean_inc(v_a_4225_);
v___x_4232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4225_, v_b_4223_, v___x_4231_);
v___x_4233_ = ((size_t)1ULL);
v___x_4234_ = lean_usize_add(v_i_4222_, v___x_4233_);
v_i_4222_ = v___x_4234_;
v_b_4223_ = v___x_4232_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4240_, lean_object* v_as_4241_, lean_object* v_sz_4242_, lean_object* v_i_4243_, lean_object* v_b_4244_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4245_; size_t v_sz_boxed_4246_; size_t v_i_boxed_4247_; lean_object* v_res_4248_; 
v_allowSimultaneousBinderUse_boxed_4245_ = lean_unbox(v_allowSimultaneousBinderUse_4240_);
v_sz_boxed_4246_ = lean_unbox_usize(v_sz_4242_);
lean_dec(v_sz_4242_);
v_i_boxed_4247_ = lean_unbox_usize(v_i_4243_);
lean_dec(v_i_4243_);
v_res_4248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4245_, v_as_4241_, v_sz_boxed_4246_, v_i_boxed_4247_, v_b_4244_);
lean_dec_ref(v_as_4241_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4249_, lean_object* v_x_4250_){
_start:
{
if (lean_obj_tag(v_x_4250_) == 0)
{
return v_x_4249_;
}
else
{
lean_object* v_value_4251_; lean_object* v_tail_4252_; lean_object* v___x_4253_; 
v_value_4251_ = lean_ctor_get(v_x_4250_, 1);
lean_inc(v_value_4251_);
v_tail_4252_ = lean_ctor_get(v_x_4250_, 2);
lean_inc(v_tail_4252_);
lean_dec_ref_known(v_x_4250_, 3);
v___x_4253_ = lean_array_push(v_x_4249_, v_value_4251_);
v_x_4249_ = v___x_4253_;
v_x_4250_ = v_tail_4252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4255_, size_t v_i_4256_, size_t v_stop_4257_, lean_object* v_b_4258_){
_start:
{
uint8_t v___x_4259_; 
v___x_4259_ = lean_usize_dec_eq(v_i_4256_, v_stop_4257_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4260_; lean_object* v___x_4261_; size_t v___x_4262_; size_t v___x_4263_; 
v___x_4260_ = lean_array_uget_borrowed(v_as_4255_, v_i_4256_);
lean_inc(v___x_4260_);
v___x_4261_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4258_, v___x_4260_);
v___x_4262_ = ((size_t)1ULL);
v___x_4263_ = lean_usize_add(v_i_4256_, v___x_4262_);
v_i_4256_ = v___x_4263_;
v_b_4258_ = v___x_4261_;
goto _start;
}
else
{
return v_b_4258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4265_, lean_object* v_i_4266_, lean_object* v_stop_4267_, lean_object* v_b_4268_){
_start:
{
size_t v_i_boxed_4269_; size_t v_stop_boxed_4270_; lean_object* v_res_4271_; 
v_i_boxed_4269_ = lean_unbox_usize(v_i_4266_);
lean_dec(v_i_4266_);
v_stop_boxed_4270_ = lean_unbox_usize(v_stop_4267_);
lean_dec(v_stop_4267_);
v_res_4271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4265_, v_i_boxed_4269_, v_stop_boxed_4270_, v_b_4268_);
lean_dec_ref(v_as_4265_);
return v_res_4271_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4272_ = lean_box(0);
v___x_4273_ = lean_unsigned_to_nat(16u);
v___x_4274_ = lean_mk_array(v___x_4273_, v___x_4272_);
return v___x_4274_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v_refsByIdAndRange_4277_; 
v___x_4275_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4276_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4277_, 0, v___x_4276_);
lean_ctor_set(v_refsByIdAndRange_4277_, 1, v___x_4275_);
return v_refsByIdAndRange_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4278_, uint8_t v_allowSimultaneousBinderUse_4279_){
_start:
{
lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4289_; lean_object* v___x_4296_; lean_object* v_refsByIdAndRange_4297_; size_t v_sz_4298_; size_t v___x_4299_; lean_object* v___x_4300_; lean_object* v_buckets_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4296_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4297_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4298_ = lean_array_size(v_refs_4278_);
v___x_4299_ = ((size_t)0ULL);
v___x_4300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4279_, v_refs_4278_, v_sz_4298_, v___x_4299_, v_refsByIdAndRange_4297_);
v_buckets_4301_ = lean_ctor_get(v___x_4300_, 1);
lean_inc_ref(v_buckets_4301_);
lean_dec_ref(v___x_4300_);
v___x_4302_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4303_ = lean_array_get_size(v_buckets_4301_);
v___x_4304_ = lean_nat_dec_lt(v___x_4296_, v___x_4303_);
if (v___x_4304_ == 0)
{
lean_dec_ref(v_buckets_4301_);
v___y_4289_ = v___x_4302_;
goto v___jp_4288_;
}
else
{
uint8_t v___x_4305_; 
v___x_4305_ = lean_nat_dec_le(v___x_4303_, v___x_4303_);
if (v___x_4305_ == 0)
{
if (v___x_4304_ == 0)
{
lean_dec_ref(v_buckets_4301_);
v___y_4289_ = v___x_4302_;
goto v___jp_4288_;
}
else
{
size_t v___x_4306_; lean_object* v___x_4307_; 
v___x_4306_ = lean_usize_of_nat(v___x_4303_);
v___x_4307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4301_, v___x_4299_, v___x_4306_, v___x_4302_);
lean_dec_ref(v_buckets_4301_);
v___y_4289_ = v___x_4307_;
goto v___jp_4288_;
}
}
else
{
size_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_usize_of_nat(v___x_4303_);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4301_, v___x_4299_, v___x_4308_, v___x_4302_);
lean_dec_ref(v_buckets_4301_);
v___y_4289_ = v___x_4309_;
goto v___jp_4288_;
}
}
v___jp_4280_:
{
uint8_t v___x_4285_; 
v___x_4285_ = lean_nat_dec_le(v___y_4284_, v___y_4283_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; 
lean_dec(v___y_4283_);
lean_inc(v___y_4284_);
v___x_4286_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4281_, v___y_4282_, v___y_4284_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec(v___y_4281_);
return v___x_4286_;
}
else
{
lean_object* v___x_4287_; 
v___x_4287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4281_, v___y_4282_, v___y_4284_, v___y_4283_);
lean_dec(v___y_4283_);
lean_dec(v___y_4281_);
return v___x_4287_;
}
}
v___jp_4288_:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4290_ = lean_array_get_size(v___y_4289_);
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = lean_nat_dec_eq(v___x_4290_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4293_ = lean_unsigned_to_nat(1u);
v___x_4294_ = lean_nat_sub(v___x_4290_, v___x_4293_);
v___x_4295_ = lean_nat_dec_le(v___x_4291_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_inc(v___x_4294_);
v___y_4281_ = v___x_4290_;
v___y_4282_ = v___y_4289_;
v___y_4283_ = v___x_4294_;
v___y_4284_ = v___x_4294_;
goto v___jp_4280_;
}
else
{
v___y_4281_ = v___x_4290_;
v___y_4282_ = v___y_4289_;
v___y_4283_ = v___x_4294_;
v___y_4284_ = v___x_4291_;
goto v___jp_4280_;
}
}
else
{
return v___y_4289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object* v_refs_4310_, lean_object* v_allowSimultaneousBinderUse_4311_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4312_; lean_object* v_res_4313_; 
v_allowSimultaneousBinderUse_boxed_4312_ = lean_unbox(v_allowSimultaneousBinderUse_4311_);
v_res_4313_ = l_Lean_Server_dedupReferences(v_refs_4310_, v_allowSimultaneousBinderUse_boxed_4312_);
lean_dec_ref(v_refs_4310_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object* v_n_4314_, lean_object* v_as_4315_, lean_object* v_lo_4316_, lean_object* v_hi_4317_, lean_object* v_w_4318_, lean_object* v_hlo_4319_, lean_object* v_hhi_4320_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4314_, v_as_4315_, v_lo_4316_, v_hi_4317_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object* v_n_4322_, lean_object* v_as_4323_, lean_object* v_lo_4324_, lean_object* v_hi_4325_, lean_object* v_w_4326_, lean_object* v_hlo_4327_, lean_object* v_hhi_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(v_n_4322_, v_as_4323_, v_lo_4324_, v_hi_4325_, v_w_4326_, v_hlo_4327_, v_hhi_4328_);
lean_dec(v_hi_4325_);
lean_dec(v_n_4322_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(lean_object* v_n_4330_, lean_object* v_lo_4331_, lean_object* v_hi_4332_, lean_object* v_hhi_4333_, lean_object* v_pivot_4334_, lean_object* v_as_4335_, lean_object* v_i_4336_, lean_object* v_k_4337_, lean_object* v_ilo_4338_, lean_object* v_ik_4339_, lean_object* v_w_4340_){
_start:
{
lean_object* v___x_4341_; 
v___x_4341_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_4332_, v_pivot_4334_, v_as_4335_, v_i_4336_, v_k_4337_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___boxed(lean_object* v_n_4342_, lean_object* v_lo_4343_, lean_object* v_hi_4344_, lean_object* v_hhi_4345_, lean_object* v_pivot_4346_, lean_object* v_as_4347_, lean_object* v_i_4348_, lean_object* v_k_4349_, lean_object* v_ilo_4350_, lean_object* v_ik_4351_, lean_object* v_w_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(v_n_4342_, v_lo_4343_, v_hi_4344_, v_hhi_4345_, v_pivot_4346_, v_as_4347_, v_i_4348_, v_k_4349_, v_ilo_4350_, v_ik_4351_, v_w_4352_);
lean_dec_ref(v_pivot_4346_);
lean_dec(v_hi_4344_);
lean_dec(v_lo_4343_);
lean_dec(v_n_4342_);
return v_res_4353_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object* v_00_u03b2_4354_, lean_object* v_a_4355_, lean_object* v_x_4356_){
_start:
{
uint8_t v___x_4357_; 
v___x_4357_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4355_, v_x_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4358_, lean_object* v_a_4359_, lean_object* v_x_4360_){
_start:
{
uint8_t v_res_4361_; lean_object* v_r_4362_; 
v_res_4361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(v_00_u03b2_4358_, v_a_4359_, v_x_4360_);
lean_dec(v_x_4360_);
lean_dec_ref(v_a_4359_);
v_r_4362_ = lean_box(v_res_4361_);
return v_r_4362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object* v_00_u03b2_4363_, lean_object* v_data_4364_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_data_4364_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4366_, lean_object* v_i_4367_, lean_object* v_source_4368_, lean_object* v_target_4369_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v_i_4367_, v_source_4368_, v_target_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4371_, lean_object* v_x_4372_, lean_object* v_x_4373_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_x_4372_, v_x_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object* v_as_4375_, size_t v_i_4376_, size_t v_stop_4377_, lean_object* v_b_4378_){
_start:
{
uint8_t v___x_4379_; 
v___x_4379_ = lean_usize_dec_eq(v_i_4376_, v_stop_4377_);
if (v___x_4379_ == 0)
{
lean_object* v___x_4380_; lean_object* v___x_4381_; size_t v___x_4382_; size_t v___x_4383_; 
v___x_4380_ = lean_array_uget_borrowed(v_as_4375_, v_i_4376_);
lean_inc(v___x_4380_);
v___x_4381_ = l_Lean_Server_ModuleRefs_addRef(v_b_4378_, v___x_4380_);
v___x_4382_ = ((size_t)1ULL);
v___x_4383_ = lean_usize_add(v_i_4376_, v___x_4382_);
v_i_4376_ = v___x_4383_;
v_b_4378_ = v___x_4381_;
goto _start;
}
else
{
return v_b_4378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object* v_as_4385_, lean_object* v_i_4386_, lean_object* v_stop_4387_, lean_object* v_b_4388_){
_start:
{
size_t v_i_boxed_4389_; size_t v_stop_boxed_4390_; lean_object* v_res_4391_; 
v_i_boxed_4389_ = lean_unbox_usize(v_i_4386_);
lean_dec(v_i_4386_);
v_stop_boxed_4390_ = lean_unbox_usize(v_stop_4387_);
lean_dec(v_stop_4387_);
v_res_4391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_as_4385_, v_i_boxed_4389_, v_stop_boxed_4390_, v_b_4388_);
lean_dec_ref(v_as_4385_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object* v_as_4392_, size_t v_i_4393_, size_t v_stop_4394_, lean_object* v_b_4395_){
_start:
{
lean_object* v___y_4397_; uint8_t v___x_4401_; 
v___x_4401_ = lean_usize_dec_eq(v_i_4393_, v_stop_4394_);
if (v___x_4401_ == 0)
{
lean_object* v___x_4402_; lean_object* v_ident_4403_; 
v___x_4402_ = lean_array_uget_borrowed(v_as_4392_, v_i_4393_);
v_ident_4403_ = lean_ctor_get(v___x_4402_, 0);
if (lean_obj_tag(v_ident_4403_) == 1)
{
v___y_4397_ = v_b_4395_;
goto v___jp_4396_;
}
else
{
lean_object* v___x_4404_; 
lean_inc(v___x_4402_);
v___x_4404_ = lean_array_push(v_b_4395_, v___x_4402_);
v___y_4397_ = v___x_4404_;
goto v___jp_4396_;
}
}
else
{
return v_b_4395_;
}
v___jp_4396_:
{
size_t v___x_4398_; size_t v___x_4399_; 
v___x_4398_ = ((size_t)1ULL);
v___x_4399_ = lean_usize_add(v_i_4393_, v___x_4398_);
v_i_4393_ = v___x_4399_;
v_b_4395_ = v___y_4397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object* v_as_4405_, lean_object* v_i_4406_, lean_object* v_stop_4407_, lean_object* v_b_4408_){
_start:
{
size_t v_i_boxed_4409_; size_t v_stop_boxed_4410_; lean_object* v_res_4411_; 
v_i_boxed_4409_ = lean_unbox_usize(v_i_4406_);
lean_dec(v_i_4406_);
v_stop_boxed_4410_ = lean_unbox_usize(v_stop_4407_);
lean_dec(v_stop_4407_);
v_res_4411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_as_4405_, v_i_boxed_4409_, v_stop_boxed_4410_, v_b_4408_);
lean_dec_ref(v_as_4405_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object* v_text_4412_, lean_object* v_trees_4413_, uint8_t v_localVars_4414_, uint8_t v_allowSimultaneousBinderUse_4415_){
_start:
{
lean_object* v_refs_4417_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v_refs_4431_; 
v___x_4429_ = l_Lean_Server_findReferences(v_text_4412_, v_trees_4413_);
v___x_4430_ = l_Lean_Server_combineIdents(v_trees_4413_, v___x_4429_);
lean_dec_ref(v___x_4429_);
v_refs_4431_ = l_Lean_Server_dedupReferences(v___x_4430_, v_allowSimultaneousBinderUse_4415_);
lean_dec_ref(v___x_4430_);
if (v_localVars_4414_ == 0)
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; uint8_t v___x_4435_; 
v___x_4432_ = lean_unsigned_to_nat(0u);
v___x_4433_ = lean_array_get_size(v_refs_4431_);
v___x_4434_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4435_ = lean_nat_dec_lt(v___x_4432_, v___x_4433_);
if (v___x_4435_ == 0)
{
lean_dec_ref(v_refs_4431_);
v_refs_4417_ = v___x_4434_;
goto v___jp_4416_;
}
else
{
uint8_t v___x_4436_; 
v___x_4436_ = lean_nat_dec_le(v___x_4433_, v___x_4433_);
if (v___x_4436_ == 0)
{
if (v___x_4435_ == 0)
{
lean_dec_ref(v_refs_4431_);
v_refs_4417_ = v___x_4434_;
goto v___jp_4416_;
}
else
{
size_t v___x_4437_; size_t v___x_4438_; lean_object* v___x_4439_; 
v___x_4437_ = ((size_t)0ULL);
v___x_4438_ = lean_usize_of_nat(v___x_4433_);
v___x_4439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4431_, v___x_4437_, v___x_4438_, v___x_4434_);
lean_dec_ref(v_refs_4431_);
v_refs_4417_ = v___x_4439_;
goto v___jp_4416_;
}
}
else
{
size_t v___x_4440_; size_t v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = ((size_t)0ULL);
v___x_4441_ = lean_usize_of_nat(v___x_4433_);
v___x_4442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4431_, v___x_4440_, v___x_4441_, v___x_4434_);
lean_dec_ref(v_refs_4431_);
v_refs_4417_ = v___x_4442_;
goto v___jp_4416_;
}
}
}
else
{
v_refs_4417_ = v_refs_4431_;
goto v___jp_4416_;
}
v___jp_4416_:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4418_ = lean_box(1);
v___x_4419_ = lean_unsigned_to_nat(0u);
v___x_4420_ = lean_array_get_size(v_refs_4417_);
v___x_4421_ = lean_nat_dec_lt(v___x_4419_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_dec_ref(v_refs_4417_);
return v___x_4418_;
}
else
{
uint8_t v___x_4422_; 
v___x_4422_ = lean_nat_dec_le(v___x_4420_, v___x_4420_);
if (v___x_4422_ == 0)
{
if (v___x_4421_ == 0)
{
lean_dec_ref(v_refs_4417_);
return v___x_4418_;
}
else
{
size_t v___x_4423_; size_t v___x_4424_; lean_object* v___x_4425_; 
v___x_4423_ = ((size_t)0ULL);
v___x_4424_ = lean_usize_of_nat(v___x_4420_);
v___x_4425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4417_, v___x_4423_, v___x_4424_, v___x_4418_);
lean_dec_ref(v_refs_4417_);
return v___x_4425_;
}
}
else
{
size_t v___x_4426_; size_t v___x_4427_; lean_object* v___x_4428_; 
v___x_4426_ = ((size_t)0ULL);
v___x_4427_ = lean_usize_of_nat(v___x_4420_);
v___x_4428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4417_, v___x_4426_, v___x_4427_, v___x_4418_);
lean_dec_ref(v_refs_4417_);
return v___x_4428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object* v_text_4443_, lean_object* v_trees_4444_, lean_object* v_localVars_4445_, lean_object* v_allowSimultaneousBinderUse_4446_){
_start:
{
uint8_t v_localVars_boxed_4447_; uint8_t v_allowSimultaneousBinderUse_boxed_4448_; lean_object* v_res_4449_; 
v_localVars_boxed_4447_ = lean_unbox(v_localVars_4445_);
v_allowSimultaneousBinderUse_boxed_4448_ = lean_unbox(v_allowSimultaneousBinderUse_4446_);
v_res_4449_ = l_Lean_Server_findModuleRefs(v_text_4443_, v_trees_4444_, v_localVars_boxed_4447_, v_allowSimultaneousBinderUse_boxed_4448_);
lean_dec_ref(v_trees_4444_);
return v_res_4449_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t v_a_4457_, uint8_t v_a_4458_){
_start:
{
switch(v_a_4457_)
{
case 0:
{
if (v_a_4458_ == 1)
{
uint8_t v___x_4459_; 
v___x_4459_ = 2;
return v___x_4459_;
}
else
{
return v_a_4458_;
}
}
case 1:
{
if (v_a_4458_ == 0)
{
uint8_t v___x_4460_; 
v___x_4460_ = 2;
return v___x_4460_;
}
else
{
return v_a_4458_;
}
}
default: 
{
return v_a_4457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
uint8_t v_a_46__boxed_4463_; uint8_t v_a_47__boxed_4464_; uint8_t v_res_4465_; lean_object* v_r_4466_; 
v_a_46__boxed_4463_ = lean_unbox(v_a_4461_);
v_a_47__boxed_4464_ = lean_unbox(v_a_4462_);
v_res_4465_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_a_46__boxed_4463_, v_a_47__boxed_4464_);
v_r_4466_ = lean_box(v_res_4465_);
return v_r_4466_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object* v_upperBound_4467_, lean_object* v_identicalImports_4468_, lean_object* v_a_4469_, lean_object* v_b_4470_){
_start:
{
uint8_t v___x_4471_; 
v___x_4471_ = lean_nat_dec_lt(v_a_4469_, v_upperBound_4467_);
if (v___x_4471_ == 0)
{
lean_object* v___x_4472_; 
lean_dec(v_a_4469_);
v___x_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4472_, 0, v_b_4470_);
return v___x_4472_;
}
else
{
lean_object* v_module_4473_; lean_object* v_uri_4474_; uint8_t v_isAll_4475_; uint8_t v_isPrivate_4476_; uint8_t v_metaKind_4477_; lean_object* v___x_4478_; lean_object* v_module_4479_; lean_object* v_uri_4480_; uint8_t v_isAll_4481_; uint8_t v_isPrivate_4482_; uint8_t v_metaKind_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4503_; 
v_module_4473_ = lean_ctor_get(v_b_4470_, 0);
lean_inc(v_module_4473_);
v_uri_4474_ = lean_ctor_get(v_b_4470_, 1);
lean_inc_ref(v_uri_4474_);
v_isAll_4475_ = lean_ctor_get_uint8(v_b_4470_, sizeof(void*)*2);
v_isPrivate_4476_ = lean_ctor_get_uint8(v_b_4470_, sizeof(void*)*2 + 1);
v_metaKind_4477_ = lean_ctor_get_uint8(v_b_4470_, sizeof(void*)*2 + 2);
lean_dec_ref(v_b_4470_);
v___x_4478_ = lean_array_fget(v_identicalImports_4468_, v_a_4469_);
v_module_4479_ = lean_ctor_get(v___x_4478_, 0);
v_uri_4480_ = lean_ctor_get(v___x_4478_, 1);
v_isAll_4481_ = lean_ctor_get_uint8(v___x_4478_, sizeof(void*)*2);
v_isPrivate_4482_ = lean_ctor_get_uint8(v___x_4478_, sizeof(void*)*2 + 1);
v_metaKind_4483_ = lean_ctor_get_uint8(v___x_4478_, sizeof(void*)*2 + 2);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4485_ = v___x_4478_;
v_isShared_4486_ = v_isSharedCheck_4503_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_uri_4480_);
lean_inc(v_module_4479_);
lean_dec(v___x_4478_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4503_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
uint8_t v___y_4488_; uint8_t v___y_4489_; uint8_t v___y_4498_; uint8_t v___x_4499_; 
v___x_4499_ = lean_name_eq(v_module_4473_, v_module_4479_);
lean_dec(v_module_4479_);
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; 
lean_del_object(v___x_4485_);
lean_dec_ref(v_uri_4480_);
lean_dec_ref(v_uri_4474_);
lean_dec(v_module_4473_);
lean_dec(v_a_4469_);
v___x_4500_ = lean_box(0);
return v___x_4500_;
}
else
{
uint8_t v___x_4501_; 
v___x_4501_ = lean_string_dec_eq(v_uri_4474_, v_uri_4480_);
lean_dec_ref(v_uri_4480_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; 
lean_del_object(v___x_4485_);
lean_dec_ref(v_uri_4474_);
lean_dec(v_module_4473_);
lean_dec(v_a_4469_);
v___x_4502_ = lean_box(0);
return v___x_4502_;
}
else
{
if (v_isAll_4475_ == 0)
{
v___y_4498_ = v_isAll_4481_;
goto v___jp_4497_;
}
else
{
v___y_4498_ = v_isAll_4475_;
goto v___jp_4497_;
}
}
}
v___jp_4487_:
{
uint8_t v___x_4490_; lean_object* v___x_4492_; 
v___x_4490_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_metaKind_4477_, v_metaKind_4483_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 1, v_uri_4474_);
lean_ctor_set(v___x_4485_, 0, v_module_4473_);
v___x_4492_ = v___x_4485_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_module_4473_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v_uri_4474_);
v___x_4492_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*2, v___y_4488_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*2 + 1, v___y_4489_);
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*2 + 2, v___x_4490_);
v___x_4493_ = lean_unsigned_to_nat(1u);
v___x_4494_ = lean_nat_add(v_a_4469_, v___x_4493_);
lean_dec(v_a_4469_);
v_a_4469_ = v___x_4494_;
v_b_4470_ = v___x_4492_;
goto _start;
}
}
v___jp_4497_:
{
if (v_isPrivate_4476_ == 0)
{
v___y_4488_ = v___y_4498_;
v___y_4489_ = v_isPrivate_4476_;
goto v___jp_4487_;
}
else
{
v___y_4488_ = v___y_4498_;
v___y_4489_ = v_isPrivate_4482_;
goto v___jp_4487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_4504_, lean_object* v_identicalImports_4505_, lean_object* v_a_4506_, lean_object* v_b_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4504_, v_identicalImports_4505_, v_a_4506_, v_b_4507_);
lean_dec_ref(v_identicalImports_4505_);
lean_dec(v_upperBound_4504_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object* v_identicalImports_4509_){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4510_ = lean_unsigned_to_nat(0u);
v___x_4511_ = lean_array_get_size(v_identicalImports_4509_);
v___x_4512_ = lean_nat_dec_lt(v___x_4510_, v___x_4511_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; 
v___x_4513_ = lean_box(0);
return v___x_4513_;
}
else
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4514_ = lean_unsigned_to_nat(1u);
v___x_4515_ = lean_array_fget_borrowed(v_identicalImports_4509_, v___x_4510_);
lean_inc(v___x_4515_);
v___x_4516_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v___x_4511_, v_identicalImports_4509_, v___x_4514_, v___x_4515_);
return v___x_4516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object* v_identicalImports_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_identicalImports_4517_);
lean_dec_ref(v_identicalImports_4517_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object* v_upperBound_4519_, lean_object* v_identicalImports_4520_, lean_object* v_inst_4521_, lean_object* v_R_4522_, lean_object* v_a_4523_, lean_object* v_b_4524_, lean_object* v_c_4525_){
_start:
{
lean_object* v___x_4526_; 
v___x_4526_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4519_, v_identicalImports_4520_, v_a_4523_, v_b_4524_);
return v___x_4526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object* v_upperBound_4527_, lean_object* v_identicalImports_4528_, lean_object* v_inst_4529_, lean_object* v_R_4530_, lean_object* v_a_4531_, lean_object* v_b_4532_, lean_object* v_c_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(v_upperBound_4527_, v_identicalImports_4528_, v_inst_4529_, v_R_4530_, v_a_4531_, v_b_4532_, v_c_4533_);
lean_dec_ref(v_identicalImports_4528_);
lean_dec(v_upperBound_4527_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object* v_x_4541_){
_start:
{
lean_object* v_module_4542_; 
v_module_4542_ = lean_ctor_get(v_x_4541_, 0);
lean_inc(v_module_4542_);
return v_module_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object* v_x_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Server_DirectImports_convertImportInfos___lam__0(v_x_4543_);
lean_dec_ref(v_x_4543_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object* v_x_4545_, lean_object* v_x_4546_){
_start:
{
if (lean_obj_tag(v_x_4546_) == 0)
{
return v_x_4545_;
}
else
{
lean_object* v_key_4547_; lean_object* v_value_4548_; lean_object* v_tail_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v_key_4547_ = lean_ctor_get(v_x_4546_, 0);
v_value_4548_ = lean_ctor_get(v_x_4546_, 1);
v_tail_4549_ = lean_ctor_get(v_x_4546_, 2);
lean_inc(v_value_4548_);
lean_inc(v_key_4547_);
v___x_4550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4550_, 0, v_key_4547_);
lean_ctor_set(v___x_4550_, 1, v_value_4548_);
v___x_4551_ = lean_array_push(v_x_4545_, v___x_4550_);
v_x_4545_ = v___x_4551_;
v_x_4546_ = v_tail_4549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object* v_x_4553_, lean_object* v_x_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_x_4553_, v_x_4554_);
lean_dec(v_x_4554_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object* v_as_4556_, size_t v_i_4557_, size_t v_stop_4558_, lean_object* v_b_4559_){
_start:
{
uint8_t v___x_4560_; 
v___x_4560_ = lean_usize_dec_eq(v_i_4557_, v_stop_4558_);
if (v___x_4560_ == 0)
{
lean_object* v___x_4561_; lean_object* v___x_4562_; size_t v___x_4563_; size_t v___x_4564_; 
v___x_4561_ = lean_array_uget_borrowed(v_as_4556_, v_i_4557_);
v___x_4562_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_b_4559_, v___x_4561_);
v___x_4563_ = ((size_t)1ULL);
v___x_4564_ = lean_usize_add(v_i_4557_, v___x_4563_);
v_i_4557_ = v___x_4564_;
v_b_4559_ = v___x_4562_;
goto _start;
}
else
{
return v_b_4559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object* v_as_4566_, lean_object* v_i_4567_, lean_object* v_stop_4568_, lean_object* v_b_4569_){
_start:
{
size_t v_i_boxed_4570_; size_t v_stop_boxed_4571_; lean_object* v_res_4572_; 
v_i_boxed_4570_ = lean_unbox_usize(v_i_4567_);
lean_dec(v_i_4567_);
v_stop_boxed_4571_ = lean_unbox_usize(v_stop_4568_);
lean_dec(v_stop_4568_);
v_res_4572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_as_4566_, v_i_boxed_4570_, v_stop_boxed_4571_, v_b_4569_);
lean_dec_ref(v_as_4566_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object* v_as_4573_, size_t v_i_4574_, size_t v_stop_4575_, lean_object* v_b_4576_){
_start:
{
uint8_t v___x_4578_; 
v___x_4578_ = lean_usize_dec_eq(v_i_4574_, v_stop_4575_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; lean_object* v_module_4580_; uint8_t v_isPrivate_4581_; uint8_t v_isAll_4582_; uint8_t v_isMeta_4583_; lean_object* v_module_4584_; lean_object* v___x_4585_; 
v___x_4579_ = lean_array_uget_borrowed(v_as_4573_, v_i_4574_);
v_module_4580_ = lean_ctor_get(v___x_4579_, 0);
v_isPrivate_4581_ = lean_ctor_get_uint8(v___x_4579_, sizeof(void*)*1);
v_isAll_4582_ = lean_ctor_get_uint8(v___x_4579_, sizeof(void*)*1 + 1);
v_isMeta_4583_ = lean_ctor_get_uint8(v___x_4579_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4580_);
v_module_4584_ = l_String_toName(v_module_4580_);
lean_inc(v_module_4584_);
v___x_4585_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4584_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v_a_4586_; lean_object* v_a_4588_; 
v_a_4586_ = lean_ctor_get(v___x_4585_, 0);
lean_inc(v_a_4586_);
lean_dec_ref_known(v___x_4585_, 1);
if (lean_obj_tag(v_a_4586_) == 1)
{
lean_object* v_val_4592_; uint8_t v___y_4594_; 
v_val_4592_ = lean_ctor_get(v_a_4586_, 0);
lean_inc(v_val_4592_);
lean_dec_ref_known(v_a_4586_, 1);
if (v_isMeta_4583_ == 0)
{
uint8_t v___x_4597_; 
v___x_4597_ = 0;
v___y_4594_ = v___x_4597_;
goto v___jp_4593_;
}
else
{
uint8_t v___x_4598_; 
v___x_4598_ = 1;
v___y_4594_ = v___x_4598_;
goto v___jp_4593_;
}
v___jp_4593_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4595_, 0, v_module_4584_);
lean_ctor_set(v___x_4595_, 1, v_val_4592_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*2, v_isAll_4582_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*2 + 1, v_isPrivate_4581_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*2 + 2, v___y_4594_);
v___x_4596_ = lean_array_push(v_b_4576_, v___x_4595_);
v_a_4588_ = v___x_4596_;
goto v___jp_4587_;
}
}
else
{
lean_dec(v_a_4586_);
lean_dec(v_module_4584_);
v_a_4588_ = v_b_4576_;
goto v___jp_4587_;
}
v___jp_4587_:
{
size_t v___x_4589_; size_t v___x_4590_; 
v___x_4589_ = ((size_t)1ULL);
v___x_4590_ = lean_usize_add(v_i_4574_, v___x_4589_);
v_i_4574_ = v___x_4590_;
v_b_4576_ = v_a_4588_;
goto _start;
}
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
lean_dec(v_module_4584_);
lean_dec_ref(v_b_4576_);
v_a_4599_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4585_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4585_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4604_; 
if (v_isShared_4602_ == 0)
{
v___x_4604_ = v___x_4601_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
else
{
lean_object* v___x_4607_; 
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v_b_4576_);
return v___x_4607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object* v_as_4608_, lean_object* v_i_4609_, lean_object* v_stop_4610_, lean_object* v_b_4611_, lean_object* v___y_4612_){
_start:
{
size_t v_i_boxed_4613_; size_t v_stop_boxed_4614_; lean_object* v_res_4615_; 
v_i_boxed_4613_ = lean_unbox_usize(v_i_4609_);
lean_dec(v_i_4609_);
v_stop_boxed_4614_ = lean_unbox_usize(v_stop_4610_);
lean_dec(v_stop_4610_);
v_res_4615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4608_, v_i_boxed_4613_, v_stop_boxed_4614_, v_b_4611_);
lean_dec_ref(v_as_4608_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object* v_as_4616_, lean_object* v_start_4617_, lean_object* v_stop_4618_){
_start:
{
lean_object* v___x_4620_; uint8_t v___x_4621_; 
v___x_4620_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_4621_ = lean_nat_dec_lt(v_start_4617_, v_stop_4618_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4620_);
return v___x_4622_;
}
else
{
lean_object* v___x_4623_; uint8_t v___x_4624_; 
v___x_4623_ = lean_array_get_size(v_as_4616_);
v___x_4624_ = lean_nat_dec_le(v_stop_4618_, v___x_4623_);
if (v___x_4624_ == 0)
{
uint8_t v___x_4625_; 
v___x_4625_ = lean_nat_dec_lt(v_start_4617_, v___x_4623_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; 
v___x_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4620_);
return v___x_4626_;
}
else
{
size_t v___x_4627_; size_t v___x_4628_; lean_object* v___x_4629_; 
v___x_4627_ = lean_usize_of_nat(v_start_4617_);
v___x_4628_ = lean_usize_of_nat(v___x_4623_);
v___x_4629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4616_, v___x_4627_, v___x_4628_, v___x_4620_);
return v___x_4629_;
}
}
else
{
size_t v___x_4630_; size_t v___x_4631_; lean_object* v___x_4632_; 
v___x_4630_ = lean_usize_of_nat(v_start_4617_);
v___x_4631_ = lean_usize_of_nat(v_stop_4618_);
v___x_4632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4616_, v___x_4630_, v___x_4631_, v___x_4620_);
return v___x_4632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object* v_as_4633_, lean_object* v_start_4634_, lean_object* v_stop_4635_, lean_object* v___y_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_as_4633_, v_start_4634_, v_stop_4635_);
lean_dec(v_stop_4635_);
lean_dec(v_start_4634_);
lean_dec_ref(v_as_4633_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object* v_k_4638_, lean_object* v_v_4639_, lean_object* v_t_4640_){
_start:
{
if (lean_obj_tag(v_t_4640_) == 0)
{
lean_object* v_size_4641_; lean_object* v_k_4642_; lean_object* v_v_4643_; lean_object* v_l_4644_; lean_object* v_r_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4925_; 
v_size_4641_ = lean_ctor_get(v_t_4640_, 0);
v_k_4642_ = lean_ctor_get(v_t_4640_, 1);
v_v_4643_ = lean_ctor_get(v_t_4640_, 2);
v_l_4644_ = lean_ctor_get(v_t_4640_, 3);
v_r_4645_ = lean_ctor_get(v_t_4640_, 4);
v_isSharedCheck_4925_ = !lean_is_exclusive(v_t_4640_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4647_ = v_t_4640_;
v_isShared_4648_ = v_isSharedCheck_4925_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_r_4645_);
lean_inc(v_l_4644_);
lean_inc(v_v_4643_);
lean_inc(v_k_4642_);
lean_inc(v_size_4641_);
lean_dec(v_t_4640_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4925_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
uint8_t v___x_4649_; 
v___x_4649_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4638_, v_k_4642_);
switch(v___x_4649_)
{
case 0:
{
lean_object* v_impl_4650_; lean_object* v___x_4651_; 
lean_dec(v_size_4641_);
v_impl_4650_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4638_, v_v_4639_, v_l_4644_);
v___x_4651_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4645_) == 0)
{
lean_object* v_size_4652_; lean_object* v_size_4653_; lean_object* v_k_4654_; lean_object* v_v_4655_; lean_object* v_l_4656_; lean_object* v_r_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; uint8_t v___x_4660_; 
v_size_4652_ = lean_ctor_get(v_r_4645_, 0);
v_size_4653_ = lean_ctor_get(v_impl_4650_, 0);
lean_inc(v_size_4653_);
v_k_4654_ = lean_ctor_get(v_impl_4650_, 1);
lean_inc(v_k_4654_);
v_v_4655_ = lean_ctor_get(v_impl_4650_, 2);
lean_inc(v_v_4655_);
v_l_4656_ = lean_ctor_get(v_impl_4650_, 3);
lean_inc(v_l_4656_);
v_r_4657_ = lean_ctor_get(v_impl_4650_, 4);
lean_inc(v_r_4657_);
v___x_4658_ = lean_unsigned_to_nat(3u);
v___x_4659_ = lean_nat_mul(v___x_4658_, v_size_4652_);
v___x_4660_ = lean_nat_dec_lt(v___x_4659_, v_size_4653_);
lean_dec(v___x_4659_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4664_; 
lean_dec(v_r_4657_);
lean_dec(v_l_4656_);
lean_dec(v_v_4655_);
lean_dec(v_k_4654_);
v___x_4661_ = lean_nat_add(v___x_4651_, v_size_4653_);
lean_dec(v_size_4653_);
v___x_4662_ = lean_nat_add(v___x_4661_, v_size_4652_);
lean_dec(v___x_4661_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 3, v_impl_4650_);
lean_ctor_set(v___x_4647_, 0, v___x_4662_);
v___x_4664_ = v___x_4647_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4662_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4665_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4665_, 3, v_impl_4650_);
lean_ctor_set(v_reuseFailAlloc_4665_, 4, v_r_4645_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
else
{
lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4731_; 
v_isSharedCheck_4731_ = !lean_is_exclusive(v_impl_4650_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; lean_object* v_unused_4733_; lean_object* v_unused_4734_; lean_object* v_unused_4735_; lean_object* v_unused_4736_; 
v_unused_4732_ = lean_ctor_get(v_impl_4650_, 4);
lean_dec(v_unused_4732_);
v_unused_4733_ = lean_ctor_get(v_impl_4650_, 3);
lean_dec(v_unused_4733_);
v_unused_4734_ = lean_ctor_get(v_impl_4650_, 2);
lean_dec(v_unused_4734_);
v_unused_4735_ = lean_ctor_get(v_impl_4650_, 1);
lean_dec(v_unused_4735_);
v_unused_4736_ = lean_ctor_get(v_impl_4650_, 0);
lean_dec(v_unused_4736_);
v___x_4667_ = v_impl_4650_;
v_isShared_4668_ = v_isSharedCheck_4731_;
goto v_resetjp_4666_;
}
else
{
lean_dec(v_impl_4650_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4731_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v_size_4669_; lean_object* v_size_4670_; lean_object* v_k_4671_; lean_object* v_v_4672_; lean_object* v_l_4673_; lean_object* v_r_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; uint8_t v___x_4677_; 
v_size_4669_ = lean_ctor_get(v_l_4656_, 0);
v_size_4670_ = lean_ctor_get(v_r_4657_, 0);
v_k_4671_ = lean_ctor_get(v_r_4657_, 1);
v_v_4672_ = lean_ctor_get(v_r_4657_, 2);
v_l_4673_ = lean_ctor_get(v_r_4657_, 3);
v_r_4674_ = lean_ctor_get(v_r_4657_, 4);
v___x_4675_ = lean_unsigned_to_nat(2u);
v___x_4676_ = lean_nat_mul(v___x_4675_, v_size_4669_);
v___x_4677_ = lean_nat_dec_lt(v_size_4670_, v___x_4676_);
lean_dec(v___x_4676_);
if (v___x_4677_ == 0)
{
lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4706_; 
lean_inc(v_r_4674_);
lean_inc(v_l_4673_);
lean_inc(v_v_4672_);
lean_inc(v_k_4671_);
v_isSharedCheck_4706_ = !lean_is_exclusive(v_r_4657_);
if (v_isSharedCheck_4706_ == 0)
{
lean_object* v_unused_4707_; lean_object* v_unused_4708_; lean_object* v_unused_4709_; lean_object* v_unused_4710_; lean_object* v_unused_4711_; 
v_unused_4707_ = lean_ctor_get(v_r_4657_, 4);
lean_dec(v_unused_4707_);
v_unused_4708_ = lean_ctor_get(v_r_4657_, 3);
lean_dec(v_unused_4708_);
v_unused_4709_ = lean_ctor_get(v_r_4657_, 2);
lean_dec(v_unused_4709_);
v_unused_4710_ = lean_ctor_get(v_r_4657_, 1);
lean_dec(v_unused_4710_);
v_unused_4711_ = lean_ctor_get(v_r_4657_, 0);
lean_dec(v_unused_4711_);
v___x_4679_ = v_r_4657_;
v_isShared_4680_ = v_isSharedCheck_4706_;
goto v_resetjp_4678_;
}
else
{
lean_dec(v_r_4657_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4706_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___x_4694_; lean_object* v___y_4696_; 
v___x_4681_ = lean_nat_add(v___x_4651_, v_size_4653_);
lean_dec(v_size_4653_);
v___x_4682_ = lean_nat_add(v___x_4681_, v_size_4652_);
lean_dec(v___x_4681_);
v___x_4694_ = lean_nat_add(v___x_4651_, v_size_4669_);
if (lean_obj_tag(v_l_4673_) == 0)
{
lean_object* v_size_4704_; 
v_size_4704_ = lean_ctor_get(v_l_4673_, 0);
lean_inc(v_size_4704_);
v___y_4696_ = v_size_4704_;
goto v___jp_4695_;
}
else
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_unsigned_to_nat(0u);
v___y_4696_ = v___x_4705_;
goto v___jp_4695_;
}
v___jp_4683_:
{
lean_object* v___x_4687_; lean_object* v___x_4689_; 
v___x_4687_ = lean_nat_add(v___y_4685_, v___y_4686_);
lean_dec(v___y_4686_);
lean_dec(v___y_4685_);
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 4, v_r_4645_);
lean_ctor_set(v___x_4679_, 3, v_r_4674_);
lean_ctor_set(v___x_4679_, 2, v_v_4643_);
lean_ctor_set(v___x_4679_, 1, v_k_4642_);
lean_ctor_set(v___x_4679_, 0, v___x_4687_);
v___x_4689_ = v___x_4679_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4687_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4693_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4693_, 3, v_r_4674_);
lean_ctor_set(v_reuseFailAlloc_4693_, 4, v_r_4645_);
v___x_4689_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4691_; 
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 4, v___x_4689_);
lean_ctor_set(v___x_4667_, 3, v___y_4684_);
lean_ctor_set(v___x_4667_, 2, v_v_4672_);
lean_ctor_set(v___x_4667_, 1, v_k_4671_);
lean_ctor_set(v___x_4667_, 0, v___x_4682_);
v___x_4691_ = v___x_4667_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4682_);
lean_ctor_set(v_reuseFailAlloc_4692_, 1, v_k_4671_);
lean_ctor_set(v_reuseFailAlloc_4692_, 2, v_v_4672_);
lean_ctor_set(v_reuseFailAlloc_4692_, 3, v___y_4684_);
lean_ctor_set(v_reuseFailAlloc_4692_, 4, v___x_4689_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
v___jp_4695_:
{
lean_object* v___x_4697_; lean_object* v___x_4699_; 
v___x_4697_ = lean_nat_add(v___x_4694_, v___y_4696_);
lean_dec(v___y_4696_);
lean_dec(v___x_4694_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_l_4673_);
lean_ctor_set(v___x_4647_, 3, v_l_4656_);
lean_ctor_set(v___x_4647_, 2, v_v_4655_);
lean_ctor_set(v___x_4647_, 1, v_k_4654_);
lean_ctor_set(v___x_4647_, 0, v___x_4697_);
v___x_4699_ = v___x_4647_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_k_4654_);
lean_ctor_set(v_reuseFailAlloc_4703_, 2, v_v_4655_);
lean_ctor_set(v_reuseFailAlloc_4703_, 3, v_l_4656_);
lean_ctor_set(v_reuseFailAlloc_4703_, 4, v_l_4673_);
v___x_4699_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4700_; 
v___x_4700_ = lean_nat_add(v___x_4651_, v_size_4652_);
if (lean_obj_tag(v_r_4674_) == 0)
{
lean_object* v_size_4701_; 
v_size_4701_ = lean_ctor_get(v_r_4674_, 0);
lean_inc(v_size_4701_);
v___y_4684_ = v___x_4699_;
v___y_4685_ = v___x_4700_;
v___y_4686_ = v_size_4701_;
goto v___jp_4683_;
}
else
{
lean_object* v___x_4702_; 
v___x_4702_ = lean_unsigned_to_nat(0u);
v___y_4684_ = v___x_4699_;
v___y_4685_ = v___x_4700_;
v___y_4686_ = v___x_4702_;
goto v___jp_4683_;
}
}
}
}
}
else
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
lean_del_object(v___x_4647_);
v___x_4712_ = lean_nat_add(v___x_4651_, v_size_4653_);
lean_dec(v_size_4653_);
v___x_4713_ = lean_nat_add(v___x_4712_, v_size_4652_);
lean_dec(v___x_4712_);
v___x_4714_ = lean_nat_add(v___x_4651_, v_size_4652_);
v___x_4715_ = lean_nat_add(v___x_4714_, v_size_4670_);
lean_dec(v___x_4714_);
lean_inc_ref(v_r_4645_);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 4, v_r_4645_);
lean_ctor_set(v___x_4667_, 3, v_r_4657_);
lean_ctor_set(v___x_4667_, 2, v_v_4643_);
lean_ctor_set(v___x_4667_, 1, v_k_4642_);
lean_ctor_set(v___x_4667_, 0, v___x_4715_);
v___x_4717_ = v___x_4667_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4715_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_r_4657_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_r_4645_);
v___x_4717_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
v_isSharedCheck_4724_ = !lean_is_exclusive(v_r_4645_);
if (v_isSharedCheck_4724_ == 0)
{
lean_object* v_unused_4725_; lean_object* v_unused_4726_; lean_object* v_unused_4727_; lean_object* v_unused_4728_; lean_object* v_unused_4729_; 
v_unused_4725_ = lean_ctor_get(v_r_4645_, 4);
lean_dec(v_unused_4725_);
v_unused_4726_ = lean_ctor_get(v_r_4645_, 3);
lean_dec(v_unused_4726_);
v_unused_4727_ = lean_ctor_get(v_r_4645_, 2);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_r_4645_, 1);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_r_4645_, 0);
lean_dec(v_unused_4729_);
v___x_4719_ = v_r_4645_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_dec(v_r_4645_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 4, v___x_4717_);
lean_ctor_set(v___x_4719_, 3, v_l_4656_);
lean_ctor_set(v___x_4719_, 2, v_v_4655_);
lean_ctor_set(v___x_4719_, 1, v_k_4654_);
lean_ctor_set(v___x_4719_, 0, v___x_4713_);
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v_k_4654_);
lean_ctor_set(v_reuseFailAlloc_4723_, 2, v_v_4655_);
lean_ctor_set(v_reuseFailAlloc_4723_, 3, v_l_4656_);
lean_ctor_set(v_reuseFailAlloc_4723_, 4, v___x_4717_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4737_; 
v_l_4737_ = lean_ctor_get(v_impl_4650_, 3);
lean_inc(v_l_4737_);
if (lean_obj_tag(v_l_4737_) == 0)
{
lean_object* v_r_4738_; lean_object* v_k_4739_; lean_object* v_v_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4751_; 
v_r_4738_ = lean_ctor_get(v_impl_4650_, 4);
v_k_4739_ = lean_ctor_get(v_impl_4650_, 1);
v_v_4740_ = lean_ctor_get(v_impl_4650_, 2);
v_isSharedCheck_4751_ = !lean_is_exclusive(v_impl_4650_);
if (v_isSharedCheck_4751_ == 0)
{
lean_object* v_unused_4752_; lean_object* v_unused_4753_; 
v_unused_4752_ = lean_ctor_get(v_impl_4650_, 3);
lean_dec(v_unused_4752_);
v_unused_4753_ = lean_ctor_get(v_impl_4650_, 0);
lean_dec(v_unused_4753_);
v___x_4742_ = v_impl_4650_;
v_isShared_4743_ = v_isSharedCheck_4751_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_r_4738_);
lean_inc(v_v_4740_);
lean_inc(v_k_4739_);
lean_dec(v_impl_4650_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4751_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4744_; lean_object* v___x_4746_; 
v___x_4744_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4738_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 3, v_r_4738_);
lean_ctor_set(v___x_4742_, 2, v_v_4643_);
lean_ctor_set(v___x_4742_, 1, v_k_4642_);
lean_ctor_set(v___x_4742_, 0, v___x_4651_);
v___x_4746_ = v___x_4742_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4750_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4750_, 3, v_r_4738_);
lean_ctor_set(v_reuseFailAlloc_4750_, 4, v_r_4738_);
v___x_4746_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
lean_object* v___x_4748_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v___x_4746_);
lean_ctor_set(v___x_4647_, 3, v_l_4737_);
lean_ctor_set(v___x_4647_, 2, v_v_4740_);
lean_ctor_set(v___x_4647_, 1, v_k_4739_);
lean_ctor_set(v___x_4647_, 0, v___x_4744_);
v___x_4748_ = v___x_4647_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4749_, 1, v_k_4739_);
lean_ctor_set(v_reuseFailAlloc_4749_, 2, v_v_4740_);
lean_ctor_set(v_reuseFailAlloc_4749_, 3, v_l_4737_);
lean_ctor_set(v_reuseFailAlloc_4749_, 4, v___x_4746_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
else
{
lean_object* v_r_4754_; 
v_r_4754_ = lean_ctor_get(v_impl_4650_, 4);
lean_inc(v_r_4754_);
if (lean_obj_tag(v_r_4754_) == 0)
{
lean_object* v_k_4755_; lean_object* v_v_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4779_; 
v_k_4755_ = lean_ctor_get(v_impl_4650_, 1);
v_v_4756_ = lean_ctor_get(v_impl_4650_, 2);
v_isSharedCheck_4779_ = !lean_is_exclusive(v_impl_4650_);
if (v_isSharedCheck_4779_ == 0)
{
lean_object* v_unused_4780_; lean_object* v_unused_4781_; lean_object* v_unused_4782_; 
v_unused_4780_ = lean_ctor_get(v_impl_4650_, 4);
lean_dec(v_unused_4780_);
v_unused_4781_ = lean_ctor_get(v_impl_4650_, 3);
lean_dec(v_unused_4781_);
v_unused_4782_ = lean_ctor_get(v_impl_4650_, 0);
lean_dec(v_unused_4782_);
v___x_4758_ = v_impl_4650_;
v_isShared_4759_ = v_isSharedCheck_4779_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_v_4756_);
lean_inc(v_k_4755_);
lean_dec(v_impl_4650_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4779_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v_k_4760_; lean_object* v_v_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4775_; 
v_k_4760_ = lean_ctor_get(v_r_4754_, 1);
v_v_4761_ = lean_ctor_get(v_r_4754_, 2);
v_isSharedCheck_4775_ = !lean_is_exclusive(v_r_4754_);
if (v_isSharedCheck_4775_ == 0)
{
lean_object* v_unused_4776_; lean_object* v_unused_4777_; lean_object* v_unused_4778_; 
v_unused_4776_ = lean_ctor_get(v_r_4754_, 4);
lean_dec(v_unused_4776_);
v_unused_4777_ = lean_ctor_get(v_r_4754_, 3);
lean_dec(v_unused_4777_);
v_unused_4778_ = lean_ctor_get(v_r_4754_, 0);
lean_dec(v_unused_4778_);
v___x_4763_ = v_r_4754_;
v_isShared_4764_ = v_isSharedCheck_4775_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_v_4761_);
lean_inc(v_k_4760_);
lean_dec(v_r_4754_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4775_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4765_; lean_object* v___x_4767_; 
v___x_4765_ = lean_unsigned_to_nat(3u);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 4, v_l_4737_);
lean_ctor_set(v___x_4763_, 3, v_l_4737_);
lean_ctor_set(v___x_4763_, 2, v_v_4756_);
lean_ctor_set(v___x_4763_, 1, v_k_4755_);
lean_ctor_set(v___x_4763_, 0, v___x_4651_);
v___x_4767_ = v___x_4763_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v_k_4755_);
lean_ctor_set(v_reuseFailAlloc_4774_, 2, v_v_4756_);
lean_ctor_set(v_reuseFailAlloc_4774_, 3, v_l_4737_);
lean_ctor_set(v_reuseFailAlloc_4774_, 4, v_l_4737_);
v___x_4767_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
lean_object* v___x_4769_; 
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 4, v_l_4737_);
lean_ctor_set(v___x_4758_, 2, v_v_4643_);
lean_ctor_set(v___x_4758_, 1, v_k_4642_);
lean_ctor_set(v___x_4758_, 0, v___x_4651_);
v___x_4769_ = v___x_4758_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4773_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4773_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4773_, 3, v_l_4737_);
lean_ctor_set(v_reuseFailAlloc_4773_, 4, v_l_4737_);
v___x_4769_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
lean_object* v___x_4771_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v___x_4769_);
lean_ctor_set(v___x_4647_, 3, v___x_4767_);
lean_ctor_set(v___x_4647_, 2, v_v_4761_);
lean_ctor_set(v___x_4647_, 1, v_k_4760_);
lean_ctor_set(v___x_4647_, 0, v___x_4765_);
v___x_4771_ = v___x_4647_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4765_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v_k_4760_);
lean_ctor_set(v_reuseFailAlloc_4772_, 2, v_v_4761_);
lean_ctor_set(v_reuseFailAlloc_4772_, 3, v___x_4767_);
lean_ctor_set(v_reuseFailAlloc_4772_, 4, v___x_4769_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
}
}
else
{
lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4783_ = lean_unsigned_to_nat(2u);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_r_4754_);
lean_ctor_set(v___x_4647_, 3, v_impl_4650_);
lean_ctor_set(v___x_4647_, 0, v___x_4783_);
v___x_4785_ = v___x_4647_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4786_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4786_, 3, v_impl_4650_);
lean_ctor_set(v_reuseFailAlloc_4786_, 4, v_r_4754_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4788_; 
lean_dec(v_v_4643_);
lean_dec(v_k_4642_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 2, v_v_4639_);
lean_ctor_set(v___x_4647_, 1, v_k_4638_);
v___x_4788_ = v___x_4647_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_size_4641_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_k_4638_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_v_4639_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v_l_4644_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v_r_4645_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
default: 
{
lean_object* v_impl_4790_; lean_object* v___x_4791_; 
lean_dec(v_size_4641_);
v_impl_4790_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4638_, v_v_4639_, v_r_4645_);
v___x_4791_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4644_) == 0)
{
lean_object* v_size_4792_; lean_object* v_size_4793_; lean_object* v_k_4794_; lean_object* v_v_4795_; lean_object* v_l_4796_; lean_object* v_r_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; uint8_t v___x_4800_; 
v_size_4792_ = lean_ctor_get(v_l_4644_, 0);
v_size_4793_ = lean_ctor_get(v_impl_4790_, 0);
lean_inc(v_size_4793_);
v_k_4794_ = lean_ctor_get(v_impl_4790_, 1);
lean_inc(v_k_4794_);
v_v_4795_ = lean_ctor_get(v_impl_4790_, 2);
lean_inc(v_v_4795_);
v_l_4796_ = lean_ctor_get(v_impl_4790_, 3);
lean_inc(v_l_4796_);
v_r_4797_ = lean_ctor_get(v_impl_4790_, 4);
lean_inc(v_r_4797_);
v___x_4798_ = lean_unsigned_to_nat(3u);
v___x_4799_ = lean_nat_mul(v___x_4798_, v_size_4792_);
v___x_4800_ = lean_nat_dec_lt(v___x_4799_, v_size_4793_);
lean_dec(v___x_4799_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4804_; 
lean_dec(v_r_4797_);
lean_dec(v_l_4796_);
lean_dec(v_v_4795_);
lean_dec(v_k_4794_);
v___x_4801_ = lean_nat_add(v___x_4791_, v_size_4792_);
v___x_4802_ = lean_nat_add(v___x_4801_, v_size_4793_);
lean_dec(v_size_4793_);
lean_dec(v___x_4801_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_impl_4790_);
lean_ctor_set(v___x_4647_, 0, v___x_4802_);
v___x_4804_ = v___x_4647_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4805_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4805_, 3, v_l_4644_);
lean_ctor_set(v_reuseFailAlloc_4805_, 4, v_impl_4790_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
else
{
lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4869_; 
v_isSharedCheck_4869_ = !lean_is_exclusive(v_impl_4790_);
if (v_isSharedCheck_4869_ == 0)
{
lean_object* v_unused_4870_; lean_object* v_unused_4871_; lean_object* v_unused_4872_; lean_object* v_unused_4873_; lean_object* v_unused_4874_; 
v_unused_4870_ = lean_ctor_get(v_impl_4790_, 4);
lean_dec(v_unused_4870_);
v_unused_4871_ = lean_ctor_get(v_impl_4790_, 3);
lean_dec(v_unused_4871_);
v_unused_4872_ = lean_ctor_get(v_impl_4790_, 2);
lean_dec(v_unused_4872_);
v_unused_4873_ = lean_ctor_get(v_impl_4790_, 1);
lean_dec(v_unused_4873_);
v_unused_4874_ = lean_ctor_get(v_impl_4790_, 0);
lean_dec(v_unused_4874_);
v___x_4807_ = v_impl_4790_;
v_isShared_4808_ = v_isSharedCheck_4869_;
goto v_resetjp_4806_;
}
else
{
lean_dec(v_impl_4790_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4869_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v_size_4809_; lean_object* v_k_4810_; lean_object* v_v_4811_; lean_object* v_l_4812_; lean_object* v_r_4813_; lean_object* v_size_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v_size_4809_ = lean_ctor_get(v_l_4796_, 0);
v_k_4810_ = lean_ctor_get(v_l_4796_, 1);
v_v_4811_ = lean_ctor_get(v_l_4796_, 2);
v_l_4812_ = lean_ctor_get(v_l_4796_, 3);
v_r_4813_ = lean_ctor_get(v_l_4796_, 4);
v_size_4814_ = lean_ctor_get(v_r_4797_, 0);
v___x_4815_ = lean_unsigned_to_nat(2u);
v___x_4816_ = lean_nat_mul(v___x_4815_, v_size_4814_);
v___x_4817_ = lean_nat_dec_lt(v_size_4809_, v___x_4816_);
lean_dec(v___x_4816_);
if (v___x_4817_ == 0)
{
lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4845_; 
lean_inc(v_r_4813_);
lean_inc(v_l_4812_);
lean_inc(v_v_4811_);
lean_inc(v_k_4810_);
v_isSharedCheck_4845_ = !lean_is_exclusive(v_l_4796_);
if (v_isSharedCheck_4845_ == 0)
{
lean_object* v_unused_4846_; lean_object* v_unused_4847_; lean_object* v_unused_4848_; lean_object* v_unused_4849_; lean_object* v_unused_4850_; 
v_unused_4846_ = lean_ctor_get(v_l_4796_, 4);
lean_dec(v_unused_4846_);
v_unused_4847_ = lean_ctor_get(v_l_4796_, 3);
lean_dec(v_unused_4847_);
v_unused_4848_ = lean_ctor_get(v_l_4796_, 2);
lean_dec(v_unused_4848_);
v_unused_4849_ = lean_ctor_get(v_l_4796_, 1);
lean_dec(v_unused_4849_);
v_unused_4850_ = lean_ctor_get(v_l_4796_, 0);
lean_dec(v_unused_4850_);
v___x_4819_ = v_l_4796_;
v_isShared_4820_ = v_isSharedCheck_4845_;
goto v_resetjp_4818_;
}
else
{
lean_dec(v_l_4796_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4845_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___y_4824_; lean_object* v___y_4825_; lean_object* v___y_4826_; lean_object* v___y_4835_; 
v___x_4821_ = lean_nat_add(v___x_4791_, v_size_4792_);
v___x_4822_ = lean_nat_add(v___x_4821_, v_size_4793_);
lean_dec(v_size_4793_);
if (lean_obj_tag(v_l_4812_) == 0)
{
lean_object* v_size_4843_; 
v_size_4843_ = lean_ctor_get(v_l_4812_, 0);
lean_inc(v_size_4843_);
v___y_4835_ = v_size_4843_;
goto v___jp_4834_;
}
else
{
lean_object* v___x_4844_; 
v___x_4844_ = lean_unsigned_to_nat(0u);
v___y_4835_ = v___x_4844_;
goto v___jp_4834_;
}
v___jp_4823_:
{
lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4827_ = lean_nat_add(v___y_4825_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec(v___y_4825_);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 4, v_r_4797_);
lean_ctor_set(v___x_4819_, 3, v_r_4813_);
lean_ctor_set(v___x_4819_, 2, v_v_4795_);
lean_ctor_set(v___x_4819_, 1, v_k_4794_);
lean_ctor_set(v___x_4819_, 0, v___x_4827_);
v___x_4829_ = v___x_4819_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_4833_, 1, v_k_4794_);
lean_ctor_set(v_reuseFailAlloc_4833_, 2, v_v_4795_);
lean_ctor_set(v_reuseFailAlloc_4833_, 3, v_r_4813_);
lean_ctor_set(v_reuseFailAlloc_4833_, 4, v_r_4797_);
v___x_4829_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4831_; 
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 4, v___x_4829_);
lean_ctor_set(v___x_4807_, 3, v___y_4824_);
lean_ctor_set(v___x_4807_, 2, v_v_4811_);
lean_ctor_set(v___x_4807_, 1, v_k_4810_);
lean_ctor_set(v___x_4807_, 0, v___x_4822_);
v___x_4831_ = v___x_4807_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4822_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v_k_4810_);
lean_ctor_set(v_reuseFailAlloc_4832_, 2, v_v_4811_);
lean_ctor_set(v_reuseFailAlloc_4832_, 3, v___y_4824_);
lean_ctor_set(v_reuseFailAlloc_4832_, 4, v___x_4829_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
v___jp_4834_:
{
lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4836_ = lean_nat_add(v___x_4821_, v___y_4835_);
lean_dec(v___y_4835_);
lean_dec(v___x_4821_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_l_4812_);
lean_ctor_set(v___x_4647_, 0, v___x_4836_);
v___x_4838_ = v___x_4647_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4842_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4842_, 3, v_l_4644_);
lean_ctor_set(v_reuseFailAlloc_4842_, 4, v_l_4812_);
v___x_4838_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
lean_object* v___x_4839_; 
v___x_4839_ = lean_nat_add(v___x_4791_, v_size_4814_);
if (lean_obj_tag(v_r_4813_) == 0)
{
lean_object* v_size_4840_; 
v_size_4840_ = lean_ctor_get(v_r_4813_, 0);
lean_inc(v_size_4840_);
v___y_4824_ = v___x_4838_;
v___y_4825_ = v___x_4839_;
v___y_4826_ = v_size_4840_;
goto v___jp_4823_;
}
else
{
lean_object* v___x_4841_; 
v___x_4841_ = lean_unsigned_to_nat(0u);
v___y_4824_ = v___x_4838_;
v___y_4825_ = v___x_4839_;
v___y_4826_ = v___x_4841_;
goto v___jp_4823_;
}
}
}
}
}
else
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4855_; 
lean_del_object(v___x_4647_);
v___x_4851_ = lean_nat_add(v___x_4791_, v_size_4792_);
v___x_4852_ = lean_nat_add(v___x_4851_, v_size_4793_);
lean_dec(v_size_4793_);
v___x_4853_ = lean_nat_add(v___x_4851_, v_size_4809_);
lean_dec(v___x_4851_);
lean_inc_ref(v_l_4644_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 4, v_l_4796_);
lean_ctor_set(v___x_4807_, 3, v_l_4644_);
lean_ctor_set(v___x_4807_, 2, v_v_4643_);
lean_ctor_set(v___x_4807_, 1, v_k_4642_);
lean_ctor_set(v___x_4807_, 0, v___x_4853_);
v___x_4855_ = v___x_4807_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4853_);
lean_ctor_set(v_reuseFailAlloc_4868_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4868_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4868_, 3, v_l_4644_);
lean_ctor_set(v_reuseFailAlloc_4868_, 4, v_l_4796_);
v___x_4855_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4862_; 
v_isSharedCheck_4862_ = !lean_is_exclusive(v_l_4644_);
if (v_isSharedCheck_4862_ == 0)
{
lean_object* v_unused_4863_; lean_object* v_unused_4864_; lean_object* v_unused_4865_; lean_object* v_unused_4866_; lean_object* v_unused_4867_; 
v_unused_4863_ = lean_ctor_get(v_l_4644_, 4);
lean_dec(v_unused_4863_);
v_unused_4864_ = lean_ctor_get(v_l_4644_, 3);
lean_dec(v_unused_4864_);
v_unused_4865_ = lean_ctor_get(v_l_4644_, 2);
lean_dec(v_unused_4865_);
v_unused_4866_ = lean_ctor_get(v_l_4644_, 1);
lean_dec(v_unused_4866_);
v_unused_4867_ = lean_ctor_get(v_l_4644_, 0);
lean_dec(v_unused_4867_);
v___x_4857_ = v_l_4644_;
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
else
{
lean_dec(v_l_4644_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4860_; 
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 4, v_r_4797_);
lean_ctor_set(v___x_4857_, 3, v___x_4855_);
lean_ctor_set(v___x_4857_, 2, v_v_4795_);
lean_ctor_set(v___x_4857_, 1, v_k_4794_);
lean_ctor_set(v___x_4857_, 0, v___x_4852_);
v___x_4860_ = v___x_4857_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4852_);
lean_ctor_set(v_reuseFailAlloc_4861_, 1, v_k_4794_);
lean_ctor_set(v_reuseFailAlloc_4861_, 2, v_v_4795_);
lean_ctor_set(v_reuseFailAlloc_4861_, 3, v___x_4855_);
lean_ctor_set(v_reuseFailAlloc_4861_, 4, v_r_4797_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4875_; 
v_l_4875_ = lean_ctor_get(v_impl_4790_, 3);
lean_inc(v_l_4875_);
if (lean_obj_tag(v_l_4875_) == 0)
{
lean_object* v_r_4876_; lean_object* v_k_4877_; lean_object* v_v_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4901_; 
v_r_4876_ = lean_ctor_get(v_impl_4790_, 4);
v_k_4877_ = lean_ctor_get(v_impl_4790_, 1);
v_v_4878_ = lean_ctor_get(v_impl_4790_, 2);
v_isSharedCheck_4901_ = !lean_is_exclusive(v_impl_4790_);
if (v_isSharedCheck_4901_ == 0)
{
lean_object* v_unused_4902_; lean_object* v_unused_4903_; 
v_unused_4902_ = lean_ctor_get(v_impl_4790_, 3);
lean_dec(v_unused_4902_);
v_unused_4903_ = lean_ctor_get(v_impl_4790_, 0);
lean_dec(v_unused_4903_);
v___x_4880_ = v_impl_4790_;
v_isShared_4881_ = v_isSharedCheck_4901_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_r_4876_);
lean_inc(v_v_4878_);
lean_inc(v_k_4877_);
lean_dec(v_impl_4790_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4901_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v_k_4882_; lean_object* v_v_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4897_; 
v_k_4882_ = lean_ctor_get(v_l_4875_, 1);
v_v_4883_ = lean_ctor_get(v_l_4875_, 2);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_l_4875_);
if (v_isSharedCheck_4897_ == 0)
{
lean_object* v_unused_4898_; lean_object* v_unused_4899_; lean_object* v_unused_4900_; 
v_unused_4898_ = lean_ctor_get(v_l_4875_, 4);
lean_dec(v_unused_4898_);
v_unused_4899_ = lean_ctor_get(v_l_4875_, 3);
lean_dec(v_unused_4899_);
v_unused_4900_ = lean_ctor_get(v_l_4875_, 0);
lean_dec(v_unused_4900_);
v___x_4885_ = v_l_4875_;
v_isShared_4886_ = v_isSharedCheck_4897_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_v_4883_);
lean_inc(v_k_4882_);
lean_dec(v_l_4875_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4897_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4887_; lean_object* v___x_4889_; 
v___x_4887_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4876_, 2);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 4, v_r_4876_);
lean_ctor_set(v___x_4885_, 3, v_r_4876_);
lean_ctor_set(v___x_4885_, 2, v_v_4643_);
lean_ctor_set(v___x_4885_, 1, v_k_4642_);
lean_ctor_set(v___x_4885_, 0, v___x_4791_);
v___x_4889_ = v___x_4885_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4791_);
lean_ctor_set(v_reuseFailAlloc_4896_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4896_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4896_, 3, v_r_4876_);
lean_ctor_set(v_reuseFailAlloc_4896_, 4, v_r_4876_);
v___x_4889_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
lean_object* v___x_4891_; 
lean_inc(v_r_4876_);
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 3, v_r_4876_);
lean_ctor_set(v___x_4880_, 0, v___x_4791_);
v___x_4891_ = v___x_4880_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4791_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v_k_4877_);
lean_ctor_set(v_reuseFailAlloc_4895_, 2, v_v_4878_);
lean_ctor_set(v_reuseFailAlloc_4895_, 3, v_r_4876_);
lean_ctor_set(v_reuseFailAlloc_4895_, 4, v_r_4876_);
v___x_4891_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
lean_object* v___x_4893_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v___x_4891_);
lean_ctor_set(v___x_4647_, 3, v___x_4889_);
lean_ctor_set(v___x_4647_, 2, v_v_4883_);
lean_ctor_set(v___x_4647_, 1, v_k_4882_);
lean_ctor_set(v___x_4647_, 0, v___x_4887_);
v___x_4893_ = v___x_4647_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4887_);
lean_ctor_set(v_reuseFailAlloc_4894_, 1, v_k_4882_);
lean_ctor_set(v_reuseFailAlloc_4894_, 2, v_v_4883_);
lean_ctor_set(v_reuseFailAlloc_4894_, 3, v___x_4889_);
lean_ctor_set(v_reuseFailAlloc_4894_, 4, v___x_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
}
else
{
lean_object* v_r_4904_; 
v_r_4904_ = lean_ctor_get(v_impl_4790_, 4);
lean_inc(v_r_4904_);
if (lean_obj_tag(v_r_4904_) == 0)
{
lean_object* v_k_4905_; lean_object* v_v_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4917_; 
v_k_4905_ = lean_ctor_get(v_impl_4790_, 1);
v_v_4906_ = lean_ctor_get(v_impl_4790_, 2);
v_isSharedCheck_4917_ = !lean_is_exclusive(v_impl_4790_);
if (v_isSharedCheck_4917_ == 0)
{
lean_object* v_unused_4918_; lean_object* v_unused_4919_; lean_object* v_unused_4920_; 
v_unused_4918_ = lean_ctor_get(v_impl_4790_, 4);
lean_dec(v_unused_4918_);
v_unused_4919_ = lean_ctor_get(v_impl_4790_, 3);
lean_dec(v_unused_4919_);
v_unused_4920_ = lean_ctor_get(v_impl_4790_, 0);
lean_dec(v_unused_4920_);
v___x_4908_ = v_impl_4790_;
v_isShared_4909_ = v_isSharedCheck_4917_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_v_4906_);
lean_inc(v_k_4905_);
lean_dec(v_impl_4790_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4917_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4910_; lean_object* v___x_4912_; 
v___x_4910_ = lean_unsigned_to_nat(3u);
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 4, v_l_4875_);
lean_ctor_set(v___x_4908_, 2, v_v_4643_);
lean_ctor_set(v___x_4908_, 1, v_k_4642_);
lean_ctor_set(v___x_4908_, 0, v___x_4791_);
v___x_4912_ = v___x_4908_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4791_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4916_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4916_, 3, v_l_4875_);
lean_ctor_set(v_reuseFailAlloc_4916_, 4, v_l_4875_);
v___x_4912_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
lean_object* v___x_4914_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_r_4904_);
lean_ctor_set(v___x_4647_, 3, v___x_4912_);
lean_ctor_set(v___x_4647_, 2, v_v_4906_);
lean_ctor_set(v___x_4647_, 1, v_k_4905_);
lean_ctor_set(v___x_4647_, 0, v___x_4910_);
v___x_4914_ = v___x_4647_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4915_, 1, v_k_4905_);
lean_ctor_set(v_reuseFailAlloc_4915_, 2, v_v_4906_);
lean_ctor_set(v_reuseFailAlloc_4915_, 3, v___x_4912_);
lean_ctor_set(v_reuseFailAlloc_4915_, 4, v_r_4904_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
}
}
else
{
lean_object* v___x_4921_; lean_object* v___x_4923_; 
v___x_4921_ = lean_unsigned_to_nat(2u);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 4, v_impl_4790_);
lean_ctor_set(v___x_4647_, 3, v_r_4904_);
lean_ctor_set(v___x_4647_, 0, v___x_4921_);
v___x_4923_ = v___x_4647_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4921_);
lean_ctor_set(v_reuseFailAlloc_4924_, 1, v_k_4642_);
lean_ctor_set(v_reuseFailAlloc_4924_, 2, v_v_4643_);
lean_ctor_set(v_reuseFailAlloc_4924_, 3, v_r_4904_);
lean_ctor_set(v_reuseFailAlloc_4924_, 4, v_impl_4790_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
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
lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4926_ = lean_unsigned_to_nat(1u);
v___x_4927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
lean_ctor_set(v___x_4927_, 1, v_k_4638_);
lean_ctor_set(v___x_4927_, 2, v_v_4639_);
lean_ctor_set(v___x_4927_, 3, v_t_4640_);
lean_ctor_set(v___x_4927_, 4, v_t_4640_);
return v___x_4927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object* v_as_4928_, size_t v_sz_4929_, size_t v_i_4930_, lean_object* v_b_4931_){
_start:
{
uint8_t v___x_4932_; 
v___x_4932_ = lean_usize_dec_lt(v_i_4930_, v_sz_4929_);
if (v___x_4932_ == 0)
{
return v_b_4931_;
}
else
{
lean_object* v_a_4933_; lean_object* v_fst_4934_; lean_object* v_snd_4935_; lean_object* v_r_4936_; size_t v___x_4937_; size_t v___x_4938_; 
v_a_4933_ = lean_array_uget_borrowed(v_as_4928_, v_i_4930_);
v_fst_4934_ = lean_ctor_get(v_a_4933_, 0);
v_snd_4935_ = lean_ctor_get(v_a_4933_, 1);
lean_inc(v_snd_4935_);
lean_inc(v_fst_4934_);
v_r_4936_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_fst_4934_, v_snd_4935_, v_b_4931_);
v___x_4937_ = ((size_t)1ULL);
v___x_4938_ = lean_usize_add(v_i_4930_, v___x_4937_);
v_i_4930_ = v___x_4938_;
v_b_4931_ = v_r_4936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object* v_as_4940_, lean_object* v_sz_4941_, lean_object* v_i_4942_, lean_object* v_b_4943_){
_start:
{
size_t v_sz_boxed_4944_; size_t v_i_boxed_4945_; lean_object* v_res_4946_; 
v_sz_boxed_4944_ = lean_unbox_usize(v_sz_4941_);
lean_dec(v_sz_4941_);
v_i_boxed_4945_ = lean_unbox_usize(v_i_4942_);
lean_dec(v_i_4942_);
v_res_4946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v_as_4940_, v_sz_boxed_4944_, v_i_boxed_4945_, v_b_4943_);
lean_dec_ref(v_as_4940_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object* v_a_4949_, lean_object* v_x_4950_){
_start:
{
lean_object* v___y_4952_; 
if (lean_obj_tag(v_x_4950_) == 0)
{
lean_object* v___x_4955_; 
v___x_4955_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___y_4952_ = v___x_4955_;
goto v___jp_4951_;
}
else
{
lean_object* v_val_4956_; 
v_val_4956_ = lean_ctor_get(v_x_4950_, 0);
lean_inc(v_val_4956_);
lean_dec_ref_known(v_x_4950_, 1);
v___y_4952_ = v_val_4956_;
goto v___jp_4951_;
}
v___jp_4951_:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = lean_array_push(v___y_4952_, v_a_4949_);
v___x_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4953_);
return v___x_4954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_x_4959_){
_start:
{
if (lean_obj_tag(v_x_4959_) == 0)
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v_val_4962_; lean_object* v___x_4963_; 
v___x_4960_ = lean_box(0);
v___x_4961_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4957_, v___x_4960_);
v_val_4962_ = lean_ctor_get(v___x_4961_, 0);
lean_inc(v_val_4962_);
lean_dec(v___x_4961_);
v___x_4963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4963_, 0, v_a_4958_);
lean_ctor_set(v___x_4963_, 1, v_val_4962_);
lean_ctor_set(v___x_4963_, 2, v_x_4959_);
return v___x_4963_;
}
else
{
lean_object* v_key_4964_; lean_object* v_value_4965_; lean_object* v_tail_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4981_; 
v_key_4964_ = lean_ctor_get(v_x_4959_, 0);
v_value_4965_ = lean_ctor_get(v_x_4959_, 1);
v_tail_4966_ = lean_ctor_get(v_x_4959_, 2);
v_isSharedCheck_4981_ = !lean_is_exclusive(v_x_4959_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4968_ = v_x_4959_;
v_isShared_4969_ = v_isSharedCheck_4981_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_tail_4966_);
lean_inc(v_value_4965_);
lean_inc(v_key_4964_);
lean_dec(v_x_4959_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4981_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
uint8_t v___x_4970_; 
v___x_4970_ = lean_name_eq(v_key_4964_, v_a_4958_);
if (v___x_4970_ == 0)
{
lean_object* v_tail_4971_; lean_object* v___x_4973_; 
v_tail_4971_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4957_, v_a_4958_, v_tail_4966_);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 2, v_tail_4971_);
v___x_4973_ = v___x_4968_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_key_4964_);
lean_ctor_set(v_reuseFailAlloc_4974_, 1, v_value_4965_);
lean_ctor_set(v_reuseFailAlloc_4974_, 2, v_tail_4971_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
else
{
lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v_val_4977_; lean_object* v___x_4979_; 
lean_dec(v_key_4964_);
v___x_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4975_, 0, v_value_4965_);
v___x_4976_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4957_, v___x_4975_);
v_val_4977_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_val_4977_);
lean_dec(v___x_4976_);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 1, v_val_4977_);
lean_ctor_set(v___x_4968_, 0, v_a_4958_);
v___x_4979_ = v___x_4968_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_a_4958_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v_val_4977_);
lean_ctor_set(v_reuseFailAlloc_4980_, 2, v_tail_4966_);
v___x_4979_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
return v___x_4979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_4982_, lean_object* v_x_4983_){
_start:
{
if (lean_obj_tag(v_x_4983_) == 0)
{
return v_x_4982_;
}
else
{
lean_object* v_key_4984_; lean_object* v_value_4985_; lean_object* v_tail_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_5012_; 
v_key_4984_ = lean_ctor_get(v_x_4983_, 0);
v_value_4985_ = lean_ctor_get(v_x_4983_, 1);
v_tail_4986_ = lean_ctor_get(v_x_4983_, 2);
v_isSharedCheck_5012_ = !lean_is_exclusive(v_x_4983_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_4988_ = v_x_4983_;
v_isShared_4989_ = v_isSharedCheck_5012_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_tail_4986_);
lean_inc(v_value_4985_);
lean_inc(v_key_4984_);
lean_dec(v_x_4983_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_5012_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4990_; uint64_t v___y_4992_; 
v___x_4990_ = lean_array_get_size(v_x_4982_);
if (lean_obj_tag(v_key_4984_) == 0)
{
uint64_t v___x_5010_; 
v___x_5010_ = 1723ULL;
v___y_4992_ = v___x_5010_;
goto v___jp_4991_;
}
else
{
uint64_t v_hash_5011_; 
v_hash_5011_ = lean_ctor_get_uint64(v_key_4984_, sizeof(void*)*2);
v___y_4992_ = v_hash_5011_;
goto v___jp_4991_;
}
v___jp_4991_:
{
uint64_t v___x_4993_; uint64_t v___x_4994_; uint64_t v_fold_4995_; uint64_t v___x_4996_; uint64_t v___x_4997_; uint64_t v___x_4998_; size_t v___x_4999_; size_t v___x_5000_; size_t v___x_5001_; size_t v___x_5002_; size_t v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5006_; 
v___x_4993_ = 32ULL;
v___x_4994_ = lean_uint64_shift_right(v___y_4992_, v___x_4993_);
v_fold_4995_ = lean_uint64_xor(v___y_4992_, v___x_4994_);
v___x_4996_ = 16ULL;
v___x_4997_ = lean_uint64_shift_right(v_fold_4995_, v___x_4996_);
v___x_4998_ = lean_uint64_xor(v_fold_4995_, v___x_4997_);
v___x_4999_ = lean_uint64_to_usize(v___x_4998_);
v___x_5000_ = lean_usize_of_nat(v___x_4990_);
v___x_5001_ = ((size_t)1ULL);
v___x_5002_ = lean_usize_sub(v___x_5000_, v___x_5001_);
v___x_5003_ = lean_usize_land(v___x_4999_, v___x_5002_);
v___x_5004_ = lean_array_uget_borrowed(v_x_4982_, v___x_5003_);
lean_inc(v___x_5004_);
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 2, v___x_5004_);
v___x_5006_ = v___x_4988_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_key_4984_);
lean_ctor_set(v_reuseFailAlloc_5009_, 1, v_value_4985_);
lean_ctor_set(v_reuseFailAlloc_5009_, 2, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
lean_object* v___x_5007_; 
v___x_5007_ = lean_array_uset(v_x_4982_, v___x_5003_, v___x_5006_);
v_x_4982_ = v___x_5007_;
v_x_4983_ = v_tail_4986_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object* v_i_5013_, lean_object* v_source_5014_, lean_object* v_target_5015_){
_start:
{
lean_object* v___x_5016_; uint8_t v___x_5017_; 
v___x_5016_ = lean_array_get_size(v_source_5014_);
v___x_5017_ = lean_nat_dec_lt(v_i_5013_, v___x_5016_);
if (v___x_5017_ == 0)
{
lean_dec_ref(v_source_5014_);
lean_dec(v_i_5013_);
return v_target_5015_;
}
else
{
lean_object* v_es_5018_; lean_object* v___x_5019_; lean_object* v_source_5020_; lean_object* v_target_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; 
v_es_5018_ = lean_array_fget(v_source_5014_, v_i_5013_);
v___x_5019_ = lean_box(0);
v_source_5020_ = lean_array_fset(v_source_5014_, v_i_5013_, v___x_5019_);
v_target_5021_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_target_5015_, v_es_5018_);
v___x_5022_ = lean_unsigned_to_nat(1u);
v___x_5023_ = lean_nat_add(v_i_5013_, v___x_5022_);
lean_dec(v_i_5013_);
v_i_5013_ = v___x_5023_;
v_source_5014_ = v_source_5020_;
v_target_5015_ = v_target_5021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object* v_data_5025_){
_start:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v_nbuckets_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5026_ = lean_array_get_size(v_data_5025_);
v___x_5027_ = lean_unsigned_to_nat(2u);
v_nbuckets_5028_ = lean_nat_mul(v___x_5026_, v___x_5027_);
v___x_5029_ = lean_unsigned_to_nat(0u);
v___x_5030_ = lean_box(0);
v___x_5031_ = lean_mk_array(v_nbuckets_5028_, v___x_5030_);
v___x_5032_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_5029_, v_data_5025_, v___x_5031_);
return v___x_5032_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_5033_, lean_object* v_x_5034_){
_start:
{
if (lean_obj_tag(v_x_5034_) == 0)
{
uint8_t v___x_5035_; 
v___x_5035_ = 0;
return v___x_5035_;
}
else
{
lean_object* v_key_5036_; lean_object* v_tail_5037_; uint8_t v___x_5038_; 
v_key_5036_ = lean_ctor_get(v_x_5034_, 0);
v_tail_5037_ = lean_ctor_get(v_x_5034_, 2);
v___x_5038_ = lean_name_eq(v_key_5036_, v_a_5033_);
if (v___x_5038_ == 0)
{
v_x_5034_ = v_tail_5037_;
goto _start;
}
else
{
return v___x_5038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_5040_, lean_object* v_x_5041_){
_start:
{
uint8_t v_res_5042_; lean_object* v_r_5043_; 
v_res_5042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5040_, v_x_5041_);
lean_dec(v_x_5041_);
lean_dec(v_a_5040_);
v_r_5043_ = lean_box(v_res_5042_);
return v_r_5043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_5044_, lean_object* v_m_5045_, lean_object* v_a_5046_){
_start:
{
lean_object* v___y_5048_; size_t v___y_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v_size_5054_; lean_object* v_buckets_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5102_; 
v_size_5054_ = lean_ctor_get(v_m_5045_, 0);
v_buckets_5055_ = lean_ctor_get(v_m_5045_, 1);
v_isSharedCheck_5102_ = !lean_is_exclusive(v_m_5045_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5057_ = v_m_5045_;
v_isShared_5058_ = v_isSharedCheck_5102_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_buckets_5055_);
lean_inc(v_size_5054_);
lean_dec(v_m_5045_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5102_;
goto v_resetjp_5056_;
}
v___jp_5047_:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5052_ = lean_array_uset(v___y_5050_, v___y_5049_, v___y_5048_);
v___x_5053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5053_, 0, v___y_5051_);
lean_ctor_set(v___x_5053_, 1, v___x_5052_);
return v___x_5053_;
}
v_resetjp_5056_:
{
lean_object* v___x_5059_; uint64_t v___y_5061_; 
v___x_5059_ = lean_array_get_size(v_buckets_5055_);
if (lean_obj_tag(v_a_5046_) == 0)
{
uint64_t v___x_5100_; 
v___x_5100_ = 1723ULL;
v___y_5061_ = v___x_5100_;
goto v___jp_5060_;
}
else
{
uint64_t v_hash_5101_; 
v_hash_5101_ = lean_ctor_get_uint64(v_a_5046_, sizeof(void*)*2);
v___y_5061_ = v_hash_5101_;
goto v___jp_5060_;
}
v___jp_5060_:
{
uint64_t v___x_5062_; uint64_t v___x_5063_; uint64_t v_fold_5064_; uint64_t v___x_5065_; uint64_t v___x_5066_; uint64_t v___x_5067_; size_t v___x_5068_; size_t v___x_5069_; size_t v___x_5070_; size_t v___x_5071_; size_t v___x_5072_; lean_object* v_bkt_5073_; uint8_t v___x_5074_; 
v___x_5062_ = 32ULL;
v___x_5063_ = lean_uint64_shift_right(v___y_5061_, v___x_5062_);
v_fold_5064_ = lean_uint64_xor(v___y_5061_, v___x_5063_);
v___x_5065_ = 16ULL;
v___x_5066_ = lean_uint64_shift_right(v_fold_5064_, v___x_5065_);
v___x_5067_ = lean_uint64_xor(v_fold_5064_, v___x_5066_);
v___x_5068_ = lean_uint64_to_usize(v___x_5067_);
v___x_5069_ = lean_usize_of_nat(v___x_5059_);
v___x_5070_ = ((size_t)1ULL);
v___x_5071_ = lean_usize_sub(v___x_5069_, v___x_5070_);
v___x_5072_ = lean_usize_land(v___x_5068_, v___x_5071_);
v_bkt_5073_ = lean_array_uget_borrowed(v_buckets_5055_, v___x_5072_);
v___x_5074_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5046_, v_bkt_5073_);
if (v___x_5074_ == 0)
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v_size_x27_5078_; lean_object* v___x_5079_; lean_object* v_buckets_x27_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; uint8_t v___x_5086_; 
v___x_5075_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_5076_ = lean_array_push(v___x_5075_, v_a_5044_);
v___x_5077_ = lean_unsigned_to_nat(1u);
v_size_x27_5078_ = lean_nat_add(v_size_5054_, v___x_5077_);
lean_dec(v_size_5054_);
lean_inc(v_bkt_5073_);
v___x_5079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5079_, 0, v_a_5046_);
lean_ctor_set(v___x_5079_, 1, v___x_5076_);
lean_ctor_set(v___x_5079_, 2, v_bkt_5073_);
v_buckets_x27_5080_ = lean_array_uset(v_buckets_5055_, v___x_5072_, v___x_5079_);
v___x_5081_ = lean_unsigned_to_nat(4u);
v___x_5082_ = lean_nat_mul(v_size_x27_5078_, v___x_5081_);
v___x_5083_ = lean_unsigned_to_nat(3u);
v___x_5084_ = lean_nat_div(v___x_5082_, v___x_5083_);
lean_dec(v___x_5082_);
v___x_5085_ = lean_array_get_size(v_buckets_x27_5080_);
v___x_5086_ = lean_nat_dec_le(v___x_5084_, v___x_5085_);
lean_dec(v___x_5084_);
if (v___x_5086_ == 0)
{
lean_object* v_val_5087_; lean_object* v___x_5089_; 
v_val_5087_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5080_);
if (v_isShared_5058_ == 0)
{
lean_ctor_set(v___x_5057_, 1, v_val_5087_);
lean_ctor_set(v___x_5057_, 0, v_size_x27_5078_);
v___x_5089_ = v___x_5057_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_size_x27_5078_);
lean_ctor_set(v_reuseFailAlloc_5090_, 1, v_val_5087_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
return v___x_5089_;
}
}
else
{
lean_object* v___x_5092_; 
if (v_isShared_5058_ == 0)
{
lean_ctor_set(v___x_5057_, 1, v_buckets_x27_5080_);
lean_ctor_set(v___x_5057_, 0, v_size_x27_5078_);
v___x_5092_ = v___x_5057_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_size_x27_5078_);
lean_ctor_set(v_reuseFailAlloc_5093_, 1, v_buckets_x27_5080_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
else
{
lean_object* v___x_5094_; lean_object* v_buckets_x27_5095_; lean_object* v_bkt_x27_5096_; uint8_t v___x_5097_; 
lean_inc(v_bkt_5073_);
lean_del_object(v___x_5057_);
v___x_5094_ = lean_box(0);
v_buckets_x27_5095_ = lean_array_uset(v_buckets_5055_, v___x_5072_, v___x_5094_);
lean_inc(v_a_5046_);
v_bkt_x27_5096_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5044_, v_a_5046_, v_bkt_5073_);
v___x_5097_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5046_, v_bkt_x27_5096_);
lean_dec(v_a_5046_);
if (v___x_5097_ == 0)
{
lean_object* v___x_5098_; lean_object* v___x_5099_; 
v___x_5098_ = lean_unsigned_to_nat(1u);
v___x_5099_ = lean_nat_sub(v_size_5054_, v___x_5098_);
lean_dec(v_size_5054_);
v___y_5048_ = v_bkt_x27_5096_;
v___y_5049_ = v___x_5072_;
v___y_5050_ = v_buckets_x27_5095_;
v___y_5051_ = v___x_5099_;
goto v___jp_5047_;
}
else
{
v___y_5048_ = v_bkt_x27_5096_;
v___y_5049_ = v___x_5072_;
v___y_5050_ = v_buckets_x27_5095_;
v___y_5051_ = v_size_5054_;
goto v___jp_5047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5103_, lean_object* v_as_5104_, size_t v_sz_5105_, size_t v_i_5106_, lean_object* v_b_5107_){
_start:
{
uint8_t v___x_5108_; 
v___x_5108_ = lean_usize_dec_lt(v_i_5106_, v_sz_5105_);
if (v___x_5108_ == 0)
{
lean_dec_ref(v_key_5103_);
return v_b_5107_;
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; size_t v___x_5112_; size_t v___x_5113_; 
v_a_5109_ = lean_array_uget_borrowed(v_as_5104_, v_i_5106_);
lean_inc_ref(v_key_5103_);
lean_inc_n(v_a_5109_, 2);
v___x_5110_ = lean_apply_1(v_key_5103_, v_a_5109_);
v___x_5111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5109_, v_b_5107_, v___x_5110_);
v___x_5112_ = ((size_t)1ULL);
v___x_5113_ = lean_usize_add(v_i_5106_, v___x_5112_);
v_i_5106_ = v___x_5113_;
v_b_5107_ = v___x_5111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5115_, lean_object* v_as_5116_, lean_object* v_sz_5117_, lean_object* v_i_5118_, lean_object* v_b_5119_){
_start:
{
size_t v_sz_boxed_5120_; size_t v_i_boxed_5121_; lean_object* v_res_5122_; 
v_sz_boxed_5120_ = lean_unbox_usize(v_sz_5117_);
lean_dec(v_sz_5117_);
v_i_boxed_5121_ = lean_unbox_usize(v_i_5118_);
lean_dec(v_i_5118_);
v_res_5122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5115_, v_as_5116_, v_sz_boxed_5120_, v_i_boxed_5121_, v_b_5119_);
lean_dec_ref(v_as_5116_);
return v_res_5122_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v___x_5123_ = lean_box(0);
v___x_5124_ = lean_unsigned_to_nat(16u);
v___x_5125_ = lean_mk_array(v___x_5124_, v___x_5123_);
return v___x_5125_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v_groups_5128_; 
v___x_5126_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5127_ = lean_unsigned_to_nat(0u);
v_groups_5128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5128_, 0, v___x_5127_);
lean_ctor_set(v_groups_5128_, 1, v___x_5126_);
return v_groups_5128_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5129_, lean_object* v_xs_5130_){
_start:
{
lean_object* v_groups_5131_; size_t v_sz_5132_; size_t v___x_5133_; lean_object* v___x_5134_; 
v_groups_5131_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5132_ = lean_array_size(v_xs_5130_);
v___x_5133_ = ((size_t)0ULL);
v___x_5134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5129_, v_xs_5130_, v_sz_5132_, v___x_5133_, v_groups_5131_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5135_, lean_object* v_xs_5136_){
_start:
{
lean_object* v_res_5137_; 
v_res_5137_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5135_, v_xs_5136_);
lean_dec_ref(v_xs_5136_);
return v_res_5137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5139_){
_start:
{
lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5141_ = lean_unsigned_to_nat(0u);
v___x_5142_ = lean_array_get_size(v_infos_5139_);
v___x_5143_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5139_, v___x_5141_, v___x_5142_);
if (lean_obj_tag(v___x_5143_) == 0)
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5172_; 
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5146_ = v___x_5143_;
v_isShared_5147_ = v_isSharedCheck_5172_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___x_5143_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5172_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___y_5149_; lean_object* v___f_5158_; lean_object* v___x_5159_; lean_object* v_size_5160_; lean_object* v_buckets_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; 
v___f_5158_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5159_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5158_, v_a_5144_);
v_size_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_size_5160_);
v_buckets_5161_ = lean_ctor_get(v___x_5159_, 1);
lean_inc_ref(v_buckets_5161_);
lean_dec_ref(v___x_5159_);
v___x_5162_ = lean_mk_empty_array_with_capacity(v_size_5160_);
lean_dec(v_size_5160_);
v___x_5163_ = lean_array_get_size(v_buckets_5161_);
v___x_5164_ = lean_nat_dec_lt(v___x_5141_, v___x_5163_);
if (v___x_5164_ == 0)
{
lean_dec_ref(v_buckets_5161_);
v___y_5149_ = v___x_5162_;
goto v___jp_5148_;
}
else
{
uint8_t v___x_5165_; 
v___x_5165_ = lean_nat_dec_le(v___x_5163_, v___x_5163_);
if (v___x_5165_ == 0)
{
if (v___x_5164_ == 0)
{
lean_dec_ref(v_buckets_5161_);
v___y_5149_ = v___x_5162_;
goto v___jp_5148_;
}
else
{
size_t v___x_5166_; size_t v___x_5167_; lean_object* v___x_5168_; 
v___x_5166_ = ((size_t)0ULL);
v___x_5167_ = lean_usize_of_nat(v___x_5163_);
v___x_5168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5161_, v___x_5166_, v___x_5167_, v___x_5162_);
lean_dec_ref(v_buckets_5161_);
v___y_5149_ = v___x_5168_;
goto v___jp_5148_;
}
}
else
{
size_t v___x_5169_; size_t v___x_5170_; lean_object* v___x_5171_; 
v___x_5169_ = ((size_t)0ULL);
v___x_5170_ = lean_usize_of_nat(v___x_5163_);
v___x_5171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5161_, v___x_5169_, v___x_5170_, v___x_5162_);
lean_dec_ref(v_buckets_5161_);
v___y_5149_ = v___x_5171_;
goto v___jp_5148_;
}
}
v___jp_5148_:
{
lean_object* v_r_5150_; size_t v_sz_5151_; size_t v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5156_; 
v_r_5150_ = lean_box(1);
v_sz_5151_ = lean_array_size(v___y_5149_);
v___x_5152_ = ((size_t)0ULL);
v___x_5153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5149_, v_sz_5151_, v___x_5152_, v_r_5150_);
lean_dec_ref(v___y_5149_);
v___x_5154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5154_, 0, v_a_5144_);
lean_ctor_set(v___x_5154_, 1, v___x_5153_);
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 0, v___x_5154_);
v___x_5156_ = v___x_5146_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5154_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
v_a_5173_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5143_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5143_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5181_, lean_object* v_a_5182_){
_start:
{
lean_object* v_res_5183_; 
v_res_5183_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5181_);
lean_dec_ref(v_infos_5181_);
return v_res_5183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5184_, lean_object* v_k_5185_, lean_object* v_v_5186_, lean_object* v_t_5187_, lean_object* v_hl_5188_){
_start:
{
lean_object* v___x_5189_; 
v___x_5189_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5185_, v_v_5186_, v_t_5187_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5190_, lean_object* v_key_5191_, lean_object* v_xs_5192_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5191_, v_xs_5192_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5194_, lean_object* v_key_5195_, lean_object* v_xs_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5194_, v_key_5195_, v_xs_5196_);
lean_dec_ref(v_xs_5196_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5198_, lean_object* v_a_5199_, lean_object* v_m_5200_, lean_object* v_a_5201_){
_start:
{
lean_object* v___x_5202_; 
v___x_5202_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5199_, v_m_5200_, v_a_5201_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5203_, lean_object* v_key_5204_, lean_object* v_as_5205_, size_t v_sz_5206_, size_t v_i_5207_, lean_object* v_b_5208_){
_start:
{
lean_object* v___x_5209_; 
v___x_5209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5204_, v_as_5205_, v_sz_5206_, v_i_5207_, v_b_5208_);
return v___x_5209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5210_, lean_object* v_key_5211_, lean_object* v_as_5212_, lean_object* v_sz_5213_, lean_object* v_i_5214_, lean_object* v_b_5215_){
_start:
{
size_t v_sz_boxed_5216_; size_t v_i_boxed_5217_; lean_object* v_res_5218_; 
v_sz_boxed_5216_ = lean_unbox_usize(v_sz_5213_);
lean_dec(v_sz_5213_);
v_i_boxed_5217_ = lean_unbox_usize(v_i_5214_);
lean_dec(v_i_5214_);
v_res_5218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5210_, v_key_5211_, v_as_5212_, v_sz_boxed_5216_, v_i_boxed_5217_, v_b_5215_);
lean_dec_ref(v_as_5212_);
return v_res_5218_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5219_, lean_object* v_a_5220_, lean_object* v_x_5221_){
_start:
{
uint8_t v___x_5222_; 
v___x_5222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5220_, v_x_5221_);
return v___x_5222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5223_, lean_object* v_a_5224_, lean_object* v_x_5225_){
_start:
{
uint8_t v_res_5226_; lean_object* v_r_5227_; 
v_res_5226_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5223_, v_a_5224_, v_x_5225_);
lean_dec(v_x_5225_);
lean_dec(v_a_5224_);
v_r_5227_ = lean_box(v_res_5226_);
return v_r_5227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5228_, lean_object* v_data_5229_){
_start:
{
lean_object* v___x_5230_; 
v___x_5230_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5229_);
return v___x_5230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_x_5234_){
_start:
{
lean_object* v___x_5235_; 
v___x_5235_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5232_, v_a_5233_, v_x_5234_);
return v___x_5235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5236_, lean_object* v_i_5237_, lean_object* v_source_5238_, lean_object* v_target_5239_){
_start:
{
lean_object* v___x_5240_; 
v___x_5240_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5237_, v_source_5238_, v_target_5239_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5241_, lean_object* v_x_5242_, lean_object* v_x_5243_){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5242_, v_x_5243_);
return v___x_5244_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5245_){
_start:
{
lean_object* v_isSetupFailure_x3f_5246_; 
v_isSetupFailure_x3f_5246_ = lean_ctor_get(v_i_5245_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5246_) == 0)
{
uint8_t v___x_5247_; 
v___x_5247_ = 0;
return v___x_5247_;
}
else
{
lean_object* v_val_5248_; uint8_t v___x_5249_; 
v_val_5248_ = lean_ctor_get(v_isSetupFailure_x3f_5246_, 0);
v___x_5249_ = lean_unbox(v_val_5248_);
if (v___x_5249_ == 0)
{
uint8_t v___x_5250_; 
v___x_5250_ = 1;
return v___x_5250_;
}
else
{
uint8_t v___x_5251_; 
v___x_5251_ = 0;
return v___x_5251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5252_){
_start:
{
uint8_t v_res_5253_; lean_object* v_r_5254_; 
v_res_5253_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5252_);
lean_dec_ref(v_i_5252_);
v_r_5254_ = lean_box(v_res_5253_);
return v_r_5254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5260_, lean_object* v_path_5261_, lean_object* v_ilean_5262_){
_start:
{
lean_object* v_module_5264_; lean_object* v_directImports_5265_; lean_object* v_references_5266_; lean_object* v_decls_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5319_; 
v_module_5264_ = lean_ctor_get(v_ilean_5262_, 1);
v_directImports_5265_ = lean_ctor_get(v_ilean_5262_, 2);
v_references_5266_ = lean_ctor_get(v_ilean_5262_, 3);
v_decls_5267_ = lean_ctor_get(v_ilean_5262_, 4);
v_isSharedCheck_5319_ = !lean_is_exclusive(v_ilean_5262_);
if (v_isSharedCheck_5319_ == 0)
{
lean_object* v_unused_5320_; 
v_unused_5320_ = lean_ctor_get(v_ilean_5262_, 0);
lean_dec(v_unused_5320_);
v___x_5269_ = v_ilean_5262_;
v_isShared_5270_ = v_isSharedCheck_5319_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_decls_5267_);
lean_inc(v_references_5266_);
lean_inc(v_directImports_5265_);
lean_inc(v_module_5264_);
lean_dec(v_ilean_5262_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5319_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5271_; 
lean_inc(v_module_5264_);
v___x_5271_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5264_);
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5310_; 
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5274_ = v___x_5271_;
v_isShared_5275_ = v_isSharedCheck_5310_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5271_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5310_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
if (lean_obj_tag(v_a_5272_) == 1)
{
lean_object* v_val_5276_; lean_object* v___x_5277_; 
lean_del_object(v___x_5274_);
v_val_5276_ = lean_ctor_get(v_a_5272_, 0);
lean_inc(v_val_5276_);
lean_dec_ref_known(v_a_5272_, 1);
v___x_5277_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5265_);
lean_dec_ref(v_directImports_5265_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_object* v_a_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5298_; 
v_a_5278_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5280_ = v___x_5277_;
v_isShared_5281_ = v_isSharedCheck_5298_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_a_5278_);
lean_dec(v___x_5277_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5298_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v_ileans_5282_; lean_object* v_workers_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5297_; 
v_ileans_5282_ = lean_ctor_get(v_self_5260_, 0);
v_workers_5283_ = lean_ctor_get(v_self_5260_, 1);
v_isSharedCheck_5297_ = !lean_is_exclusive(v_self_5260_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5285_ = v_self_5260_;
v_isShared_5286_ = v_isSharedCheck_5297_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_workers_5283_);
lean_inc(v_ileans_5282_);
lean_dec(v_self_5260_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5297_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v___x_5288_; 
if (v_isShared_5270_ == 0)
{
lean_ctor_set(v___x_5269_, 2, v_a_5278_);
lean_ctor_set(v___x_5269_, 1, v_path_5261_);
lean_ctor_set(v___x_5269_, 0, v_val_5276_);
v___x_5288_ = v___x_5269_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_val_5276_);
lean_ctor_set(v_reuseFailAlloc_5296_, 1, v_path_5261_);
lean_ctor_set(v_reuseFailAlloc_5296_, 2, v_a_5278_);
lean_ctor_set(v_reuseFailAlloc_5296_, 3, v_references_5266_);
lean_ctor_set(v_reuseFailAlloc_5296_, 4, v_decls_5267_);
v___x_5288_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
lean_object* v___x_5289_; lean_object* v___x_5291_; 
v___x_5289_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5264_, v___x_5288_, v_ileans_5282_);
if (v_isShared_5286_ == 0)
{
lean_ctor_set(v___x_5285_, 0, v___x_5289_);
v___x_5291_ = v___x_5285_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v___x_5289_);
lean_ctor_set(v_reuseFailAlloc_5295_, 1, v_workers_5283_);
v___x_5291_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
lean_object* v___x_5293_; 
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 0, v___x_5291_);
v___x_5293_ = v___x_5280_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v___x_5291_);
v___x_5293_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
return v___x_5293_;
}
}
}
}
}
}
else
{
lean_object* v_a_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5306_; 
lean_dec(v_val_5276_);
lean_del_object(v___x_5269_);
lean_dec(v_decls_5267_);
lean_dec(v_references_5266_);
lean_dec(v_module_5264_);
lean_dec_ref(v_path_5261_);
lean_dec_ref(v_self_5260_);
v_a_5299_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5306_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5306_ == 0)
{
v___x_5301_ = v___x_5277_;
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_a_5299_);
lean_dec(v___x_5277_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5304_; 
if (v_isShared_5302_ == 0)
{
v___x_5304_ = v___x_5301_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_a_5299_);
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
else
{
lean_object* v___x_5308_; 
lean_dec(v_a_5272_);
lean_del_object(v___x_5269_);
lean_dec(v_decls_5267_);
lean_dec(v_references_5266_);
lean_dec_ref(v_directImports_5265_);
lean_dec(v_module_5264_);
lean_dec_ref(v_path_5261_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 0, v_self_5260_);
v___x_5308_ = v___x_5274_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_self_5260_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
}
}
else
{
lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5318_; 
lean_del_object(v___x_5269_);
lean_dec(v_decls_5267_);
lean_dec(v_references_5266_);
lean_dec_ref(v_directImports_5265_);
lean_dec(v_module_5264_);
lean_dec_ref(v_path_5261_);
lean_dec_ref(v_self_5260_);
v_a_5311_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5318_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5318_ == 0)
{
v___x_5313_ = v___x_5271_;
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_dec(v___x_5271_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5316_; 
if (v_isShared_5314_ == 0)
{
v___x_5316_ = v___x_5313_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5311_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5321_, lean_object* v_path_5322_, lean_object* v_ilean_5323_, lean_object* v_a_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l_Lean_Server_References_addIlean(v_self_5321_, v_path_5322_, v_ilean_5323_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5326_, lean_object* v_t_5327_){
_start:
{
if (lean_obj_tag(v_t_5327_) == 0)
{
lean_object* v_v_5328_; lean_object* v_k_5329_; lean_object* v_l_5330_; lean_object* v_r_5331_; lean_object* v_ileanPath_5332_; uint8_t v___x_5333_; 
v_v_5328_ = lean_ctor_get(v_t_5327_, 2);
lean_inc(v_v_5328_);
v_k_5329_ = lean_ctor_get(v_t_5327_, 1);
lean_inc(v_k_5329_);
v_l_5330_ = lean_ctor_get(v_t_5327_, 3);
lean_inc(v_l_5330_);
v_r_5331_ = lean_ctor_get(v_t_5327_, 4);
lean_inc(v_r_5331_);
lean_dec_ref_known(v_t_5327_, 5);
v_ileanPath_5332_ = lean_ctor_get(v_v_5328_, 1);
v___x_5333_ = lean_string_dec_eq(v_ileanPath_5332_, v_path_5326_);
if (v___x_5333_ == 0)
{
lean_object* v_impl_5334_; lean_object* v_impl_5335_; lean_object* v___x_5336_; 
lean_dec(v_k_5329_);
lean_dec(v_v_5328_);
v_impl_5334_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5326_, v_l_5330_);
v_impl_5335_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5326_, v_r_5331_);
v___x_5336_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5334_, v_impl_5335_);
return v___x_5336_;
}
else
{
lean_object* v_impl_5337_; lean_object* v_impl_5338_; lean_object* v___x_5339_; 
v_impl_5337_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5326_, v_l_5330_);
v_impl_5338_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5326_, v_r_5331_);
v___x_5339_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5329_, v_v_5328_, v_impl_5337_, v_impl_5338_);
return v___x_5339_;
}
}
else
{
return v_t_5327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5340_, lean_object* v_t_5341_){
_start:
{
lean_object* v_res_5342_; 
v_res_5342_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5340_, v_t_5341_);
lean_dec_ref(v_path_5340_);
return v_res_5342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5343_, lean_object* v_t_5344_){
_start:
{
if (lean_obj_tag(v_t_5344_) == 0)
{
lean_object* v_k_5345_; lean_object* v_v_5346_; lean_object* v_l_5347_; lean_object* v_r_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_6002_; 
v_k_5345_ = lean_ctor_get(v_t_5344_, 1);
v_v_5346_ = lean_ctor_get(v_t_5344_, 2);
v_l_5347_ = lean_ctor_get(v_t_5344_, 3);
v_r_5348_ = lean_ctor_get(v_t_5344_, 4);
v_isSharedCheck_6002_ = !lean_is_exclusive(v_t_5344_);
if (v_isSharedCheck_6002_ == 0)
{
lean_object* v_unused_6003_; 
v_unused_6003_ = lean_ctor_get(v_t_5344_, 0);
lean_dec(v_unused_6003_);
v___x_5350_ = v_t_5344_;
v_isShared_5351_ = v_isSharedCheck_6002_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_r_5348_);
lean_inc(v_l_5347_);
lean_inc(v_v_5346_);
lean_inc(v_k_5345_);
lean_dec(v_t_5344_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_6002_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
uint8_t v___x_5352_; 
v___x_5352_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5343_, v_k_5345_);
switch(v___x_5352_)
{
case 0:
{
lean_object* v_impl_5353_; lean_object* v___x_5354_; 
v_impl_5353_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5343_, v_l_5347_);
v___x_5354_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5353_) == 0)
{
if (lean_obj_tag(v_r_5348_) == 0)
{
lean_object* v_size_5355_; lean_object* v_size_5356_; lean_object* v_k_5357_; lean_object* v_v_5358_; lean_object* v_l_5359_; lean_object* v_r_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; uint8_t v___x_5363_; 
v_size_5355_ = lean_ctor_get(v_impl_5353_, 0);
lean_inc(v_size_5355_);
v_size_5356_ = lean_ctor_get(v_r_5348_, 0);
v_k_5357_ = lean_ctor_get(v_r_5348_, 1);
v_v_5358_ = lean_ctor_get(v_r_5348_, 2);
v_l_5359_ = lean_ctor_get(v_r_5348_, 3);
lean_inc(v_l_5359_);
v_r_5360_ = lean_ctor_get(v_r_5348_, 4);
v___x_5361_ = lean_unsigned_to_nat(3u);
v___x_5362_ = lean_nat_mul(v___x_5361_, v_size_5355_);
v___x_5363_ = lean_nat_dec_lt(v___x_5362_, v_size_5356_);
lean_dec(v___x_5362_);
if (v___x_5363_ == 0)
{
lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5367_; 
lean_dec(v_l_5359_);
v___x_5364_ = lean_nat_add(v___x_5354_, v_size_5355_);
lean_dec(v_size_5355_);
v___x_5365_ = lean_nat_add(v___x_5364_, v_size_5356_);
lean_dec(v___x_5364_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 3, v_impl_5353_);
lean_ctor_set(v___x_5350_, 0, v___x_5365_);
v___x_5367_ = v___x_5350_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v___x_5365_);
lean_ctor_set(v_reuseFailAlloc_5368_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5368_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5368_, 3, v_impl_5353_);
lean_ctor_set(v_reuseFailAlloc_5368_, 4, v_r_5348_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
else
{
lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5432_; 
lean_inc(v_r_5360_);
lean_inc(v_v_5358_);
lean_inc(v_k_5357_);
lean_inc(v_size_5356_);
v_isSharedCheck_5432_ = !lean_is_exclusive(v_r_5348_);
if (v_isSharedCheck_5432_ == 0)
{
lean_object* v_unused_5433_; lean_object* v_unused_5434_; lean_object* v_unused_5435_; lean_object* v_unused_5436_; lean_object* v_unused_5437_; 
v_unused_5433_ = lean_ctor_get(v_r_5348_, 4);
lean_dec(v_unused_5433_);
v_unused_5434_ = lean_ctor_get(v_r_5348_, 3);
lean_dec(v_unused_5434_);
v_unused_5435_ = lean_ctor_get(v_r_5348_, 2);
lean_dec(v_unused_5435_);
v_unused_5436_ = lean_ctor_get(v_r_5348_, 1);
lean_dec(v_unused_5436_);
v_unused_5437_ = lean_ctor_get(v_r_5348_, 0);
lean_dec(v_unused_5437_);
v___x_5370_ = v_r_5348_;
v_isShared_5371_ = v_isSharedCheck_5432_;
goto v_resetjp_5369_;
}
else
{
lean_dec(v_r_5348_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5432_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v_size_5372_; lean_object* v_k_5373_; lean_object* v_v_5374_; lean_object* v_l_5375_; lean_object* v_r_5376_; lean_object* v_size_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; uint8_t v___x_5380_; 
v_size_5372_ = lean_ctor_get(v_l_5359_, 0);
v_k_5373_ = lean_ctor_get(v_l_5359_, 1);
v_v_5374_ = lean_ctor_get(v_l_5359_, 2);
v_l_5375_ = lean_ctor_get(v_l_5359_, 3);
v_r_5376_ = lean_ctor_get(v_l_5359_, 4);
v_size_5377_ = lean_ctor_get(v_r_5360_, 0);
v___x_5378_ = lean_unsigned_to_nat(2u);
v___x_5379_ = lean_nat_mul(v___x_5378_, v_size_5377_);
v___x_5380_ = lean_nat_dec_lt(v_size_5372_, v___x_5379_);
lean_dec(v___x_5379_);
if (v___x_5380_ == 0)
{
lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5408_; 
lean_inc(v_r_5376_);
lean_inc(v_l_5375_);
lean_inc(v_v_5374_);
lean_inc(v_k_5373_);
v_isSharedCheck_5408_ = !lean_is_exclusive(v_l_5359_);
if (v_isSharedCheck_5408_ == 0)
{
lean_object* v_unused_5409_; lean_object* v_unused_5410_; lean_object* v_unused_5411_; lean_object* v_unused_5412_; lean_object* v_unused_5413_; 
v_unused_5409_ = lean_ctor_get(v_l_5359_, 4);
lean_dec(v_unused_5409_);
v_unused_5410_ = lean_ctor_get(v_l_5359_, 3);
lean_dec(v_unused_5410_);
v_unused_5411_ = lean_ctor_get(v_l_5359_, 2);
lean_dec(v_unused_5411_);
v_unused_5412_ = lean_ctor_get(v_l_5359_, 1);
lean_dec(v_unused_5412_);
v_unused_5413_ = lean_ctor_get(v_l_5359_, 0);
lean_dec(v_unused_5413_);
v___x_5382_ = v_l_5359_;
v_isShared_5383_ = v_isSharedCheck_5408_;
goto v_resetjp_5381_;
}
else
{
lean_dec(v_l_5359_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5408_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___y_5387_; lean_object* v___y_5388_; lean_object* v___y_5389_; lean_object* v___y_5398_; 
v___x_5384_ = lean_nat_add(v___x_5354_, v_size_5355_);
lean_dec(v_size_5355_);
v___x_5385_ = lean_nat_add(v___x_5384_, v_size_5356_);
lean_dec(v_size_5356_);
if (lean_obj_tag(v_l_5375_) == 0)
{
lean_object* v_size_5406_; 
v_size_5406_ = lean_ctor_get(v_l_5375_, 0);
lean_inc(v_size_5406_);
v___y_5398_ = v_size_5406_;
goto v___jp_5397_;
}
else
{
lean_object* v___x_5407_; 
v___x_5407_ = lean_unsigned_to_nat(0u);
v___y_5398_ = v___x_5407_;
goto v___jp_5397_;
}
v___jp_5386_:
{
lean_object* v___x_5390_; lean_object* v___x_5392_; 
v___x_5390_ = lean_nat_add(v___y_5387_, v___y_5389_);
lean_dec(v___y_5389_);
lean_dec(v___y_5387_);
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 4, v_r_5360_);
lean_ctor_set(v___x_5382_, 3, v_r_5376_);
lean_ctor_set(v___x_5382_, 2, v_v_5358_);
lean_ctor_set(v___x_5382_, 1, v_k_5357_);
lean_ctor_set(v___x_5382_, 0, v___x_5390_);
v___x_5392_ = v___x_5382_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v___x_5390_);
lean_ctor_set(v_reuseFailAlloc_5396_, 1, v_k_5357_);
lean_ctor_set(v_reuseFailAlloc_5396_, 2, v_v_5358_);
lean_ctor_set(v_reuseFailAlloc_5396_, 3, v_r_5376_);
lean_ctor_set(v_reuseFailAlloc_5396_, 4, v_r_5360_);
v___x_5392_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
lean_object* v___x_5394_; 
if (v_isShared_5371_ == 0)
{
lean_ctor_set(v___x_5370_, 4, v___x_5392_);
lean_ctor_set(v___x_5370_, 3, v___y_5388_);
lean_ctor_set(v___x_5370_, 2, v_v_5374_);
lean_ctor_set(v___x_5370_, 1, v_k_5373_);
lean_ctor_set(v___x_5370_, 0, v___x_5385_);
v___x_5394_ = v___x_5370_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v___x_5385_);
lean_ctor_set(v_reuseFailAlloc_5395_, 1, v_k_5373_);
lean_ctor_set(v_reuseFailAlloc_5395_, 2, v_v_5374_);
lean_ctor_set(v_reuseFailAlloc_5395_, 3, v___y_5388_);
lean_ctor_set(v_reuseFailAlloc_5395_, 4, v___x_5392_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
v___jp_5397_:
{
lean_object* v___x_5399_; lean_object* v___x_5401_; 
v___x_5399_ = lean_nat_add(v___x_5384_, v___y_5398_);
lean_dec(v___y_5398_);
lean_dec(v___x_5384_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v_l_5375_);
lean_ctor_set(v___x_5350_, 3, v_impl_5353_);
lean_ctor_set(v___x_5350_, 0, v___x_5399_);
v___x_5401_ = v___x_5350_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5399_);
lean_ctor_set(v_reuseFailAlloc_5405_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5405_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5405_, 3, v_impl_5353_);
lean_ctor_set(v_reuseFailAlloc_5405_, 4, v_l_5375_);
v___x_5401_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
lean_object* v___x_5402_; 
v___x_5402_ = lean_nat_add(v___x_5354_, v_size_5377_);
if (lean_obj_tag(v_r_5376_) == 0)
{
lean_object* v_size_5403_; 
v_size_5403_ = lean_ctor_get(v_r_5376_, 0);
lean_inc(v_size_5403_);
v___y_5387_ = v___x_5402_;
v___y_5388_ = v___x_5401_;
v___y_5389_ = v_size_5403_;
goto v___jp_5386_;
}
else
{
lean_object* v___x_5404_; 
v___x_5404_ = lean_unsigned_to_nat(0u);
v___y_5387_ = v___x_5402_;
v___y_5388_ = v___x_5401_;
v___y_5389_ = v___x_5404_;
goto v___jp_5386_;
}
}
}
}
}
else
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5418_; 
lean_del_object(v___x_5350_);
v___x_5414_ = lean_nat_add(v___x_5354_, v_size_5355_);
lean_dec(v_size_5355_);
v___x_5415_ = lean_nat_add(v___x_5414_, v_size_5356_);
lean_dec(v_size_5356_);
v___x_5416_ = lean_nat_add(v___x_5414_, v_size_5372_);
lean_dec(v___x_5414_);
lean_inc_ref(v_impl_5353_);
if (v_isShared_5371_ == 0)
{
lean_ctor_set(v___x_5370_, 4, v_l_5359_);
lean_ctor_set(v___x_5370_, 3, v_impl_5353_);
lean_ctor_set(v___x_5370_, 2, v_v_5346_);
lean_ctor_set(v___x_5370_, 1, v_k_5345_);
lean_ctor_set(v___x_5370_, 0, v___x_5416_);
v___x_5418_ = v___x_5370_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v___x_5416_);
lean_ctor_set(v_reuseFailAlloc_5431_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5431_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5431_, 3, v_impl_5353_);
lean_ctor_set(v_reuseFailAlloc_5431_, 4, v_l_5359_);
v___x_5418_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5425_; 
v_isSharedCheck_5425_ = !lean_is_exclusive(v_impl_5353_);
if (v_isSharedCheck_5425_ == 0)
{
lean_object* v_unused_5426_; lean_object* v_unused_5427_; lean_object* v_unused_5428_; lean_object* v_unused_5429_; lean_object* v_unused_5430_; 
v_unused_5426_ = lean_ctor_get(v_impl_5353_, 4);
lean_dec(v_unused_5426_);
v_unused_5427_ = lean_ctor_get(v_impl_5353_, 3);
lean_dec(v_unused_5427_);
v_unused_5428_ = lean_ctor_get(v_impl_5353_, 2);
lean_dec(v_unused_5428_);
v_unused_5429_ = lean_ctor_get(v_impl_5353_, 1);
lean_dec(v_unused_5429_);
v_unused_5430_ = lean_ctor_get(v_impl_5353_, 0);
lean_dec(v_unused_5430_);
v___x_5420_ = v_impl_5353_;
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
else
{
lean_dec(v_impl_5353_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5425_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___x_5423_; 
if (v_isShared_5421_ == 0)
{
lean_ctor_set(v___x_5420_, 4, v_r_5360_);
lean_ctor_set(v___x_5420_, 3, v___x_5418_);
lean_ctor_set(v___x_5420_, 2, v_v_5358_);
lean_ctor_set(v___x_5420_, 1, v_k_5357_);
lean_ctor_set(v___x_5420_, 0, v___x_5415_);
v___x_5423_ = v___x_5420_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v___x_5415_);
lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_k_5357_);
lean_ctor_set(v_reuseFailAlloc_5424_, 2, v_v_5358_);
lean_ctor_set(v_reuseFailAlloc_5424_, 3, v___x_5418_);
lean_ctor_set(v_reuseFailAlloc_5424_, 4, v_r_5360_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5438_; lean_object* v___x_5439_; lean_object* v___x_5441_; 
v_size_5438_ = lean_ctor_get(v_impl_5353_, 0);
lean_inc(v_size_5438_);
v___x_5439_ = lean_nat_add(v___x_5354_, v_size_5438_);
lean_dec(v_size_5438_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 3, v_impl_5353_);
lean_ctor_set(v___x_5350_, 0, v___x_5439_);
v___x_5441_ = v___x_5350_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v___x_5439_);
lean_ctor_set(v_reuseFailAlloc_5442_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5442_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5442_, 3, v_impl_5353_);
lean_ctor_set(v_reuseFailAlloc_5442_, 4, v_r_5348_);
v___x_5441_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
return v___x_5441_;
}
}
}
else
{
if (lean_obj_tag(v_r_5348_) == 0)
{
lean_object* v_l_5443_; 
v_l_5443_ = lean_ctor_get(v_r_5348_, 3);
lean_inc(v_l_5443_);
if (lean_obj_tag(v_l_5443_) == 0)
{
lean_object* v_r_5444_; 
v_r_5444_ = lean_ctor_get(v_r_5348_, 4);
lean_inc(v_r_5444_);
if (lean_obj_tag(v_r_5444_) == 0)
{
lean_object* v_size_5445_; lean_object* v_k_5446_; lean_object* v_v_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5460_; 
v_size_5445_ = lean_ctor_get(v_r_5348_, 0);
v_k_5446_ = lean_ctor_get(v_r_5348_, 1);
v_v_5447_ = lean_ctor_get(v_r_5348_, 2);
v_isSharedCheck_5460_ = !lean_is_exclusive(v_r_5348_);
if (v_isSharedCheck_5460_ == 0)
{
lean_object* v_unused_5461_; lean_object* v_unused_5462_; 
v_unused_5461_ = lean_ctor_get(v_r_5348_, 4);
lean_dec(v_unused_5461_);
v_unused_5462_ = lean_ctor_get(v_r_5348_, 3);
lean_dec(v_unused_5462_);
v___x_5449_ = v_r_5348_;
v_isShared_5450_ = v_isSharedCheck_5460_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_v_5447_);
lean_inc(v_k_5446_);
lean_inc(v_size_5445_);
lean_dec(v_r_5348_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5460_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v_size_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5455_; 
v_size_5451_ = lean_ctor_get(v_l_5443_, 0);
v___x_5452_ = lean_nat_add(v___x_5354_, v_size_5445_);
lean_dec(v_size_5445_);
v___x_5453_ = lean_nat_add(v___x_5354_, v_size_5451_);
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 4, v_l_5443_);
lean_ctor_set(v___x_5449_, 3, v_impl_5353_);
lean_ctor_set(v___x_5449_, 2, v_v_5346_);
lean_ctor_set(v___x_5449_, 1, v_k_5345_);
lean_ctor_set(v___x_5449_, 0, v___x_5453_);
v___x_5455_ = v___x_5449_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v___x_5453_);
lean_ctor_set(v_reuseFailAlloc_5459_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5459_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5459_, 3, v_impl_5353_);
lean_ctor_set(v_reuseFailAlloc_5459_, 4, v_l_5443_);
v___x_5455_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
lean_object* v___x_5457_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v_r_5444_);
lean_ctor_set(v___x_5350_, 3, v___x_5455_);
lean_ctor_set(v___x_5350_, 2, v_v_5447_);
lean_ctor_set(v___x_5350_, 1, v_k_5446_);
lean_ctor_set(v___x_5350_, 0, v___x_5452_);
v___x_5457_ = v___x_5350_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5452_);
lean_ctor_set(v_reuseFailAlloc_5458_, 1, v_k_5446_);
lean_ctor_set(v_reuseFailAlloc_5458_, 2, v_v_5447_);
lean_ctor_set(v_reuseFailAlloc_5458_, 3, v___x_5455_);
lean_ctor_set(v_reuseFailAlloc_5458_, 4, v_r_5444_);
v___x_5457_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
return v___x_5457_;
}
}
}
}
else
{
lean_object* v_k_5463_; lean_object* v_v_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5487_; 
v_k_5463_ = lean_ctor_get(v_r_5348_, 1);
v_v_5464_ = lean_ctor_get(v_r_5348_, 2);
v_isSharedCheck_5487_ = !lean_is_exclusive(v_r_5348_);
if (v_isSharedCheck_5487_ == 0)
{
lean_object* v_unused_5488_; lean_object* v_unused_5489_; lean_object* v_unused_5490_; 
v_unused_5488_ = lean_ctor_get(v_r_5348_, 4);
lean_dec(v_unused_5488_);
v_unused_5489_ = lean_ctor_get(v_r_5348_, 3);
lean_dec(v_unused_5489_);
v_unused_5490_ = lean_ctor_get(v_r_5348_, 0);
lean_dec(v_unused_5490_);
v___x_5466_ = v_r_5348_;
v_isShared_5467_ = v_isSharedCheck_5487_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_v_5464_);
lean_inc(v_k_5463_);
lean_dec(v_r_5348_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5487_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v_k_5468_; lean_object* v_v_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5483_; 
v_k_5468_ = lean_ctor_get(v_l_5443_, 1);
v_v_5469_ = lean_ctor_get(v_l_5443_, 2);
v_isSharedCheck_5483_ = !lean_is_exclusive(v_l_5443_);
if (v_isSharedCheck_5483_ == 0)
{
lean_object* v_unused_5484_; lean_object* v_unused_5485_; lean_object* v_unused_5486_; 
v_unused_5484_ = lean_ctor_get(v_l_5443_, 4);
lean_dec(v_unused_5484_);
v_unused_5485_ = lean_ctor_get(v_l_5443_, 3);
lean_dec(v_unused_5485_);
v_unused_5486_ = lean_ctor_get(v_l_5443_, 0);
lean_dec(v_unused_5486_);
v___x_5471_ = v_l_5443_;
v_isShared_5472_ = v_isSharedCheck_5483_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_v_5469_);
lean_inc(v_k_5468_);
lean_dec(v_l_5443_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5483_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___x_5473_; lean_object* v___x_5475_; 
v___x_5473_ = lean_unsigned_to_nat(3u);
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 4, v_r_5444_);
lean_ctor_set(v___x_5471_, 3, v_r_5444_);
lean_ctor_set(v___x_5471_, 2, v_v_5346_);
lean_ctor_set(v___x_5471_, 1, v_k_5345_);
lean_ctor_set(v___x_5471_, 0, v___x_5354_);
v___x_5475_ = v___x_5471_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v___x_5354_);
lean_ctor_set(v_reuseFailAlloc_5482_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5482_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5482_, 3, v_r_5444_);
lean_ctor_set(v_reuseFailAlloc_5482_, 4, v_r_5444_);
v___x_5475_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
lean_object* v___x_5477_; 
if (v_isShared_5467_ == 0)
{
lean_ctor_set(v___x_5466_, 3, v_r_5444_);
lean_ctor_set(v___x_5466_, 0, v___x_5354_);
v___x_5477_ = v___x_5466_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v___x_5354_);
lean_ctor_set(v_reuseFailAlloc_5481_, 1, v_k_5463_);
lean_ctor_set(v_reuseFailAlloc_5481_, 2, v_v_5464_);
lean_ctor_set(v_reuseFailAlloc_5481_, 3, v_r_5444_);
lean_ctor_set(v_reuseFailAlloc_5481_, 4, v_r_5444_);
v___x_5477_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
lean_object* v___x_5479_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v___x_5477_);
lean_ctor_set(v___x_5350_, 3, v___x_5475_);
lean_ctor_set(v___x_5350_, 2, v_v_5469_);
lean_ctor_set(v___x_5350_, 1, v_k_5468_);
lean_ctor_set(v___x_5350_, 0, v___x_5473_);
v___x_5479_ = v___x_5350_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5473_);
lean_ctor_set(v_reuseFailAlloc_5480_, 1, v_k_5468_);
lean_ctor_set(v_reuseFailAlloc_5480_, 2, v_v_5469_);
lean_ctor_set(v_reuseFailAlloc_5480_, 3, v___x_5475_);
lean_ctor_set(v_reuseFailAlloc_5480_, 4, v___x_5477_);
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
}
}
}
else
{
lean_object* v_r_5491_; 
v_r_5491_ = lean_ctor_get(v_r_5348_, 4);
lean_inc(v_r_5491_);
if (lean_obj_tag(v_r_5491_) == 0)
{
lean_object* v_k_5492_; lean_object* v_v_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5504_; 
v_k_5492_ = lean_ctor_get(v_r_5348_, 1);
v_v_5493_ = lean_ctor_get(v_r_5348_, 2);
v_isSharedCheck_5504_ = !lean_is_exclusive(v_r_5348_);
if (v_isSharedCheck_5504_ == 0)
{
lean_object* v_unused_5505_; lean_object* v_unused_5506_; lean_object* v_unused_5507_; 
v_unused_5505_ = lean_ctor_get(v_r_5348_, 4);
lean_dec(v_unused_5505_);
v_unused_5506_ = lean_ctor_get(v_r_5348_, 3);
lean_dec(v_unused_5506_);
v_unused_5507_ = lean_ctor_get(v_r_5348_, 0);
lean_dec(v_unused_5507_);
v___x_5495_ = v_r_5348_;
v_isShared_5496_ = v_isSharedCheck_5504_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_v_5493_);
lean_inc(v_k_5492_);
lean_dec(v_r_5348_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5504_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5497_; lean_object* v___x_5499_; 
v___x_5497_ = lean_unsigned_to_nat(3u);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 4, v_l_5443_);
lean_ctor_set(v___x_5495_, 2, v_v_5346_);
lean_ctor_set(v___x_5495_, 1, v_k_5345_);
lean_ctor_set(v___x_5495_, 0, v___x_5354_);
v___x_5499_ = v___x_5495_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5354_);
lean_ctor_set(v_reuseFailAlloc_5503_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5503_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5503_, 3, v_l_5443_);
lean_ctor_set(v_reuseFailAlloc_5503_, 4, v_l_5443_);
v___x_5499_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
lean_object* v___x_5501_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v_r_5491_);
lean_ctor_set(v___x_5350_, 3, v___x_5499_);
lean_ctor_set(v___x_5350_, 2, v_v_5493_);
lean_ctor_set(v___x_5350_, 1, v_k_5492_);
lean_ctor_set(v___x_5350_, 0, v___x_5497_);
v___x_5501_ = v___x_5350_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v___x_5497_);
lean_ctor_set(v_reuseFailAlloc_5502_, 1, v_k_5492_);
lean_ctor_set(v_reuseFailAlloc_5502_, 2, v_v_5493_);
lean_ctor_set(v_reuseFailAlloc_5502_, 3, v___x_5499_);
lean_ctor_set(v_reuseFailAlloc_5502_, 4, v_r_5491_);
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
else
{
lean_object* v_size_5508_; lean_object* v_k_5509_; lean_object* v_v_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5521_; 
v_size_5508_ = lean_ctor_get(v_r_5348_, 0);
v_k_5509_ = lean_ctor_get(v_r_5348_, 1);
v_v_5510_ = lean_ctor_get(v_r_5348_, 2);
v_isSharedCheck_5521_ = !lean_is_exclusive(v_r_5348_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; lean_object* v_unused_5523_; 
v_unused_5522_ = lean_ctor_get(v_r_5348_, 4);
lean_dec(v_unused_5522_);
v_unused_5523_ = lean_ctor_get(v_r_5348_, 3);
lean_dec(v_unused_5523_);
v___x_5512_ = v_r_5348_;
v_isShared_5513_ = v_isSharedCheck_5521_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_v_5510_);
lean_inc(v_k_5509_);
lean_inc(v_size_5508_);
lean_dec(v_r_5348_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5521_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 3, v_r_5491_);
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_size_5508_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v_k_5509_);
lean_ctor_set(v_reuseFailAlloc_5520_, 2, v_v_5510_);
lean_ctor_set(v_reuseFailAlloc_5520_, 3, v_r_5491_);
lean_ctor_set(v_reuseFailAlloc_5520_, 4, v_r_5491_);
v___x_5515_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
lean_object* v___x_5516_; lean_object* v___x_5518_; 
v___x_5516_ = lean_unsigned_to_nat(2u);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v___x_5515_);
lean_ctor_set(v___x_5350_, 3, v_r_5491_);
lean_ctor_set(v___x_5350_, 0, v___x_5516_);
v___x_5518_ = v___x_5350_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v___x_5516_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5519_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5519_, 3, v_r_5491_);
lean_ctor_set(v_reuseFailAlloc_5519_, 4, v___x_5515_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
}
}
else
{
lean_object* v___x_5525_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 3, v_r_5348_);
lean_ctor_set(v___x_5350_, 0, v___x_5354_);
v___x_5525_ = v___x_5350_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v___x_5354_);
lean_ctor_set(v_reuseFailAlloc_5526_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5526_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5526_, 3, v_r_5348_);
lean_ctor_set(v_reuseFailAlloc_5526_, 4, v_r_5348_);
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
case 1:
{
lean_del_object(v___x_5350_);
lean_dec(v_v_5346_);
lean_dec(v_k_5345_);
if (lean_obj_tag(v_l_5347_) == 0)
{
if (lean_obj_tag(v_r_5348_) == 0)
{
lean_object* v_size_5527_; lean_object* v_k_5528_; lean_object* v_v_5529_; lean_object* v_l_5530_; lean_object* v_r_5531_; lean_object* v_size_5532_; lean_object* v_k_5533_; lean_object* v_v_5534_; lean_object* v_l_5535_; lean_object* v_r_5536_; lean_object* v___x_5537_; uint8_t v___x_5538_; 
v_size_5527_ = lean_ctor_get(v_l_5347_, 0);
v_k_5528_ = lean_ctor_get(v_l_5347_, 1);
v_v_5529_ = lean_ctor_get(v_l_5347_, 2);
v_l_5530_ = lean_ctor_get(v_l_5347_, 3);
v_r_5531_ = lean_ctor_get(v_l_5347_, 4);
lean_inc(v_r_5531_);
v_size_5532_ = lean_ctor_get(v_r_5348_, 0);
v_k_5533_ = lean_ctor_get(v_r_5348_, 1);
v_v_5534_ = lean_ctor_get(v_r_5348_, 2);
v_l_5535_ = lean_ctor_get(v_r_5348_, 3);
lean_inc(v_l_5535_);
v_r_5536_ = lean_ctor_get(v_r_5348_, 4);
v___x_5537_ = lean_unsigned_to_nat(1u);
v___x_5538_ = lean_nat_dec_lt(v_size_5527_, v_size_5532_);
if (v___x_5538_ == 0)
{
lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5674_; 
lean_inc(v_l_5530_);
lean_inc(v_v_5529_);
lean_inc(v_k_5528_);
v_isSharedCheck_5674_ = !lean_is_exclusive(v_l_5347_);
if (v_isSharedCheck_5674_ == 0)
{
lean_object* v_unused_5675_; lean_object* v_unused_5676_; lean_object* v_unused_5677_; lean_object* v_unused_5678_; lean_object* v_unused_5679_; 
v_unused_5675_ = lean_ctor_get(v_l_5347_, 4);
lean_dec(v_unused_5675_);
v_unused_5676_ = lean_ctor_get(v_l_5347_, 3);
lean_dec(v_unused_5676_);
v_unused_5677_ = lean_ctor_get(v_l_5347_, 2);
lean_dec(v_unused_5677_);
v_unused_5678_ = lean_ctor_get(v_l_5347_, 1);
lean_dec(v_unused_5678_);
v_unused_5679_ = lean_ctor_get(v_l_5347_, 0);
lean_dec(v_unused_5679_);
v___x_5540_ = v_l_5347_;
v_isShared_5541_ = v_isSharedCheck_5674_;
goto v_resetjp_5539_;
}
else
{
lean_dec(v_l_5347_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5674_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5542_; lean_object* v_tree_5543_; 
v___x_5542_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5528_, v_v_5529_, v_l_5530_, v_r_5531_);
v_tree_5543_ = lean_ctor_get(v___x_5542_, 2);
lean_inc(v_tree_5543_);
if (lean_obj_tag(v_tree_5543_) == 0)
{
lean_object* v_k_5544_; lean_object* v_v_5545_; lean_object* v_size_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; uint8_t v___x_5549_; 
v_k_5544_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_k_5544_);
v_v_5545_ = lean_ctor_get(v___x_5542_, 1);
lean_inc(v_v_5545_);
lean_dec_ref(v___x_5542_);
v_size_5546_ = lean_ctor_get(v_tree_5543_, 0);
v___x_5547_ = lean_unsigned_to_nat(3u);
v___x_5548_ = lean_nat_mul(v___x_5547_, v_size_5546_);
v___x_5549_ = lean_nat_dec_lt(v___x_5548_, v_size_5532_);
lean_dec(v___x_5548_);
if (v___x_5549_ == 0)
{
lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5553_; 
lean_dec(v_l_5535_);
v___x_5550_ = lean_nat_add(v___x_5537_, v_size_5546_);
v___x_5551_ = lean_nat_add(v___x_5550_, v_size_5532_);
lean_dec(v___x_5550_);
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 4, v_r_5348_);
lean_ctor_set(v___x_5540_, 3, v_tree_5543_);
lean_ctor_set(v___x_5540_, 2, v_v_5545_);
lean_ctor_set(v___x_5540_, 1, v_k_5544_);
lean_ctor_set(v___x_5540_, 0, v___x_5551_);
v___x_5553_ = v___x_5540_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v___x_5551_);
lean_ctor_set(v_reuseFailAlloc_5554_, 1, v_k_5544_);
lean_ctor_set(v_reuseFailAlloc_5554_, 2, v_v_5545_);
lean_ctor_set(v_reuseFailAlloc_5554_, 3, v_tree_5543_);
lean_ctor_set(v_reuseFailAlloc_5554_, 4, v_r_5348_);
v___x_5553_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
return v___x_5553_;
}
}
else
{
lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5609_; 
lean_inc(v_r_5536_);
lean_inc(v_v_5534_);
lean_inc(v_k_5533_);
lean_inc(v_size_5532_);
v_isSharedCheck_5609_ = !lean_is_exclusive(v_r_5348_);
if (v_isSharedCheck_5609_ == 0)
{
lean_object* v_unused_5610_; lean_object* v_unused_5611_; lean_object* v_unused_5612_; lean_object* v_unused_5613_; lean_object* v_unused_5614_; 
v_unused_5610_ = lean_ctor_get(v_r_5348_, 4);
lean_dec(v_unused_5610_);
v_unused_5611_ = lean_ctor_get(v_r_5348_, 3);
lean_dec(v_unused_5611_);
v_unused_5612_ = lean_ctor_get(v_r_5348_, 2);
lean_dec(v_unused_5612_);
v_unused_5613_ = lean_ctor_get(v_r_5348_, 1);
lean_dec(v_unused_5613_);
v_unused_5614_ = lean_ctor_get(v_r_5348_, 0);
lean_dec(v_unused_5614_);
v___x_5556_ = v_r_5348_;
v_isShared_5557_ = v_isSharedCheck_5609_;
goto v_resetjp_5555_;
}
else
{
lean_dec(v_r_5348_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5609_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v_size_5558_; lean_object* v_k_5559_; lean_object* v_v_5560_; lean_object* v_l_5561_; lean_object* v_r_5562_; lean_object* v_size_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; uint8_t v___x_5566_; 
v_size_5558_ = lean_ctor_get(v_l_5535_, 0);
v_k_5559_ = lean_ctor_get(v_l_5535_, 1);
v_v_5560_ = lean_ctor_get(v_l_5535_, 2);
v_l_5561_ = lean_ctor_get(v_l_5535_, 3);
v_r_5562_ = lean_ctor_get(v_l_5535_, 4);
v_size_5563_ = lean_ctor_get(v_r_5536_, 0);
v___x_5564_ = lean_unsigned_to_nat(2u);
v___x_5565_ = lean_nat_mul(v___x_5564_, v_size_5563_);
v___x_5566_ = lean_nat_dec_lt(v_size_5558_, v___x_5565_);
lean_dec(v___x_5565_);
if (v___x_5566_ == 0)
{
lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5594_; 
lean_inc(v_r_5562_);
lean_inc(v_l_5561_);
lean_inc(v_v_5560_);
lean_inc(v_k_5559_);
v_isSharedCheck_5594_ = !lean_is_exclusive(v_l_5535_);
if (v_isSharedCheck_5594_ == 0)
{
lean_object* v_unused_5595_; lean_object* v_unused_5596_; lean_object* v_unused_5597_; lean_object* v_unused_5598_; lean_object* v_unused_5599_; 
v_unused_5595_ = lean_ctor_get(v_l_5535_, 4);
lean_dec(v_unused_5595_);
v_unused_5596_ = lean_ctor_get(v_l_5535_, 3);
lean_dec(v_unused_5596_);
v_unused_5597_ = lean_ctor_get(v_l_5535_, 2);
lean_dec(v_unused_5597_);
v_unused_5598_ = lean_ctor_get(v_l_5535_, 1);
lean_dec(v_unused_5598_);
v_unused_5599_ = lean_ctor_get(v_l_5535_, 0);
lean_dec(v_unused_5599_);
v___x_5568_ = v_l_5535_;
v_isShared_5569_ = v_isSharedCheck_5594_;
goto v_resetjp_5567_;
}
else
{
lean_dec(v_l_5535_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5594_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___y_5573_; lean_object* v___y_5574_; lean_object* v___y_5575_; lean_object* v___y_5584_; 
v___x_5570_ = lean_nat_add(v___x_5537_, v_size_5546_);
v___x_5571_ = lean_nat_add(v___x_5570_, v_size_5532_);
lean_dec(v_size_5532_);
if (lean_obj_tag(v_l_5561_) == 0)
{
lean_object* v_size_5592_; 
v_size_5592_ = lean_ctor_get(v_l_5561_, 0);
lean_inc(v_size_5592_);
v___y_5584_ = v_size_5592_;
goto v___jp_5583_;
}
else
{
lean_object* v___x_5593_; 
v___x_5593_ = lean_unsigned_to_nat(0u);
v___y_5584_ = v___x_5593_;
goto v___jp_5583_;
}
v___jp_5572_:
{
lean_object* v___x_5576_; lean_object* v___x_5578_; 
v___x_5576_ = lean_nat_add(v___y_5574_, v___y_5575_);
lean_dec(v___y_5575_);
lean_dec(v___y_5574_);
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 4, v_r_5536_);
lean_ctor_set(v___x_5568_, 3, v_r_5562_);
lean_ctor_set(v___x_5568_, 2, v_v_5534_);
lean_ctor_set(v___x_5568_, 1, v_k_5533_);
lean_ctor_set(v___x_5568_, 0, v___x_5576_);
v___x_5578_ = v___x_5568_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v___x_5576_);
lean_ctor_set(v_reuseFailAlloc_5582_, 1, v_k_5533_);
lean_ctor_set(v_reuseFailAlloc_5582_, 2, v_v_5534_);
lean_ctor_set(v_reuseFailAlloc_5582_, 3, v_r_5562_);
lean_ctor_set(v_reuseFailAlloc_5582_, 4, v_r_5536_);
v___x_5578_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
lean_object* v___x_5580_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 4, v___x_5578_);
lean_ctor_set(v___x_5556_, 3, v___y_5573_);
lean_ctor_set(v___x_5556_, 2, v_v_5560_);
lean_ctor_set(v___x_5556_, 1, v_k_5559_);
lean_ctor_set(v___x_5556_, 0, v___x_5571_);
v___x_5580_ = v___x_5556_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v___x_5571_);
lean_ctor_set(v_reuseFailAlloc_5581_, 1, v_k_5559_);
lean_ctor_set(v_reuseFailAlloc_5581_, 2, v_v_5560_);
lean_ctor_set(v_reuseFailAlloc_5581_, 3, v___y_5573_);
lean_ctor_set(v_reuseFailAlloc_5581_, 4, v___x_5578_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
v___jp_5583_:
{
lean_object* v___x_5585_; lean_object* v___x_5587_; 
v___x_5585_ = lean_nat_add(v___x_5570_, v___y_5584_);
lean_dec(v___y_5584_);
lean_dec(v___x_5570_);
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 4, v_l_5561_);
lean_ctor_set(v___x_5540_, 3, v_tree_5543_);
lean_ctor_set(v___x_5540_, 2, v_v_5545_);
lean_ctor_set(v___x_5540_, 1, v_k_5544_);
lean_ctor_set(v___x_5540_, 0, v___x_5585_);
v___x_5587_ = v___x_5540_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v___x_5585_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v_k_5544_);
lean_ctor_set(v_reuseFailAlloc_5591_, 2, v_v_5545_);
lean_ctor_set(v_reuseFailAlloc_5591_, 3, v_tree_5543_);
lean_ctor_set(v_reuseFailAlloc_5591_, 4, v_l_5561_);
v___x_5587_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5588_; 
v___x_5588_ = lean_nat_add(v___x_5537_, v_size_5563_);
if (lean_obj_tag(v_r_5562_) == 0)
{
lean_object* v_size_5589_; 
v_size_5589_ = lean_ctor_get(v_r_5562_, 0);
lean_inc(v_size_5589_);
v___y_5573_ = v___x_5587_;
v___y_5574_ = v___x_5588_;
v___y_5575_ = v_size_5589_;
goto v___jp_5572_;
}
else
{
lean_object* v___x_5590_; 
v___x_5590_ = lean_unsigned_to_nat(0u);
v___y_5573_ = v___x_5587_;
v___y_5574_ = v___x_5588_;
v___y_5575_ = v___x_5590_;
goto v___jp_5572_;
}
}
}
}
}
else
{
lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5604_; 
v___x_5600_ = lean_nat_add(v___x_5537_, v_size_5546_);
v___x_5601_ = lean_nat_add(v___x_5600_, v_size_5532_);
lean_dec(v_size_5532_);
v___x_5602_ = lean_nat_add(v___x_5600_, v_size_5558_);
lean_dec(v___x_5600_);
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 4, v_l_5535_);
lean_ctor_set(v___x_5556_, 3, v_tree_5543_);
lean_ctor_set(v___x_5556_, 2, v_v_5545_);
lean_ctor_set(v___x_5556_, 1, v_k_5544_);
lean_ctor_set(v___x_5556_, 0, v___x_5602_);
v___x_5604_ = v___x_5556_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v___x_5602_);
lean_ctor_set(v_reuseFailAlloc_5608_, 1, v_k_5544_);
lean_ctor_set(v_reuseFailAlloc_5608_, 2, v_v_5545_);
lean_ctor_set(v_reuseFailAlloc_5608_, 3, v_tree_5543_);
lean_ctor_set(v_reuseFailAlloc_5608_, 4, v_l_5535_);
v___x_5604_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
lean_object* v___x_5606_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 4, v_r_5536_);
lean_ctor_set(v___x_5540_, 3, v___x_5604_);
lean_ctor_set(v___x_5540_, 2, v_v_5534_);
lean_ctor_set(v___x_5540_, 1, v_k_5533_);
lean_ctor_set(v___x_5540_, 0, v___x_5601_);
v___x_5606_ = v___x_5540_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v___x_5601_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v_k_5533_);
lean_ctor_set(v_reuseFailAlloc_5607_, 2, v_v_5534_);
lean_ctor_set(v_reuseFailAlloc_5607_, 3, v___x_5604_);
lean_ctor_set(v_reuseFailAlloc_5607_, 4, v_r_5536_);
v___x_5606_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
return v___x_5606_;
}
}
}
}
}
}
else
{
lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5668_; 
lean_inc(v_r_5536_);
lean_inc(v_v_5534_);
lean_inc(v_k_5533_);
lean_inc(v_size_5532_);
v_isSharedCheck_5668_ = !lean_is_exclusive(v_r_5348_);
if (v_isSharedCheck_5668_ == 0)
{
lean_object* v_unused_5669_; lean_object* v_unused_5670_; lean_object* v_unused_5671_; lean_object* v_unused_5672_; lean_object* v_unused_5673_; 
v_unused_5669_ = lean_ctor_get(v_r_5348_, 4);
lean_dec(v_unused_5669_);
v_unused_5670_ = lean_ctor_get(v_r_5348_, 3);
lean_dec(v_unused_5670_);
v_unused_5671_ = lean_ctor_get(v_r_5348_, 2);
lean_dec(v_unused_5671_);
v_unused_5672_ = lean_ctor_get(v_r_5348_, 1);
lean_dec(v_unused_5672_);
v_unused_5673_ = lean_ctor_get(v_r_5348_, 0);
lean_dec(v_unused_5673_);
v___x_5616_ = v_r_5348_;
v_isShared_5617_ = v_isSharedCheck_5668_;
goto v_resetjp_5615_;
}
else
{
lean_dec(v_r_5348_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5668_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
if (lean_obj_tag(v_l_5535_) == 0)
{
if (lean_obj_tag(v_r_5536_) == 0)
{
lean_object* v_k_5618_; lean_object* v_v_5619_; lean_object* v_size_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5624_; 
v_k_5618_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_k_5618_);
v_v_5619_ = lean_ctor_get(v___x_5542_, 1);
lean_inc(v_v_5619_);
lean_dec_ref(v___x_5542_);
v_size_5620_ = lean_ctor_get(v_l_5535_, 0);
v___x_5621_ = lean_nat_add(v___x_5537_, v_size_5532_);
lean_dec(v_size_5532_);
v___x_5622_ = lean_nat_add(v___x_5537_, v_size_5620_);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 4, v_l_5535_);
lean_ctor_set(v___x_5616_, 3, v_tree_5543_);
lean_ctor_set(v___x_5616_, 2, v_v_5619_);
lean_ctor_set(v___x_5616_, 1, v_k_5618_);
lean_ctor_set(v___x_5616_, 0, v___x_5622_);
v___x_5624_ = v___x_5616_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v___x_5622_);
lean_ctor_set(v_reuseFailAlloc_5628_, 1, v_k_5618_);
lean_ctor_set(v_reuseFailAlloc_5628_, 2, v_v_5619_);
lean_ctor_set(v_reuseFailAlloc_5628_, 3, v_tree_5543_);
lean_ctor_set(v_reuseFailAlloc_5628_, 4, v_l_5535_);
v___x_5624_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
lean_object* v___x_5626_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 4, v_r_5536_);
lean_ctor_set(v___x_5540_, 3, v___x_5624_);
lean_ctor_set(v___x_5540_, 2, v_v_5534_);
lean_ctor_set(v___x_5540_, 1, v_k_5533_);
lean_ctor_set(v___x_5540_, 0, v___x_5621_);
v___x_5626_ = v___x_5540_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v___x_5621_);
lean_ctor_set(v_reuseFailAlloc_5627_, 1, v_k_5533_);
lean_ctor_set(v_reuseFailAlloc_5627_, 2, v_v_5534_);
lean_ctor_set(v_reuseFailAlloc_5627_, 3, v___x_5624_);
lean_ctor_set(v_reuseFailAlloc_5627_, 4, v_r_5536_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
else
{
lean_object* v_k_5629_; lean_object* v_v_5630_; lean_object* v_k_5631_; lean_object* v_v_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5646_; 
lean_dec(v_size_5532_);
v_k_5629_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_k_5629_);
v_v_5630_ = lean_ctor_get(v___x_5542_, 1);
lean_inc(v_v_5630_);
lean_dec_ref(v___x_5542_);
v_k_5631_ = lean_ctor_get(v_l_5535_, 1);
v_v_5632_ = lean_ctor_get(v_l_5535_, 2);
v_isSharedCheck_5646_ = !lean_is_exclusive(v_l_5535_);
if (v_isSharedCheck_5646_ == 0)
{
lean_object* v_unused_5647_; lean_object* v_unused_5648_; lean_object* v_unused_5649_; 
v_unused_5647_ = lean_ctor_get(v_l_5535_, 4);
lean_dec(v_unused_5647_);
v_unused_5648_ = lean_ctor_get(v_l_5535_, 3);
lean_dec(v_unused_5648_);
v_unused_5649_ = lean_ctor_get(v_l_5535_, 0);
lean_dec(v_unused_5649_);
v___x_5634_ = v_l_5535_;
v_isShared_5635_ = v_isSharedCheck_5646_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_v_5632_);
lean_inc(v_k_5631_);
lean_dec(v_l_5535_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5646_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5636_; lean_object* v___x_5638_; 
v___x_5636_ = lean_unsigned_to_nat(3u);
if (v_isShared_5635_ == 0)
{
lean_ctor_set(v___x_5634_, 4, v_r_5536_);
lean_ctor_set(v___x_5634_, 3, v_r_5536_);
lean_ctor_set(v___x_5634_, 2, v_v_5630_);
lean_ctor_set(v___x_5634_, 1, v_k_5629_);
lean_ctor_set(v___x_5634_, 0, v___x_5537_);
v___x_5638_ = v___x_5634_;
goto v_reusejp_5637_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v___x_5537_);
lean_ctor_set(v_reuseFailAlloc_5645_, 1, v_k_5629_);
lean_ctor_set(v_reuseFailAlloc_5645_, 2, v_v_5630_);
lean_ctor_set(v_reuseFailAlloc_5645_, 3, v_r_5536_);
lean_ctor_set(v_reuseFailAlloc_5645_, 4, v_r_5536_);
v___x_5638_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5637_;
}
v_reusejp_5637_:
{
lean_object* v___x_5640_; 
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 3, v_r_5536_);
lean_ctor_set(v___x_5616_, 0, v___x_5537_);
v___x_5640_ = v___x_5616_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5644_; 
v_reuseFailAlloc_5644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5644_, 0, v___x_5537_);
lean_ctor_set(v_reuseFailAlloc_5644_, 1, v_k_5533_);
lean_ctor_set(v_reuseFailAlloc_5644_, 2, v_v_5534_);
lean_ctor_set(v_reuseFailAlloc_5644_, 3, v_r_5536_);
lean_ctor_set(v_reuseFailAlloc_5644_, 4, v_r_5536_);
v___x_5640_ = v_reuseFailAlloc_5644_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
lean_object* v___x_5642_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 4, v___x_5640_);
lean_ctor_set(v___x_5540_, 3, v___x_5638_);
lean_ctor_set(v___x_5540_, 2, v_v_5632_);
lean_ctor_set(v___x_5540_, 1, v_k_5631_);
lean_ctor_set(v___x_5540_, 0, v___x_5636_);
v___x_5642_ = v___x_5540_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v___x_5636_);
lean_ctor_set(v_reuseFailAlloc_5643_, 1, v_k_5631_);
lean_ctor_set(v_reuseFailAlloc_5643_, 2, v_v_5632_);
lean_ctor_set(v_reuseFailAlloc_5643_, 3, v___x_5638_);
lean_ctor_set(v_reuseFailAlloc_5643_, 4, v___x_5640_);
v___x_5642_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
return v___x_5642_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5536_) == 0)
{
lean_object* v_k_5650_; lean_object* v_v_5651_; lean_object* v___x_5652_; lean_object* v___x_5654_; 
lean_dec(v_size_5532_);
v_k_5650_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_k_5650_);
v_v_5651_ = lean_ctor_get(v___x_5542_, 1);
lean_inc(v_v_5651_);
lean_dec_ref(v___x_5542_);
v___x_5652_ = lean_unsigned_to_nat(3u);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 4, v_l_5535_);
lean_ctor_set(v___x_5616_, 2, v_v_5651_);
lean_ctor_set(v___x_5616_, 1, v_k_5650_);
lean_ctor_set(v___x_5616_, 0, v___x_5537_);
v___x_5654_ = v___x_5616_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v___x_5537_);
lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_k_5650_);
lean_ctor_set(v_reuseFailAlloc_5658_, 2, v_v_5651_);
lean_ctor_set(v_reuseFailAlloc_5658_, 3, v_l_5535_);
lean_ctor_set(v_reuseFailAlloc_5658_, 4, v_l_5535_);
v___x_5654_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
lean_object* v___x_5656_; 
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 4, v_r_5536_);
lean_ctor_set(v___x_5540_, 3, v___x_5654_);
lean_ctor_set(v___x_5540_, 2, v_v_5534_);
lean_ctor_set(v___x_5540_, 1, v_k_5533_);
lean_ctor_set(v___x_5540_, 0, v___x_5652_);
v___x_5656_ = v___x_5540_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v___x_5652_);
lean_ctor_set(v_reuseFailAlloc_5657_, 1, v_k_5533_);
lean_ctor_set(v_reuseFailAlloc_5657_, 2, v_v_5534_);
lean_ctor_set(v_reuseFailAlloc_5657_, 3, v___x_5654_);
lean_ctor_set(v_reuseFailAlloc_5657_, 4, v_r_5536_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
else
{
lean_object* v_k_5659_; lean_object* v_v_5660_; lean_object* v___x_5662_; 
v_k_5659_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_k_5659_);
v_v_5660_ = lean_ctor_get(v___x_5542_, 1);
lean_inc(v_v_5660_);
lean_dec_ref(v___x_5542_);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 3, v_r_5536_);
v___x_5662_ = v___x_5616_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_size_5532_);
lean_ctor_set(v_reuseFailAlloc_5667_, 1, v_k_5533_);
lean_ctor_set(v_reuseFailAlloc_5667_, 2, v_v_5534_);
lean_ctor_set(v_reuseFailAlloc_5667_, 3, v_r_5536_);
lean_ctor_set(v_reuseFailAlloc_5667_, 4, v_r_5536_);
v___x_5662_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
lean_object* v___x_5663_; lean_object* v___x_5665_; 
v___x_5663_ = lean_unsigned_to_nat(2u);
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 4, v___x_5662_);
lean_ctor_set(v___x_5540_, 3, v_r_5536_);
lean_ctor_set(v___x_5540_, 2, v_v_5660_);
lean_ctor_set(v___x_5540_, 1, v_k_5659_);
lean_ctor_set(v___x_5540_, 0, v___x_5663_);
v___x_5665_ = v___x_5540_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v___x_5663_);
lean_ctor_set(v_reuseFailAlloc_5666_, 1, v_k_5659_);
lean_ctor_set(v_reuseFailAlloc_5666_, 2, v_v_5660_);
lean_ctor_set(v_reuseFailAlloc_5666_, 3, v_r_5536_);
lean_ctor_set(v_reuseFailAlloc_5666_, 4, v___x_5662_);
v___x_5665_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
return v___x_5665_;
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
lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5832_; 
lean_inc(v_r_5536_);
lean_inc(v_v_5534_);
lean_inc(v_k_5533_);
v_isSharedCheck_5832_ = !lean_is_exclusive(v_r_5348_);
if (v_isSharedCheck_5832_ == 0)
{
lean_object* v_unused_5833_; lean_object* v_unused_5834_; lean_object* v_unused_5835_; lean_object* v_unused_5836_; lean_object* v_unused_5837_; 
v_unused_5833_ = lean_ctor_get(v_r_5348_, 4);
lean_dec(v_unused_5833_);
v_unused_5834_ = lean_ctor_get(v_r_5348_, 3);
lean_dec(v_unused_5834_);
v_unused_5835_ = lean_ctor_get(v_r_5348_, 2);
lean_dec(v_unused_5835_);
v_unused_5836_ = lean_ctor_get(v_r_5348_, 1);
lean_dec(v_unused_5836_);
v_unused_5837_ = lean_ctor_get(v_r_5348_, 0);
lean_dec(v_unused_5837_);
v___x_5681_ = v_r_5348_;
v_isShared_5682_ = v_isSharedCheck_5832_;
goto v_resetjp_5680_;
}
else
{
lean_dec(v_r_5348_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5832_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
lean_object* v___x_5683_; lean_object* v_tree_5684_; 
v___x_5683_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5533_, v_v_5534_, v_l_5535_, v_r_5536_);
v_tree_5684_ = lean_ctor_get(v___x_5683_, 2);
lean_inc(v_tree_5684_);
if (lean_obj_tag(v_tree_5684_) == 0)
{
lean_object* v_k_5685_; lean_object* v_v_5686_; lean_object* v_size_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; uint8_t v___x_5690_; 
v_k_5685_ = lean_ctor_get(v___x_5683_, 0);
lean_inc(v_k_5685_);
v_v_5686_ = lean_ctor_get(v___x_5683_, 1);
lean_inc(v_v_5686_);
lean_dec_ref(v___x_5683_);
v_size_5687_ = lean_ctor_get(v_tree_5684_, 0);
v___x_5688_ = lean_unsigned_to_nat(3u);
v___x_5689_ = lean_nat_mul(v___x_5688_, v_size_5687_);
v___x_5690_ = lean_nat_dec_lt(v___x_5689_, v_size_5527_);
lean_dec(v___x_5689_);
if (v___x_5690_ == 0)
{
lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5694_; 
lean_dec(v_r_5531_);
v___x_5691_ = lean_nat_add(v___x_5537_, v_size_5527_);
v___x_5692_ = lean_nat_add(v___x_5691_, v_size_5687_);
lean_dec(v___x_5691_);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 4, v_tree_5684_);
lean_ctor_set(v___x_5681_, 3, v_l_5347_);
lean_ctor_set(v___x_5681_, 2, v_v_5686_);
lean_ctor_set(v___x_5681_, 1, v_k_5685_);
lean_ctor_set(v___x_5681_, 0, v___x_5692_);
v___x_5694_ = v___x_5681_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v___x_5692_);
lean_ctor_set(v_reuseFailAlloc_5695_, 1, v_k_5685_);
lean_ctor_set(v_reuseFailAlloc_5695_, 2, v_v_5686_);
lean_ctor_set(v_reuseFailAlloc_5695_, 3, v_l_5347_);
lean_ctor_set(v_reuseFailAlloc_5695_, 4, v_tree_5684_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
else
{
lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5761_; 
lean_inc(v_l_5530_);
lean_inc(v_v_5529_);
lean_inc(v_k_5528_);
lean_inc(v_size_5527_);
v_isSharedCheck_5761_ = !lean_is_exclusive(v_l_5347_);
if (v_isSharedCheck_5761_ == 0)
{
lean_object* v_unused_5762_; lean_object* v_unused_5763_; lean_object* v_unused_5764_; lean_object* v_unused_5765_; lean_object* v_unused_5766_; 
v_unused_5762_ = lean_ctor_get(v_l_5347_, 4);
lean_dec(v_unused_5762_);
v_unused_5763_ = lean_ctor_get(v_l_5347_, 3);
lean_dec(v_unused_5763_);
v_unused_5764_ = lean_ctor_get(v_l_5347_, 2);
lean_dec(v_unused_5764_);
v_unused_5765_ = lean_ctor_get(v_l_5347_, 1);
lean_dec(v_unused_5765_);
v_unused_5766_ = lean_ctor_get(v_l_5347_, 0);
lean_dec(v_unused_5766_);
v___x_5697_ = v_l_5347_;
v_isShared_5698_ = v_isSharedCheck_5761_;
goto v_resetjp_5696_;
}
else
{
lean_dec(v_l_5347_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5761_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v_size_5699_; lean_object* v_size_5700_; lean_object* v_k_5701_; lean_object* v_v_5702_; lean_object* v_l_5703_; lean_object* v_r_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; uint8_t v___x_5707_; 
v_size_5699_ = lean_ctor_get(v_l_5530_, 0);
v_size_5700_ = lean_ctor_get(v_r_5531_, 0);
v_k_5701_ = lean_ctor_get(v_r_5531_, 1);
v_v_5702_ = lean_ctor_get(v_r_5531_, 2);
v_l_5703_ = lean_ctor_get(v_r_5531_, 3);
v_r_5704_ = lean_ctor_get(v_r_5531_, 4);
v___x_5705_ = lean_unsigned_to_nat(2u);
v___x_5706_ = lean_nat_mul(v___x_5705_, v_size_5699_);
v___x_5707_ = lean_nat_dec_lt(v_size_5700_, v___x_5706_);
lean_dec(v___x_5706_);
if (v___x_5707_ == 0)
{
lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5745_; 
lean_inc(v_r_5704_);
lean_inc(v_l_5703_);
lean_inc(v_v_5702_);
lean_inc(v_k_5701_);
lean_del_object(v___x_5697_);
v_isSharedCheck_5745_ = !lean_is_exclusive(v_r_5531_);
if (v_isSharedCheck_5745_ == 0)
{
lean_object* v_unused_5746_; lean_object* v_unused_5747_; lean_object* v_unused_5748_; lean_object* v_unused_5749_; lean_object* v_unused_5750_; 
v_unused_5746_ = lean_ctor_get(v_r_5531_, 4);
lean_dec(v_unused_5746_);
v_unused_5747_ = lean_ctor_get(v_r_5531_, 3);
lean_dec(v_unused_5747_);
v_unused_5748_ = lean_ctor_get(v_r_5531_, 2);
lean_dec(v_unused_5748_);
v_unused_5749_ = lean_ctor_get(v_r_5531_, 1);
lean_dec(v_unused_5749_);
v_unused_5750_ = lean_ctor_get(v_r_5531_, 0);
lean_dec(v_unused_5750_);
v___x_5709_ = v_r_5531_;
v_isShared_5710_ = v_isSharedCheck_5745_;
goto v_resetjp_5708_;
}
else
{
lean_dec(v_r_5531_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5745_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___y_5714_; lean_object* v___y_5715_; lean_object* v___y_5716_; lean_object* v___x_5733_; lean_object* v___y_5735_; 
v___x_5711_ = lean_nat_add(v___x_5537_, v_size_5527_);
lean_dec(v_size_5527_);
v___x_5712_ = lean_nat_add(v___x_5711_, v_size_5687_);
lean_dec(v___x_5711_);
v___x_5733_ = lean_nat_add(v___x_5537_, v_size_5699_);
if (lean_obj_tag(v_l_5703_) == 0)
{
lean_object* v_size_5743_; 
v_size_5743_ = lean_ctor_get(v_l_5703_, 0);
lean_inc(v_size_5743_);
v___y_5735_ = v_size_5743_;
goto v___jp_5734_;
}
else
{
lean_object* v___x_5744_; 
v___x_5744_ = lean_unsigned_to_nat(0u);
v___y_5735_ = v___x_5744_;
goto v___jp_5734_;
}
v___jp_5713_:
{
lean_object* v___x_5717_; lean_object* v___x_5719_; 
v___x_5717_ = lean_nat_add(v___y_5714_, v___y_5716_);
lean_dec(v___y_5716_);
lean_dec(v___y_5714_);
lean_inc_ref(v_tree_5684_);
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 4, v_tree_5684_);
lean_ctor_set(v___x_5709_, 3, v_r_5704_);
lean_ctor_set(v___x_5709_, 2, v_v_5686_);
lean_ctor_set(v___x_5709_, 1, v_k_5685_);
lean_ctor_set(v___x_5709_, 0, v___x_5717_);
v___x_5719_ = v___x_5709_;
goto v_reusejp_5718_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v___x_5717_);
lean_ctor_set(v_reuseFailAlloc_5732_, 1, v_k_5685_);
lean_ctor_set(v_reuseFailAlloc_5732_, 2, v_v_5686_);
lean_ctor_set(v_reuseFailAlloc_5732_, 3, v_r_5704_);
lean_ctor_set(v_reuseFailAlloc_5732_, 4, v_tree_5684_);
v___x_5719_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5718_;
}
v_reusejp_5718_:
{
lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5726_; 
v_isSharedCheck_5726_ = !lean_is_exclusive(v_tree_5684_);
if (v_isSharedCheck_5726_ == 0)
{
lean_object* v_unused_5727_; lean_object* v_unused_5728_; lean_object* v_unused_5729_; lean_object* v_unused_5730_; lean_object* v_unused_5731_; 
v_unused_5727_ = lean_ctor_get(v_tree_5684_, 4);
lean_dec(v_unused_5727_);
v_unused_5728_ = lean_ctor_get(v_tree_5684_, 3);
lean_dec(v_unused_5728_);
v_unused_5729_ = lean_ctor_get(v_tree_5684_, 2);
lean_dec(v_unused_5729_);
v_unused_5730_ = lean_ctor_get(v_tree_5684_, 1);
lean_dec(v_unused_5730_);
v_unused_5731_ = lean_ctor_get(v_tree_5684_, 0);
lean_dec(v_unused_5731_);
v___x_5721_ = v_tree_5684_;
v_isShared_5722_ = v_isSharedCheck_5726_;
goto v_resetjp_5720_;
}
else
{
lean_dec(v_tree_5684_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5726_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
lean_object* v___x_5724_; 
if (v_isShared_5722_ == 0)
{
lean_ctor_set(v___x_5721_, 4, v___x_5719_);
lean_ctor_set(v___x_5721_, 3, v___y_5715_);
lean_ctor_set(v___x_5721_, 2, v_v_5702_);
lean_ctor_set(v___x_5721_, 1, v_k_5701_);
lean_ctor_set(v___x_5721_, 0, v___x_5712_);
v___x_5724_ = v___x_5721_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v___x_5712_);
lean_ctor_set(v_reuseFailAlloc_5725_, 1, v_k_5701_);
lean_ctor_set(v_reuseFailAlloc_5725_, 2, v_v_5702_);
lean_ctor_set(v_reuseFailAlloc_5725_, 3, v___y_5715_);
lean_ctor_set(v_reuseFailAlloc_5725_, 4, v___x_5719_);
v___x_5724_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
return v___x_5724_;
}
}
}
}
v___jp_5734_:
{
lean_object* v___x_5736_; lean_object* v___x_5738_; 
v___x_5736_ = lean_nat_add(v___x_5733_, v___y_5735_);
lean_dec(v___y_5735_);
lean_dec(v___x_5733_);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 4, v_l_5703_);
lean_ctor_set(v___x_5681_, 3, v_l_5530_);
lean_ctor_set(v___x_5681_, 2, v_v_5529_);
lean_ctor_set(v___x_5681_, 1, v_k_5528_);
lean_ctor_set(v___x_5681_, 0, v___x_5736_);
v___x_5738_ = v___x_5681_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v___x_5736_);
lean_ctor_set(v_reuseFailAlloc_5742_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5742_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5742_, 3, v_l_5530_);
lean_ctor_set(v_reuseFailAlloc_5742_, 4, v_l_5703_);
v___x_5738_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
lean_object* v___x_5739_; 
v___x_5739_ = lean_nat_add(v___x_5537_, v_size_5687_);
if (lean_obj_tag(v_r_5704_) == 0)
{
lean_object* v_size_5740_; 
v_size_5740_ = lean_ctor_get(v_r_5704_, 0);
lean_inc(v_size_5740_);
v___y_5714_ = v___x_5739_;
v___y_5715_ = v___x_5738_;
v___y_5716_ = v_size_5740_;
goto v___jp_5713_;
}
else
{
lean_object* v___x_5741_; 
v___x_5741_ = lean_unsigned_to_nat(0u);
v___y_5714_ = v___x_5739_;
v___y_5715_ = v___x_5738_;
v___y_5716_ = v___x_5741_;
goto v___jp_5713_;
}
}
}
}
}
else
{
lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5756_; 
v___x_5751_ = lean_nat_add(v___x_5537_, v_size_5527_);
lean_dec(v_size_5527_);
v___x_5752_ = lean_nat_add(v___x_5751_, v_size_5687_);
lean_dec(v___x_5751_);
v___x_5753_ = lean_nat_add(v___x_5537_, v_size_5687_);
v___x_5754_ = lean_nat_add(v___x_5753_, v_size_5700_);
lean_dec(v___x_5753_);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 4, v_tree_5684_);
lean_ctor_set(v___x_5681_, 3, v_r_5531_);
lean_ctor_set(v___x_5681_, 2, v_v_5686_);
lean_ctor_set(v___x_5681_, 1, v_k_5685_);
lean_ctor_set(v___x_5681_, 0, v___x_5754_);
v___x_5756_ = v___x_5681_;
goto v_reusejp_5755_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v___x_5754_);
lean_ctor_set(v_reuseFailAlloc_5760_, 1, v_k_5685_);
lean_ctor_set(v_reuseFailAlloc_5760_, 2, v_v_5686_);
lean_ctor_set(v_reuseFailAlloc_5760_, 3, v_r_5531_);
lean_ctor_set(v_reuseFailAlloc_5760_, 4, v_tree_5684_);
v___x_5756_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5755_;
}
v_reusejp_5755_:
{
lean_object* v___x_5758_; 
if (v_isShared_5698_ == 0)
{
lean_ctor_set(v___x_5697_, 4, v___x_5756_);
lean_ctor_set(v___x_5697_, 0, v___x_5752_);
v___x_5758_ = v___x_5697_;
goto v_reusejp_5757_;
}
else
{
lean_object* v_reuseFailAlloc_5759_; 
v_reuseFailAlloc_5759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5759_, 0, v___x_5752_);
lean_ctor_set(v_reuseFailAlloc_5759_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5759_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5759_, 3, v_l_5530_);
lean_ctor_set(v_reuseFailAlloc_5759_, 4, v___x_5756_);
v___x_5758_ = v_reuseFailAlloc_5759_;
goto v_reusejp_5757_;
}
v_reusejp_5757_:
{
return v___x_5758_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_5530_) == 0)
{
lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5790_; 
lean_inc_ref(v_l_5530_);
lean_inc(v_v_5529_);
lean_inc(v_k_5528_);
lean_inc(v_size_5527_);
v_isSharedCheck_5790_ = !lean_is_exclusive(v_l_5347_);
if (v_isSharedCheck_5790_ == 0)
{
lean_object* v_unused_5791_; lean_object* v_unused_5792_; lean_object* v_unused_5793_; lean_object* v_unused_5794_; lean_object* v_unused_5795_; 
v_unused_5791_ = lean_ctor_get(v_l_5347_, 4);
lean_dec(v_unused_5791_);
v_unused_5792_ = lean_ctor_get(v_l_5347_, 3);
lean_dec(v_unused_5792_);
v_unused_5793_ = lean_ctor_get(v_l_5347_, 2);
lean_dec(v_unused_5793_);
v_unused_5794_ = lean_ctor_get(v_l_5347_, 1);
lean_dec(v_unused_5794_);
v_unused_5795_ = lean_ctor_get(v_l_5347_, 0);
lean_dec(v_unused_5795_);
v___x_5768_ = v_l_5347_;
v_isShared_5769_ = v_isSharedCheck_5790_;
goto v_resetjp_5767_;
}
else
{
lean_dec(v_l_5347_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5790_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
if (lean_obj_tag(v_r_5531_) == 0)
{
lean_object* v_k_5770_; lean_object* v_v_5771_; lean_object* v_size_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5776_; 
v_k_5770_ = lean_ctor_get(v___x_5683_, 0);
lean_inc(v_k_5770_);
v_v_5771_ = lean_ctor_get(v___x_5683_, 1);
lean_inc(v_v_5771_);
lean_dec_ref(v___x_5683_);
v_size_5772_ = lean_ctor_get(v_r_5531_, 0);
v___x_5773_ = lean_nat_add(v___x_5537_, v_size_5527_);
lean_dec(v_size_5527_);
v___x_5774_ = lean_nat_add(v___x_5537_, v_size_5772_);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 4, v_tree_5684_);
lean_ctor_set(v___x_5681_, 3, v_r_5531_);
lean_ctor_set(v___x_5681_, 2, v_v_5771_);
lean_ctor_set(v___x_5681_, 1, v_k_5770_);
lean_ctor_set(v___x_5681_, 0, v___x_5774_);
v___x_5776_ = v___x_5681_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v___x_5774_);
lean_ctor_set(v_reuseFailAlloc_5780_, 1, v_k_5770_);
lean_ctor_set(v_reuseFailAlloc_5780_, 2, v_v_5771_);
lean_ctor_set(v_reuseFailAlloc_5780_, 3, v_r_5531_);
lean_ctor_set(v_reuseFailAlloc_5780_, 4, v_tree_5684_);
v___x_5776_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
lean_object* v___x_5778_; 
if (v_isShared_5769_ == 0)
{
lean_ctor_set(v___x_5768_, 4, v___x_5776_);
lean_ctor_set(v___x_5768_, 0, v___x_5773_);
v___x_5778_ = v___x_5768_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5779_; 
v_reuseFailAlloc_5779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5779_, 0, v___x_5773_);
lean_ctor_set(v_reuseFailAlloc_5779_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5779_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5779_, 3, v_l_5530_);
lean_ctor_set(v_reuseFailAlloc_5779_, 4, v___x_5776_);
v___x_5778_ = v_reuseFailAlloc_5779_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
return v___x_5778_;
}
}
}
else
{
lean_object* v_k_5781_; lean_object* v_v_5782_; lean_object* v___x_5783_; lean_object* v___x_5785_; 
lean_dec(v_size_5527_);
v_k_5781_ = lean_ctor_get(v___x_5683_, 0);
lean_inc(v_k_5781_);
v_v_5782_ = lean_ctor_get(v___x_5683_, 1);
lean_inc(v_v_5782_);
lean_dec_ref(v___x_5683_);
v___x_5783_ = lean_unsigned_to_nat(3u);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 4, v_r_5531_);
lean_ctor_set(v___x_5681_, 3, v_r_5531_);
lean_ctor_set(v___x_5681_, 2, v_v_5782_);
lean_ctor_set(v___x_5681_, 1, v_k_5781_);
lean_ctor_set(v___x_5681_, 0, v___x_5537_);
v___x_5785_ = v___x_5681_;
goto v_reusejp_5784_;
}
else
{
lean_object* v_reuseFailAlloc_5789_; 
v_reuseFailAlloc_5789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5789_, 0, v___x_5537_);
lean_ctor_set(v_reuseFailAlloc_5789_, 1, v_k_5781_);
lean_ctor_set(v_reuseFailAlloc_5789_, 2, v_v_5782_);
lean_ctor_set(v_reuseFailAlloc_5789_, 3, v_r_5531_);
lean_ctor_set(v_reuseFailAlloc_5789_, 4, v_r_5531_);
v___x_5785_ = v_reuseFailAlloc_5789_;
goto v_reusejp_5784_;
}
v_reusejp_5784_:
{
lean_object* v___x_5787_; 
if (v_isShared_5769_ == 0)
{
lean_ctor_set(v___x_5768_, 4, v___x_5785_);
lean_ctor_set(v___x_5768_, 0, v___x_5783_);
v___x_5787_ = v___x_5768_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v___x_5783_);
lean_ctor_set(v_reuseFailAlloc_5788_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5788_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5788_, 3, v_l_5530_);
lean_ctor_set(v_reuseFailAlloc_5788_, 4, v___x_5785_);
v___x_5787_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
return v___x_5787_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5531_) == 0)
{
lean_object* v___x_5797_; uint8_t v_isShared_5798_; uint8_t v_isSharedCheck_5820_; 
lean_inc(v_l_5530_);
lean_inc(v_v_5529_);
lean_inc(v_k_5528_);
v_isSharedCheck_5820_ = !lean_is_exclusive(v_l_5347_);
if (v_isSharedCheck_5820_ == 0)
{
lean_object* v_unused_5821_; lean_object* v_unused_5822_; lean_object* v_unused_5823_; lean_object* v_unused_5824_; lean_object* v_unused_5825_; 
v_unused_5821_ = lean_ctor_get(v_l_5347_, 4);
lean_dec(v_unused_5821_);
v_unused_5822_ = lean_ctor_get(v_l_5347_, 3);
lean_dec(v_unused_5822_);
v_unused_5823_ = lean_ctor_get(v_l_5347_, 2);
lean_dec(v_unused_5823_);
v_unused_5824_ = lean_ctor_get(v_l_5347_, 1);
lean_dec(v_unused_5824_);
v_unused_5825_ = lean_ctor_get(v_l_5347_, 0);
lean_dec(v_unused_5825_);
v___x_5797_ = v_l_5347_;
v_isShared_5798_ = v_isSharedCheck_5820_;
goto v_resetjp_5796_;
}
else
{
lean_dec(v_l_5347_);
v___x_5797_ = lean_box(0);
v_isShared_5798_ = v_isSharedCheck_5820_;
goto v_resetjp_5796_;
}
v_resetjp_5796_:
{
lean_object* v_k_5799_; lean_object* v_v_5800_; lean_object* v_k_5801_; lean_object* v_v_5802_; lean_object* v___x_5804_; uint8_t v_isShared_5805_; uint8_t v_isSharedCheck_5816_; 
v_k_5799_ = lean_ctor_get(v___x_5683_, 0);
lean_inc(v_k_5799_);
v_v_5800_ = lean_ctor_get(v___x_5683_, 1);
lean_inc(v_v_5800_);
lean_dec_ref(v___x_5683_);
v_k_5801_ = lean_ctor_get(v_r_5531_, 1);
v_v_5802_ = lean_ctor_get(v_r_5531_, 2);
v_isSharedCheck_5816_ = !lean_is_exclusive(v_r_5531_);
if (v_isSharedCheck_5816_ == 0)
{
lean_object* v_unused_5817_; lean_object* v_unused_5818_; lean_object* v_unused_5819_; 
v_unused_5817_ = lean_ctor_get(v_r_5531_, 4);
lean_dec(v_unused_5817_);
v_unused_5818_ = lean_ctor_get(v_r_5531_, 3);
lean_dec(v_unused_5818_);
v_unused_5819_ = lean_ctor_get(v_r_5531_, 0);
lean_dec(v_unused_5819_);
v___x_5804_ = v_r_5531_;
v_isShared_5805_ = v_isSharedCheck_5816_;
goto v_resetjp_5803_;
}
else
{
lean_inc(v_v_5802_);
lean_inc(v_k_5801_);
lean_dec(v_r_5531_);
v___x_5804_ = lean_box(0);
v_isShared_5805_ = v_isSharedCheck_5816_;
goto v_resetjp_5803_;
}
v_resetjp_5803_:
{
lean_object* v___x_5806_; lean_object* v___x_5808_; 
v___x_5806_ = lean_unsigned_to_nat(3u);
if (v_isShared_5805_ == 0)
{
lean_ctor_set(v___x_5804_, 4, v_l_5530_);
lean_ctor_set(v___x_5804_, 3, v_l_5530_);
lean_ctor_set(v___x_5804_, 2, v_v_5529_);
lean_ctor_set(v___x_5804_, 1, v_k_5528_);
lean_ctor_set(v___x_5804_, 0, v___x_5537_);
v___x_5808_ = v___x_5804_;
goto v_reusejp_5807_;
}
else
{
lean_object* v_reuseFailAlloc_5815_; 
v_reuseFailAlloc_5815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5815_, 0, v___x_5537_);
lean_ctor_set(v_reuseFailAlloc_5815_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5815_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5815_, 3, v_l_5530_);
lean_ctor_set(v_reuseFailAlloc_5815_, 4, v_l_5530_);
v___x_5808_ = v_reuseFailAlloc_5815_;
goto v_reusejp_5807_;
}
v_reusejp_5807_:
{
lean_object* v___x_5810_; 
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 4, v_l_5530_);
lean_ctor_set(v___x_5681_, 3, v_l_5530_);
lean_ctor_set(v___x_5681_, 2, v_v_5800_);
lean_ctor_set(v___x_5681_, 1, v_k_5799_);
lean_ctor_set(v___x_5681_, 0, v___x_5537_);
v___x_5810_ = v___x_5681_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v___x_5537_);
lean_ctor_set(v_reuseFailAlloc_5814_, 1, v_k_5799_);
lean_ctor_set(v_reuseFailAlloc_5814_, 2, v_v_5800_);
lean_ctor_set(v_reuseFailAlloc_5814_, 3, v_l_5530_);
lean_ctor_set(v_reuseFailAlloc_5814_, 4, v_l_5530_);
v___x_5810_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
lean_object* v___x_5812_; 
if (v_isShared_5798_ == 0)
{
lean_ctor_set(v___x_5797_, 4, v___x_5810_);
lean_ctor_set(v___x_5797_, 3, v___x_5808_);
lean_ctor_set(v___x_5797_, 2, v_v_5802_);
lean_ctor_set(v___x_5797_, 1, v_k_5801_);
lean_ctor_set(v___x_5797_, 0, v___x_5806_);
v___x_5812_ = v___x_5797_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5806_);
lean_ctor_set(v_reuseFailAlloc_5813_, 1, v_k_5801_);
lean_ctor_set(v_reuseFailAlloc_5813_, 2, v_v_5802_);
lean_ctor_set(v_reuseFailAlloc_5813_, 3, v___x_5808_);
lean_ctor_set(v_reuseFailAlloc_5813_, 4, v___x_5810_);
v___x_5812_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
return v___x_5812_;
}
}
}
}
}
}
else
{
lean_object* v_k_5826_; lean_object* v_v_5827_; lean_object* v___x_5828_; lean_object* v___x_5830_; 
v_k_5826_ = lean_ctor_get(v___x_5683_, 0);
lean_inc(v_k_5826_);
v_v_5827_ = lean_ctor_get(v___x_5683_, 1);
lean_inc(v_v_5827_);
lean_dec_ref(v___x_5683_);
v___x_5828_ = lean_unsigned_to_nat(2u);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 4, v_r_5531_);
lean_ctor_set(v___x_5681_, 3, v_l_5347_);
lean_ctor_set(v___x_5681_, 2, v_v_5827_);
lean_ctor_set(v___x_5681_, 1, v_k_5826_);
lean_ctor_set(v___x_5681_, 0, v___x_5828_);
v___x_5830_ = v___x_5681_;
goto v_reusejp_5829_;
}
else
{
lean_object* v_reuseFailAlloc_5831_; 
v_reuseFailAlloc_5831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5831_, 0, v___x_5828_);
lean_ctor_set(v_reuseFailAlloc_5831_, 1, v_k_5826_);
lean_ctor_set(v_reuseFailAlloc_5831_, 2, v_v_5827_);
lean_ctor_set(v_reuseFailAlloc_5831_, 3, v_l_5347_);
lean_ctor_set(v_reuseFailAlloc_5831_, 4, v_r_5531_);
v___x_5830_ = v_reuseFailAlloc_5831_;
goto v_reusejp_5829_;
}
v_reusejp_5829_:
{
return v___x_5830_;
}
}
}
}
}
}
}
else
{
return v_l_5347_;
}
}
else
{
return v_r_5348_;
}
}
default: 
{
lean_object* v_impl_5838_; lean_object* v___x_5839_; 
v_impl_5838_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5343_, v_r_5348_);
v___x_5839_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5838_) == 0)
{
if (lean_obj_tag(v_l_5347_) == 0)
{
lean_object* v_size_5840_; lean_object* v_size_5841_; lean_object* v_k_5842_; lean_object* v_v_5843_; lean_object* v_l_5844_; lean_object* v_r_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; uint8_t v___x_5848_; 
v_size_5840_ = lean_ctor_get(v_impl_5838_, 0);
lean_inc(v_size_5840_);
v_size_5841_ = lean_ctor_get(v_l_5347_, 0);
v_k_5842_ = lean_ctor_get(v_l_5347_, 1);
v_v_5843_ = lean_ctor_get(v_l_5347_, 2);
v_l_5844_ = lean_ctor_get(v_l_5347_, 3);
v_r_5845_ = lean_ctor_get(v_l_5347_, 4);
lean_inc(v_r_5845_);
v___x_5846_ = lean_unsigned_to_nat(3u);
v___x_5847_ = lean_nat_mul(v___x_5846_, v_size_5840_);
v___x_5848_ = lean_nat_dec_lt(v___x_5847_, v_size_5841_);
lean_dec(v___x_5847_);
if (v___x_5848_ == 0)
{
lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5852_; 
lean_dec(v_r_5845_);
v___x_5849_ = lean_nat_add(v___x_5839_, v_size_5841_);
v___x_5850_ = lean_nat_add(v___x_5849_, v_size_5840_);
lean_dec(v_size_5840_);
lean_dec(v___x_5849_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v_impl_5838_);
lean_ctor_set(v___x_5350_, 0, v___x_5850_);
v___x_5852_ = v___x_5350_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5853_; 
v_reuseFailAlloc_5853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5853_, 0, v___x_5850_);
lean_ctor_set(v_reuseFailAlloc_5853_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5853_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5853_, 3, v_l_5347_);
lean_ctor_set(v_reuseFailAlloc_5853_, 4, v_impl_5838_);
v___x_5852_ = v_reuseFailAlloc_5853_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
return v___x_5852_;
}
}
else
{
lean_object* v___x_5855_; uint8_t v_isShared_5856_; uint8_t v_isSharedCheck_5919_; 
lean_inc(v_l_5844_);
lean_inc(v_v_5843_);
lean_inc(v_k_5842_);
lean_inc(v_size_5841_);
v_isSharedCheck_5919_ = !lean_is_exclusive(v_l_5347_);
if (v_isSharedCheck_5919_ == 0)
{
lean_object* v_unused_5920_; lean_object* v_unused_5921_; lean_object* v_unused_5922_; lean_object* v_unused_5923_; lean_object* v_unused_5924_; 
v_unused_5920_ = lean_ctor_get(v_l_5347_, 4);
lean_dec(v_unused_5920_);
v_unused_5921_ = lean_ctor_get(v_l_5347_, 3);
lean_dec(v_unused_5921_);
v_unused_5922_ = lean_ctor_get(v_l_5347_, 2);
lean_dec(v_unused_5922_);
v_unused_5923_ = lean_ctor_get(v_l_5347_, 1);
lean_dec(v_unused_5923_);
v_unused_5924_ = lean_ctor_get(v_l_5347_, 0);
lean_dec(v_unused_5924_);
v___x_5855_ = v_l_5347_;
v_isShared_5856_ = v_isSharedCheck_5919_;
goto v_resetjp_5854_;
}
else
{
lean_dec(v_l_5347_);
v___x_5855_ = lean_box(0);
v_isShared_5856_ = v_isSharedCheck_5919_;
goto v_resetjp_5854_;
}
v_resetjp_5854_:
{
lean_object* v_size_5857_; lean_object* v_size_5858_; lean_object* v_k_5859_; lean_object* v_v_5860_; lean_object* v_l_5861_; lean_object* v_r_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; uint8_t v___x_5865_; 
v_size_5857_ = lean_ctor_get(v_l_5844_, 0);
v_size_5858_ = lean_ctor_get(v_r_5845_, 0);
v_k_5859_ = lean_ctor_get(v_r_5845_, 1);
v_v_5860_ = lean_ctor_get(v_r_5845_, 2);
v_l_5861_ = lean_ctor_get(v_r_5845_, 3);
v_r_5862_ = lean_ctor_get(v_r_5845_, 4);
v___x_5863_ = lean_unsigned_to_nat(2u);
v___x_5864_ = lean_nat_mul(v___x_5863_, v_size_5857_);
v___x_5865_ = lean_nat_dec_lt(v_size_5858_, v___x_5864_);
lean_dec(v___x_5864_);
if (v___x_5865_ == 0)
{
lean_object* v___x_5867_; uint8_t v_isShared_5868_; uint8_t v_isSharedCheck_5894_; 
lean_inc(v_r_5862_);
lean_inc(v_l_5861_);
lean_inc(v_v_5860_);
lean_inc(v_k_5859_);
v_isSharedCheck_5894_ = !lean_is_exclusive(v_r_5845_);
if (v_isSharedCheck_5894_ == 0)
{
lean_object* v_unused_5895_; lean_object* v_unused_5896_; lean_object* v_unused_5897_; lean_object* v_unused_5898_; lean_object* v_unused_5899_; 
v_unused_5895_ = lean_ctor_get(v_r_5845_, 4);
lean_dec(v_unused_5895_);
v_unused_5896_ = lean_ctor_get(v_r_5845_, 3);
lean_dec(v_unused_5896_);
v_unused_5897_ = lean_ctor_get(v_r_5845_, 2);
lean_dec(v_unused_5897_);
v_unused_5898_ = lean_ctor_get(v_r_5845_, 1);
lean_dec(v_unused_5898_);
v_unused_5899_ = lean_ctor_get(v_r_5845_, 0);
lean_dec(v_unused_5899_);
v___x_5867_ = v_r_5845_;
v_isShared_5868_ = v_isSharedCheck_5894_;
goto v_resetjp_5866_;
}
else
{
lean_dec(v_r_5845_);
v___x_5867_ = lean_box(0);
v_isShared_5868_ = v_isSharedCheck_5894_;
goto v_resetjp_5866_;
}
v_resetjp_5866_:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___y_5872_; lean_object* v___y_5873_; lean_object* v___y_5874_; lean_object* v___x_5882_; lean_object* v___y_5884_; 
v___x_5869_ = lean_nat_add(v___x_5839_, v_size_5841_);
lean_dec(v_size_5841_);
v___x_5870_ = lean_nat_add(v___x_5869_, v_size_5840_);
lean_dec(v___x_5869_);
v___x_5882_ = lean_nat_add(v___x_5839_, v_size_5857_);
if (lean_obj_tag(v_l_5861_) == 0)
{
lean_object* v_size_5892_; 
v_size_5892_ = lean_ctor_get(v_l_5861_, 0);
lean_inc(v_size_5892_);
v___y_5884_ = v_size_5892_;
goto v___jp_5883_;
}
else
{
lean_object* v___x_5893_; 
v___x_5893_ = lean_unsigned_to_nat(0u);
v___y_5884_ = v___x_5893_;
goto v___jp_5883_;
}
v___jp_5871_:
{
lean_object* v___x_5875_; lean_object* v___x_5877_; 
v___x_5875_ = lean_nat_add(v___y_5872_, v___y_5874_);
lean_dec(v___y_5874_);
lean_dec(v___y_5872_);
if (v_isShared_5868_ == 0)
{
lean_ctor_set(v___x_5867_, 4, v_impl_5838_);
lean_ctor_set(v___x_5867_, 3, v_r_5862_);
lean_ctor_set(v___x_5867_, 2, v_v_5346_);
lean_ctor_set(v___x_5867_, 1, v_k_5345_);
lean_ctor_set(v___x_5867_, 0, v___x_5875_);
v___x_5877_ = v___x_5867_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5881_; 
v_reuseFailAlloc_5881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5881_, 0, v___x_5875_);
lean_ctor_set(v_reuseFailAlloc_5881_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5881_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5881_, 3, v_r_5862_);
lean_ctor_set(v_reuseFailAlloc_5881_, 4, v_impl_5838_);
v___x_5877_ = v_reuseFailAlloc_5881_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
lean_object* v___x_5879_; 
if (v_isShared_5856_ == 0)
{
lean_ctor_set(v___x_5855_, 4, v___x_5877_);
lean_ctor_set(v___x_5855_, 3, v___y_5873_);
lean_ctor_set(v___x_5855_, 2, v_v_5860_);
lean_ctor_set(v___x_5855_, 1, v_k_5859_);
lean_ctor_set(v___x_5855_, 0, v___x_5870_);
v___x_5879_ = v___x_5855_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v___x_5870_);
lean_ctor_set(v_reuseFailAlloc_5880_, 1, v_k_5859_);
lean_ctor_set(v_reuseFailAlloc_5880_, 2, v_v_5860_);
lean_ctor_set(v_reuseFailAlloc_5880_, 3, v___y_5873_);
lean_ctor_set(v_reuseFailAlloc_5880_, 4, v___x_5877_);
v___x_5879_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
return v___x_5879_;
}
}
}
v___jp_5883_:
{
lean_object* v___x_5885_; lean_object* v___x_5887_; 
v___x_5885_ = lean_nat_add(v___x_5882_, v___y_5884_);
lean_dec(v___y_5884_);
lean_dec(v___x_5882_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v_l_5861_);
lean_ctor_set(v___x_5350_, 3, v_l_5844_);
lean_ctor_set(v___x_5350_, 2, v_v_5843_);
lean_ctor_set(v___x_5350_, 1, v_k_5842_);
lean_ctor_set(v___x_5350_, 0, v___x_5885_);
v___x_5887_ = v___x_5350_;
goto v_reusejp_5886_;
}
else
{
lean_object* v_reuseFailAlloc_5891_; 
v_reuseFailAlloc_5891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5891_, 0, v___x_5885_);
lean_ctor_set(v_reuseFailAlloc_5891_, 1, v_k_5842_);
lean_ctor_set(v_reuseFailAlloc_5891_, 2, v_v_5843_);
lean_ctor_set(v_reuseFailAlloc_5891_, 3, v_l_5844_);
lean_ctor_set(v_reuseFailAlloc_5891_, 4, v_l_5861_);
v___x_5887_ = v_reuseFailAlloc_5891_;
goto v_reusejp_5886_;
}
v_reusejp_5886_:
{
lean_object* v___x_5888_; 
v___x_5888_ = lean_nat_add(v___x_5839_, v_size_5840_);
lean_dec(v_size_5840_);
if (lean_obj_tag(v_r_5862_) == 0)
{
lean_object* v_size_5889_; 
v_size_5889_ = lean_ctor_get(v_r_5862_, 0);
lean_inc(v_size_5889_);
v___y_5872_ = v___x_5888_;
v___y_5873_ = v___x_5887_;
v___y_5874_ = v_size_5889_;
goto v___jp_5871_;
}
else
{
lean_object* v___x_5890_; 
v___x_5890_ = lean_unsigned_to_nat(0u);
v___y_5872_ = v___x_5888_;
v___y_5873_ = v___x_5887_;
v___y_5874_ = v___x_5890_;
goto v___jp_5871_;
}
}
}
}
}
else
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5905_; 
lean_del_object(v___x_5350_);
v___x_5900_ = lean_nat_add(v___x_5839_, v_size_5841_);
lean_dec(v_size_5841_);
v___x_5901_ = lean_nat_add(v___x_5900_, v_size_5840_);
lean_dec(v___x_5900_);
v___x_5902_ = lean_nat_add(v___x_5839_, v_size_5840_);
lean_dec(v_size_5840_);
v___x_5903_ = lean_nat_add(v___x_5902_, v_size_5858_);
lean_dec(v___x_5902_);
lean_inc_ref(v_impl_5838_);
if (v_isShared_5856_ == 0)
{
lean_ctor_set(v___x_5855_, 4, v_impl_5838_);
lean_ctor_set(v___x_5855_, 3, v_r_5845_);
lean_ctor_set(v___x_5855_, 2, v_v_5346_);
lean_ctor_set(v___x_5855_, 1, v_k_5345_);
lean_ctor_set(v___x_5855_, 0, v___x_5903_);
v___x_5905_ = v___x_5855_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5918_; 
v_reuseFailAlloc_5918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5918_, 0, v___x_5903_);
lean_ctor_set(v_reuseFailAlloc_5918_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5918_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5918_, 3, v_r_5845_);
lean_ctor_set(v_reuseFailAlloc_5918_, 4, v_impl_5838_);
v___x_5905_ = v_reuseFailAlloc_5918_;
goto v_reusejp_5904_;
}
v_reusejp_5904_:
{
lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5912_; 
v_isSharedCheck_5912_ = !lean_is_exclusive(v_impl_5838_);
if (v_isSharedCheck_5912_ == 0)
{
lean_object* v_unused_5913_; lean_object* v_unused_5914_; lean_object* v_unused_5915_; lean_object* v_unused_5916_; lean_object* v_unused_5917_; 
v_unused_5913_ = lean_ctor_get(v_impl_5838_, 4);
lean_dec(v_unused_5913_);
v_unused_5914_ = lean_ctor_get(v_impl_5838_, 3);
lean_dec(v_unused_5914_);
v_unused_5915_ = lean_ctor_get(v_impl_5838_, 2);
lean_dec(v_unused_5915_);
v_unused_5916_ = lean_ctor_get(v_impl_5838_, 1);
lean_dec(v_unused_5916_);
v_unused_5917_ = lean_ctor_get(v_impl_5838_, 0);
lean_dec(v_unused_5917_);
v___x_5907_ = v_impl_5838_;
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
else
{
lean_dec(v_impl_5838_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
if (v_isShared_5908_ == 0)
{
lean_ctor_set(v___x_5907_, 4, v___x_5905_);
lean_ctor_set(v___x_5907_, 3, v_l_5844_);
lean_ctor_set(v___x_5907_, 2, v_v_5843_);
lean_ctor_set(v___x_5907_, 1, v_k_5842_);
lean_ctor_set(v___x_5907_, 0, v___x_5901_);
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v___x_5901_);
lean_ctor_set(v_reuseFailAlloc_5911_, 1, v_k_5842_);
lean_ctor_set(v_reuseFailAlloc_5911_, 2, v_v_5843_);
lean_ctor_set(v_reuseFailAlloc_5911_, 3, v_l_5844_);
lean_ctor_set(v_reuseFailAlloc_5911_, 4, v___x_5905_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5925_; lean_object* v___x_5926_; lean_object* v___x_5928_; 
v_size_5925_ = lean_ctor_get(v_impl_5838_, 0);
lean_inc(v_size_5925_);
v___x_5926_ = lean_nat_add(v___x_5839_, v_size_5925_);
lean_dec(v_size_5925_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v_impl_5838_);
lean_ctor_set(v___x_5350_, 0, v___x_5926_);
v___x_5928_ = v___x_5350_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5929_; 
v_reuseFailAlloc_5929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5929_, 0, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_5929_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5929_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5929_, 3, v_l_5347_);
lean_ctor_set(v_reuseFailAlloc_5929_, 4, v_impl_5838_);
v___x_5928_ = v_reuseFailAlloc_5929_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
return v___x_5928_;
}
}
}
else
{
if (lean_obj_tag(v_l_5347_) == 0)
{
lean_object* v_l_5930_; 
v_l_5930_ = lean_ctor_get(v_l_5347_, 3);
if (lean_obj_tag(v_l_5930_) == 0)
{
lean_object* v_r_5931_; 
lean_inc_ref(v_l_5930_);
v_r_5931_ = lean_ctor_get(v_l_5347_, 4);
lean_inc(v_r_5931_);
if (lean_obj_tag(v_r_5931_) == 0)
{
lean_object* v_size_5932_; lean_object* v_k_5933_; lean_object* v_v_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5947_; 
v_size_5932_ = lean_ctor_get(v_l_5347_, 0);
v_k_5933_ = lean_ctor_get(v_l_5347_, 1);
v_v_5934_ = lean_ctor_get(v_l_5347_, 2);
v_isSharedCheck_5947_ = !lean_is_exclusive(v_l_5347_);
if (v_isSharedCheck_5947_ == 0)
{
lean_object* v_unused_5948_; lean_object* v_unused_5949_; 
v_unused_5948_ = lean_ctor_get(v_l_5347_, 4);
lean_dec(v_unused_5948_);
v_unused_5949_ = lean_ctor_get(v_l_5347_, 3);
lean_dec(v_unused_5949_);
v___x_5936_ = v_l_5347_;
v_isShared_5937_ = v_isSharedCheck_5947_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_v_5934_);
lean_inc(v_k_5933_);
lean_inc(v_size_5932_);
lean_dec(v_l_5347_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5947_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
lean_object* v_size_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5942_; 
v_size_5938_ = lean_ctor_get(v_r_5931_, 0);
v___x_5939_ = lean_nat_add(v___x_5839_, v_size_5932_);
lean_dec(v_size_5932_);
v___x_5940_ = lean_nat_add(v___x_5839_, v_size_5938_);
if (v_isShared_5937_ == 0)
{
lean_ctor_set(v___x_5936_, 4, v_impl_5838_);
lean_ctor_set(v___x_5936_, 3, v_r_5931_);
lean_ctor_set(v___x_5936_, 2, v_v_5346_);
lean_ctor_set(v___x_5936_, 1, v_k_5345_);
lean_ctor_set(v___x_5936_, 0, v___x_5940_);
v___x_5942_ = v___x_5936_;
goto v_reusejp_5941_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v___x_5940_);
lean_ctor_set(v_reuseFailAlloc_5946_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5946_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5946_, 3, v_r_5931_);
lean_ctor_set(v_reuseFailAlloc_5946_, 4, v_impl_5838_);
v___x_5942_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5941_;
}
v_reusejp_5941_:
{
lean_object* v___x_5944_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v___x_5942_);
lean_ctor_set(v___x_5350_, 3, v_l_5930_);
lean_ctor_set(v___x_5350_, 2, v_v_5934_);
lean_ctor_set(v___x_5350_, 1, v_k_5933_);
lean_ctor_set(v___x_5350_, 0, v___x_5939_);
v___x_5944_ = v___x_5350_;
goto v_reusejp_5943_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v___x_5939_);
lean_ctor_set(v_reuseFailAlloc_5945_, 1, v_k_5933_);
lean_ctor_set(v_reuseFailAlloc_5945_, 2, v_v_5934_);
lean_ctor_set(v_reuseFailAlloc_5945_, 3, v_l_5930_);
lean_ctor_set(v_reuseFailAlloc_5945_, 4, v___x_5942_);
v___x_5944_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5943_;
}
v_reusejp_5943_:
{
return v___x_5944_;
}
}
}
}
else
{
lean_object* v_k_5950_; lean_object* v_v_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_5962_; 
v_k_5950_ = lean_ctor_get(v_l_5347_, 1);
v_v_5951_ = lean_ctor_get(v_l_5347_, 2);
v_isSharedCheck_5962_ = !lean_is_exclusive(v_l_5347_);
if (v_isSharedCheck_5962_ == 0)
{
lean_object* v_unused_5963_; lean_object* v_unused_5964_; lean_object* v_unused_5965_; 
v_unused_5963_ = lean_ctor_get(v_l_5347_, 4);
lean_dec(v_unused_5963_);
v_unused_5964_ = lean_ctor_get(v_l_5347_, 3);
lean_dec(v_unused_5964_);
v_unused_5965_ = lean_ctor_get(v_l_5347_, 0);
lean_dec(v_unused_5965_);
v___x_5953_ = v_l_5347_;
v_isShared_5954_ = v_isSharedCheck_5962_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_v_5951_);
lean_inc(v_k_5950_);
lean_dec(v_l_5347_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_5962_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
lean_object* v___x_5955_; lean_object* v___x_5957_; 
v___x_5955_ = lean_unsigned_to_nat(3u);
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 3, v_r_5931_);
lean_ctor_set(v___x_5953_, 2, v_v_5346_);
lean_ctor_set(v___x_5953_, 1, v_k_5345_);
lean_ctor_set(v___x_5953_, 0, v___x_5839_);
v___x_5957_ = v___x_5953_;
goto v_reusejp_5956_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v___x_5839_);
lean_ctor_set(v_reuseFailAlloc_5961_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5961_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5961_, 3, v_r_5931_);
lean_ctor_set(v_reuseFailAlloc_5961_, 4, v_r_5931_);
v___x_5957_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5956_;
}
v_reusejp_5956_:
{
lean_object* v___x_5959_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v___x_5957_);
lean_ctor_set(v___x_5350_, 3, v_l_5930_);
lean_ctor_set(v___x_5350_, 2, v_v_5951_);
lean_ctor_set(v___x_5350_, 1, v_k_5950_);
lean_ctor_set(v___x_5350_, 0, v___x_5955_);
v___x_5959_ = v___x_5350_;
goto v_reusejp_5958_;
}
else
{
lean_object* v_reuseFailAlloc_5960_; 
v_reuseFailAlloc_5960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5960_, 0, v___x_5955_);
lean_ctor_set(v_reuseFailAlloc_5960_, 1, v_k_5950_);
lean_ctor_set(v_reuseFailAlloc_5960_, 2, v_v_5951_);
lean_ctor_set(v_reuseFailAlloc_5960_, 3, v_l_5930_);
lean_ctor_set(v_reuseFailAlloc_5960_, 4, v___x_5957_);
v___x_5959_ = v_reuseFailAlloc_5960_;
goto v_reusejp_5958_;
}
v_reusejp_5958_:
{
return v___x_5959_;
}
}
}
}
}
else
{
lean_object* v_r_5966_; 
v_r_5966_ = lean_ctor_get(v_l_5347_, 4);
lean_inc(v_r_5966_);
if (lean_obj_tag(v_r_5966_) == 0)
{
lean_object* v_k_5967_; lean_object* v_v_5968_; lean_object* v___x_5970_; uint8_t v_isShared_5971_; uint8_t v_isSharedCheck_5991_; 
lean_inc(v_l_5930_);
v_k_5967_ = lean_ctor_get(v_l_5347_, 1);
v_v_5968_ = lean_ctor_get(v_l_5347_, 2);
v_isSharedCheck_5991_ = !lean_is_exclusive(v_l_5347_);
if (v_isSharedCheck_5991_ == 0)
{
lean_object* v_unused_5992_; lean_object* v_unused_5993_; lean_object* v_unused_5994_; 
v_unused_5992_ = lean_ctor_get(v_l_5347_, 4);
lean_dec(v_unused_5992_);
v_unused_5993_ = lean_ctor_get(v_l_5347_, 3);
lean_dec(v_unused_5993_);
v_unused_5994_ = lean_ctor_get(v_l_5347_, 0);
lean_dec(v_unused_5994_);
v___x_5970_ = v_l_5347_;
v_isShared_5971_ = v_isSharedCheck_5991_;
goto v_resetjp_5969_;
}
else
{
lean_inc(v_v_5968_);
lean_inc(v_k_5967_);
lean_dec(v_l_5347_);
v___x_5970_ = lean_box(0);
v_isShared_5971_ = v_isSharedCheck_5991_;
goto v_resetjp_5969_;
}
v_resetjp_5969_:
{
lean_object* v_k_5972_; lean_object* v_v_5973_; lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_5987_; 
v_k_5972_ = lean_ctor_get(v_r_5966_, 1);
v_v_5973_ = lean_ctor_get(v_r_5966_, 2);
v_isSharedCheck_5987_ = !lean_is_exclusive(v_r_5966_);
if (v_isSharedCheck_5987_ == 0)
{
lean_object* v_unused_5988_; lean_object* v_unused_5989_; lean_object* v_unused_5990_; 
v_unused_5988_ = lean_ctor_get(v_r_5966_, 4);
lean_dec(v_unused_5988_);
v_unused_5989_ = lean_ctor_get(v_r_5966_, 3);
lean_dec(v_unused_5989_);
v_unused_5990_ = lean_ctor_get(v_r_5966_, 0);
lean_dec(v_unused_5990_);
v___x_5975_ = v_r_5966_;
v_isShared_5976_ = v_isSharedCheck_5987_;
goto v_resetjp_5974_;
}
else
{
lean_inc(v_v_5973_);
lean_inc(v_k_5972_);
lean_dec(v_r_5966_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_5987_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v___x_5977_; lean_object* v___x_5979_; 
v___x_5977_ = lean_unsigned_to_nat(3u);
if (v_isShared_5976_ == 0)
{
lean_ctor_set(v___x_5975_, 4, v_l_5930_);
lean_ctor_set(v___x_5975_, 3, v_l_5930_);
lean_ctor_set(v___x_5975_, 2, v_v_5968_);
lean_ctor_set(v___x_5975_, 1, v_k_5967_);
lean_ctor_set(v___x_5975_, 0, v___x_5839_);
v___x_5979_ = v___x_5975_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5986_; 
v_reuseFailAlloc_5986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5986_, 0, v___x_5839_);
lean_ctor_set(v_reuseFailAlloc_5986_, 1, v_k_5967_);
lean_ctor_set(v_reuseFailAlloc_5986_, 2, v_v_5968_);
lean_ctor_set(v_reuseFailAlloc_5986_, 3, v_l_5930_);
lean_ctor_set(v_reuseFailAlloc_5986_, 4, v_l_5930_);
v___x_5979_ = v_reuseFailAlloc_5986_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
lean_object* v___x_5981_; 
if (v_isShared_5971_ == 0)
{
lean_ctor_set(v___x_5970_, 4, v_l_5930_);
lean_ctor_set(v___x_5970_, 2, v_v_5346_);
lean_ctor_set(v___x_5970_, 1, v_k_5345_);
lean_ctor_set(v___x_5970_, 0, v___x_5839_);
v___x_5981_ = v___x_5970_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v___x_5839_);
lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5985_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5985_, 3, v_l_5930_);
lean_ctor_set(v_reuseFailAlloc_5985_, 4, v_l_5930_);
v___x_5981_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
lean_object* v___x_5983_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v___x_5981_);
lean_ctor_set(v___x_5350_, 3, v___x_5979_);
lean_ctor_set(v___x_5350_, 2, v_v_5973_);
lean_ctor_set(v___x_5350_, 1, v_k_5972_);
lean_ctor_set(v___x_5350_, 0, v___x_5977_);
v___x_5983_ = v___x_5350_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v___x_5977_);
lean_ctor_set(v_reuseFailAlloc_5984_, 1, v_k_5972_);
lean_ctor_set(v_reuseFailAlloc_5984_, 2, v_v_5973_);
lean_ctor_set(v_reuseFailAlloc_5984_, 3, v___x_5979_);
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
}
else
{
lean_object* v___x_5995_; lean_object* v___x_5997_; 
v___x_5995_ = lean_unsigned_to_nat(2u);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v_r_5966_);
lean_ctor_set(v___x_5350_, 0, v___x_5995_);
v___x_5997_ = v___x_5350_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_5998_; 
v_reuseFailAlloc_5998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5998_, 0, v___x_5995_);
lean_ctor_set(v_reuseFailAlloc_5998_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_5998_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5998_, 3, v_l_5347_);
lean_ctor_set(v_reuseFailAlloc_5998_, 4, v_r_5966_);
v___x_5997_ = v_reuseFailAlloc_5998_;
goto v_reusejp_5996_;
}
v_reusejp_5996_:
{
return v___x_5997_;
}
}
}
}
else
{
lean_object* v___x_6000_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 4, v_l_5347_);
lean_ctor_set(v___x_5350_, 0, v___x_5839_);
v___x_6000_ = v___x_5350_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v___x_5839_);
lean_ctor_set(v_reuseFailAlloc_6001_, 1, v_k_5345_);
lean_ctor_set(v_reuseFailAlloc_6001_, 2, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_6001_, 3, v_l_5347_);
lean_ctor_set(v_reuseFailAlloc_6001_, 4, v_l_5347_);
v___x_6000_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
return v___x_6000_;
}
}
}
}
}
}
}
else
{
return v_t_5344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_6004_, lean_object* v_t_6005_){
_start:
{
lean_object* v_res_6006_; 
v_res_6006_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6004_, v_t_6005_);
lean_dec(v_k_6004_);
return v_res_6006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_6007_, lean_object* v_x_6008_){
_start:
{
if (lean_obj_tag(v_x_6008_) == 0)
{
lean_object* v_k_6009_; lean_object* v_l_6010_; lean_object* v_r_6011_; lean_object* v___x_6012_; lean_object* v_ileans_6013_; lean_object* v_workers_6014_; lean_object* v___x_6016_; uint8_t v_isShared_6017_; uint8_t v_isSharedCheck_6023_; 
v_k_6009_ = lean_ctor_get(v_x_6008_, 1);
v_l_6010_ = lean_ctor_get(v_x_6008_, 3);
v_r_6011_ = lean_ctor_get(v_x_6008_, 4);
v___x_6012_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6007_, v_l_6010_);
v_ileans_6013_ = lean_ctor_get(v___x_6012_, 0);
v_workers_6014_ = lean_ctor_get(v___x_6012_, 1);
v_isSharedCheck_6023_ = !lean_is_exclusive(v___x_6012_);
if (v_isSharedCheck_6023_ == 0)
{
v___x_6016_ = v___x_6012_;
v_isShared_6017_ = v_isSharedCheck_6023_;
goto v_resetjp_6015_;
}
else
{
lean_inc(v_workers_6014_);
lean_inc(v_ileans_6013_);
lean_dec(v___x_6012_);
v___x_6016_ = lean_box(0);
v_isShared_6017_ = v_isSharedCheck_6023_;
goto v_resetjp_6015_;
}
v_resetjp_6015_:
{
lean_object* v___x_6018_; lean_object* v___x_6020_; 
v___x_6018_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6009_, v_ileans_6013_);
if (v_isShared_6017_ == 0)
{
lean_ctor_set(v___x_6016_, 0, v___x_6018_);
v___x_6020_ = v___x_6016_;
goto v_reusejp_6019_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v___x_6018_);
lean_ctor_set(v_reuseFailAlloc_6022_, 1, v_workers_6014_);
v___x_6020_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6019_;
}
v_reusejp_6019_:
{
v_init_6007_ = v___x_6020_;
v_x_6008_ = v_r_6011_;
goto _start;
}
}
}
else
{
return v_init_6007_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_6024_, lean_object* v_x_6025_){
_start:
{
lean_object* v_res_6026_; 
v_res_6026_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6024_, v_x_6025_);
lean_dec(v_x_6025_);
return v_res_6026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_6027_, lean_object* v_path_6028_){
_start:
{
lean_object* v_ileans_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; 
v_ileans_6029_ = lean_ctor_get(v_self_6027_, 0);
lean_inc(v_ileans_6029_);
v___x_6030_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6028_, v_ileans_6029_);
v___x_6031_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_6027_, v___x_6030_);
lean_dec(v___x_6030_);
return v___x_6031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_6032_, lean_object* v_path_6033_){
_start:
{
lean_object* v_res_6034_; 
v_res_6034_ = l_Lean_Server_References_removeIlean(v_self_6032_, v_path_6033_);
lean_dec_ref(v_path_6033_);
return v_res_6034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_6035_, lean_object* v_k_6036_, lean_object* v_t_6037_, lean_object* v_h_6038_){
_start:
{
lean_object* v___x_6039_; 
v___x_6039_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6036_, v_t_6037_);
return v___x_6039_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_6040_, lean_object* v_k_6041_, lean_object* v_t_6042_, lean_object* v_h_6043_){
_start:
{
lean_object* v_res_6044_; 
v_res_6044_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_6040_, v_k_6041_, v_t_6042_, v_h_6043_);
lean_dec(v_k_6041_);
return v_res_6044_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_6045_, lean_object* v_t_6046_, lean_object* v_hl_6047_){
_start:
{
lean_object* v___x_6048_; 
v___x_6048_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6045_, v_t_6046_);
return v___x_6048_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_6049_, lean_object* v_t_6050_, lean_object* v_hl_6051_){
_start:
{
lean_object* v_res_6052_; 
v_res_6052_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_6049_, v_t_6050_, v_hl_6051_);
lean_dec_ref(v_path_6049_);
return v_res_6052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_6053_, lean_object* v_t_6054_){
_start:
{
lean_object* v___x_6055_; 
v___x_6055_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6053_, v_t_6054_);
return v___x_6055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_6056_, lean_object* v_t_6057_){
_start:
{
lean_object* v_res_6058_; 
v_res_6058_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_6056_, v_t_6057_);
lean_dec(v_t_6057_);
return v_res_6058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_6059_, lean_object* v_k_6060_){
_start:
{
if (lean_obj_tag(v_t_6059_) == 0)
{
lean_object* v_k_6061_; lean_object* v_v_6062_; lean_object* v_l_6063_; lean_object* v_r_6064_; uint8_t v___x_6065_; 
v_k_6061_ = lean_ctor_get(v_t_6059_, 1);
v_v_6062_ = lean_ctor_get(v_t_6059_, 2);
v_l_6063_ = lean_ctor_get(v_t_6059_, 3);
v_r_6064_ = lean_ctor_get(v_t_6059_, 4);
v___x_6065_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6060_, v_k_6061_);
switch(v___x_6065_)
{
case 0:
{
v_t_6059_ = v_l_6063_;
goto _start;
}
case 1:
{
lean_object* v___x_6067_; 
lean_inc(v_v_6062_);
v___x_6067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6067_, 0, v_v_6062_);
return v___x_6067_;
}
default: 
{
v_t_6059_ = v_r_6064_;
goto _start;
}
}
}
else
{
lean_object* v___x_6069_; 
v___x_6069_ = lean_box(0);
return v___x_6069_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_6070_, lean_object* v_k_6071_){
_start:
{
lean_object* v_res_6072_; 
v_res_6072_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6070_, v_k_6071_);
lean_dec(v_k_6071_);
lean_dec(v_t_6070_);
return v_res_6072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_6073_, lean_object* v_name_6074_, lean_object* v_moduleUri_6075_, lean_object* v_version_6076_, lean_object* v_directImports_6077_, uint8_t v_isSetupFailure_6078_){
_start:
{
lean_object* v___x_6080_; 
v___x_6080_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_6077_);
if (lean_obj_tag(v___x_6080_) == 0)
{
lean_object* v_a_6081_; lean_object* v___x_6083_; uint8_t v_isShared_6084_; uint8_t v_isSharedCheck_6147_; 
v_a_6081_ = lean_ctor_get(v___x_6080_, 0);
v_isSharedCheck_6147_ = !lean_is_exclusive(v___x_6080_);
if (v_isSharedCheck_6147_ == 0)
{
v___x_6083_ = v___x_6080_;
v_isShared_6084_ = v_isSharedCheck_6147_;
goto v_resetjp_6082_;
}
else
{
lean_inc(v_a_6081_);
lean_dec(v___x_6080_);
v___x_6083_ = lean_box(0);
v_isShared_6084_ = v_isSharedCheck_6147_;
goto v_resetjp_6082_;
}
v_resetjp_6082_:
{
lean_object* v_ileans_6085_; lean_object* v_workers_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; 
v_ileans_6085_ = lean_ctor_get(v_self_6073_, 0);
v_workers_6086_ = lean_ctor_get(v_self_6073_, 1);
v___x_6087_ = lean_box(1);
v___x_6088_ = lean_box(v_isSetupFailure_6078_);
v___x_6089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6088_);
v___x_6090_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6086_, v_name_6074_);
if (lean_obj_tag(v___x_6090_) == 1)
{
lean_object* v_val_6091_; lean_object* v_version_6092_; lean_object* v_refs_6093_; lean_object* v_decls_6094_; lean_object* v___x_6096_; uint8_t v_isShared_6097_; uint8_t v_isSharedCheck_6129_; 
v_val_6091_ = lean_ctor_get(v___x_6090_, 0);
lean_inc(v_val_6091_);
lean_dec_ref_known(v___x_6090_, 1);
v_version_6092_ = lean_ctor_get(v_val_6091_, 1);
v_refs_6093_ = lean_ctor_get(v_val_6091_, 4);
v_decls_6094_ = lean_ctor_get(v_val_6091_, 5);
v_isSharedCheck_6129_ = !lean_is_exclusive(v_val_6091_);
if (v_isSharedCheck_6129_ == 0)
{
lean_object* v_unused_6130_; lean_object* v_unused_6131_; lean_object* v_unused_6132_; 
v_unused_6130_ = lean_ctor_get(v_val_6091_, 3);
lean_dec(v_unused_6130_);
v_unused_6131_ = lean_ctor_get(v_val_6091_, 2);
lean_dec(v_unused_6131_);
v_unused_6132_ = lean_ctor_get(v_val_6091_, 0);
lean_dec(v_unused_6132_);
v___x_6096_ = v_val_6091_;
v_isShared_6097_ = v_isSharedCheck_6129_;
goto v_resetjp_6095_;
}
else
{
lean_inc(v_decls_6094_);
lean_inc(v_refs_6093_);
lean_inc(v_version_6092_);
lean_dec(v_val_6091_);
v___x_6096_ = lean_box(0);
v_isShared_6097_ = v_isSharedCheck_6129_;
goto v_resetjp_6095_;
}
v_resetjp_6095_:
{
uint8_t v___x_6098_; 
v___x_6098_ = lean_nat_dec_lt(v_version_6076_, v_version_6092_);
if (v___x_6098_ == 0)
{
lean_object* v___x_6100_; uint8_t v_isShared_6101_; uint8_t v_isSharedCheck_6123_; 
lean_inc(v_workers_6086_);
lean_inc(v_ileans_6085_);
v_isSharedCheck_6123_ = !lean_is_exclusive(v_self_6073_);
if (v_isSharedCheck_6123_ == 0)
{
lean_object* v_unused_6124_; lean_object* v_unused_6125_; 
v_unused_6124_ = lean_ctor_get(v_self_6073_, 1);
lean_dec(v_unused_6124_);
v_unused_6125_ = lean_ctor_get(v_self_6073_, 0);
lean_dec(v_unused_6125_);
v___x_6100_ = v_self_6073_;
v_isShared_6101_ = v_isSharedCheck_6123_;
goto v_resetjp_6099_;
}
else
{
lean_dec(v_self_6073_);
v___x_6100_ = lean_box(0);
v_isShared_6101_ = v_isSharedCheck_6123_;
goto v_resetjp_6099_;
}
v_resetjp_6099_:
{
uint8_t v___x_6102_; 
v___x_6102_ = lean_nat_dec_eq(v_version_6076_, v_version_6092_);
lean_dec(v_version_6092_);
if (v___x_6102_ == 0)
{
lean_object* v___x_6104_; 
lean_dec(v_decls_6094_);
lean_dec(v_refs_6093_);
if (v_isShared_6097_ == 0)
{
lean_ctor_set(v___x_6096_, 5, v___x_6087_);
lean_ctor_set(v___x_6096_, 4, v___x_6087_);
lean_ctor_set(v___x_6096_, 3, v___x_6089_);
lean_ctor_set(v___x_6096_, 2, v_a_6081_);
lean_ctor_set(v___x_6096_, 1, v_version_6076_);
lean_ctor_set(v___x_6096_, 0, v_moduleUri_6075_);
v___x_6104_ = v___x_6096_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6112_; 
v_reuseFailAlloc_6112_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_moduleUri_6075_);
lean_ctor_set(v_reuseFailAlloc_6112_, 1, v_version_6076_);
lean_ctor_set(v_reuseFailAlloc_6112_, 2, v_a_6081_);
lean_ctor_set(v_reuseFailAlloc_6112_, 3, v___x_6089_);
lean_ctor_set(v_reuseFailAlloc_6112_, 4, v___x_6087_);
lean_ctor_set(v_reuseFailAlloc_6112_, 5, v___x_6087_);
v___x_6104_ = v_reuseFailAlloc_6112_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
lean_object* v___x_6105_; lean_object* v___x_6107_; 
v___x_6105_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6074_, v___x_6104_, v_workers_6086_);
if (v_isShared_6101_ == 0)
{
lean_ctor_set(v___x_6100_, 1, v___x_6105_);
v___x_6107_ = v___x_6100_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6111_; 
v_reuseFailAlloc_6111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6111_, 0, v_ileans_6085_);
lean_ctor_set(v_reuseFailAlloc_6111_, 1, v___x_6105_);
v___x_6107_ = v_reuseFailAlloc_6111_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
lean_object* v___x_6109_; 
if (v_isShared_6084_ == 0)
{
lean_ctor_set(v___x_6083_, 0, v___x_6107_);
v___x_6109_ = v___x_6083_;
goto v_reusejp_6108_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v___x_6107_);
v___x_6109_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6108_;
}
v_reusejp_6108_:
{
return v___x_6109_;
}
}
}
}
else
{
lean_object* v___x_6114_; 
if (v_isShared_6097_ == 0)
{
lean_ctor_set(v___x_6096_, 3, v___x_6089_);
lean_ctor_set(v___x_6096_, 2, v_a_6081_);
lean_ctor_set(v___x_6096_, 1, v_version_6076_);
lean_ctor_set(v___x_6096_, 0, v_moduleUri_6075_);
v___x_6114_ = v___x_6096_;
goto v_reusejp_6113_;
}
else
{
lean_object* v_reuseFailAlloc_6122_; 
v_reuseFailAlloc_6122_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6122_, 0, v_moduleUri_6075_);
lean_ctor_set(v_reuseFailAlloc_6122_, 1, v_version_6076_);
lean_ctor_set(v_reuseFailAlloc_6122_, 2, v_a_6081_);
lean_ctor_set(v_reuseFailAlloc_6122_, 3, v___x_6089_);
lean_ctor_set(v_reuseFailAlloc_6122_, 4, v_refs_6093_);
lean_ctor_set(v_reuseFailAlloc_6122_, 5, v_decls_6094_);
v___x_6114_ = v_reuseFailAlloc_6122_;
goto v_reusejp_6113_;
}
v_reusejp_6113_:
{
lean_object* v___x_6115_; lean_object* v___x_6117_; 
v___x_6115_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6074_, v___x_6114_, v_workers_6086_);
if (v_isShared_6101_ == 0)
{
lean_ctor_set(v___x_6100_, 1, v___x_6115_);
v___x_6117_ = v___x_6100_;
goto v_reusejp_6116_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v_ileans_6085_);
lean_ctor_set(v_reuseFailAlloc_6121_, 1, v___x_6115_);
v___x_6117_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6116_;
}
v_reusejp_6116_:
{
lean_object* v___x_6119_; 
if (v_isShared_6084_ == 0)
{
lean_ctor_set(v___x_6083_, 0, v___x_6117_);
v___x_6119_ = v___x_6083_;
goto v_reusejp_6118_;
}
else
{
lean_object* v_reuseFailAlloc_6120_; 
v_reuseFailAlloc_6120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6120_, 0, v___x_6117_);
v___x_6119_ = v_reuseFailAlloc_6120_;
goto v_reusejp_6118_;
}
v_reusejp_6118_:
{
return v___x_6119_;
}
}
}
}
}
}
else
{
lean_object* v___x_6127_; 
lean_del_object(v___x_6096_);
lean_dec(v_decls_6094_);
lean_dec(v_refs_6093_);
lean_dec(v_version_6092_);
lean_dec_ref_known(v___x_6089_, 1);
lean_dec(v_a_6081_);
lean_dec(v_version_6076_);
lean_dec_ref(v_moduleUri_6075_);
lean_dec(v_name_6074_);
if (v_isShared_6084_ == 0)
{
lean_ctor_set(v___x_6083_, 0, v_self_6073_);
v___x_6127_ = v___x_6083_;
goto v_reusejp_6126_;
}
else
{
lean_object* v_reuseFailAlloc_6128_; 
v_reuseFailAlloc_6128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6128_, 0, v_self_6073_);
v___x_6127_ = v_reuseFailAlloc_6128_;
goto v_reusejp_6126_;
}
v_reusejp_6126_:
{
return v___x_6127_;
}
}
}
}
else
{
lean_object* v___x_6134_; uint8_t v_isShared_6135_; uint8_t v_isSharedCheck_6144_; 
lean_inc(v_workers_6086_);
lean_inc(v_ileans_6085_);
lean_dec(v___x_6090_);
v_isSharedCheck_6144_ = !lean_is_exclusive(v_self_6073_);
if (v_isSharedCheck_6144_ == 0)
{
lean_object* v_unused_6145_; lean_object* v_unused_6146_; 
v_unused_6145_ = lean_ctor_get(v_self_6073_, 1);
lean_dec(v_unused_6145_);
v_unused_6146_ = lean_ctor_get(v_self_6073_, 0);
lean_dec(v_unused_6146_);
v___x_6134_ = v_self_6073_;
v_isShared_6135_ = v_isSharedCheck_6144_;
goto v_resetjp_6133_;
}
else
{
lean_dec(v_self_6073_);
v___x_6134_ = lean_box(0);
v_isShared_6135_ = v_isSharedCheck_6144_;
goto v_resetjp_6133_;
}
v_resetjp_6133_:
{
lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6139_; 
v___x_6136_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6136_, 0, v_moduleUri_6075_);
lean_ctor_set(v___x_6136_, 1, v_version_6076_);
lean_ctor_set(v___x_6136_, 2, v_a_6081_);
lean_ctor_set(v___x_6136_, 3, v___x_6089_);
lean_ctor_set(v___x_6136_, 4, v___x_6087_);
lean_ctor_set(v___x_6136_, 5, v___x_6087_);
v___x_6137_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6074_, v___x_6136_, v_workers_6086_);
if (v_isShared_6135_ == 0)
{
lean_ctor_set(v___x_6134_, 1, v___x_6137_);
v___x_6139_ = v___x_6134_;
goto v_reusejp_6138_;
}
else
{
lean_object* v_reuseFailAlloc_6143_; 
v_reuseFailAlloc_6143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6143_, 0, v_ileans_6085_);
lean_ctor_set(v_reuseFailAlloc_6143_, 1, v___x_6137_);
v___x_6139_ = v_reuseFailAlloc_6143_;
goto v_reusejp_6138_;
}
v_reusejp_6138_:
{
lean_object* v___x_6141_; 
if (v_isShared_6084_ == 0)
{
lean_ctor_set(v___x_6083_, 0, v___x_6139_);
v___x_6141_ = v___x_6083_;
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
lean_object* v_a_6148_; lean_object* v___x_6150_; uint8_t v_isShared_6151_; uint8_t v_isSharedCheck_6155_; 
lean_dec(v_version_6076_);
lean_dec_ref(v_moduleUri_6075_);
lean_dec(v_name_6074_);
lean_dec_ref(v_self_6073_);
v_a_6148_ = lean_ctor_get(v___x_6080_, 0);
v_isSharedCheck_6155_ = !lean_is_exclusive(v___x_6080_);
if (v_isSharedCheck_6155_ == 0)
{
v___x_6150_ = v___x_6080_;
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
else
{
lean_inc(v_a_6148_);
lean_dec(v___x_6080_);
v___x_6150_ = lean_box(0);
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
v_resetjp_6149_:
{
lean_object* v___x_6153_; 
if (v_isShared_6151_ == 0)
{
v___x_6153_ = v___x_6150_;
goto v_reusejp_6152_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_a_6148_);
v___x_6153_ = v_reuseFailAlloc_6154_;
goto v_reusejp_6152_;
}
v_reusejp_6152_:
{
return v___x_6153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6156_, lean_object* v_name_6157_, lean_object* v_moduleUri_6158_, lean_object* v_version_6159_, lean_object* v_directImports_6160_, lean_object* v_isSetupFailure_6161_, lean_object* v_a_6162_){
_start:
{
uint8_t v_isSetupFailure_boxed_6163_; lean_object* v_res_6164_; 
v_isSetupFailure_boxed_6163_ = lean_unbox(v_isSetupFailure_6161_);
v_res_6164_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6156_, v_name_6157_, v_moduleUri_6158_, v_version_6159_, v_directImports_6160_, v_isSetupFailure_boxed_6163_);
lean_dec_ref(v_directImports_6160_);
return v_res_6164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6165_, lean_object* v_t_6166_, lean_object* v_k_6167_){
_start:
{
lean_object* v___x_6168_; 
v___x_6168_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6166_, v_k_6167_);
return v___x_6168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6169_, lean_object* v_t_6170_, lean_object* v_k_6171_){
_start:
{
lean_object* v_res_6172_; 
v_res_6172_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6169_, v_t_6170_, v_k_6171_);
lean_dec(v_k_6171_);
lean_dec(v_t_6170_);
return v_res_6172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6173_, lean_object* v_____s_6174_){
_start:
{
lean_object* v_fst_6175_; lean_object* v_snd_6176_; lean_object* v_r_6177_; lean_object* v___x_6178_; 
v_fst_6175_ = lean_ctor_get(v_x_6173_, 0);
lean_inc(v_fst_6175_);
v_snd_6176_ = lean_ctor_get(v_x_6173_, 1);
lean_inc(v_snd_6176_);
lean_dec_ref(v_x_6173_);
v_r_6177_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6175_, v_snd_6176_, v_____s_6174_);
v___x_6178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6178_, 0, v_r_6177_);
return v___x_6178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6179_, lean_object* v_k_6180_, lean_object* v_fallback_6181_){
_start:
{
if (lean_obj_tag(v_t_6179_) == 0)
{
lean_object* v_k_6182_; lean_object* v_v_6183_; lean_object* v_l_6184_; lean_object* v_r_6185_; uint8_t v___x_6186_; 
v_k_6182_ = lean_ctor_get(v_t_6179_, 1);
v_v_6183_ = lean_ctor_get(v_t_6179_, 2);
v_l_6184_ = lean_ctor_get(v_t_6179_, 3);
v_r_6185_ = lean_ctor_get(v_t_6179_, 4);
v___x_6186_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6180_, v_k_6182_);
switch(v___x_6186_)
{
case 0:
{
v_t_6179_ = v_l_6184_;
goto _start;
}
case 1:
{
lean_inc(v_v_6183_);
return v_v_6183_;
}
default: 
{
v_t_6179_ = v_r_6185_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6181_);
return v_fallback_6181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6189_, lean_object* v_k_6190_, lean_object* v_fallback_6191_){
_start:
{
lean_object* v_res_6192_; 
v_res_6192_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6189_, v_k_6190_, v_fallback_6191_);
lean_dec(v_fallback_6191_);
lean_dec_ref(v_k_6190_);
lean_dec(v_t_6189_);
return v_res_6192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6193_, lean_object* v_x_6194_){
_start:
{
if (lean_obj_tag(v_x_6194_) == 0)
{
lean_object* v_k_6195_; lean_object* v_v_6196_; lean_object* v_l_6197_; lean_object* v_r_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; 
v_k_6195_ = lean_ctor_get(v_x_6194_, 1);
lean_inc(v_k_6195_);
v_v_6196_ = lean_ctor_get(v_x_6194_, 2);
lean_inc(v_v_6196_);
v_l_6197_ = lean_ctor_get(v_x_6194_, 3);
lean_inc(v_l_6197_);
v_r_6198_ = lean_ctor_get(v_x_6194_, 4);
lean_inc(v_r_6198_);
lean_dec_ref_known(v_x_6194_, 5);
v___x_6199_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6193_, v_l_6197_);
v___x_6200_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6201_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6199_, v_k_6195_, v___x_6200_);
v___x_6202_ = l_Lean_Lsp_RefInfo_merge(v___x_6201_, v_v_6196_);
v___x_6203_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6195_, v___x_6202_, v___x_6199_);
v_init_6193_ = v___x_6203_;
v_x_6194_ = v_r_6198_;
goto _start;
}
else
{
return v_init_6193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6206_, lean_object* v_name_6207_, lean_object* v_moduleUri_6208_, lean_object* v_version_6209_, lean_object* v_refs_6210_, lean_object* v_decls_6211_){
_start:
{
lean_object* v_ileans_6213_; lean_object* v_workers_6214_; lean_object* v___x_6215_; 
v_ileans_6213_ = lean_ctor_get(v_self_6206_, 0);
v_workers_6214_ = lean_ctor_get(v_self_6206_, 1);
v___x_6215_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6214_, v_name_6207_);
if (lean_obj_tag(v___x_6215_) == 1)
{
lean_object* v_val_6216_; lean_object* v___x_6218_; uint8_t v_isShared_6219_; uint8_t v_isSharedCheck_6264_; 
v_val_6216_ = lean_ctor_get(v___x_6215_, 0);
v_isSharedCheck_6264_ = !lean_is_exclusive(v___x_6215_);
if (v_isSharedCheck_6264_ == 0)
{
v___x_6218_ = v___x_6215_;
v_isShared_6219_ = v_isSharedCheck_6264_;
goto v_resetjp_6217_;
}
else
{
lean_inc(v_val_6216_);
lean_dec(v___x_6215_);
v___x_6218_ = lean_box(0);
v_isShared_6219_ = v_isSharedCheck_6264_;
goto v_resetjp_6217_;
}
v_resetjp_6217_:
{
lean_object* v_version_6220_; lean_object* v_directImports_6221_; lean_object* v_isSetupFailure_x3f_6222_; lean_object* v_refs_6223_; lean_object* v_decls_6224_; lean_object* v___x_6226_; uint8_t v_isShared_6227_; uint8_t v_isSharedCheck_6262_; 
v_version_6220_ = lean_ctor_get(v_val_6216_, 1);
v_directImports_6221_ = lean_ctor_get(v_val_6216_, 2);
v_isSetupFailure_x3f_6222_ = lean_ctor_get(v_val_6216_, 3);
v_refs_6223_ = lean_ctor_get(v_val_6216_, 4);
v_decls_6224_ = lean_ctor_get(v_val_6216_, 5);
v_isSharedCheck_6262_ = !lean_is_exclusive(v_val_6216_);
if (v_isSharedCheck_6262_ == 0)
{
lean_object* v_unused_6263_; 
v_unused_6263_ = lean_ctor_get(v_val_6216_, 0);
lean_dec(v_unused_6263_);
v___x_6226_ = v_val_6216_;
v_isShared_6227_ = v_isSharedCheck_6262_;
goto v_resetjp_6225_;
}
else
{
lean_inc(v_decls_6224_);
lean_inc(v_refs_6223_);
lean_inc(v_isSetupFailure_x3f_6222_);
lean_inc(v_directImports_6221_);
lean_inc(v_version_6220_);
lean_dec(v_val_6216_);
v___x_6226_ = lean_box(0);
v_isShared_6227_ = v_isSharedCheck_6262_;
goto v_resetjp_6225_;
}
v_resetjp_6225_:
{
uint8_t v___x_6228_; 
v___x_6228_ = lean_nat_dec_lt(v_version_6209_, v_version_6220_);
if (v___x_6228_ == 0)
{
lean_object* v___x_6230_; uint8_t v_isShared_6231_; uint8_t v_isSharedCheck_6256_; 
lean_inc(v_workers_6214_);
lean_inc(v_ileans_6213_);
v_isSharedCheck_6256_ = !lean_is_exclusive(v_self_6206_);
if (v_isSharedCheck_6256_ == 0)
{
lean_object* v_unused_6257_; lean_object* v_unused_6258_; 
v_unused_6257_ = lean_ctor_get(v_self_6206_, 1);
lean_dec(v_unused_6257_);
v_unused_6258_ = lean_ctor_get(v_self_6206_, 0);
lean_dec(v_unused_6258_);
v___x_6230_ = v_self_6206_;
v_isShared_6231_ = v_isSharedCheck_6256_;
goto v_resetjp_6229_;
}
else
{
lean_dec(v_self_6206_);
v___x_6230_ = lean_box(0);
v_isShared_6231_ = v_isSharedCheck_6256_;
goto v_resetjp_6229_;
}
v_resetjp_6229_:
{
uint8_t v___x_6232_; 
v___x_6232_ = lean_nat_dec_eq(v_version_6209_, v_version_6220_);
lean_dec(v_version_6220_);
if (v___x_6232_ == 0)
{
lean_object* v___x_6234_; 
lean_dec(v_decls_6224_);
lean_dec(v_refs_6223_);
if (v_isShared_6227_ == 0)
{
lean_ctor_set(v___x_6226_, 5, v_decls_6211_);
lean_ctor_set(v___x_6226_, 4, v_refs_6210_);
lean_ctor_set(v___x_6226_, 1, v_version_6209_);
lean_ctor_set(v___x_6226_, 0, v_moduleUri_6208_);
v___x_6234_ = v___x_6226_;
goto v_reusejp_6233_;
}
else
{
lean_object* v_reuseFailAlloc_6242_; 
v_reuseFailAlloc_6242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6242_, 0, v_moduleUri_6208_);
lean_ctor_set(v_reuseFailAlloc_6242_, 1, v_version_6209_);
lean_ctor_set(v_reuseFailAlloc_6242_, 2, v_directImports_6221_);
lean_ctor_set(v_reuseFailAlloc_6242_, 3, v_isSetupFailure_x3f_6222_);
lean_ctor_set(v_reuseFailAlloc_6242_, 4, v_refs_6210_);
lean_ctor_set(v_reuseFailAlloc_6242_, 5, v_decls_6211_);
v___x_6234_ = v_reuseFailAlloc_6242_;
goto v_reusejp_6233_;
}
v_reusejp_6233_:
{
lean_object* v___x_6235_; lean_object* v___x_6237_; 
v___x_6235_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6207_, v___x_6234_, v_workers_6214_);
if (v_isShared_6231_ == 0)
{
lean_ctor_set(v___x_6230_, 1, v___x_6235_);
v___x_6237_ = v___x_6230_;
goto v_reusejp_6236_;
}
else
{
lean_object* v_reuseFailAlloc_6241_; 
v_reuseFailAlloc_6241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6241_, 0, v_ileans_6213_);
lean_ctor_set(v_reuseFailAlloc_6241_, 1, v___x_6235_);
v___x_6237_ = v_reuseFailAlloc_6241_;
goto v_reusejp_6236_;
}
v_reusejp_6236_:
{
lean_object* v___x_6239_; 
if (v_isShared_6219_ == 0)
{
lean_ctor_set_tag(v___x_6218_, 0);
lean_ctor_set(v___x_6218_, 0, v___x_6237_);
v___x_6239_ = v___x_6218_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6240_; 
v_reuseFailAlloc_6240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6240_, 0, v___x_6237_);
v___x_6239_ = v_reuseFailAlloc_6240_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
return v___x_6239_;
}
}
}
}
else
{
lean_object* v___f_6243_; lean_object* v_mergedRefs_6244_; lean_object* v_mergedDecls_6245_; lean_object* v___x_6247_; 
v___f_6243_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6244_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6223_, v_refs_6210_);
v_mergedDecls_6245_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6211_, v_decls_6224_, v___f_6243_);
lean_dec(v_decls_6211_);
if (v_isShared_6227_ == 0)
{
lean_ctor_set(v___x_6226_, 5, v_mergedDecls_6245_);
lean_ctor_set(v___x_6226_, 4, v_mergedRefs_6244_);
lean_ctor_set(v___x_6226_, 1, v_version_6209_);
lean_ctor_set(v___x_6226_, 0, v_moduleUri_6208_);
v___x_6247_ = v___x_6226_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_moduleUri_6208_);
lean_ctor_set(v_reuseFailAlloc_6255_, 1, v_version_6209_);
lean_ctor_set(v_reuseFailAlloc_6255_, 2, v_directImports_6221_);
lean_ctor_set(v_reuseFailAlloc_6255_, 3, v_isSetupFailure_x3f_6222_);
lean_ctor_set(v_reuseFailAlloc_6255_, 4, v_mergedRefs_6244_);
lean_ctor_set(v_reuseFailAlloc_6255_, 5, v_mergedDecls_6245_);
v___x_6247_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
lean_object* v___x_6248_; lean_object* v___x_6250_; 
v___x_6248_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6207_, v___x_6247_, v_workers_6214_);
if (v_isShared_6231_ == 0)
{
lean_ctor_set(v___x_6230_, 1, v___x_6248_);
v___x_6250_ = v___x_6230_;
goto v_reusejp_6249_;
}
else
{
lean_object* v_reuseFailAlloc_6254_; 
v_reuseFailAlloc_6254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6254_, 0, v_ileans_6213_);
lean_ctor_set(v_reuseFailAlloc_6254_, 1, v___x_6248_);
v___x_6250_ = v_reuseFailAlloc_6254_;
goto v_reusejp_6249_;
}
v_reusejp_6249_:
{
lean_object* v___x_6252_; 
if (v_isShared_6219_ == 0)
{
lean_ctor_set_tag(v___x_6218_, 0);
lean_ctor_set(v___x_6218_, 0, v___x_6250_);
v___x_6252_ = v___x_6218_;
goto v_reusejp_6251_;
}
else
{
lean_object* v_reuseFailAlloc_6253_; 
v_reuseFailAlloc_6253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6253_, 0, v___x_6250_);
v___x_6252_ = v_reuseFailAlloc_6253_;
goto v_reusejp_6251_;
}
v_reusejp_6251_:
{
return v___x_6252_;
}
}
}
}
}
}
else
{
lean_object* v___x_6260_; 
lean_del_object(v___x_6226_);
lean_dec(v_decls_6224_);
lean_dec(v_refs_6223_);
lean_dec(v_isSetupFailure_x3f_6222_);
lean_dec_ref(v_directImports_6221_);
lean_dec(v_version_6220_);
lean_dec(v_decls_6211_);
lean_dec(v_refs_6210_);
lean_dec(v_version_6209_);
lean_dec_ref(v_moduleUri_6208_);
lean_dec(v_name_6207_);
if (v_isShared_6219_ == 0)
{
lean_ctor_set_tag(v___x_6218_, 0);
lean_ctor_set(v___x_6218_, 0, v_self_6206_);
v___x_6260_ = v___x_6218_;
goto v_reusejp_6259_;
}
else
{
lean_object* v_reuseFailAlloc_6261_; 
v_reuseFailAlloc_6261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_self_6206_);
v___x_6260_ = v_reuseFailAlloc_6261_;
goto v_reusejp_6259_;
}
v_reusejp_6259_:
{
return v___x_6260_;
}
}
}
}
}
else
{
lean_object* v___x_6266_; uint8_t v_isShared_6267_; uint8_t v_isSharedCheck_6276_; 
lean_inc(v_workers_6214_);
lean_inc(v_ileans_6213_);
lean_dec(v___x_6215_);
v_isSharedCheck_6276_ = !lean_is_exclusive(v_self_6206_);
if (v_isSharedCheck_6276_ == 0)
{
lean_object* v_unused_6277_; lean_object* v_unused_6278_; 
v_unused_6277_ = lean_ctor_get(v_self_6206_, 1);
lean_dec(v_unused_6277_);
v_unused_6278_ = lean_ctor_get(v_self_6206_, 0);
lean_dec(v_unused_6278_);
v___x_6266_ = v_self_6206_;
v_isShared_6267_ = v_isSharedCheck_6276_;
goto v_resetjp_6265_;
}
else
{
lean_dec(v_self_6206_);
v___x_6266_ = lean_box(0);
v_isShared_6267_ = v_isSharedCheck_6276_;
goto v_resetjp_6265_;
}
v_resetjp_6265_:
{
lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6273_; 
v___x_6268_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6269_ = lean_box(0);
v___x_6270_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6270_, 0, v_moduleUri_6208_);
lean_ctor_set(v___x_6270_, 1, v_version_6209_);
lean_ctor_set(v___x_6270_, 2, v___x_6268_);
lean_ctor_set(v___x_6270_, 3, v___x_6269_);
lean_ctor_set(v___x_6270_, 4, v_refs_6210_);
lean_ctor_set(v___x_6270_, 5, v_decls_6211_);
v___x_6271_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6207_, v___x_6270_, v_workers_6214_);
if (v_isShared_6267_ == 0)
{
lean_ctor_set(v___x_6266_, 1, v___x_6271_);
v___x_6273_ = v___x_6266_;
goto v_reusejp_6272_;
}
else
{
lean_object* v_reuseFailAlloc_6275_; 
v_reuseFailAlloc_6275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6275_, 0, v_ileans_6213_);
lean_ctor_set(v_reuseFailAlloc_6275_, 1, v___x_6271_);
v___x_6273_ = v_reuseFailAlloc_6275_;
goto v_reusejp_6272_;
}
v_reusejp_6272_:
{
lean_object* v___x_6274_; 
v___x_6274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6274_, 0, v___x_6273_);
return v___x_6274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6279_, lean_object* v_name_6280_, lean_object* v_moduleUri_6281_, lean_object* v_version_6282_, lean_object* v_refs_6283_, lean_object* v_decls_6284_, lean_object* v_a_6285_){
_start:
{
lean_object* v_res_6286_; 
v_res_6286_ = l_Lean_Server_References_updateWorkerRefs(v_self_6279_, v_name_6280_, v_moduleUri_6281_, v_version_6282_, v_refs_6283_, v_decls_6284_);
return v_res_6286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6287_, lean_object* v_t_6288_, lean_object* v_k_6289_, lean_object* v_fallback_6290_){
_start:
{
lean_object* v___x_6291_; 
v___x_6291_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6288_, v_k_6289_, v_fallback_6290_);
return v___x_6291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6292_, lean_object* v_t_6293_, lean_object* v_k_6294_, lean_object* v_fallback_6295_){
_start:
{
lean_object* v_res_6296_; 
v_res_6296_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6292_, v_t_6293_, v_k_6294_, v_fallback_6295_);
lean_dec(v_fallback_6295_);
lean_dec_ref(v_k_6294_);
lean_dec(v_t_6293_);
return v_res_6296_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6297_, lean_object* v_t_6298_){
_start:
{
lean_object* v___x_6299_; 
v___x_6299_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6297_, v_t_6298_);
return v___x_6299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6300_, lean_object* v_name_6301_, lean_object* v_moduleUri_6302_, lean_object* v_version_6303_, lean_object* v_refs_6304_, lean_object* v_decls_6305_){
_start:
{
lean_object* v_ileans_6307_; lean_object* v_workers_6308_; lean_object* v___x_6309_; 
v_ileans_6307_ = lean_ctor_get(v_self_6300_, 0);
v_workers_6308_ = lean_ctor_get(v_self_6300_, 1);
v___x_6309_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6308_, v_name_6301_);
if (lean_obj_tag(v___x_6309_) == 1)
{
lean_object* v_val_6310_; lean_object* v___x_6312_; uint8_t v_isShared_6313_; uint8_t v_isSharedCheck_6344_; 
v_val_6310_ = lean_ctor_get(v___x_6309_, 0);
v_isSharedCheck_6344_ = !lean_is_exclusive(v___x_6309_);
if (v_isSharedCheck_6344_ == 0)
{
v___x_6312_ = v___x_6309_;
v_isShared_6313_ = v_isSharedCheck_6344_;
goto v_resetjp_6311_;
}
else
{
lean_inc(v_val_6310_);
lean_dec(v___x_6309_);
v___x_6312_ = lean_box(0);
v_isShared_6313_ = v_isSharedCheck_6344_;
goto v_resetjp_6311_;
}
v_resetjp_6311_:
{
lean_object* v_version_6314_; lean_object* v_directImports_6315_; lean_object* v_isSetupFailure_x3f_6316_; lean_object* v___x_6318_; uint8_t v_isShared_6319_; uint8_t v_isSharedCheck_6340_; 
v_version_6314_ = lean_ctor_get(v_val_6310_, 1);
v_directImports_6315_ = lean_ctor_get(v_val_6310_, 2);
v_isSetupFailure_x3f_6316_ = lean_ctor_get(v_val_6310_, 3);
v_isSharedCheck_6340_ = !lean_is_exclusive(v_val_6310_);
if (v_isSharedCheck_6340_ == 0)
{
lean_object* v_unused_6341_; lean_object* v_unused_6342_; lean_object* v_unused_6343_; 
v_unused_6341_ = lean_ctor_get(v_val_6310_, 5);
lean_dec(v_unused_6341_);
v_unused_6342_ = lean_ctor_get(v_val_6310_, 4);
lean_dec(v_unused_6342_);
v_unused_6343_ = lean_ctor_get(v_val_6310_, 0);
lean_dec(v_unused_6343_);
v___x_6318_ = v_val_6310_;
v_isShared_6319_ = v_isSharedCheck_6340_;
goto v_resetjp_6317_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6316_);
lean_inc(v_directImports_6315_);
lean_inc(v_version_6314_);
lean_dec(v_val_6310_);
v___x_6318_ = lean_box(0);
v_isShared_6319_ = v_isSharedCheck_6340_;
goto v_resetjp_6317_;
}
v_resetjp_6317_:
{
uint8_t v___x_6320_; 
v___x_6320_ = lean_nat_dec_lt(v_version_6303_, v_version_6314_);
lean_dec(v_version_6314_);
if (v___x_6320_ == 0)
{
lean_object* v___x_6322_; uint8_t v_isShared_6323_; uint8_t v_isSharedCheck_6334_; 
lean_inc(v_workers_6308_);
lean_inc(v_ileans_6307_);
v_isSharedCheck_6334_ = !lean_is_exclusive(v_self_6300_);
if (v_isSharedCheck_6334_ == 0)
{
lean_object* v_unused_6335_; lean_object* v_unused_6336_; 
v_unused_6335_ = lean_ctor_get(v_self_6300_, 1);
lean_dec(v_unused_6335_);
v_unused_6336_ = lean_ctor_get(v_self_6300_, 0);
lean_dec(v_unused_6336_);
v___x_6322_ = v_self_6300_;
v_isShared_6323_ = v_isSharedCheck_6334_;
goto v_resetjp_6321_;
}
else
{
lean_dec(v_self_6300_);
v___x_6322_ = lean_box(0);
v_isShared_6323_ = v_isSharedCheck_6334_;
goto v_resetjp_6321_;
}
v_resetjp_6321_:
{
lean_object* v___x_6325_; 
if (v_isShared_6319_ == 0)
{
lean_ctor_set(v___x_6318_, 5, v_decls_6305_);
lean_ctor_set(v___x_6318_, 4, v_refs_6304_);
lean_ctor_set(v___x_6318_, 1, v_version_6303_);
lean_ctor_set(v___x_6318_, 0, v_moduleUri_6302_);
v___x_6325_ = v___x_6318_;
goto v_reusejp_6324_;
}
else
{
lean_object* v_reuseFailAlloc_6333_; 
v_reuseFailAlloc_6333_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6333_, 0, v_moduleUri_6302_);
lean_ctor_set(v_reuseFailAlloc_6333_, 1, v_version_6303_);
lean_ctor_set(v_reuseFailAlloc_6333_, 2, v_directImports_6315_);
lean_ctor_set(v_reuseFailAlloc_6333_, 3, v_isSetupFailure_x3f_6316_);
lean_ctor_set(v_reuseFailAlloc_6333_, 4, v_refs_6304_);
lean_ctor_set(v_reuseFailAlloc_6333_, 5, v_decls_6305_);
v___x_6325_ = v_reuseFailAlloc_6333_;
goto v_reusejp_6324_;
}
v_reusejp_6324_:
{
lean_object* v___x_6326_; lean_object* v___x_6328_; 
v___x_6326_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6301_, v___x_6325_, v_workers_6308_);
if (v_isShared_6323_ == 0)
{
lean_ctor_set(v___x_6322_, 1, v___x_6326_);
v___x_6328_ = v___x_6322_;
goto v_reusejp_6327_;
}
else
{
lean_object* v_reuseFailAlloc_6332_; 
v_reuseFailAlloc_6332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6332_, 0, v_ileans_6307_);
lean_ctor_set(v_reuseFailAlloc_6332_, 1, v___x_6326_);
v___x_6328_ = v_reuseFailAlloc_6332_;
goto v_reusejp_6327_;
}
v_reusejp_6327_:
{
lean_object* v___x_6330_; 
if (v_isShared_6313_ == 0)
{
lean_ctor_set_tag(v___x_6312_, 0);
lean_ctor_set(v___x_6312_, 0, v___x_6328_);
v___x_6330_ = v___x_6312_;
goto v_reusejp_6329_;
}
else
{
lean_object* v_reuseFailAlloc_6331_; 
v_reuseFailAlloc_6331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6331_, 0, v___x_6328_);
v___x_6330_ = v_reuseFailAlloc_6331_;
goto v_reusejp_6329_;
}
v_reusejp_6329_:
{
return v___x_6330_;
}
}
}
}
}
else
{
lean_object* v___x_6338_; 
lean_del_object(v___x_6318_);
lean_dec(v_isSetupFailure_x3f_6316_);
lean_dec_ref(v_directImports_6315_);
lean_dec(v_decls_6305_);
lean_dec(v_refs_6304_);
lean_dec(v_version_6303_);
lean_dec_ref(v_moduleUri_6302_);
lean_dec(v_name_6301_);
if (v_isShared_6313_ == 0)
{
lean_ctor_set_tag(v___x_6312_, 0);
lean_ctor_set(v___x_6312_, 0, v_self_6300_);
v___x_6338_ = v___x_6312_;
goto v_reusejp_6337_;
}
else
{
lean_object* v_reuseFailAlloc_6339_; 
v_reuseFailAlloc_6339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_self_6300_);
v___x_6338_ = v_reuseFailAlloc_6339_;
goto v_reusejp_6337_;
}
v_reusejp_6337_:
{
return v___x_6338_;
}
}
}
}
}
else
{
lean_object* v___x_6346_; uint8_t v_isShared_6347_; uint8_t v_isSharedCheck_6356_; 
lean_inc(v_workers_6308_);
lean_inc(v_ileans_6307_);
lean_dec(v___x_6309_);
v_isSharedCheck_6356_ = !lean_is_exclusive(v_self_6300_);
if (v_isSharedCheck_6356_ == 0)
{
lean_object* v_unused_6357_; lean_object* v_unused_6358_; 
v_unused_6357_ = lean_ctor_get(v_self_6300_, 1);
lean_dec(v_unused_6357_);
v_unused_6358_ = lean_ctor_get(v_self_6300_, 0);
lean_dec(v_unused_6358_);
v___x_6346_ = v_self_6300_;
v_isShared_6347_ = v_isSharedCheck_6356_;
goto v_resetjp_6345_;
}
else
{
lean_dec(v_self_6300_);
v___x_6346_ = lean_box(0);
v_isShared_6347_ = v_isSharedCheck_6356_;
goto v_resetjp_6345_;
}
v_resetjp_6345_:
{
lean_object* v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6353_; 
v___x_6348_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6349_ = lean_box(0);
v___x_6350_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6350_, 0, v_moduleUri_6302_);
lean_ctor_set(v___x_6350_, 1, v_version_6303_);
lean_ctor_set(v___x_6350_, 2, v___x_6348_);
lean_ctor_set(v___x_6350_, 3, v___x_6349_);
lean_ctor_set(v___x_6350_, 4, v_refs_6304_);
lean_ctor_set(v___x_6350_, 5, v_decls_6305_);
v___x_6351_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6301_, v___x_6350_, v_workers_6308_);
if (v_isShared_6347_ == 0)
{
lean_ctor_set(v___x_6346_, 1, v___x_6351_);
v___x_6353_ = v___x_6346_;
goto v_reusejp_6352_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_ileans_6307_);
lean_ctor_set(v_reuseFailAlloc_6355_, 1, v___x_6351_);
v___x_6353_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6352_;
}
v_reusejp_6352_:
{
lean_object* v___x_6354_; 
v___x_6354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6354_, 0, v___x_6353_);
return v___x_6354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6359_, lean_object* v_name_6360_, lean_object* v_moduleUri_6361_, lean_object* v_version_6362_, lean_object* v_refs_6363_, lean_object* v_decls_6364_, lean_object* v_a_6365_){
_start:
{
lean_object* v_res_6366_; 
v_res_6366_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6359_, v_name_6360_, v_moduleUri_6361_, v_version_6362_, v_refs_6363_, v_decls_6364_);
return v_res_6366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6367_, lean_object* v_name_6368_){
_start:
{
lean_object* v_ileans_6369_; lean_object* v_workers_6370_; lean_object* v___x_6372_; uint8_t v_isShared_6373_; uint8_t v_isSharedCheck_6378_; 
v_ileans_6369_ = lean_ctor_get(v_self_6367_, 0);
v_workers_6370_ = lean_ctor_get(v_self_6367_, 1);
v_isSharedCheck_6378_ = !lean_is_exclusive(v_self_6367_);
if (v_isSharedCheck_6378_ == 0)
{
v___x_6372_ = v_self_6367_;
v_isShared_6373_ = v_isSharedCheck_6378_;
goto v_resetjp_6371_;
}
else
{
lean_inc(v_workers_6370_);
lean_inc(v_ileans_6369_);
lean_dec(v_self_6367_);
v___x_6372_ = lean_box(0);
v_isShared_6373_ = v_isSharedCheck_6378_;
goto v_resetjp_6371_;
}
v_resetjp_6371_:
{
lean_object* v___x_6374_; lean_object* v___x_6376_; 
v___x_6374_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6368_, v_workers_6370_);
if (v_isShared_6373_ == 0)
{
lean_ctor_set(v___x_6372_, 1, v___x_6374_);
v___x_6376_ = v___x_6372_;
goto v_reusejp_6375_;
}
else
{
lean_object* v_reuseFailAlloc_6377_; 
v_reuseFailAlloc_6377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6377_, 0, v_ileans_6369_);
lean_ctor_set(v_reuseFailAlloc_6377_, 1, v___x_6374_);
v___x_6376_ = v_reuseFailAlloc_6377_;
goto v_reusejp_6375_;
}
v_reusejp_6375_:
{
return v___x_6376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6379_, lean_object* v_name_6380_){
_start:
{
lean_object* v_res_6381_; 
v_res_6381_ = l_Lean_Server_References_removeWorkerRefs(v_self_6379_, v_name_6380_);
lean_dec(v_name_6380_);
return v_res_6381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6382_, lean_object* v_x_6383_){
_start:
{
if (lean_obj_tag(v_x_6383_) == 0)
{
lean_object* v_v_6384_; lean_object* v_k_6385_; lean_object* v_l_6386_; lean_object* v_r_6387_; lean_object* v_moduleUri_6388_; lean_object* v_refs_6389_; lean_object* v_decls_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; 
v_v_6384_ = lean_ctor_get(v_x_6383_, 2);
lean_inc(v_v_6384_);
v_k_6385_ = lean_ctor_get(v_x_6383_, 1);
lean_inc(v_k_6385_);
v_l_6386_ = lean_ctor_get(v_x_6383_, 3);
lean_inc(v_l_6386_);
v_r_6387_ = lean_ctor_get(v_x_6383_, 4);
lean_inc(v_r_6387_);
lean_dec_ref_known(v_x_6383_, 5);
v_moduleUri_6388_ = lean_ctor_get(v_v_6384_, 0);
lean_inc_ref(v_moduleUri_6388_);
v_refs_6389_ = lean_ctor_get(v_v_6384_, 3);
lean_inc(v_refs_6389_);
v_decls_6390_ = lean_ctor_get(v_v_6384_, 4);
lean_inc(v_decls_6390_);
lean_dec(v_v_6384_);
v___x_6391_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6382_, v_l_6386_);
v___x_6392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6392_, 0, v_refs_6389_);
lean_ctor_set(v___x_6392_, 1, v_decls_6390_);
v___x_6393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6393_, 0, v_moduleUri_6388_);
lean_ctor_set(v___x_6393_, 1, v___x_6392_);
v___x_6394_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6385_, v___x_6393_, v___x_6391_);
v_init_6382_ = v___x_6394_;
v_x_6383_ = v_r_6387_;
goto _start;
}
else
{
return v_init_6382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6396_, lean_object* v_x_6397_){
_start:
{
if (lean_obj_tag(v_x_6397_) == 0)
{
lean_object* v_v_6398_; lean_object* v_k_6399_; lean_object* v_l_6400_; lean_object* v_r_6401_; lean_object* v_moduleUri_6402_; lean_object* v_refs_6403_; lean_object* v_decls_6404_; lean_object* v___x_6405_; uint8_t v___x_6406_; 
v_v_6398_ = lean_ctor_get(v_x_6397_, 2);
lean_inc(v_v_6398_);
v_k_6399_ = lean_ctor_get(v_x_6397_, 1);
lean_inc(v_k_6399_);
v_l_6400_ = lean_ctor_get(v_x_6397_, 3);
lean_inc(v_l_6400_);
v_r_6401_ = lean_ctor_get(v_x_6397_, 4);
lean_inc(v_r_6401_);
lean_dec_ref_known(v_x_6397_, 5);
v_moduleUri_6402_ = lean_ctor_get(v_v_6398_, 0);
lean_inc_ref(v_moduleUri_6402_);
v_refs_6403_ = lean_ctor_get(v_v_6398_, 4);
lean_inc(v_refs_6403_);
v_decls_6404_ = lean_ctor_get(v_v_6398_, 5);
lean_inc(v_decls_6404_);
v___x_6405_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6396_, v_l_6400_);
v___x_6406_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6398_);
lean_dec(v_v_6398_);
if (v___x_6406_ == 0)
{
lean_dec(v_decls_6404_);
lean_dec(v_refs_6403_);
lean_dec_ref(v_moduleUri_6402_);
lean_dec(v_k_6399_);
v_init_6396_ = v___x_6405_;
v_x_6397_ = v_r_6401_;
goto _start;
}
else
{
lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; 
v___x_6408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6408_, 0, v_refs_6403_);
lean_ctor_set(v___x_6408_, 1, v_decls_6404_);
v___x_6409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6409_, 0, v_moduleUri_6402_);
lean_ctor_set(v___x_6409_, 1, v___x_6408_);
v___x_6410_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6399_, v___x_6409_, v___x_6405_);
v_init_6396_ = v___x_6410_;
v_x_6397_ = v_r_6401_;
goto _start;
}
}
else
{
return v_init_6396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6412_){
_start:
{
lean_object* v_ileans_6413_; lean_object* v_workers_6414_; lean_object* v___x_6415_; lean_object* v_ileanRefs_6416_; lean_object* v___x_6417_; 
v_ileans_6413_ = lean_ctor_get(v_self_6412_, 0);
lean_inc(v_ileans_6413_);
v_workers_6414_ = lean_ctor_get(v_self_6412_, 1);
lean_inc(v_workers_6414_);
lean_dec_ref(v_self_6412_);
v___x_6415_ = lean_box(1);
v_ileanRefs_6416_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6415_, v_ileans_6413_);
v___x_6417_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6416_, v_workers_6414_);
return v___x_6417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6418_, lean_object* v_t_6419_){
_start:
{
lean_object* v___x_6420_; 
v___x_6420_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6418_, v_t_6419_);
return v___x_6420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6421_, lean_object* v_t_6422_){
_start:
{
lean_object* v___x_6423_; 
v___x_6423_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6421_, v_t_6422_);
return v___x_6423_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6424_, lean_object* v_x_6425_){
_start:
{
if (lean_obj_tag(v_x_6425_) == 0)
{
lean_object* v_k_6426_; lean_object* v_v_6427_; lean_object* v_l_6428_; lean_object* v_r_6429_; lean_object* v___x_6430_; lean_object* v_a_6431_; uint8_t v___x_6432_; 
v_k_6426_ = lean_ctor_get(v_x_6425_, 1);
lean_inc(v_k_6426_);
v_v_6427_ = lean_ctor_get(v_x_6425_, 2);
lean_inc(v_v_6427_);
v_l_6428_ = lean_ctor_get(v_x_6425_, 3);
lean_inc(v_l_6428_);
v_r_6429_ = lean_ctor_get(v_x_6425_, 4);
lean_inc(v_r_6429_);
lean_dec_ref_known(v_x_6425_, 5);
v___x_6430_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6424_, v_l_6428_);
v_a_6431_ = lean_ctor_get(v___x_6430_, 0);
lean_inc(v_a_6431_);
v___x_6432_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6427_);
if (v___x_6432_ == 0)
{
lean_object* v_a_6433_; 
lean_dec(v_a_6431_);
lean_dec(v_v_6427_);
lean_dec(v_k_6426_);
v_a_6433_ = lean_ctor_get(v___x_6430_, 0);
lean_inc(v_a_6433_);
lean_dec_ref(v___x_6430_);
v_init_6424_ = v_a_6433_;
v_x_6425_ = v_r_6429_;
goto _start;
}
else
{
lean_object* v_moduleUri_6435_; lean_object* v_directImports_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; 
lean_dec_ref(v___x_6430_);
v_moduleUri_6435_ = lean_ctor_get(v_v_6427_, 0);
lean_inc_ref(v_moduleUri_6435_);
v_directImports_6436_ = lean_ctor_get(v_v_6427_, 2);
lean_inc_ref(v_directImports_6436_);
lean_dec(v_v_6427_);
v___x_6437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6437_, 0, v_moduleUri_6435_);
lean_ctor_set(v___x_6437_, 1, v_directImports_6436_);
v___x_6438_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6426_, v___x_6437_, v_a_6431_);
v_init_6424_ = v___x_6438_;
v_x_6425_ = v_r_6429_;
goto _start;
}
}
else
{
lean_object* v___x_6440_; 
v___x_6440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6440_, 0, v_init_6424_);
return v___x_6440_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6441_, lean_object* v_x_6442_){
_start:
{
if (lean_obj_tag(v_x_6442_) == 0)
{
lean_object* v_k_6443_; lean_object* v_v_6444_; lean_object* v_l_6445_; lean_object* v_r_6446_; lean_object* v___x_6447_; lean_object* v_a_6448_; lean_object* v_moduleUri_6449_; lean_object* v_directImports_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; 
v_k_6443_ = lean_ctor_get(v_x_6442_, 1);
lean_inc(v_k_6443_);
v_v_6444_ = lean_ctor_get(v_x_6442_, 2);
lean_inc(v_v_6444_);
v_l_6445_ = lean_ctor_get(v_x_6442_, 3);
lean_inc(v_l_6445_);
v_r_6446_ = lean_ctor_get(v_x_6442_, 4);
lean_inc(v_r_6446_);
lean_dec_ref_known(v_x_6442_, 5);
v___x_6447_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6441_, v_l_6445_);
v_a_6448_ = lean_ctor_get(v___x_6447_, 0);
lean_inc(v_a_6448_);
lean_dec_ref(v___x_6447_);
v_moduleUri_6449_ = lean_ctor_get(v_v_6444_, 0);
lean_inc_ref(v_moduleUri_6449_);
v_directImports_6450_ = lean_ctor_get(v_v_6444_, 2);
lean_inc_ref(v_directImports_6450_);
lean_dec(v_v_6444_);
v___x_6451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6451_, 0, v_moduleUri_6449_);
lean_ctor_set(v___x_6451_, 1, v_directImports_6450_);
v___x_6452_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6443_, v___x_6451_, v_a_6448_);
v_init_6441_ = v___x_6452_;
v_x_6442_ = v_r_6446_;
goto _start;
}
else
{
lean_object* v___x_6454_; 
v___x_6454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6454_, 0, v_init_6441_);
return v___x_6454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6455_){
_start:
{
lean_object* v_ileans_6456_; lean_object* v_workers_6457_; lean_object* v___y_6459_; lean_object* v_allDirectImports_6462_; lean_object* v___x_6463_; lean_object* v_a_6464_; 
v_ileans_6456_ = lean_ctor_get(v_self_6455_, 0);
lean_inc(v_ileans_6456_);
v_workers_6457_ = lean_ctor_get(v_self_6455_, 1);
lean_inc(v_workers_6457_);
lean_dec_ref(v_self_6455_);
v_allDirectImports_6462_ = lean_box(1);
v___x_6463_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6462_, v_ileans_6456_);
v_a_6464_ = lean_ctor_get(v___x_6463_, 0);
lean_inc(v_a_6464_);
lean_dec_ref(v___x_6463_);
v___y_6459_ = v_a_6464_;
goto v___jp_6458_;
v___jp_6458_:
{
lean_object* v___x_6460_; lean_object* v_a_6461_; 
v___x_6460_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6459_, v_workers_6457_);
v_a_6461_ = lean_ctor_get(v___x_6460_, 0);
lean_inc(v_a_6461_);
lean_dec_ref(v___x_6460_);
return v_a_6461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6465_, lean_object* v_mod_6466_){
_start:
{
lean_object* v_ileans_6467_; lean_object* v_workers_6468_; lean_object* v___x_6470_; uint8_t v_isShared_6471_; uint8_t v_isSharedCheck_6505_; 
v_ileans_6467_ = lean_ctor_get(v_self_6465_, 0);
v_workers_6468_ = lean_ctor_get(v_self_6465_, 1);
v_isSharedCheck_6505_ = !lean_is_exclusive(v_self_6465_);
if (v_isSharedCheck_6505_ == 0)
{
v___x_6470_ = v_self_6465_;
v_isShared_6471_ = v_isSharedCheck_6505_;
goto v_resetjp_6469_;
}
else
{
lean_inc(v_workers_6468_);
lean_inc(v_ileans_6467_);
lean_dec(v_self_6465_);
v___x_6470_ = lean_box(0);
v_isShared_6471_ = v_isSharedCheck_6505_;
goto v_resetjp_6469_;
}
v_resetjp_6469_:
{
lean_object* v___x_6490_; 
v___x_6490_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6468_, v_mod_6466_);
lean_dec(v_workers_6468_);
if (lean_obj_tag(v___x_6490_) == 1)
{
lean_object* v_val_6491_; lean_object* v___x_6493_; uint8_t v_isShared_6494_; uint8_t v_isSharedCheck_6504_; 
v_val_6491_ = lean_ctor_get(v___x_6490_, 0);
v_isSharedCheck_6504_ = !lean_is_exclusive(v___x_6490_);
if (v_isSharedCheck_6504_ == 0)
{
v___x_6493_ = v___x_6490_;
v_isShared_6494_ = v_isSharedCheck_6504_;
goto v_resetjp_6492_;
}
else
{
lean_inc(v_val_6491_);
lean_dec(v___x_6490_);
v___x_6493_ = lean_box(0);
v_isShared_6494_ = v_isSharedCheck_6504_;
goto v_resetjp_6492_;
}
v_resetjp_6492_:
{
uint8_t v___x_6495_; 
v___x_6495_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6491_);
if (v___x_6495_ == 0)
{
lean_del_object(v___x_6493_);
lean_dec(v_val_6491_);
goto v___jp_6472_;
}
else
{
lean_object* v_moduleUri_6496_; lean_object* v_refs_6497_; lean_object* v_decls_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v___x_6502_; 
lean_del_object(v___x_6470_);
lean_dec(v_ileans_6467_);
v_moduleUri_6496_ = lean_ctor_get(v_val_6491_, 0);
lean_inc_ref(v_moduleUri_6496_);
v_refs_6497_ = lean_ctor_get(v_val_6491_, 4);
lean_inc(v_refs_6497_);
v_decls_6498_ = lean_ctor_get(v_val_6491_, 5);
lean_inc(v_decls_6498_);
lean_dec(v_val_6491_);
v___x_6499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6499_, 0, v_refs_6497_);
lean_ctor_set(v___x_6499_, 1, v_decls_6498_);
v___x_6500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6500_, 0, v_moduleUri_6496_);
lean_ctor_set(v___x_6500_, 1, v___x_6499_);
if (v_isShared_6494_ == 0)
{
lean_ctor_set(v___x_6493_, 0, v___x_6500_);
v___x_6502_ = v___x_6493_;
goto v_reusejp_6501_;
}
else
{
lean_object* v_reuseFailAlloc_6503_; 
v_reuseFailAlloc_6503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6503_, 0, v___x_6500_);
v___x_6502_ = v_reuseFailAlloc_6503_;
goto v_reusejp_6501_;
}
v_reusejp_6501_:
{
return v___x_6502_;
}
}
}
}
else
{
lean_dec(v___x_6490_);
goto v___jp_6472_;
}
v___jp_6472_:
{
lean_object* v___x_6473_; 
v___x_6473_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6467_, v_mod_6466_);
lean_dec(v_ileans_6467_);
if (lean_obj_tag(v___x_6473_) == 1)
{
lean_object* v_val_6474_; lean_object* v___x_6476_; uint8_t v_isShared_6477_; uint8_t v_isSharedCheck_6488_; 
v_val_6474_ = lean_ctor_get(v___x_6473_, 0);
v_isSharedCheck_6488_ = !lean_is_exclusive(v___x_6473_);
if (v_isSharedCheck_6488_ == 0)
{
v___x_6476_ = v___x_6473_;
v_isShared_6477_ = v_isSharedCheck_6488_;
goto v_resetjp_6475_;
}
else
{
lean_inc(v_val_6474_);
lean_dec(v___x_6473_);
v___x_6476_ = lean_box(0);
v_isShared_6477_ = v_isSharedCheck_6488_;
goto v_resetjp_6475_;
}
v_resetjp_6475_:
{
lean_object* v_moduleUri_6478_; lean_object* v_refs_6479_; lean_object* v_decls_6480_; lean_object* v___x_6482_; 
v_moduleUri_6478_ = lean_ctor_get(v_val_6474_, 0);
lean_inc_ref(v_moduleUri_6478_);
v_refs_6479_ = lean_ctor_get(v_val_6474_, 3);
lean_inc(v_refs_6479_);
v_decls_6480_ = lean_ctor_get(v_val_6474_, 4);
lean_inc(v_decls_6480_);
lean_dec(v_val_6474_);
if (v_isShared_6471_ == 0)
{
lean_ctor_set(v___x_6470_, 1, v_decls_6480_);
lean_ctor_set(v___x_6470_, 0, v_refs_6479_);
v___x_6482_ = v___x_6470_;
goto v_reusejp_6481_;
}
else
{
lean_object* v_reuseFailAlloc_6487_; 
v_reuseFailAlloc_6487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6487_, 0, v_refs_6479_);
lean_ctor_set(v_reuseFailAlloc_6487_, 1, v_decls_6480_);
v___x_6482_ = v_reuseFailAlloc_6487_;
goto v_reusejp_6481_;
}
v_reusejp_6481_:
{
lean_object* v___x_6483_; lean_object* v___x_6485_; 
v___x_6483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6483_, 0, v_moduleUri_6478_);
lean_ctor_set(v___x_6483_, 1, v___x_6482_);
if (v_isShared_6477_ == 0)
{
lean_ctor_set(v___x_6476_, 0, v___x_6483_);
v___x_6485_ = v___x_6476_;
goto v_reusejp_6484_;
}
else
{
lean_object* v_reuseFailAlloc_6486_; 
v_reuseFailAlloc_6486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6486_, 0, v___x_6483_);
v___x_6485_ = v_reuseFailAlloc_6486_;
goto v_reusejp_6484_;
}
v_reusejp_6484_:
{
return v___x_6485_;
}
}
}
}
else
{
lean_object* v___x_6489_; 
lean_dec(v___x_6473_);
lean_del_object(v___x_6470_);
v___x_6489_ = lean_box(0);
return v___x_6489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6506_, lean_object* v_mod_6507_){
_start:
{
lean_object* v_res_6508_; 
v_res_6508_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6506_, v_mod_6507_);
lean_dec(v_mod_6507_);
return v_res_6508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6509_, lean_object* v_mod_6510_){
_start:
{
lean_object* v_ileans_6511_; lean_object* v_workers_6512_; lean_object* v___x_6525_; 
v_ileans_6511_ = lean_ctor_get(v_self_6509_, 0);
v_workers_6512_ = lean_ctor_get(v_self_6509_, 1);
v___x_6525_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6512_, v_mod_6510_);
if (lean_obj_tag(v___x_6525_) == 1)
{
lean_object* v_val_6526_; lean_object* v___x_6528_; uint8_t v_isShared_6529_; uint8_t v_isSharedCheck_6535_; 
v_val_6526_ = lean_ctor_get(v___x_6525_, 0);
v_isSharedCheck_6535_ = !lean_is_exclusive(v___x_6525_);
if (v_isSharedCheck_6535_ == 0)
{
v___x_6528_ = v___x_6525_;
v_isShared_6529_ = v_isSharedCheck_6535_;
goto v_resetjp_6527_;
}
else
{
lean_inc(v_val_6526_);
lean_dec(v___x_6525_);
v___x_6528_ = lean_box(0);
v_isShared_6529_ = v_isSharedCheck_6535_;
goto v_resetjp_6527_;
}
v_resetjp_6527_:
{
uint8_t v___x_6530_; 
v___x_6530_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6526_);
if (v___x_6530_ == 0)
{
lean_del_object(v___x_6528_);
lean_dec(v_val_6526_);
goto v___jp_6513_;
}
else
{
lean_object* v_directImports_6531_; lean_object* v___x_6533_; 
v_directImports_6531_ = lean_ctor_get(v_val_6526_, 2);
lean_inc_ref(v_directImports_6531_);
lean_dec(v_val_6526_);
if (v_isShared_6529_ == 0)
{
lean_ctor_set(v___x_6528_, 0, v_directImports_6531_);
v___x_6533_ = v___x_6528_;
goto v_reusejp_6532_;
}
else
{
lean_object* v_reuseFailAlloc_6534_; 
v_reuseFailAlloc_6534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6534_, 0, v_directImports_6531_);
v___x_6533_ = v_reuseFailAlloc_6534_;
goto v_reusejp_6532_;
}
v_reusejp_6532_:
{
return v___x_6533_;
}
}
}
}
else
{
lean_dec(v___x_6525_);
goto v___jp_6513_;
}
v___jp_6513_:
{
lean_object* v___x_6514_; 
v___x_6514_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6511_, v_mod_6510_);
if (lean_obj_tag(v___x_6514_) == 1)
{
lean_object* v_val_6515_; lean_object* v___x_6517_; uint8_t v_isShared_6518_; uint8_t v_isSharedCheck_6523_; 
v_val_6515_ = lean_ctor_get(v___x_6514_, 0);
v_isSharedCheck_6523_ = !lean_is_exclusive(v___x_6514_);
if (v_isSharedCheck_6523_ == 0)
{
v___x_6517_ = v___x_6514_;
v_isShared_6518_ = v_isSharedCheck_6523_;
goto v_resetjp_6516_;
}
else
{
lean_inc(v_val_6515_);
lean_dec(v___x_6514_);
v___x_6517_ = lean_box(0);
v_isShared_6518_ = v_isSharedCheck_6523_;
goto v_resetjp_6516_;
}
v_resetjp_6516_:
{
lean_object* v_directImports_6519_; lean_object* v___x_6521_; 
v_directImports_6519_ = lean_ctor_get(v_val_6515_, 2);
lean_inc_ref(v_directImports_6519_);
lean_dec(v_val_6515_);
if (v_isShared_6518_ == 0)
{
lean_ctor_set(v___x_6517_, 0, v_directImports_6519_);
v___x_6521_ = v___x_6517_;
goto v_reusejp_6520_;
}
else
{
lean_object* v_reuseFailAlloc_6522_; 
v_reuseFailAlloc_6522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6522_, 0, v_directImports_6519_);
v___x_6521_ = v_reuseFailAlloc_6522_;
goto v_reusejp_6520_;
}
v_reusejp_6520_:
{
return v___x_6521_;
}
}
}
else
{
lean_object* v___x_6524_; 
lean_dec(v___x_6514_);
v___x_6524_ = lean_box(0);
return v___x_6524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6536_, lean_object* v_mod_6537_){
_start:
{
lean_object* v_res_6538_; 
v_res_6538_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6536_, v_mod_6537_);
lean_dec(v_mod_6537_);
lean_dec_ref(v_self_6536_);
return v_res_6538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6539_, lean_object* v_mod_6540_){
_start:
{
lean_object* v_ileans_6541_; lean_object* v_workers_6542_; lean_object* v___x_6555_; 
v_ileans_6541_ = lean_ctor_get(v_self_6539_, 0);
v_workers_6542_ = lean_ctor_get(v_self_6539_, 1);
v___x_6555_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6542_, v_mod_6540_);
if (lean_obj_tag(v___x_6555_) == 1)
{
lean_object* v_val_6556_; lean_object* v___x_6558_; uint8_t v_isShared_6559_; uint8_t v_isSharedCheck_6565_; 
v_val_6556_ = lean_ctor_get(v___x_6555_, 0);
v_isSharedCheck_6565_ = !lean_is_exclusive(v___x_6555_);
if (v_isSharedCheck_6565_ == 0)
{
v___x_6558_ = v___x_6555_;
v_isShared_6559_ = v_isSharedCheck_6565_;
goto v_resetjp_6557_;
}
else
{
lean_inc(v_val_6556_);
lean_dec(v___x_6555_);
v___x_6558_ = lean_box(0);
v_isShared_6559_ = v_isSharedCheck_6565_;
goto v_resetjp_6557_;
}
v_resetjp_6557_:
{
uint8_t v___x_6560_; 
v___x_6560_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6556_);
if (v___x_6560_ == 0)
{
lean_del_object(v___x_6558_);
lean_dec(v_val_6556_);
goto v___jp_6543_;
}
else
{
lean_object* v_decls_6561_; lean_object* v___x_6563_; 
v_decls_6561_ = lean_ctor_get(v_val_6556_, 5);
lean_inc(v_decls_6561_);
lean_dec(v_val_6556_);
if (v_isShared_6559_ == 0)
{
lean_ctor_set(v___x_6558_, 0, v_decls_6561_);
v___x_6563_ = v___x_6558_;
goto v_reusejp_6562_;
}
else
{
lean_object* v_reuseFailAlloc_6564_; 
v_reuseFailAlloc_6564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6564_, 0, v_decls_6561_);
v___x_6563_ = v_reuseFailAlloc_6564_;
goto v_reusejp_6562_;
}
v_reusejp_6562_:
{
return v___x_6563_;
}
}
}
}
else
{
lean_dec(v___x_6555_);
goto v___jp_6543_;
}
v___jp_6543_:
{
lean_object* v___x_6544_; 
v___x_6544_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6541_, v_mod_6540_);
if (lean_obj_tag(v___x_6544_) == 1)
{
lean_object* v_val_6545_; lean_object* v___x_6547_; uint8_t v_isShared_6548_; uint8_t v_isSharedCheck_6553_; 
v_val_6545_ = lean_ctor_get(v___x_6544_, 0);
v_isSharedCheck_6553_ = !lean_is_exclusive(v___x_6544_);
if (v_isSharedCheck_6553_ == 0)
{
v___x_6547_ = v___x_6544_;
v_isShared_6548_ = v_isSharedCheck_6553_;
goto v_resetjp_6546_;
}
else
{
lean_inc(v_val_6545_);
lean_dec(v___x_6544_);
v___x_6547_ = lean_box(0);
v_isShared_6548_ = v_isSharedCheck_6553_;
goto v_resetjp_6546_;
}
v_resetjp_6546_:
{
lean_object* v_decls_6549_; lean_object* v___x_6551_; 
v_decls_6549_ = lean_ctor_get(v_val_6545_, 4);
lean_inc(v_decls_6549_);
lean_dec(v_val_6545_);
if (v_isShared_6548_ == 0)
{
lean_ctor_set(v___x_6547_, 0, v_decls_6549_);
v___x_6551_ = v___x_6547_;
goto v_reusejp_6550_;
}
else
{
lean_object* v_reuseFailAlloc_6552_; 
v_reuseFailAlloc_6552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6552_, 0, v_decls_6549_);
v___x_6551_ = v_reuseFailAlloc_6552_;
goto v_reusejp_6550_;
}
v_reusejp_6550_:
{
return v___x_6551_;
}
}
}
else
{
lean_object* v___x_6554_; 
lean_dec(v___x_6544_);
v___x_6554_ = lean_box(0);
return v___x_6554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6566_, lean_object* v_mod_6567_){
_start:
{
lean_object* v_res_6568_; 
v_res_6568_ = l_Lean_Server_References_getDecls_x3f(v_self_6566_, v_mod_6567_);
lean_dec(v_mod_6567_);
lean_dec_ref(v_self_6566_);
return v_res_6568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6569_, lean_object* v_x_6570_){
_start:
{
if (lean_obj_tag(v_x_6570_) == 0)
{
lean_object* v_k_6571_; lean_object* v_v_6572_; lean_object* v_l_6573_; lean_object* v_r_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; 
v_k_6571_ = lean_ctor_get(v_x_6570_, 1);
v_v_6572_ = lean_ctor_get(v_x_6570_, 2);
v_l_6573_ = lean_ctor_get(v_x_6570_, 3);
v_r_6574_ = lean_ctor_get(v_x_6570_, 4);
v___x_6575_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6569_, v_l_6573_);
lean_inc(v_v_6572_);
lean_inc(v_k_6571_);
v___x_6576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6576_, 0, v_k_6571_);
lean_ctor_set(v___x_6576_, 1, v_v_6572_);
v___x_6577_ = lean_array_push(v___x_6575_, v___x_6576_);
v_init_6569_ = v___x_6577_;
v_x_6570_ = v_r_6574_;
goto _start;
}
else
{
return v_init_6569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6579_, lean_object* v_x_6580_){
_start:
{
lean_object* v_res_6581_; 
v_res_6581_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6579_, v_x_6580_);
lean_dec(v_x_6580_);
return v_res_6581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6582_, lean_object* v_k_6583_){
_start:
{
if (lean_obj_tag(v_t_6582_) == 0)
{
lean_object* v_k_6584_; lean_object* v_v_6585_; lean_object* v_l_6586_; lean_object* v_r_6587_; uint8_t v___x_6588_; 
v_k_6584_ = lean_ctor_get(v_t_6582_, 1);
v_v_6585_ = lean_ctor_get(v_t_6582_, 2);
v_l_6586_ = lean_ctor_get(v_t_6582_, 3);
v_r_6587_ = lean_ctor_get(v_t_6582_, 4);
v___x_6588_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6583_, v_k_6584_);
switch(v___x_6588_)
{
case 0:
{
v_t_6582_ = v_l_6586_;
goto _start;
}
case 1:
{
lean_object* v___x_6590_; 
lean_inc(v_v_6585_);
v___x_6590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6590_, 0, v_v_6585_);
return v___x_6590_;
}
default: 
{
v_t_6582_ = v_r_6587_;
goto _start;
}
}
}
else
{
lean_object* v___x_6592_; 
v___x_6592_ = lean_box(0);
return v___x_6592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6593_, lean_object* v_k_6594_){
_start:
{
lean_object* v_res_6595_; 
v_res_6595_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6593_, v_k_6594_);
lean_dec_ref(v_k_6594_);
lean_dec(v_t_6593_);
return v_res_6595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6596_, lean_object* v_as_6597_, size_t v_sz_6598_, size_t v_i_6599_, lean_object* v_b_6600_){
_start:
{
lean_object* v_a_6602_; uint8_t v___x_6606_; 
v___x_6606_ = lean_usize_dec_lt(v_i_6599_, v_sz_6598_);
if (v___x_6606_ == 0)
{
return v_b_6600_;
}
else
{
lean_object* v_a_6607_; lean_object* v_snd_6608_; lean_object* v_snd_6609_; lean_object* v_fst_6610_; lean_object* v___x_6612_; uint8_t v_isShared_6613_; uint8_t v_isSharedCheck_6638_; 
v_a_6607_ = lean_array_uget(v_as_6597_, v_i_6599_);
v_snd_6608_ = lean_ctor_get(v_a_6607_, 1);
lean_inc(v_snd_6608_);
v_snd_6609_ = lean_ctor_get(v_snd_6608_, 1);
lean_inc(v_snd_6609_);
v_fst_6610_ = lean_ctor_get(v_a_6607_, 0);
v_isSharedCheck_6638_ = !lean_is_exclusive(v_a_6607_);
if (v_isSharedCheck_6638_ == 0)
{
lean_object* v_unused_6639_; 
v_unused_6639_ = lean_ctor_get(v_a_6607_, 1);
lean_dec(v_unused_6639_);
v___x_6612_ = v_a_6607_;
v_isShared_6613_ = v_isSharedCheck_6638_;
goto v_resetjp_6611_;
}
else
{
lean_inc(v_fst_6610_);
lean_dec(v_a_6607_);
v___x_6612_ = lean_box(0);
v_isShared_6613_ = v_isSharedCheck_6638_;
goto v_resetjp_6611_;
}
v_resetjp_6611_:
{
lean_object* v_fst_6614_; lean_object* v___x_6616_; uint8_t v_isShared_6617_; uint8_t v_isSharedCheck_6636_; 
v_fst_6614_ = lean_ctor_get(v_snd_6608_, 0);
v_isSharedCheck_6636_ = !lean_is_exclusive(v_snd_6608_);
if (v_isSharedCheck_6636_ == 0)
{
lean_object* v_unused_6637_; 
v_unused_6637_ = lean_ctor_get(v_snd_6608_, 1);
lean_dec(v_unused_6637_);
v___x_6616_ = v_snd_6608_;
v_isShared_6617_ = v_isSharedCheck_6636_;
goto v_resetjp_6615_;
}
else
{
lean_inc(v_fst_6614_);
lean_dec(v_snd_6608_);
v___x_6616_ = lean_box(0);
v_isShared_6617_ = v_isSharedCheck_6636_;
goto v_resetjp_6615_;
}
v_resetjp_6615_:
{
lean_object* v_fst_6618_; lean_object* v_snd_6619_; lean_object* v___x_6621_; uint8_t v_isShared_6622_; uint8_t v_isSharedCheck_6635_; 
v_fst_6618_ = lean_ctor_get(v_snd_6609_, 0);
v_snd_6619_ = lean_ctor_get(v_snd_6609_, 1);
v_isSharedCheck_6635_ = !lean_is_exclusive(v_snd_6609_);
if (v_isSharedCheck_6635_ == 0)
{
v___x_6621_ = v_snd_6609_;
v_isShared_6622_ = v_isSharedCheck_6635_;
goto v_resetjp_6620_;
}
else
{
lean_inc(v_snd_6619_);
lean_inc(v_fst_6618_);
lean_dec(v_snd_6609_);
v___x_6621_ = lean_box(0);
v_isShared_6622_ = v_isSharedCheck_6635_;
goto v_resetjp_6620_;
}
v_resetjp_6620_:
{
lean_object* v___x_6623_; 
v___x_6623_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6618_, v_ident_6596_);
lean_dec(v_fst_6618_);
if (lean_obj_tag(v___x_6623_) == 1)
{
lean_object* v_val_6624_; lean_object* v___x_6626_; 
v_val_6624_ = lean_ctor_get(v___x_6623_, 0);
lean_inc(v_val_6624_);
lean_dec_ref_known(v___x_6623_, 1);
if (v_isShared_6622_ == 0)
{
lean_ctor_set(v___x_6621_, 0, v_val_6624_);
v___x_6626_ = v___x_6621_;
goto v_reusejp_6625_;
}
else
{
lean_object* v_reuseFailAlloc_6634_; 
v_reuseFailAlloc_6634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6634_, 0, v_val_6624_);
lean_ctor_set(v_reuseFailAlloc_6634_, 1, v_snd_6619_);
v___x_6626_ = v_reuseFailAlloc_6634_;
goto v_reusejp_6625_;
}
v_reusejp_6625_:
{
lean_object* v___x_6628_; 
if (v_isShared_6617_ == 0)
{
lean_ctor_set(v___x_6616_, 1, v___x_6626_);
lean_ctor_set(v___x_6616_, 0, v_fst_6610_);
v___x_6628_ = v___x_6616_;
goto v_reusejp_6627_;
}
else
{
lean_object* v_reuseFailAlloc_6633_; 
v_reuseFailAlloc_6633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6633_, 0, v_fst_6610_);
lean_ctor_set(v_reuseFailAlloc_6633_, 1, v___x_6626_);
v___x_6628_ = v_reuseFailAlloc_6633_;
goto v_reusejp_6627_;
}
v_reusejp_6627_:
{
lean_object* v___x_6630_; 
if (v_isShared_6613_ == 0)
{
lean_ctor_set(v___x_6612_, 1, v___x_6628_);
lean_ctor_set(v___x_6612_, 0, v_fst_6614_);
v___x_6630_ = v___x_6612_;
goto v_reusejp_6629_;
}
else
{
lean_object* v_reuseFailAlloc_6632_; 
v_reuseFailAlloc_6632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6632_, 0, v_fst_6614_);
lean_ctor_set(v_reuseFailAlloc_6632_, 1, v___x_6628_);
v___x_6630_ = v_reuseFailAlloc_6632_;
goto v_reusejp_6629_;
}
v_reusejp_6629_:
{
lean_object* v___x_6631_; 
v___x_6631_ = lean_array_push(v_b_6600_, v___x_6630_);
v_a_6602_ = v___x_6631_;
goto v___jp_6601_;
}
}
}
}
else
{
lean_dec(v___x_6623_);
lean_del_object(v___x_6621_);
lean_dec(v_snd_6619_);
lean_del_object(v___x_6616_);
lean_dec(v_fst_6614_);
lean_del_object(v___x_6612_);
lean_dec(v_fst_6610_);
v_a_6602_ = v_b_6600_;
goto v___jp_6601_;
}
}
}
}
}
v___jp_6601_:
{
size_t v___x_6603_; size_t v___x_6604_; 
v___x_6603_ = ((size_t)1ULL);
v___x_6604_ = lean_usize_add(v_i_6599_, v___x_6603_);
v_i_6599_ = v___x_6604_;
v_b_6600_ = v_a_6602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6640_, lean_object* v_as_6641_, lean_object* v_sz_6642_, lean_object* v_i_6643_, lean_object* v_b_6644_){
_start:
{
size_t v_sz_boxed_6645_; size_t v_i_boxed_6646_; lean_object* v_res_6647_; 
v_sz_boxed_6645_ = lean_unbox_usize(v_sz_6642_);
lean_dec(v_sz_6642_);
v_i_boxed_6646_ = lean_unbox_usize(v_i_6643_);
lean_dec(v_i_6643_);
v_res_6647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6640_, v_as_6641_, v_sz_boxed_6645_, v_i_boxed_6646_, v_b_6644_);
lean_dec_ref(v_as_6641_);
lean_dec_ref(v_ident_6640_);
return v_res_6647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6654_, lean_object* v_ident_6655_){
_start:
{
lean_object* v___y_6657_; 
if (lean_obj_tag(v_ident_6655_) == 0)
{
lean_object* v___x_6662_; lean_object* v___x_6663_; lean_object* v___x_6664_; 
v___x_6662_ = l_Lean_Server_References_allRefs(v_self_6654_);
v___x_6663_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6664_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6663_, v___x_6662_);
lean_dec(v___x_6662_);
v___y_6657_ = v___x_6664_;
goto v___jp_6656_;
}
else
{
lean_object* v_moduleName_6665_; lean_object* v_identModuleName_6666_; lean_object* v___x_6667_; 
v_moduleName_6665_ = lean_ctor_get(v_ident_6655_, 0);
lean_inc_ref(v_moduleName_6665_);
v_identModuleName_6666_ = l_String_toName(v_moduleName_6665_);
v___x_6667_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6654_, v_identModuleName_6666_);
if (lean_obj_tag(v___x_6667_) == 0)
{
lean_object* v___x_6668_; 
lean_dec(v_identModuleName_6666_);
v___x_6668_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6657_ = v___x_6668_;
goto v___jp_6656_;
}
else
{
lean_object* v_val_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; 
v_val_6669_ = lean_ctor_get(v___x_6667_, 0);
lean_inc(v_val_6669_);
lean_dec_ref_known(v___x_6667_, 1);
v___x_6670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6670_, 0, v_identModuleName_6666_);
lean_ctor_set(v___x_6670_, 1, v_val_6669_);
v___x_6671_ = lean_unsigned_to_nat(1u);
v___x_6672_ = lean_mk_empty_array_with_capacity(v___x_6671_);
v___x_6673_ = lean_array_push(v___x_6672_, v___x_6670_);
v___y_6657_ = v___x_6673_;
goto v___jp_6656_;
}
}
v___jp_6656_:
{
lean_object* v_result_6658_; size_t v_sz_6659_; size_t v___x_6660_; lean_object* v___x_6661_; 
v_result_6658_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6659_ = lean_array_size(v___y_6657_);
v___x_6660_ = ((size_t)0ULL);
v___x_6661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6655_, v___y_6657_, v_sz_6659_, v___x_6660_, v_result_6658_);
lean_dec_ref(v___y_6657_);
lean_dec_ref(v_ident_6655_);
return v___x_6661_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6674_, lean_object* v_t_6675_, lean_object* v_k_6676_){
_start:
{
lean_object* v___x_6677_; 
v___x_6677_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6675_, v_k_6676_);
return v___x_6677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6678_, lean_object* v_t_6679_, lean_object* v_k_6680_){
_start:
{
lean_object* v_res_6681_; 
v_res_6681_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6678_, v_t_6679_, v_k_6680_);
lean_dec_ref(v_k_6680_);
lean_dec(v_t_6679_);
return v_res_6681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6682_, lean_object* v_t_6683_){
_start:
{
lean_object* v___x_6684_; 
v___x_6684_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6682_, v_t_6683_);
return v___x_6684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6685_, lean_object* v_t_6686_){
_start:
{
lean_object* v_res_6687_; 
v_res_6687_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6685_, v_t_6686_);
lean_dec(v_t_6686_);
return v_res_6687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6688_, lean_object* v_module_6689_, lean_object* v_pos_6690_, uint8_t v_includeStop_6691_){
_start:
{
lean_object* v___x_6692_; 
v___x_6692_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6688_, v_module_6689_);
if (lean_obj_tag(v___x_6692_) == 1)
{
lean_object* v_val_6693_; lean_object* v_snd_6694_; lean_object* v_fst_6695_; lean_object* v___x_6696_; 
v_val_6693_ = lean_ctor_get(v___x_6692_, 0);
lean_inc(v_val_6693_);
lean_dec_ref_known(v___x_6692_, 1);
v_snd_6694_ = lean_ctor_get(v_val_6693_, 1);
lean_inc(v_snd_6694_);
lean_dec(v_val_6693_);
v_fst_6695_ = lean_ctor_get(v_snd_6694_, 0);
lean_inc(v_fst_6695_);
lean_dec(v_snd_6694_);
v___x_6696_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6695_, v_pos_6690_, v_includeStop_6691_);
return v___x_6696_;
}
else
{
lean_object* v___x_6697_; 
lean_dec(v___x_6692_);
v___x_6697_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6698_, lean_object* v_module_6699_, lean_object* v_pos_6700_, lean_object* v_includeStop_6701_){
_start:
{
uint8_t v_includeStop_boxed_6702_; lean_object* v_res_6703_; 
v_includeStop_boxed_6702_ = lean_unbox(v_includeStop_6701_);
v_res_6703_ = l_Lean_Server_References_findAt(v_self_6698_, v_module_6699_, v_pos_6700_, v_includeStop_boxed_6702_);
lean_dec_ref(v_pos_6700_);
lean_dec(v_module_6699_);
return v_res_6703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6704_, lean_object* v_module_6705_, lean_object* v_pos_6706_, uint8_t v_includeStop_6707_){
_start:
{
lean_object* v___x_6708_; 
v___x_6708_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6704_, v_module_6705_);
if (lean_obj_tag(v___x_6708_) == 0)
{
lean_object* v___x_6709_; 
v___x_6709_ = lean_box(0);
return v___x_6709_;
}
else
{
lean_object* v_val_6710_; lean_object* v_snd_6711_; lean_object* v_fst_6712_; lean_object* v___x_6713_; 
v_val_6710_ = lean_ctor_get(v___x_6708_, 0);
lean_inc(v_val_6710_);
lean_dec_ref_known(v___x_6708_, 1);
v_snd_6711_ = lean_ctor_get(v_val_6710_, 1);
lean_inc(v_snd_6711_);
lean_dec(v_val_6710_);
v_fst_6712_ = lean_ctor_get(v_snd_6711_, 0);
lean_inc(v_fst_6712_);
lean_dec(v_snd_6711_);
v___x_6713_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6712_, v_pos_6706_, v_includeStop_6707_);
lean_dec(v_fst_6712_);
return v___x_6713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6714_, lean_object* v_module_6715_, lean_object* v_pos_6716_, lean_object* v_includeStop_6717_){
_start:
{
uint8_t v_includeStop_boxed_6718_; lean_object* v_res_6719_; 
v_includeStop_boxed_6718_ = lean_unbox(v_includeStop_6717_);
v_res_6719_ = l_Lean_Server_References_findRange_x3f(v_self_6714_, v_module_6715_, v_pos_6716_, v_includeStop_boxed_6718_);
lean_dec_ref(v_pos_6716_);
lean_dec(v_module_6715_);
return v_res_6719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6720_, lean_object* v_k_6721_){
_start:
{
if (lean_obj_tag(v_t_6720_) == 0)
{
lean_object* v_k_6722_; lean_object* v_v_6723_; lean_object* v_l_6724_; lean_object* v_r_6725_; uint8_t v___x_6726_; 
v_k_6722_ = lean_ctor_get(v_t_6720_, 1);
v_v_6723_ = lean_ctor_get(v_t_6720_, 2);
v_l_6724_ = lean_ctor_get(v_t_6720_, 3);
v_r_6725_ = lean_ctor_get(v_t_6720_, 4);
v___x_6726_ = lean_string_compare(v_k_6721_, v_k_6722_);
switch(v___x_6726_)
{
case 0:
{
v_t_6720_ = v_l_6724_;
goto _start;
}
case 1:
{
lean_object* v___x_6728_; 
lean_inc(v_v_6723_);
v___x_6728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6728_, 0, v_v_6723_);
return v___x_6728_;
}
default: 
{
v_t_6720_ = v_r_6725_;
goto _start;
}
}
}
else
{
lean_object* v___x_6730_; 
v___x_6730_ = lean_box(0);
return v___x_6730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6731_, lean_object* v_k_6732_){
_start:
{
lean_object* v_res_6733_; 
v_res_6733_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6731_, v_k_6732_);
lean_dec_ref(v_k_6732_);
lean_dec(v_t_6731_);
return v_res_6733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6734_, lean_object* v_name_6735_){
_start:
{
lean_object* v___x_6736_; 
v___x_6736_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6734_, v_name_6735_);
if (lean_obj_tag(v___x_6736_) == 0)
{
lean_object* v___x_6737_; 
lean_dec_ref(v_name_6735_);
v___x_6737_ = lean_box(0);
return v___x_6737_;
}
else
{
lean_object* v_val_6738_; lean_object* v___x_6740_; uint8_t v_isShared_6741_; uint8_t v_isSharedCheck_6748_; 
v_val_6738_ = lean_ctor_get(v___x_6736_, 0);
v_isSharedCheck_6748_ = !lean_is_exclusive(v___x_6736_);
if (v_isSharedCheck_6748_ == 0)
{
v___x_6740_ = v___x_6736_;
v_isShared_6741_ = v_isSharedCheck_6748_;
goto v_resetjp_6739_;
}
else
{
lean_inc(v_val_6738_);
lean_dec(v___x_6736_);
v___x_6740_ = lean_box(0);
v_isShared_6741_ = v_isSharedCheck_6748_;
goto v_resetjp_6739_;
}
v_resetjp_6739_:
{
lean_object* v___x_6742_; lean_object* v___x_6743_; lean_object* v___x_6744_; lean_object* v___x_6746_; 
v___x_6742_ = l_Lean_Lsp_DeclInfo_range(v_val_6738_);
v___x_6743_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6738_);
lean_dec(v_val_6738_);
v___x_6744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6744_, 0, v_name_6735_);
lean_ctor_set(v___x_6744_, 1, v___x_6742_);
lean_ctor_set(v___x_6744_, 2, v___x_6743_);
if (v_isShared_6741_ == 0)
{
lean_ctor_set(v___x_6740_, 0, v___x_6744_);
v___x_6746_ = v___x_6740_;
goto v_reusejp_6745_;
}
else
{
lean_object* v_reuseFailAlloc_6747_; 
v_reuseFailAlloc_6747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6747_, 0, v___x_6744_);
v___x_6746_ = v_reuseFailAlloc_6747_;
goto v_reusejp_6745_;
}
v_reusejp_6745_:
{
return v___x_6746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6749_, lean_object* v_name_6750_){
_start:
{
lean_object* v_res_6751_; 
v_res_6751_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6749_, v_name_6750_);
lean_dec(v_ds_6749_);
return v_res_6751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6752_, lean_object* v_t_6753_, lean_object* v_k_6754_){
_start:
{
lean_object* v___x_6755_; 
v___x_6755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6753_, v_k_6754_);
return v___x_6755_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6756_, lean_object* v_t_6757_, lean_object* v_k_6758_){
_start:
{
lean_object* v_res_6759_; 
v_res_6759_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6756_, v_t_6757_, v_k_6758_);
lean_dec_ref(v_k_6758_);
lean_dec(v_t_6757_);
return v_res_6759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6760_, lean_object* v_fst_6761_, lean_object* v_snd_6762_, lean_object* v_as_6763_, size_t v_sz_6764_, size_t v_i_6765_, lean_object* v_b_6766_){
_start:
{
uint8_t v___x_6767_; 
v___x_6767_ = lean_usize_dec_lt(v_i_6765_, v_sz_6764_);
if (v___x_6767_ == 0)
{
lean_dec(v_fst_6761_);
lean_dec_ref(v_fst_6760_);
return v_b_6766_;
}
else
{
lean_object* v_a_6768_; lean_object* v___y_6770_; lean_object* v___x_6778_; 
v_a_6768_ = lean_array_uget_borrowed(v_as_6763_, v_i_6765_);
v___x_6778_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6768_);
if (lean_obj_tag(v___x_6778_) == 0)
{
lean_object* v___x_6779_; 
v___x_6779_ = lean_box(0);
v___y_6770_ = v___x_6779_;
goto v___jp_6769_;
}
else
{
lean_object* v_val_6780_; lean_object* v___x_6781_; 
v_val_6780_ = lean_ctor_get(v___x_6778_, 0);
lean_inc(v_val_6780_);
lean_dec_ref_known(v___x_6778_, 1);
v___x_6781_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6762_, v_val_6780_);
v___y_6770_ = v___x_6781_;
goto v___jp_6769_;
}
v___jp_6769_:
{
lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; size_t v___x_6775_; size_t v___x_6776_; 
v___x_6771_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6768_);
lean_inc_ref(v_fst_6760_);
v___x_6772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6772_, 0, v_fst_6760_);
lean_ctor_set(v___x_6772_, 1, v___x_6771_);
lean_inc(v_fst_6761_);
v___x_6773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6773_, 0, v___x_6772_);
lean_ctor_set(v___x_6773_, 1, v_fst_6761_);
lean_ctor_set(v___x_6773_, 2, v___y_6770_);
v___x_6774_ = lean_array_push(v_b_6766_, v___x_6773_);
v___x_6775_ = ((size_t)1ULL);
v___x_6776_ = lean_usize_add(v_i_6765_, v___x_6775_);
v_i_6765_ = v___x_6776_;
v_b_6766_ = v___x_6774_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6782_, lean_object* v_fst_6783_, lean_object* v_snd_6784_, lean_object* v_as_6785_, lean_object* v_sz_6786_, lean_object* v_i_6787_, lean_object* v_b_6788_){
_start:
{
size_t v_sz_boxed_6789_; size_t v_i_boxed_6790_; lean_object* v_res_6791_; 
v_sz_boxed_6789_ = lean_unbox_usize(v_sz_6786_);
lean_dec(v_sz_6786_);
v_i_boxed_6790_ = lean_unbox_usize(v_i_6787_);
lean_dec(v_i_6787_);
v_res_6791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6782_, v_fst_6783_, v_snd_6784_, v_as_6785_, v_sz_boxed_6789_, v_i_boxed_6790_, v_b_6788_);
lean_dec_ref(v_as_6785_);
lean_dec(v_snd_6784_);
return v_res_6791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6792_, lean_object* v_as_6793_, size_t v_sz_6794_, size_t v_i_6795_, lean_object* v_b_6796_){
_start:
{
uint8_t v___x_6797_; 
v___x_6797_ = lean_usize_dec_lt(v_i_6795_, v_sz_6794_);
if (v___x_6797_ == 0)
{
return v_b_6796_;
}
else
{
lean_object* v_a_6798_; lean_object* v_snd_6799_; lean_object* v_snd_6800_; lean_object* v_fst_6801_; lean_object* v_fst_6802_; lean_object* v_fst_6803_; lean_object* v_snd_6804_; lean_object* v___x_6806_; uint8_t v_isShared_6807_; uint8_t v_isSharedCheck_6831_; 
v_a_6798_ = lean_array_uget_borrowed(v_as_6793_, v_i_6795_);
v_snd_6799_ = lean_ctor_get(v_a_6798_, 1);
v_snd_6800_ = lean_ctor_get(v_snd_6799_, 1);
lean_inc(v_snd_6800_);
v_fst_6801_ = lean_ctor_get(v_a_6798_, 0);
v_fst_6802_ = lean_ctor_get(v_snd_6799_, 0);
v_fst_6803_ = lean_ctor_get(v_snd_6800_, 0);
v_snd_6804_ = lean_ctor_get(v_snd_6800_, 1);
v_isSharedCheck_6831_ = !lean_is_exclusive(v_snd_6800_);
if (v_isSharedCheck_6831_ == 0)
{
v___x_6806_ = v_snd_6800_;
v_isShared_6807_ = v_isSharedCheck_6831_;
goto v_resetjp_6805_;
}
else
{
lean_inc(v_snd_6804_);
lean_inc(v_fst_6803_);
lean_dec(v_snd_6800_);
v___x_6806_ = lean_box(0);
v_isShared_6807_ = v_isSharedCheck_6831_;
goto v_resetjp_6805_;
}
v_resetjp_6805_:
{
lean_object* v_result_6809_; 
if (v_includeDefinition_6792_ == 0)
{
lean_del_object(v___x_6806_);
v_result_6809_ = v_b_6796_;
goto v___jp_6808_;
}
else
{
lean_object* v_definition_x3f_6817_; 
v_definition_x3f_6817_ = lean_ctor_get(v_fst_6803_, 0);
if (lean_obj_tag(v_definition_x3f_6817_) == 1)
{
lean_object* v_val_6818_; lean_object* v___y_6820_; lean_object* v___x_6827_; 
v_val_6818_ = lean_ctor_get(v_definition_x3f_6817_, 0);
v___x_6827_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6818_);
if (lean_obj_tag(v___x_6827_) == 0)
{
lean_object* v___x_6828_; 
v___x_6828_ = lean_box(0);
v___y_6820_ = v___x_6828_;
goto v___jp_6819_;
}
else
{
lean_object* v_val_6829_; lean_object* v___x_6830_; 
v_val_6829_ = lean_ctor_get(v___x_6827_, 0);
lean_inc(v_val_6829_);
lean_dec_ref_known(v___x_6827_, 1);
v___x_6830_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6804_, v_val_6829_);
v___y_6820_ = v___x_6830_;
goto v___jp_6819_;
}
v___jp_6819_:
{
lean_object* v___x_6821_; lean_object* v___x_6823_; 
v___x_6821_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6818_);
lean_inc(v_fst_6801_);
if (v_isShared_6807_ == 0)
{
lean_ctor_set(v___x_6806_, 1, v___x_6821_);
lean_ctor_set(v___x_6806_, 0, v_fst_6801_);
v___x_6823_ = v___x_6806_;
goto v_reusejp_6822_;
}
else
{
lean_object* v_reuseFailAlloc_6826_; 
v_reuseFailAlloc_6826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6826_, 0, v_fst_6801_);
lean_ctor_set(v_reuseFailAlloc_6826_, 1, v___x_6821_);
v___x_6823_ = v_reuseFailAlloc_6826_;
goto v_reusejp_6822_;
}
v_reusejp_6822_:
{
lean_object* v___x_6824_; lean_object* v___x_6825_; 
lean_inc(v_fst_6802_);
v___x_6824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6824_, 0, v___x_6823_);
lean_ctor_set(v___x_6824_, 1, v_fst_6802_);
lean_ctor_set(v___x_6824_, 2, v___y_6820_);
v___x_6825_ = lean_array_push(v_b_6796_, v___x_6824_);
v_result_6809_ = v___x_6825_;
goto v___jp_6808_;
}
}
}
else
{
lean_del_object(v___x_6806_);
v_result_6809_ = v_b_6796_;
goto v___jp_6808_;
}
}
v___jp_6808_:
{
lean_object* v_usages_6810_; size_t v_sz_6811_; size_t v___x_6812_; lean_object* v___x_6813_; size_t v___x_6814_; size_t v___x_6815_; 
v_usages_6810_ = lean_ctor_get(v_fst_6803_, 1);
lean_inc_ref(v_usages_6810_);
lean_dec(v_fst_6803_);
v_sz_6811_ = lean_array_size(v_usages_6810_);
v___x_6812_ = ((size_t)0ULL);
lean_inc(v_fst_6802_);
lean_inc(v_fst_6801_);
v___x_6813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6801_, v_fst_6802_, v_snd_6804_, v_usages_6810_, v_sz_6811_, v___x_6812_, v_result_6809_);
lean_dec_ref(v_usages_6810_);
lean_dec(v_snd_6804_);
v___x_6814_ = ((size_t)1ULL);
v___x_6815_ = lean_usize_add(v_i_6795_, v___x_6814_);
v_i_6795_ = v___x_6815_;
v_b_6796_ = v___x_6813_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6832_, lean_object* v_as_6833_, lean_object* v_sz_6834_, lean_object* v_i_6835_, lean_object* v_b_6836_){
_start:
{
uint8_t v_includeDefinition_boxed_6837_; size_t v_sz_boxed_6838_; size_t v_i_boxed_6839_; lean_object* v_res_6840_; 
v_includeDefinition_boxed_6837_ = lean_unbox(v_includeDefinition_6832_);
v_sz_boxed_6838_ = lean_unbox_usize(v_sz_6834_);
lean_dec(v_sz_6834_);
v_i_boxed_6839_ = lean_unbox_usize(v_i_6835_);
lean_dec(v_i_6835_);
v_res_6840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6837_, v_as_6833_, v_sz_boxed_6838_, v_i_boxed_6839_, v_b_6836_);
lean_dec_ref(v_as_6833_);
return v_res_6840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6843_, lean_object* v_ident_6844_, uint8_t v_includeDefinition_6845_){
_start:
{
lean_object* v_result_6846_; lean_object* v___x_6847_; size_t v_sz_6848_; size_t v___x_6849_; lean_object* v___x_6850_; 
v_result_6846_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6847_ = l_Lean_Server_References_allRefsFor(v_self_6843_, v_ident_6844_);
v_sz_6848_ = lean_array_size(v___x_6847_);
v___x_6849_ = ((size_t)0ULL);
v___x_6850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6845_, v___x_6847_, v_sz_6848_, v___x_6849_, v_result_6846_);
lean_dec_ref(v___x_6847_);
return v___x_6850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6851_, lean_object* v_ident_6852_, lean_object* v_includeDefinition_6853_){
_start:
{
uint8_t v_includeDefinition_boxed_6854_; lean_object* v_res_6855_; 
v_includeDefinition_boxed_6854_ = lean_unbox(v_includeDefinition_6853_);
v_res_6855_ = l_Lean_Server_References_referringTo(v_self_6851_, v_ident_6852_, v_includeDefinition_boxed_6854_);
return v_res_6855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6859_, size_t v_sz_6860_, size_t v_i_6861_, lean_object* v_b_6862_){
_start:
{
uint8_t v___x_6863_; 
v___x_6863_ = lean_usize_dec_lt(v_i_6861_, v_sz_6860_);
if (v___x_6863_ == 0)
{
lean_inc_ref(v_b_6862_);
return v_b_6862_;
}
else
{
lean_object* v_a_6864_; lean_object* v_snd_6865_; lean_object* v_snd_6866_; lean_object* v_fst_6867_; lean_object* v_fst_6868_; lean_object* v_fst_6869_; lean_object* v_snd_6870_; lean_object* v___x_6872_; uint8_t v_isShared_6873_; uint8_t v_isSharedCheck_6908_; 
v_a_6864_ = lean_array_uget_borrowed(v_as_6859_, v_i_6861_);
v_snd_6865_ = lean_ctor_get(v_a_6864_, 1);
v_snd_6866_ = lean_ctor_get(v_snd_6865_, 1);
lean_inc(v_snd_6866_);
v_fst_6867_ = lean_ctor_get(v_snd_6866_, 0);
lean_inc(v_fst_6867_);
v_fst_6868_ = lean_ctor_get(v_a_6864_, 0);
v_fst_6869_ = lean_ctor_get(v_snd_6865_, 0);
v_snd_6870_ = lean_ctor_get(v_snd_6866_, 1);
v_isSharedCheck_6908_ = !lean_is_exclusive(v_snd_6866_);
if (v_isSharedCheck_6908_ == 0)
{
lean_object* v_unused_6909_; 
v_unused_6909_ = lean_ctor_get(v_snd_6866_, 0);
lean_dec(v_unused_6909_);
v___x_6872_ = v_snd_6866_;
v_isShared_6873_ = v_isSharedCheck_6908_;
goto v_resetjp_6871_;
}
else
{
lean_inc(v_snd_6870_);
lean_dec(v_snd_6866_);
v___x_6872_ = lean_box(0);
v_isShared_6873_ = v_isSharedCheck_6908_;
goto v_resetjp_6871_;
}
v_resetjp_6871_:
{
lean_object* v_definition_x3f_6874_; lean_object* v___x_6876_; uint8_t v_isShared_6877_; uint8_t v_isSharedCheck_6906_; 
v_definition_x3f_6874_ = lean_ctor_get(v_fst_6867_, 0);
v_isSharedCheck_6906_ = !lean_is_exclusive(v_fst_6867_);
if (v_isSharedCheck_6906_ == 0)
{
lean_object* v_unused_6907_; 
v_unused_6907_ = lean_ctor_get(v_fst_6867_, 1);
lean_dec(v_unused_6907_);
v___x_6876_ = v_fst_6867_;
v_isShared_6877_ = v_isSharedCheck_6906_;
goto v_resetjp_6875_;
}
else
{
lean_inc(v_definition_x3f_6874_);
lean_dec(v_fst_6867_);
v___x_6876_ = lean_box(0);
v_isShared_6877_ = v_isSharedCheck_6906_;
goto v_resetjp_6875_;
}
v_resetjp_6875_:
{
lean_object* v___x_6878_; 
v___x_6878_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6874_) == 1)
{
lean_object* v_val_6879_; lean_object* v___x_6881_; uint8_t v_isShared_6882_; uint8_t v_isSharedCheck_6901_; 
v_val_6879_ = lean_ctor_get(v_definition_x3f_6874_, 0);
v_isSharedCheck_6901_ = !lean_is_exclusive(v_definition_x3f_6874_);
if (v_isSharedCheck_6901_ == 0)
{
v___x_6881_ = v_definition_x3f_6874_;
v_isShared_6882_ = v_isSharedCheck_6901_;
goto v_resetjp_6880_;
}
else
{
lean_inc(v_val_6879_);
lean_dec(v_definition_x3f_6874_);
v___x_6881_ = lean_box(0);
v_isShared_6882_ = v_isSharedCheck_6901_;
goto v_resetjp_6880_;
}
v_resetjp_6880_:
{
lean_object* v___y_6884_; lean_object* v___x_6897_; 
v___x_6897_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6879_);
if (lean_obj_tag(v___x_6897_) == 0)
{
lean_object* v___x_6898_; 
lean_dec(v_snd_6870_);
v___x_6898_ = lean_box(0);
v___y_6884_ = v___x_6898_;
goto v___jp_6883_;
}
else
{
lean_object* v_val_6899_; lean_object* v___x_6900_; 
v_val_6899_ = lean_ctor_get(v___x_6897_, 0);
lean_inc(v_val_6899_);
lean_dec_ref_known(v___x_6897_, 1);
v___x_6900_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6870_, v_val_6899_);
lean_dec(v_snd_6870_);
v___y_6884_ = v___x_6900_;
goto v___jp_6883_;
}
v___jp_6883_:
{
lean_object* v___x_6885_; lean_object* v___x_6887_; 
v___x_6885_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6879_);
lean_dec(v_val_6879_);
lean_inc(v_fst_6868_);
if (v_isShared_6877_ == 0)
{
lean_ctor_set(v___x_6876_, 1, v___x_6885_);
lean_ctor_set(v___x_6876_, 0, v_fst_6868_);
v___x_6887_ = v___x_6876_;
goto v_reusejp_6886_;
}
else
{
lean_object* v_reuseFailAlloc_6896_; 
v_reuseFailAlloc_6896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6896_, 0, v_fst_6868_);
lean_ctor_set(v_reuseFailAlloc_6896_, 1, v___x_6885_);
v___x_6887_ = v_reuseFailAlloc_6896_;
goto v_reusejp_6886_;
}
v_reusejp_6886_:
{
lean_object* v___x_6888_; lean_object* v___x_6890_; 
lean_inc(v_fst_6869_);
v___x_6888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6888_, 0, v___x_6887_);
lean_ctor_set(v___x_6888_, 1, v_fst_6869_);
lean_ctor_set(v___x_6888_, 2, v___y_6884_);
if (v_isShared_6882_ == 0)
{
lean_ctor_set(v___x_6881_, 0, v___x_6888_);
v___x_6890_ = v___x_6881_;
goto v_reusejp_6889_;
}
else
{
lean_object* v_reuseFailAlloc_6895_; 
v_reuseFailAlloc_6895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6895_, 0, v___x_6888_);
v___x_6890_ = v_reuseFailAlloc_6895_;
goto v_reusejp_6889_;
}
v_reusejp_6889_:
{
lean_object* v___x_6891_; lean_object* v___x_6893_; 
v___x_6891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6891_, 0, v___x_6890_);
if (v_isShared_6873_ == 0)
{
lean_ctor_set(v___x_6872_, 1, v___x_6878_);
lean_ctor_set(v___x_6872_, 0, v___x_6891_);
v___x_6893_ = v___x_6872_;
goto v_reusejp_6892_;
}
else
{
lean_object* v_reuseFailAlloc_6894_; 
v_reuseFailAlloc_6894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6894_, 0, v___x_6891_);
lean_ctor_set(v_reuseFailAlloc_6894_, 1, v___x_6878_);
v___x_6893_ = v_reuseFailAlloc_6894_;
goto v_reusejp_6892_;
}
v_reusejp_6892_:
{
return v___x_6893_;
}
}
}
}
}
}
else
{
lean_object* v___x_6902_; size_t v___x_6903_; size_t v___x_6904_; 
lean_del_object(v___x_6876_);
lean_dec(v_definition_x3f_6874_);
lean_del_object(v___x_6872_);
lean_dec(v_snd_6870_);
v___x_6902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6903_ = ((size_t)1ULL);
v___x_6904_ = lean_usize_add(v_i_6861_, v___x_6903_);
v_i_6861_ = v___x_6904_;
v_b_6862_ = v___x_6902_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6910_, lean_object* v_sz_6911_, lean_object* v_i_6912_, lean_object* v_b_6913_){
_start:
{
size_t v_sz_boxed_6914_; size_t v_i_boxed_6915_; lean_object* v_res_6916_; 
v_sz_boxed_6914_ = lean_unbox_usize(v_sz_6911_);
lean_dec(v_sz_6911_);
v_i_boxed_6915_ = lean_unbox_usize(v_i_6912_);
lean_dec(v_i_6912_);
v_res_6916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6910_, v_sz_boxed_6914_, v_i_boxed_6915_, v_b_6913_);
lean_dec_ref(v_b_6913_);
lean_dec_ref(v_as_6910_);
return v_res_6916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6917_, lean_object* v_ident_6918_){
_start:
{
lean_object* v___x_6919_; lean_object* v___x_6920_; lean_object* v___x_6921_; size_t v_sz_6922_; size_t v___x_6923_; lean_object* v___x_6924_; lean_object* v_fst_6925_; 
v___x_6919_ = l_Lean_Server_References_allRefsFor(v_self_6917_, v_ident_6918_);
v___x_6920_ = lean_box(0);
v___x_6921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6922_ = lean_array_size(v___x_6919_);
v___x_6923_ = ((size_t)0ULL);
v___x_6924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6919_, v_sz_6922_, v___x_6923_, v___x_6921_);
lean_dec_ref(v___x_6919_);
v_fst_6925_ = lean_ctor_get(v___x_6924_, 0);
lean_inc(v_fst_6925_);
lean_dec_ref(v___x_6924_);
if (lean_obj_tag(v_fst_6925_) == 0)
{
return v___x_6920_;
}
else
{
lean_object* v_val_6926_; 
v_val_6926_ = lean_ctor_get(v_fst_6925_, 0);
lean_inc(v_val_6926_);
lean_dec_ref_known(v_fst_6925_, 1);
return v_val_6926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6927_, lean_object* v_a_6928_, lean_object* v_fst_6929_, lean_object* v_init_6930_, lean_object* v_x_6931_){
_start:
{
lean_object* v_d_6934_; 
if (lean_obj_tag(v_x_6931_) == 0)
{
lean_object* v_k_6936_; lean_object* v_v_6937_; lean_object* v_l_6938_; lean_object* v_r_6939_; lean_object* v___y_6941_; lean_object* v___x_6945_; 
v_k_6936_ = lean_ctor_get(v_x_6931_, 1);
lean_inc(v_k_6936_);
v_v_6937_ = lean_ctor_get(v_x_6931_, 2);
lean_inc(v_v_6937_);
v_l_6938_ = lean_ctor_get(v_x_6931_, 3);
lean_inc(v_l_6938_);
v_r_6939_ = lean_ctor_get(v_x_6931_, 4);
lean_inc(v_r_6939_);
lean_dec_ref_known(v_x_6931_, 5);
lean_inc_ref(v_fst_6929_);
lean_inc(v_a_6928_);
lean_inc_ref(v_filterMapIdent_6927_);
v___x_6945_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6927_, v_a_6928_, v_fst_6929_, v_init_6930_, v_l_6938_);
if (lean_obj_tag(v___x_6945_) == 0)
{
lean_object* v_a_6946_; 
lean_dec(v_r_6939_);
lean_dec(v_v_6937_);
lean_dec(v_k_6936_);
lean_dec_ref(v_fst_6929_);
lean_dec(v_a_6928_);
lean_dec_ref(v_filterMapIdent_6927_);
v_a_6946_ = lean_ctor_get(v___x_6945_, 0);
lean_inc(v_a_6946_);
lean_dec_ref_known(v___x_6945_, 1);
v_d_6934_ = v_a_6946_;
goto v___jp_6933_;
}
else
{
if (lean_obj_tag(v_k_6936_) == 0)
{
lean_object* v_definition_x3f_6947_; 
v_definition_x3f_6947_ = lean_ctor_get(v_v_6937_, 0);
lean_inc(v_definition_x3f_6947_);
lean_dec(v_v_6937_);
if (lean_obj_tag(v_definition_x3f_6947_) == 1)
{
lean_object* v_a_6948_; lean_object* v_identName_6949_; lean_object* v_val_6950_; lean_object* v___x_6951_; lean_object* v___x_6952_; 
v_a_6948_ = lean_ctor_get(v___x_6945_, 0);
lean_inc(v_a_6948_);
v_identName_6949_ = lean_ctor_get(v_k_6936_, 1);
lean_inc_ref(v_identName_6949_);
lean_dec_ref_known(v_k_6936_, 2);
v_val_6950_ = lean_ctor_get(v_definition_x3f_6947_, 0);
lean_inc(v_val_6950_);
lean_dec_ref_known(v_definition_x3f_6947_, 1);
v___x_6951_ = l_String_toName(v_identName_6949_);
lean_inc_ref(v_filterMapIdent_6927_);
v___x_6952_ = lean_apply_1(v_filterMapIdent_6927_, v___x_6951_);
if (lean_obj_tag(v___x_6952_) == 1)
{
lean_object* v_val_6953_; lean_object* v___x_6954_; lean_object* v___x_6955_; lean_object* v___x_6956_; 
lean_dec_ref_known(v___x_6945_, 1);
v_val_6953_ = lean_ctor_get(v___x_6952_, 0);
lean_inc(v_val_6953_);
lean_dec_ref_known(v___x_6952_, 1);
v___x_6954_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6950_);
lean_dec(v_val_6950_);
lean_inc_ref(v_fst_6929_);
lean_inc(v_a_6928_);
v___x_6955_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6955_, 0, v_a_6928_);
lean_ctor_set(v___x_6955_, 1, v_fst_6929_);
lean_ctor_set(v___x_6955_, 2, v_val_6953_);
lean_ctor_set(v___x_6955_, 3, v___x_6954_);
v___x_6956_ = lean_array_push(v_a_6948_, v___x_6955_);
v_init_6930_ = v___x_6956_;
v_x_6931_ = v_r_6939_;
goto _start;
}
else
{
lean_dec(v___x_6952_);
lean_dec(v_val_6950_);
lean_dec(v_a_6948_);
v___y_6941_ = v___x_6945_;
goto v___jp_6940_;
}
}
else
{
lean_dec_ref_known(v_k_6936_, 2);
lean_dec(v_definition_x3f_6947_);
v___y_6941_ = v___x_6945_;
goto v___jp_6940_;
}
}
else
{
lean_dec(v_v_6937_);
lean_dec(v_k_6936_);
v___y_6941_ = v___x_6945_;
goto v___jp_6940_;
}
}
v___jp_6940_:
{
if (lean_obj_tag(v___y_6941_) == 0)
{
lean_object* v_a_6942_; 
lean_dec(v_r_6939_);
lean_dec_ref(v_fst_6929_);
lean_dec(v_a_6928_);
lean_dec_ref(v_filterMapIdent_6927_);
v_a_6942_ = lean_ctor_get(v___y_6941_, 0);
lean_inc(v_a_6942_);
lean_dec_ref_known(v___y_6941_, 1);
v_d_6934_ = v_a_6942_;
goto v___jp_6933_;
}
else
{
lean_object* v_a_6943_; 
v_a_6943_ = lean_ctor_get(v___y_6941_, 0);
lean_inc(v_a_6943_);
lean_dec_ref_known(v___y_6941_, 1);
v_init_6930_ = v_a_6943_;
v_x_6931_ = v_r_6939_;
goto _start;
}
}
}
else
{
lean_object* v___x_6958_; 
lean_dec_ref(v_fst_6929_);
lean_dec(v_a_6928_);
lean_dec_ref(v_filterMapIdent_6927_);
v___x_6958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6958_, 0, v_init_6930_);
return v___x_6958_;
}
v___jp_6933_:
{
lean_object* v___x_6935_; 
v___x_6935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6935_, 0, v_d_6934_);
return v___x_6935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6959_, lean_object* v_a_6960_, lean_object* v_fst_6961_, lean_object* v_init_6962_, lean_object* v_x_6963_, lean_object* v___y_6964_){
_start:
{
lean_object* v_res_6965_; 
v_res_6965_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6959_, v_a_6960_, v_fst_6961_, v_init_6962_, v_x_6963_);
return v_res_6965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6966_, lean_object* v_cancelTk_x3f_6967_, lean_object* v_init_6968_, lean_object* v_x_6969_){
_start:
{
lean_object* v_d_6972_; 
if (lean_obj_tag(v_x_6969_) == 0)
{
lean_object* v_k_6974_; lean_object* v_v_6975_; lean_object* v_l_6976_; lean_object* v_r_6977_; lean_object* v___x_6978_; 
v_k_6974_ = lean_ctor_get(v_x_6969_, 1);
lean_inc(v_k_6974_);
v_v_6975_ = lean_ctor_get(v_x_6969_, 2);
lean_inc(v_v_6975_);
v_l_6976_ = lean_ctor_get(v_x_6969_, 3);
lean_inc(v_l_6976_);
v_r_6977_ = lean_ctor_get(v_x_6969_, 4);
lean_inc(v_r_6977_);
lean_dec_ref_known(v_x_6969_, 5);
lean_inc(v_cancelTk_x3f_6967_);
lean_inc_ref(v_filterMapIdent_6966_);
v___x_6978_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6966_, v_cancelTk_x3f_6967_, v_init_6968_, v_l_6976_);
if (lean_obj_tag(v___x_6978_) == 0)
{
lean_object* v_a_6979_; 
lean_dec(v_r_6977_);
lean_dec(v_v_6975_);
lean_dec(v_k_6974_);
lean_dec(v_cancelTk_x3f_6967_);
lean_dec_ref(v_filterMapIdent_6966_);
v_a_6979_ = lean_ctor_get(v___x_6978_, 0);
lean_inc(v_a_6979_);
lean_dec_ref_known(v___x_6978_, 1);
v_d_6972_ = v_a_6979_;
goto v___jp_6971_;
}
else
{
lean_object* v_snd_6980_; lean_object* v_a_6981_; lean_object* v_fst_6982_; lean_object* v_fst_6983_; lean_object* v___x_6985_; uint8_t v_isShared_6986_; uint8_t v_isSharedCheck_7016_; 
v_snd_6980_ = lean_ctor_get(v_v_6975_, 1);
lean_inc(v_snd_6980_);
v_a_6981_ = lean_ctor_get(v___x_6978_, 0);
lean_inc(v_a_6981_);
lean_dec_ref_known(v___x_6978_, 1);
v_fst_6982_ = lean_ctor_get(v_v_6975_, 0);
lean_inc(v_fst_6982_);
lean_dec(v_v_6975_);
v_fst_6983_ = lean_ctor_get(v_snd_6980_, 0);
v_isSharedCheck_7016_ = !lean_is_exclusive(v_snd_6980_);
if (v_isSharedCheck_7016_ == 0)
{
lean_object* v_unused_7017_; 
v_unused_7017_ = lean_ctor_get(v_snd_6980_, 1);
lean_dec(v_unused_7017_);
v___x_6985_ = v_snd_6980_;
v_isShared_6986_ = v_isSharedCheck_7016_;
goto v_resetjp_6984_;
}
else
{
lean_inc(v_fst_6983_);
lean_dec(v_snd_6980_);
v___x_6985_ = lean_box(0);
v_isShared_6986_ = v_isSharedCheck_7016_;
goto v_resetjp_6984_;
}
v_resetjp_6984_:
{
lean_object* v_snd_6987_; lean_object* v___x_6989_; uint8_t v_isShared_6990_; uint8_t v_isSharedCheck_7014_; 
v_snd_6987_ = lean_ctor_get(v_a_6981_, 1);
v_isSharedCheck_7014_ = !lean_is_exclusive(v_a_6981_);
if (v_isSharedCheck_7014_ == 0)
{
lean_object* v_unused_7015_; 
v_unused_7015_ = lean_ctor_get(v_a_6981_, 0);
lean_dec(v_unused_7015_);
v___x_6989_ = v_a_6981_;
v_isShared_6990_ = v_isSharedCheck_7014_;
goto v_resetjp_6988_;
}
else
{
lean_inc(v_snd_6987_);
lean_dec(v_a_6981_);
v___x_6989_ = lean_box(0);
v_isShared_6990_ = v_isSharedCheck_7014_;
goto v_resetjp_6988_;
}
v_resetjp_6988_:
{
lean_object* v___x_6991_; lean_object* v_val_6993_; 
v___x_6991_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_6967_) == 1)
{
lean_object* v_val_7001_; uint8_t v___x_7002_; 
v_val_7001_ = lean_ctor_get(v_cancelTk_x3f_6967_, 0);
v___x_7002_ = l_IO_CancelToken_isSet(v_val_7001_);
if (v___x_7002_ == 0)
{
lean_del_object(v___x_6985_);
goto v___jp_6998_;
}
else
{
lean_object* v___x_7004_; uint8_t v_isShared_7005_; uint8_t v_isSharedCheck_7012_; 
lean_del_object(v___x_6989_);
lean_dec(v_fst_6983_);
lean_dec(v_fst_6982_);
lean_dec(v_r_6977_);
lean_dec(v_k_6974_);
lean_dec_ref(v_filterMapIdent_6966_);
v_isSharedCheck_7012_ = !lean_is_exclusive(v_cancelTk_x3f_6967_);
if (v_isSharedCheck_7012_ == 0)
{
lean_object* v_unused_7013_; 
v_unused_7013_ = lean_ctor_get(v_cancelTk_x3f_6967_, 0);
lean_dec(v_unused_7013_);
v___x_7004_ = v_cancelTk_x3f_6967_;
v_isShared_7005_ = v_isSharedCheck_7012_;
goto v_resetjp_7003_;
}
else
{
lean_dec(v_cancelTk_x3f_6967_);
v___x_7004_ = lean_box(0);
v_isShared_7005_ = v_isSharedCheck_7012_;
goto v_resetjp_7003_;
}
v_resetjp_7003_:
{
lean_object* v___x_7007_; 
lean_inc(v_snd_6987_);
if (v_isShared_7005_ == 0)
{
lean_ctor_set(v___x_7004_, 0, v_snd_6987_);
v___x_7007_ = v___x_7004_;
goto v_reusejp_7006_;
}
else
{
lean_object* v_reuseFailAlloc_7011_; 
v_reuseFailAlloc_7011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7011_, 0, v_snd_6987_);
v___x_7007_ = v_reuseFailAlloc_7011_;
goto v_reusejp_7006_;
}
v_reusejp_7006_:
{
lean_object* v___x_7009_; 
if (v_isShared_6986_ == 0)
{
lean_ctor_set(v___x_6985_, 1, v_snd_6987_);
lean_ctor_set(v___x_6985_, 0, v___x_7007_);
v___x_7009_ = v___x_6985_;
goto v_reusejp_7008_;
}
else
{
lean_object* v_reuseFailAlloc_7010_; 
v_reuseFailAlloc_7010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7010_, 0, v___x_7007_);
lean_ctor_set(v_reuseFailAlloc_7010_, 1, v_snd_6987_);
v___x_7009_ = v_reuseFailAlloc_7010_;
goto v_reusejp_7008_;
}
v_reusejp_7008_:
{
v_d_6972_ = v___x_7009_;
goto v___jp_6971_;
}
}
}
}
}
else
{
lean_del_object(v___x_6985_);
goto v___jp_6998_;
}
v___jp_6992_:
{
lean_object* v___x_6995_; 
if (v_isShared_6990_ == 0)
{
lean_ctor_set(v___x_6989_, 1, v_val_6993_);
lean_ctor_set(v___x_6989_, 0, v___x_6991_);
v___x_6995_ = v___x_6989_;
goto v_reusejp_6994_;
}
else
{
lean_object* v_reuseFailAlloc_6997_; 
v_reuseFailAlloc_6997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6997_, 0, v___x_6991_);
lean_ctor_set(v_reuseFailAlloc_6997_, 1, v_val_6993_);
v___x_6995_ = v_reuseFailAlloc_6997_;
goto v_reusejp_6994_;
}
v_reusejp_6994_:
{
v_init_6968_ = v___x_6995_;
v_x_6969_ = v_r_6977_;
goto _start;
}
}
v___jp_6998_:
{
lean_object* v___x_6999_; lean_object* v_a_7000_; 
lean_inc_ref(v_filterMapIdent_6966_);
v___x_6999_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6966_, v_k_6974_, v_fst_6982_, v_snd_6987_, v_fst_6983_);
v_a_7000_ = lean_ctor_get(v___x_6999_, 0);
lean_inc(v_a_7000_);
lean_dec_ref(v___x_6999_);
v_val_6993_ = v_a_7000_;
goto v___jp_6992_;
}
}
}
}
}
else
{
lean_object* v___x_7018_; 
lean_dec(v_cancelTk_x3f_6967_);
lean_dec_ref(v_filterMapIdent_6966_);
v___x_7018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7018_, 0, v_init_6968_);
return v___x_7018_;
}
v___jp_6971_:
{
lean_object* v___x_6973_; 
v___x_6973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6973_, 0, v_d_6972_);
return v___x_6973_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_7019_, lean_object* v_cancelTk_x3f_7020_, lean_object* v_init_7021_, lean_object* v_x_7022_, lean_object* v___y_7023_){
_start:
{
lean_object* v_res_7024_; 
v_res_7024_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7019_, v_cancelTk_x3f_7020_, v_init_7021_, v_x_7022_);
return v_res_7024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_7030_, lean_object* v_filterMapIdent_7031_, lean_object* v_cancelTk_x3f_7032_){
_start:
{
lean_object* v___x_7034_; lean_object* v___x_7035_; lean_object* v___x_7036_; lean_object* v_val_7038_; lean_object* v_a_7042_; 
v___x_7034_ = l_Lean_Server_References_allRefs(v_self_7030_);
v___x_7035_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_7036_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7031_, v_cancelTk_x3f_7032_, v___x_7035_, v___x_7034_);
v_a_7042_ = lean_ctor_get(v___x_7036_, 0);
lean_inc(v_a_7042_);
lean_dec_ref(v___x_7036_);
v_val_7038_ = v_a_7042_;
goto v___jp_7037_;
v___jp_7037_:
{
lean_object* v_fst_7039_; 
v_fst_7039_ = lean_ctor_get(v_val_7038_, 0);
if (lean_obj_tag(v_fst_7039_) == 0)
{
lean_object* v_snd_7040_; 
v_snd_7040_ = lean_ctor_get(v_val_7038_, 1);
lean_inc(v_snd_7040_);
lean_dec_ref(v_val_7038_);
return v_snd_7040_;
}
else
{
lean_object* v_val_7041_; 
lean_inc_ref(v_fst_7039_);
lean_dec_ref(v_val_7038_);
v_val_7041_ = lean_ctor_get(v_fst_7039_, 0);
lean_inc(v_val_7041_);
lean_dec_ref_known(v_fst_7039_, 1);
return v_val_7041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_7043_, lean_object* v_filterMapIdent_7044_, lean_object* v_cancelTk_x3f_7045_, lean_object* v_a_7046_){
_start:
{
lean_object* v_res_7047_; 
v_res_7047_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7043_, v_filterMapIdent_7044_, v_cancelTk_x3f_7045_);
return v_res_7047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_7048_, lean_object* v_self_7049_, lean_object* v_filterMapIdent_7050_, lean_object* v_cancelTk_x3f_7051_){
_start:
{
lean_object* v___x_7053_; 
v___x_7053_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7049_, v_filterMapIdent_7050_, v_cancelTk_x3f_7051_);
return v___x_7053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_7054_, lean_object* v_self_7055_, lean_object* v_filterMapIdent_7056_, lean_object* v_cancelTk_x3f_7057_, lean_object* v_a_7058_){
_start:
{
lean_object* v_res_7059_; 
v_res_7059_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_7054_, v_self_7055_, v_filterMapIdent_7056_, v_cancelTk_x3f_7057_);
return v_res_7059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_7060_, lean_object* v_filterMapIdent_7061_, lean_object* v_a_7062_, lean_object* v_fst_7063_, lean_object* v_init_7064_, lean_object* v_x_7065_){
_start:
{
lean_object* v___x_7067_; 
v___x_7067_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_7061_, v_a_7062_, v_fst_7063_, v_init_7064_, v_x_7065_);
return v___x_7067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_7068_, lean_object* v_filterMapIdent_7069_, lean_object* v_a_7070_, lean_object* v_fst_7071_, lean_object* v_init_7072_, lean_object* v_x_7073_, lean_object* v___y_7074_){
_start:
{
lean_object* v_res_7075_; 
v_res_7075_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_7068_, v_filterMapIdent_7069_, v_a_7070_, v_fst_7071_, v_init_7072_, v_x_7073_);
return v_res_7075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_7076_, lean_object* v_filterMapIdent_7077_, lean_object* v_cancelTk_x3f_7078_, lean_object* v_init_7079_, lean_object* v_x_7080_){
_start:
{
lean_object* v___x_7082_; 
v___x_7082_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7077_, v_cancelTk_x3f_7078_, v_init_7079_, v_x_7080_);
return v___x_7082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7083_, lean_object* v_filterMapIdent_7084_, lean_object* v_cancelTk_x3f_7085_, lean_object* v_init_7086_, lean_object* v_x_7087_, lean_object* v___y_7088_){
_start:
{
lean_object* v_res_7089_; 
v_res_7089_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7083_, v_filterMapIdent_7084_, v_cancelTk_x3f_7085_, v_init_7086_, v_x_7087_);
return v_res_7089_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7090_){
_start:
{
lean_object* v___x_7091_; lean_object* v___x_7092_; 
v___x_7091_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7092_ = lean_panic_fn_borrowed(v___x_7091_, v_msg_7090_);
return v___x_7092_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7096_; lean_object* v___x_7097_; lean_object* v___x_7098_; lean_object* v___x_7099_; lean_object* v___x_7100_; lean_object* v___x_7101_; 
v___x_7096_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7097_ = lean_unsigned_to_nat(14u);
v___x_7098_ = lean_unsigned_to_nat(22u);
v___x_7099_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7100_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7101_ = l_mkPanicMessageWithDecl(v___x_7100_, v___x_7099_, v___x_7098_, v___x_7097_, v___x_7096_);
return v___x_7101_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7102_, lean_object* v_init_7103_, lean_object* v_x_7104_){
_start:
{
if (lean_obj_tag(v_x_7104_) == 0)
{
lean_object* v_k_7105_; lean_object* v_v_7106_; lean_object* v_l_7107_; lean_object* v_r_7108_; lean_object* v___x_7109_; lean_object* v_a_7110_; lean_object* v_fst_7111_; lean_object* v_snd_7112_; lean_object* v___y_7114_; lean_object* v_index_7129_; lean_object* v___x_7130_; 
v_k_7105_ = lean_ctor_get(v_x_7104_, 1);
v_v_7106_ = lean_ctor_get(v_x_7104_, 2);
v_l_7107_ = lean_ctor_get(v_x_7104_, 3);
v_r_7108_ = lean_ctor_get(v_x_7104_, 4);
v___x_7109_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7102_, v_init_7103_, v_l_7107_);
v_a_7110_ = lean_ctor_get(v___x_7109_, 0);
lean_inc(v_a_7110_);
v_fst_7111_ = lean_ctor_get(v_v_7106_, 0);
v_snd_7112_ = lean_ctor_get(v_v_7106_, 1);
v_index_7129_ = lean_ctor_get(v_snd_7112_, 1);
v___x_7130_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7129_, v_requestedMod_7102_);
if (lean_obj_tag(v___x_7130_) == 1)
{
lean_object* v_val_7131_; lean_object* v___x_7132_; 
lean_dec_ref(v___x_7109_);
v_val_7131_ = lean_ctor_get(v___x_7130_, 0);
lean_inc(v_val_7131_);
lean_dec_ref_known(v___x_7130_, 1);
v___x_7132_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7131_);
lean_dec(v_val_7131_);
if (lean_obj_tag(v___x_7132_) == 0)
{
lean_object* v___x_7133_; lean_object* v___x_7134_; 
v___x_7133_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7134_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7133_);
v___y_7114_ = v___x_7134_;
goto v___jp_7113_;
}
else
{
lean_object* v_val_7135_; 
v_val_7135_ = lean_ctor_get(v___x_7132_, 0);
lean_inc(v_val_7135_);
lean_dec_ref_known(v___x_7132_, 1);
v___y_7114_ = v_val_7135_;
goto v___jp_7113_;
}
}
else
{
lean_object* v_a_7136_; 
lean_dec(v___x_7130_);
lean_dec(v_a_7110_);
v_a_7136_ = lean_ctor_get(v___x_7109_, 0);
lean_inc(v_a_7136_);
lean_dec_ref(v___x_7109_);
v_init_7103_ = v_a_7136_;
v_x_7104_ = v_r_7108_;
goto _start;
}
v___jp_7113_:
{
uint8_t v_isAll_7115_; uint8_t v_isPrivate_7116_; uint8_t v_metaKind_7117_; lean_object* v___x_7119_; uint8_t v_isShared_7120_; uint8_t v_isSharedCheck_7126_; 
v_isAll_7115_ = lean_ctor_get_uint8(v___y_7114_, sizeof(void*)*2);
v_isPrivate_7116_ = lean_ctor_get_uint8(v___y_7114_, sizeof(void*)*2 + 1);
v_metaKind_7117_ = lean_ctor_get_uint8(v___y_7114_, sizeof(void*)*2 + 2);
v_isSharedCheck_7126_ = !lean_is_exclusive(v___y_7114_);
if (v_isSharedCheck_7126_ == 0)
{
lean_object* v_unused_7127_; lean_object* v_unused_7128_; 
v_unused_7127_ = lean_ctor_get(v___y_7114_, 1);
lean_dec(v_unused_7127_);
v_unused_7128_ = lean_ctor_get(v___y_7114_, 0);
lean_dec(v_unused_7128_);
v___x_7119_ = v___y_7114_;
v_isShared_7120_ = v_isSharedCheck_7126_;
goto v_resetjp_7118_;
}
else
{
lean_dec(v___y_7114_);
v___x_7119_ = lean_box(0);
v_isShared_7120_ = v_isSharedCheck_7126_;
goto v_resetjp_7118_;
}
v_resetjp_7118_:
{
lean_object* v___x_7122_; 
lean_inc(v_fst_7111_);
lean_inc(v_k_7105_);
if (v_isShared_7120_ == 0)
{
lean_ctor_set(v___x_7119_, 1, v_fst_7111_);
lean_ctor_set(v___x_7119_, 0, v_k_7105_);
v___x_7122_ = v___x_7119_;
goto v_reusejp_7121_;
}
else
{
lean_object* v_reuseFailAlloc_7125_; 
v_reuseFailAlloc_7125_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7125_, 0, v_k_7105_);
lean_ctor_set(v_reuseFailAlloc_7125_, 1, v_fst_7111_);
lean_ctor_set_uint8(v_reuseFailAlloc_7125_, sizeof(void*)*2, v_isAll_7115_);
lean_ctor_set_uint8(v_reuseFailAlloc_7125_, sizeof(void*)*2 + 1, v_isPrivate_7116_);
lean_ctor_set_uint8(v_reuseFailAlloc_7125_, sizeof(void*)*2 + 2, v_metaKind_7117_);
v___x_7122_ = v_reuseFailAlloc_7125_;
goto v_reusejp_7121_;
}
v_reusejp_7121_:
{
lean_object* v___x_7123_; 
v___x_7123_ = lean_array_push(v_a_7110_, v___x_7122_);
v_init_7103_ = v___x_7123_;
v_x_7104_ = v_r_7108_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7138_; 
v___x_7138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7138_, 0, v_init_7103_);
return v___x_7138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object* v_requestedMod_7139_, lean_object* v_init_7140_, lean_object* v_x_7141_){
_start:
{
lean_object* v_res_7142_; 
v_res_7142_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7139_, v_init_7140_, v_x_7141_);
lean_dec(v_x_7141_);
lean_dec(v_requestedMod_7139_);
return v_res_7142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object* v_self_7143_, lean_object* v_requestedMod_7144_){
_start:
{
lean_object* v_result_7145_; lean_object* v___x_7146_; lean_object* v___x_7147_; lean_object* v_a_7148_; 
v_result_7145_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_7146_ = l_Lean_Server_References_allDirectImports(v_self_7143_);
v___x_7147_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7144_, v_result_7145_, v___x_7146_);
lean_dec(v___x_7146_);
v_a_7148_ = lean_ctor_get(v___x_7147_, 0);
lean_inc(v_a_7148_);
lean_dec_ref(v___x_7147_);
return v_a_7148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object* v_self_7149_, lean_object* v_requestedMod_7150_){
_start:
{
lean_object* v_res_7151_; 
v_res_7151_ = l_Lean_Server_References_importedBy(v_self_7149_, v_requestedMod_7150_);
lean_dec(v_requestedMod_7150_);
return v_res_7151_;
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

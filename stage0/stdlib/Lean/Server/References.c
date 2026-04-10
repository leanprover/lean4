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
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqRefIdent_beq(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object*);
uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Lsp_instHashableRange_hash(lean_object*);
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
uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_Range_toLspRange(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_DeclInfo_range(lean_object*);
lean_object* l_Lean_Lsp_DeclInfo_selectionRange(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_IO_throwServerError___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Expected list of length 4 or 5, not "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "usages"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Expected array, got other JSON type"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0;
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
lean_object* v_size_71_; lean_object* v_k_72_; lean_object* v_v_73_; lean_object* v_l_74_; lean_object* v_r_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_356_; 
v_size_71_ = lean_ctor_get(v_t_70_, 0);
v_k_72_ = lean_ctor_get(v_t_70_, 1);
v_v_73_ = lean_ctor_get(v_t_70_, 2);
v_l_74_ = lean_ctor_get(v_t_70_, 3);
v_r_75_ = lean_ctor_get(v_t_70_, 4);
v_isSharedCheck_356_ = !lean_is_exclusive(v_t_70_);
if (v_isSharedCheck_356_ == 0)
{
v___x_77_ = v_t_70_;
v_isShared_78_ = v_isSharedCheck_356_;
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
v_isShared_78_ = v_isSharedCheck_356_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint8_t v___x_79_; 
v___x_79_ = lean_string_dec_lt(v_k_68_, v_k_72_);
if (v___x_79_ == 0)
{
uint8_t v___x_80_; 
v___x_80_ = lean_string_dec_eq(v_k_68_, v_k_72_);
if (v___x_80_ == 0)
{
lean_object* v_impl_81_; lean_object* v___x_82_; 
lean_dec(v_size_71_);
v_impl_81_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_68_, v_v_69_, v_r_75_);
v___x_82_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_74_) == 0)
{
lean_object* v_size_83_; lean_object* v_size_84_; lean_object* v_k_85_; lean_object* v_v_86_; lean_object* v_l_87_; lean_object* v_r_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_size_83_ = lean_ctor_get(v_l_74_, 0);
v_size_84_ = lean_ctor_get(v_impl_81_, 0);
lean_inc(v_size_84_);
v_k_85_ = lean_ctor_get(v_impl_81_, 1);
lean_inc(v_k_85_);
v_v_86_ = lean_ctor_get(v_impl_81_, 2);
lean_inc(v_v_86_);
v_l_87_ = lean_ctor_get(v_impl_81_, 3);
lean_inc(v_l_87_);
v_r_88_ = lean_ctor_get(v_impl_81_, 4);
lean_inc(v_r_88_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_nat_mul(v___x_89_, v_size_83_);
v___x_91_ = lean_nat_dec_lt(v___x_90_, v_size_84_);
lean_dec(v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
lean_dec(v_r_88_);
lean_dec(v_l_87_);
lean_dec(v_v_86_);
lean_dec(v_k_85_);
v___x_92_ = lean_nat_add(v___x_82_, v_size_83_);
v___x_93_ = lean_nat_add(v___x_92_, v_size_84_);
lean_dec(v_size_84_);
lean_dec(v___x_92_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_impl_81_);
lean_ctor_set(v___x_77_, 0, v___x_93_);
v___x_95_ = v___x_77_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_96_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_96_, 4, v_impl_81_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_160_; 
v_isSharedCheck_160_ = !lean_is_exclusive(v_impl_81_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; lean_object* v_unused_162_; lean_object* v_unused_163_; lean_object* v_unused_164_; lean_object* v_unused_165_; 
v_unused_161_ = lean_ctor_get(v_impl_81_, 4);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v_impl_81_, 3);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_impl_81_, 2);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_impl_81_, 1);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_impl_81_, 0);
lean_dec(v_unused_165_);
v___x_98_ = v_impl_81_;
v_isShared_99_ = v_isSharedCheck_160_;
goto v_resetjp_97_;
}
else
{
lean_dec(v_impl_81_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_160_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_size_100_; lean_object* v_k_101_; lean_object* v_v_102_; lean_object* v_l_103_; lean_object* v_r_104_; lean_object* v_size_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_size_100_ = lean_ctor_get(v_l_87_, 0);
v_k_101_ = lean_ctor_get(v_l_87_, 1);
v_v_102_ = lean_ctor_get(v_l_87_, 2);
v_l_103_ = lean_ctor_get(v_l_87_, 3);
v_r_104_ = lean_ctor_get(v_l_87_, 4);
v_size_105_ = lean_ctor_get(v_r_88_, 0);
v___x_106_ = lean_unsigned_to_nat(2u);
v___x_107_ = lean_nat_mul(v___x_106_, v_size_105_);
v___x_108_ = lean_nat_dec_lt(v_size_100_, v___x_107_);
lean_dec(v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_136_; 
lean_inc(v_r_104_);
lean_inc(v_l_103_);
lean_inc(v_v_102_);
lean_inc(v_k_101_);
v_isSharedCheck_136_ = !lean_is_exclusive(v_l_87_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; lean_object* v_unused_138_; lean_object* v_unused_139_; lean_object* v_unused_140_; lean_object* v_unused_141_; 
v_unused_137_ = lean_ctor_get(v_l_87_, 4);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_l_87_, 3);
lean_dec(v_unused_138_);
v_unused_139_ = lean_ctor_get(v_l_87_, 2);
lean_dec(v_unused_139_);
v_unused_140_ = lean_ctor_get(v_l_87_, 1);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_l_87_, 0);
lean_dec(v_unused_141_);
v___x_110_ = v_l_87_;
v_isShared_111_ = v_isSharedCheck_136_;
goto v_resetjp_109_;
}
else
{
lean_dec(v_l_87_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_136_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___y_115_; lean_object* v___y_116_; lean_object* v___y_117_; lean_object* v___y_126_; 
v___x_112_ = lean_nat_add(v___x_82_, v_size_83_);
v___x_113_ = lean_nat_add(v___x_112_, v_size_84_);
lean_dec(v_size_84_);
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
v___jp_114_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = lean_nat_add(v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec(v___y_116_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 4, v_r_88_);
lean_ctor_set(v___x_110_, 3, v_r_104_);
lean_ctor_set(v___x_110_, 2, v_v_86_);
lean_ctor_set(v___x_110_, 1, v_k_85_);
lean_ctor_set(v___x_110_, 0, v___x_118_);
v___x_120_ = v___x_110_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_k_85_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v_v_86_);
lean_ctor_set(v_reuseFailAlloc_124_, 3, v_r_104_);
lean_ctor_set(v_reuseFailAlloc_124_, 4, v_r_88_);
v___x_120_ = v_reuseFailAlloc_124_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_122_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v___x_120_);
lean_ctor_set(v___x_98_, 3, v___y_115_);
lean_ctor_set(v___x_98_, 2, v_v_102_);
lean_ctor_set(v___x_98_, 1, v_k_101_);
lean_ctor_set(v___x_98_, 0, v___x_113_);
v___x_122_ = v___x_98_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_k_101_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v_v_102_);
lean_ctor_set(v_reuseFailAlloc_123_, 3, v___y_115_);
lean_ctor_set(v_reuseFailAlloc_123_, 4, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_nat_add(v___x_112_, v___y_126_);
lean_dec(v___y_126_);
lean_dec(v___x_112_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_l_103_);
lean_ctor_set(v___x_77_, 0, v___x_127_);
v___x_129_ = v___x_77_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_133_, 4, v_l_103_);
v___x_129_ = v_reuseFailAlloc_133_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; 
v___x_130_ = lean_nat_add(v___x_82_, v_size_105_);
if (lean_obj_tag(v_r_104_) == 0)
{
lean_object* v_size_131_; 
v_size_131_ = lean_ctor_get(v_r_104_, 0);
lean_inc(v_size_131_);
v___y_115_ = v___x_129_;
v___y_116_ = v___x_130_;
v___y_117_ = v_size_131_;
goto v___jp_114_;
}
else
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___y_115_ = v___x_129_;
v___y_116_ = v___x_130_;
v___y_117_ = v___x_132_;
goto v___jp_114_;
}
}
}
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
lean_del_object(v___x_77_);
v___x_142_ = lean_nat_add(v___x_82_, v_size_83_);
v___x_143_ = lean_nat_add(v___x_142_, v_size_84_);
lean_dec(v_size_84_);
v___x_144_ = lean_nat_add(v___x_142_, v_size_100_);
lean_dec(v___x_142_);
lean_inc_ref(v_l_74_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v_l_87_);
lean_ctor_set(v___x_98_, 3, v_l_74_);
lean_ctor_set(v___x_98_, 2, v_v_73_);
lean_ctor_set(v___x_98_, 1, v_k_72_);
lean_ctor_set(v___x_98_, 0, v___x_144_);
v___x_146_ = v___x_98_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_159_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_159_, 4, v_l_87_);
v___x_146_ = v_reuseFailAlloc_159_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_isSharedCheck_153_ = !lean_is_exclusive(v_l_74_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; lean_object* v_unused_155_; lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; 
v_unused_154_ = lean_ctor_get(v_l_74_, 4);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_l_74_, 3);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_l_74_, 2);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_l_74_, 1);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_l_74_, 0);
lean_dec(v_unused_158_);
v___x_148_ = v_l_74_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_dec(v_l_74_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 4, v_r_88_);
lean_ctor_set(v___x_148_, 3, v___x_146_);
lean_ctor_set(v___x_148_, 2, v_v_86_);
lean_ctor_set(v___x_148_, 1, v_k_85_);
lean_ctor_set(v___x_148_, 0, v___x_143_);
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_k_85_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_v_86_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_r_88_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_166_; 
v_l_166_ = lean_ctor_get(v_impl_81_, 3);
lean_inc(v_l_166_);
if (lean_obj_tag(v_l_166_) == 0)
{
lean_object* v_r_167_; lean_object* v_k_168_; lean_object* v_v_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_192_; 
v_r_167_ = lean_ctor_get(v_impl_81_, 4);
v_k_168_ = lean_ctor_get(v_impl_81_, 1);
v_v_169_ = lean_ctor_get(v_impl_81_, 2);
v_isSharedCheck_192_ = !lean_is_exclusive(v_impl_81_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; lean_object* v_unused_194_; 
v_unused_193_ = lean_ctor_get(v_impl_81_, 3);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_impl_81_, 0);
lean_dec(v_unused_194_);
v___x_171_ = v_impl_81_;
v_isShared_172_ = v_isSharedCheck_192_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_r_167_);
lean_inc(v_v_169_);
lean_inc(v_k_168_);
lean_dec(v_impl_81_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_192_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_k_173_; lean_object* v_v_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_188_; 
v_k_173_ = lean_ctor_get(v_l_166_, 1);
v_v_174_ = lean_ctor_get(v_l_166_, 2);
v_isSharedCheck_188_ = !lean_is_exclusive(v_l_166_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; 
v_unused_189_ = lean_ctor_get(v_l_166_, 4);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_l_166_, 3);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_l_166_, 0);
lean_dec(v_unused_191_);
v___x_176_ = v_l_166_;
v_isShared_177_ = v_isSharedCheck_188_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_v_174_);
lean_inc(v_k_173_);
lean_dec(v_l_166_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_188_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_167_, 2);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v_r_167_);
lean_ctor_set(v___x_176_, 3, v_r_167_);
lean_ctor_set(v___x_176_, 2, v_v_73_);
lean_ctor_set(v___x_176_, 1, v_k_72_);
lean_ctor_set(v___x_176_, 0, v___x_82_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_r_167_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v_r_167_);
v___x_180_ = v_reuseFailAlloc_187_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_182_; 
lean_inc(v_r_167_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 3, v_r_167_);
lean_ctor_set(v___x_171_, 0, v___x_82_);
v___x_182_ = v___x_171_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_r_167_);
lean_ctor_set(v_reuseFailAlloc_186_, 4, v_r_167_);
v___x_182_ = v_reuseFailAlloc_186_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_182_);
lean_ctor_set(v___x_77_, 3, v___x_180_);
lean_ctor_set(v___x_77_, 2, v_v_174_);
lean_ctor_set(v___x_77_, 1, v_k_173_);
lean_ctor_set(v___x_77_, 0, v___x_178_);
v___x_184_ = v___x_77_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
else
{
lean_object* v_r_195_; 
v_r_195_ = lean_ctor_get(v_impl_81_, 4);
lean_inc(v_r_195_);
if (lean_obj_tag(v_r_195_) == 0)
{
lean_object* v_k_196_; lean_object* v_v_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_208_; 
v_k_196_ = lean_ctor_get(v_impl_81_, 1);
v_v_197_ = lean_ctor_get(v_impl_81_, 2);
v_isSharedCheck_208_ = !lean_is_exclusive(v_impl_81_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; lean_object* v_unused_210_; lean_object* v_unused_211_; 
v_unused_209_ = lean_ctor_get(v_impl_81_, 4);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_impl_81_, 3);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_impl_81_, 0);
lean_dec(v_unused_211_);
v___x_199_ = v_impl_81_;
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_v_197_);
lean_inc(v_k_196_);
lean_dec(v_impl_81_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_unsigned_to_nat(3u);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 4, v_l_166_);
lean_ctor_set(v___x_199_, 2, v_v_73_);
lean_ctor_set(v___x_199_, 1, v_k_72_);
lean_ctor_set(v___x_199_, 0, v___x_82_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_207_, 3, v_l_166_);
lean_ctor_set(v_reuseFailAlloc_207_, 4, v_l_166_);
v___x_203_ = v_reuseFailAlloc_207_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_205_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_r_195_);
lean_ctor_set(v___x_77_, 3, v___x_203_);
lean_ctor_set(v___x_77_, 2, v_v_197_);
lean_ctor_set(v___x_77_, 1, v_k_196_);
lean_ctor_set(v___x_77_, 0, v___x_201_);
v___x_205_ = v___x_77_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_k_196_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_v_197_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_r_195_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = lean_unsigned_to_nat(2u);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_impl_81_);
lean_ctor_set(v___x_77_, 3, v_r_195_);
lean_ctor_set(v___x_77_, 0, v___x_212_);
v___x_214_ = v___x_77_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_r_195_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_impl_81_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
else
{
lean_object* v___x_217_; 
lean_dec(v_v_73_);
lean_dec(v_k_72_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 2, v_v_69_);
lean_ctor_set(v___x_77_, 1, v_k_68_);
v___x_217_ = v___x_77_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_size_71_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v_r_75_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v_impl_219_; lean_object* v___x_220_; 
lean_dec(v_size_71_);
v_impl_219_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_68_, v_v_69_, v_l_74_);
v___x_220_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_75_) == 0)
{
lean_object* v_size_221_; lean_object* v_size_222_; lean_object* v_k_223_; lean_object* v_v_224_; lean_object* v_l_225_; lean_object* v_r_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_size_221_ = lean_ctor_get(v_r_75_, 0);
v_size_222_ = lean_ctor_get(v_impl_219_, 0);
lean_inc(v_size_222_);
v_k_223_ = lean_ctor_get(v_impl_219_, 1);
lean_inc(v_k_223_);
v_v_224_ = lean_ctor_get(v_impl_219_, 2);
lean_inc(v_v_224_);
v_l_225_ = lean_ctor_get(v_impl_219_, 3);
lean_inc(v_l_225_);
v_r_226_ = lean_ctor_get(v_impl_219_, 4);
lean_inc(v_r_226_);
v___x_227_ = lean_unsigned_to_nat(3u);
v___x_228_ = lean_nat_mul(v___x_227_, v_size_221_);
v___x_229_ = lean_nat_dec_lt(v___x_228_, v_size_222_);
lean_dec(v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_r_226_);
lean_dec(v_l_225_);
lean_dec(v_v_224_);
lean_dec(v_k_223_);
v___x_230_ = lean_nat_add(v___x_220_, v_size_222_);
lean_dec(v_size_222_);
v___x_231_ = lean_nat_add(v___x_230_, v_size_221_);
lean_dec(v___x_230_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 3, v_impl_219_);
lean_ctor_set(v___x_77_, 0, v___x_231_);
v___x_233_ = v___x_77_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_impl_219_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v_r_75_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_300_; 
v_isSharedCheck_300_ = !lean_is_exclusive(v_impl_219_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_301_ = lean_ctor_get(v_impl_219_, 4);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_impl_219_, 3);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_impl_219_, 2);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_impl_219_, 1);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_impl_219_, 0);
lean_dec(v_unused_305_);
v___x_236_ = v_impl_219_;
v_isShared_237_ = v_isSharedCheck_300_;
goto v_resetjp_235_;
}
else
{
lean_dec(v_impl_219_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_300_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_size_238_; lean_object* v_size_239_; lean_object* v_k_240_; lean_object* v_v_241_; lean_object* v_l_242_; lean_object* v_r_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_size_238_ = lean_ctor_get(v_l_225_, 0);
v_size_239_ = lean_ctor_get(v_r_226_, 0);
v_k_240_ = lean_ctor_get(v_r_226_, 1);
v_v_241_ = lean_ctor_get(v_r_226_, 2);
v_l_242_ = lean_ctor_get(v_r_226_, 3);
v_r_243_ = lean_ctor_get(v_r_226_, 4);
v___x_244_ = lean_unsigned_to_nat(2u);
v___x_245_ = lean_nat_mul(v___x_244_, v_size_238_);
v___x_246_ = lean_nat_dec_lt(v_size_239_, v___x_245_);
lean_dec(v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_275_; 
lean_inc(v_r_243_);
lean_inc(v_l_242_);
lean_inc(v_v_241_);
lean_inc(v_k_240_);
v_isSharedCheck_275_ = !lean_is_exclusive(v_r_226_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; lean_object* v_unused_277_; lean_object* v_unused_278_; lean_object* v_unused_279_; lean_object* v_unused_280_; 
v_unused_276_ = lean_ctor_get(v_r_226_, 4);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_r_226_, 3);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_r_226_, 2);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_r_226_, 1);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_r_226_, 0);
lean_dec(v_unused_280_);
v___x_248_ = v_r_226_;
v_isShared_249_ = v_isSharedCheck_275_;
goto v_resetjp_247_;
}
else
{
lean_dec(v_r_226_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_275_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___x_263_; lean_object* v___y_265_; 
v___x_250_ = lean_nat_add(v___x_220_, v_size_222_);
lean_dec(v_size_222_);
v___x_251_ = lean_nat_add(v___x_250_, v_size_221_);
lean_dec(v___x_250_);
v___x_263_ = lean_nat_add(v___x_220_, v_size_238_);
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
v___jp_252_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = lean_nat_add(v___y_253_, v___y_255_);
lean_dec(v___y_255_);
lean_dec(v___y_253_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 4, v_r_75_);
lean_ctor_set(v___x_248_, 3, v_r_243_);
lean_ctor_set(v___x_248_, 2, v_v_73_);
lean_ctor_set(v___x_248_, 1, v_k_72_);
lean_ctor_set(v___x_248_, 0, v___x_256_);
v___x_258_ = v___x_248_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_r_243_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_r_75_);
v___x_258_ = v_reuseFailAlloc_262_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 4, v___x_258_);
lean_ctor_set(v___x_236_, 3, v___y_254_);
lean_ctor_set(v___x_236_, 2, v_v_241_);
lean_ctor_set(v___x_236_, 1, v_k_240_);
lean_ctor_set(v___x_236_, 0, v___x_251_);
v___x_260_ = v___x_236_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_240_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_241_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v___y_254_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_nat_add(v___x_263_, v___y_265_);
lean_dec(v___y_265_);
lean_dec(v___x_263_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_l_242_);
lean_ctor_set(v___x_77_, 3, v_l_225_);
lean_ctor_set(v___x_77_, 2, v_v_224_);
lean_ctor_set(v___x_77_, 1, v_k_223_);
lean_ctor_set(v___x_77_, 0, v___x_266_);
v___x_268_ = v___x_77_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_k_223_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_v_224_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_l_225_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v_l_242_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; 
v___x_269_ = lean_nat_add(v___x_220_, v_size_221_);
if (lean_obj_tag(v_r_243_) == 0)
{
lean_object* v_size_270_; 
v_size_270_ = lean_ctor_get(v_r_243_, 0);
lean_inc(v_size_270_);
v___y_253_ = v___x_269_;
v___y_254_ = v___x_268_;
v___y_255_ = v_size_270_;
goto v___jp_252_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_unsigned_to_nat(0u);
v___y_253_ = v___x_269_;
v___y_254_ = v___x_268_;
v___y_255_ = v___x_271_;
goto v___jp_252_;
}
}
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
lean_del_object(v___x_77_);
v___x_281_ = lean_nat_add(v___x_220_, v_size_222_);
lean_dec(v_size_222_);
v___x_282_ = lean_nat_add(v___x_281_, v_size_221_);
lean_dec(v___x_281_);
v___x_283_ = lean_nat_add(v___x_220_, v_size_221_);
v___x_284_ = lean_nat_add(v___x_283_, v_size_239_);
lean_dec(v___x_283_);
lean_inc_ref(v_r_75_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 4, v_r_75_);
lean_ctor_set(v___x_236_, 3, v_r_226_);
lean_ctor_set(v___x_236_, 2, v_v_73_);
lean_ctor_set(v___x_236_, 1, v_k_72_);
lean_ctor_set(v___x_236_, 0, v___x_284_);
v___x_286_ = v___x_236_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_r_226_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_r_75_);
v___x_286_ = v_reuseFailAlloc_299_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_isSharedCheck_293_ = !lean_is_exclusive(v_r_75_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_294_ = lean_ctor_get(v_r_75_, 4);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_r_75_, 3);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_r_75_, 2);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_r_75_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_r_75_, 0);
lean_dec(v_unused_298_);
v___x_288_ = v_r_75_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_r_75_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 4, v___x_286_);
lean_ctor_set(v___x_288_, 3, v_l_225_);
lean_ctor_set(v___x_288_, 2, v_v_224_);
lean_ctor_set(v___x_288_, 1, v_k_223_);
lean_ctor_set(v___x_288_, 0, v___x_282_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_k_223_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_v_224_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_l_225_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v___x_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_306_; 
v_l_306_ = lean_ctor_get(v_impl_219_, 3);
lean_inc(v_l_306_);
if (lean_obj_tag(v_l_306_) == 0)
{
lean_object* v_r_307_; lean_object* v_k_308_; lean_object* v_v_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_320_; 
v_r_307_ = lean_ctor_get(v_impl_219_, 4);
v_k_308_ = lean_ctor_get(v_impl_219_, 1);
v_v_309_ = lean_ctor_get(v_impl_219_, 2);
v_isSharedCheck_320_ = !lean_is_exclusive(v_impl_219_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; lean_object* v_unused_322_; 
v_unused_321_ = lean_ctor_get(v_impl_219_, 3);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_impl_219_, 0);
lean_dec(v_unused_322_);
v___x_311_ = v_impl_219_;
v_isShared_312_ = v_isSharedCheck_320_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_r_307_);
lean_inc(v_v_309_);
lean_inc(v_k_308_);
lean_dec(v_impl_219_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_320_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_307_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 3, v_r_307_);
lean_ctor_set(v___x_311_, 2, v_v_73_);
lean_ctor_set(v___x_311_, 1, v_k_72_);
lean_ctor_set(v___x_311_, 0, v___x_220_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_r_307_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_r_307_);
v___x_315_ = v_reuseFailAlloc_319_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_317_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_315_);
lean_ctor_set(v___x_77_, 3, v_l_306_);
lean_ctor_set(v___x_77_, 2, v_v_309_);
lean_ctor_set(v___x_77_, 1, v_k_308_);
lean_ctor_set(v___x_77_, 0, v___x_313_);
v___x_317_ = v___x_77_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_l_306_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v_r_323_; 
v_r_323_ = lean_ctor_get(v_impl_219_, 4);
lean_inc(v_r_323_);
if (lean_obj_tag(v_r_323_) == 0)
{
lean_object* v_k_324_; lean_object* v_v_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_348_; 
v_k_324_ = lean_ctor_get(v_impl_219_, 1);
v_v_325_ = lean_ctor_get(v_impl_219_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v_impl_219_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; lean_object* v_unused_350_; lean_object* v_unused_351_; 
v_unused_349_ = lean_ctor_get(v_impl_219_, 4);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_impl_219_, 3);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_impl_219_, 0);
lean_dec(v_unused_351_);
v___x_327_ = v_impl_219_;
v_isShared_328_ = v_isSharedCheck_348_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_v_325_);
lean_inc(v_k_324_);
lean_dec(v_impl_219_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_348_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_k_329_; lean_object* v_v_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_344_; 
v_k_329_ = lean_ctor_get(v_r_323_, 1);
v_v_330_ = lean_ctor_get(v_r_323_, 2);
v_isSharedCheck_344_ = !lean_is_exclusive(v_r_323_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; 
v_unused_345_ = lean_ctor_get(v_r_323_, 4);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_r_323_, 3);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_r_323_, 0);
lean_dec(v_unused_347_);
v___x_332_ = v_r_323_;
v_isShared_333_ = v_isSharedCheck_344_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_v_330_);
lean_inc(v_k_329_);
lean_dec(v_r_323_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_344_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = lean_unsigned_to_nat(3u);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 4, v_l_306_);
lean_ctor_set(v___x_332_, 3, v_l_306_);
lean_ctor_set(v___x_332_, 2, v_v_325_);
lean_ctor_set(v___x_332_, 1, v_k_324_);
lean_ctor_set(v___x_332_, 0, v___x_220_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_k_324_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_v_325_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_l_306_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_l_306_);
v___x_336_ = v_reuseFailAlloc_343_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 4, v_l_306_);
lean_ctor_set(v___x_327_, 2, v_v_73_);
lean_ctor_set(v___x_327_, 1, v_k_72_);
lean_ctor_set(v___x_327_, 0, v___x_220_);
v___x_338_ = v___x_327_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_l_306_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v_l_306_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_338_);
lean_ctor_set(v___x_77_, 3, v___x_336_);
lean_ctor_set(v___x_77_, 2, v_v_330_);
lean_ctor_set(v___x_77_, 1, v_k_329_);
lean_ctor_set(v___x_77_, 0, v___x_334_);
v___x_340_ = v___x_77_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_k_329_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_v_330_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_unsigned_to_nat(2u);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_r_323_);
lean_ctor_set(v___x_77_, 3, v_impl_219_);
lean_ctor_set(v___x_77_, 0, v___x_352_);
v___x_354_ = v___x_77_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_impl_219_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_r_323_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_k_68_);
lean_ctor_set(v___x_358_, 2, v_v_69_);
lean_ctor_set(v___x_358_, 3, v_t_70_);
lean_ctor_set(v___x_358_, 4, v_t_70_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1(size_t v_sz_359_, size_t v_i_360_, lean_object* v_bs_361_, lean_object* v___y_362_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = lean_usize_dec_lt(v_i_360_, v_sz_359_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_bs_361_);
lean_ctor_set(v___x_365_, 1, v___y_362_);
return v___x_365_;
}
else
{
lean_object* v_v_366_; lean_object* v_ci_367_; lean_object* v_range_368_; lean_object* v_toCommandContextInfo_369_; lean_object* v_parentDecl_x3f_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_bs_x27_373_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_389_; 
v_v_366_ = lean_array_uget_borrowed(v_bs_361_, v_i_360_);
v_ci_367_ = lean_ctor_get(v_v_366_, 4);
v_range_368_ = lean_ctor_get(v_v_366_, 2);
lean_inc_ref(v_range_368_);
v_toCommandContextInfo_369_ = lean_ctor_get(v_ci_367_, 0);
lean_inc_ref(v_toCommandContextInfo_369_);
v_parentDecl_x3f_370_ = lean_ctor_get(v_ci_367_, 1);
lean_inc(v_parentDecl_x3f_370_);
v___x_371_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_372_ = lean_unsigned_to_nat(0u);
v_bs_x27_373_ = lean_array_uset(v_bs_361_, v_i_360_, v___x_372_);
if (lean_obj_tag(v_parentDecl_x3f_370_) == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_box(0);
v___y_389_ = v___x_409_;
goto v___jp_388_;
}
else
{
lean_object* v_val_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_val_410_ = lean_ctor_get(v_parentDecl_x3f_370_, 0);
lean_inc(v_val_410_);
v___x_411_ = l_Lean_Name_toString(v_val_410_, v___x_364_);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
v___y_389_ = v___x_412_;
goto v___jp_388_;
}
v___jp_374_:
{
lean_object* v___x_377_; size_t v___x_378_; size_t v___x_379_; lean_object* v___x_380_; 
v___x_377_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_368_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v_range_368_);
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_360_, v___x_378_);
v___x_380_ = lean_array_uset(v_bs_x27_373_, v_i_360_, v___x_377_);
v_i_360_ = v___x_379_;
v_bs_361_ = v___x_380_;
v___y_362_ = v___y_376_;
goto _start;
}
v___jp_382_:
{
if (lean_obj_tag(v___y_383_) == 1)
{
if (lean_obj_tag(v___y_384_) == 1)
{
lean_object* v_val_385_; lean_object* v_val_386_; lean_object* v___x_387_; 
v_val_385_ = lean_ctor_get(v___y_383_, 0);
v_val_386_ = lean_ctor_get(v___y_384_, 0);
lean_inc(v_val_386_);
lean_dec_ref(v___y_384_);
lean_inc(v_val_385_);
v___x_387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_val_385_, v_val_386_, v___y_362_);
v___y_375_ = v___y_383_;
v___y_376_ = v___x_387_;
goto v___jp_374_;
}
else
{
lean_dec(v___y_384_);
v___y_375_ = v___y_383_;
v___y_376_ = v___y_362_;
goto v___jp_374_;
}
}
else
{
lean_dec(v___y_384_);
v___y_375_ = v___y_383_;
v___y_376_ = v___y_362_;
goto v___jp_374_;
}
}
v___jp_388_:
{
lean_object* v_cmdEnv_x3f_390_; 
v_cmdEnv_x3f_390_ = lean_ctor_get(v_toCommandContextInfo_369_, 1);
lean_inc(v_cmdEnv_x3f_390_);
lean_dec_ref(v_toCommandContextInfo_369_);
if (lean_obj_tag(v_cmdEnv_x3f_390_) == 0)
{
lean_object* v___x_391_; 
lean_dec(v_parentDecl_x3f_370_);
v___x_391_ = lean_box(0);
v___y_383_ = v___y_389_;
v___y_384_ = v___x_391_;
goto v___jp_382_;
}
else
{
if (lean_obj_tag(v_parentDecl_x3f_370_) == 0)
{
lean_object* v___x_392_; 
lean_dec_ref(v_cmdEnv_x3f_390_);
v___x_392_ = lean_box(0);
v___y_383_ = v___y_389_;
v___y_384_ = v___x_392_;
goto v___jp_382_;
}
else
{
lean_object* v_val_393_; lean_object* v_val_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; 
v_val_393_ = lean_ctor_get(v_cmdEnv_x3f_390_, 0);
lean_inc(v_val_393_);
lean_dec_ref(v_cmdEnv_x3f_390_);
v_val_394_ = lean_ctor_get(v_parentDecl_x3f_370_, 0);
lean_inc(v_val_394_);
lean_dec_ref(v_parentDecl_x3f_370_);
v___x_395_ = l_Lean_declRangeExt;
v___x_396_ = lean_box(1);
v___x_397_ = 0;
v___x_398_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_371_, v___x_395_, v_val_393_, v_val_394_, v___x_396_, v___x_397_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
v___y_383_ = v___y_389_;
v___y_384_ = v___x_399_;
goto v___jp_382_;
}
else
{
lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_408_; 
v_val_400_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_408_ == 0)
{
v___x_402_ = v___x_398_;
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_dec(v___x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_val_400_);
lean_dec(v_val_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
v___y_383_ = v___y_389_;
v___y_384_ = v___x_406_;
goto v___jp_382_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1___boxed(lean_object* v_sz_413_, lean_object* v_i_414_, lean_object* v_bs_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
size_t v_sz_boxed_418_; size_t v_i_boxed_419_; lean_object* v_res_420_; 
v_sz_boxed_418_ = lean_unbox_usize(v_sz_413_);
lean_dec(v_sz_413_);
v_i_boxed_419_ = lean_unbox_usize(v_i_414_);
lean_dec(v_i_414_);
v_res_420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1(v_sz_boxed_418_, v_i_boxed_419_, v_bs_415_, v___y_416_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_toLspRefInfo(lean_object* v_i_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_definition_424_; lean_object* v_usages_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_497_; 
v_definition_424_ = lean_ctor_get(v_i_421_, 0);
v_usages_425_ = lean_ctor_get(v_i_421_, 1);
v_isSharedCheck_497_ = !lean_is_exclusive(v_i_421_);
if (v_isSharedCheck_497_ == 0)
{
v___x_427_ = v_i_421_;
v_isShared_428_ = v_isSharedCheck_497_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_usages_425_);
lean_inc(v_definition_424_);
lean_dec(v_i_421_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_497_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_fst_430_; lean_object* v_snd_431_; 
if (lean_obj_tag(v_definition_424_) == 0)
{
lean_object* v___x_447_; 
v___x_447_ = lean_box(0);
v_fst_430_ = v___x_447_;
v_snd_431_ = v_a_422_;
goto v___jp_429_;
}
else
{
lean_object* v_val_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_496_; 
v_val_448_ = lean_ctor_get(v_definition_424_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_definition_424_);
if (v_isSharedCheck_496_ == 0)
{
v___x_450_ = v_definition_424_;
v_isShared_451_ = v_isSharedCheck_496_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_val_448_);
lean_dec(v_definition_424_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_496_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_range_452_; lean_object* v_ci_453_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v_toCommandContextInfo_467_; lean_object* v_parentDecl_x3f_468_; lean_object* v___x_469_; lean_object* v___y_471_; 
v_range_452_ = lean_ctor_get(v_val_448_, 2);
lean_inc_ref(v_range_452_);
v_ci_453_ = lean_ctor_get(v_val_448_, 4);
lean_inc_ref(v_ci_453_);
lean_dec(v_val_448_);
v_toCommandContextInfo_467_ = lean_ctor_get(v_ci_453_, 0);
lean_inc_ref(v_toCommandContextInfo_467_);
v_parentDecl_x3f_468_ = lean_ctor_get(v_ci_453_, 1);
lean_inc(v_parentDecl_x3f_468_);
lean_dec_ref(v_ci_453_);
v___x_469_ = l_Lean_instInhabitedDeclarationRanges_default;
if (lean_obj_tag(v_parentDecl_x3f_468_) == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_box(0);
v___y_471_ = v___x_491_;
goto v___jp_470_;
}
else
{
lean_object* v_val_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_val_492_ = lean_ctor_get(v_parentDecl_x3f_468_, 0);
v___x_493_ = 1;
lean_inc(v_val_492_);
v___x_494_ = l_Lean_Name_toString(v_val_492_, v___x_493_);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
v___y_471_ = v___x_495_;
goto v___jp_470_;
}
v___jp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_452_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v_range_452_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_457_);
v___x_459_ = v___x_450_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v_fst_430_ = v___x_459_;
v_snd_431_ = v___y_456_;
goto v___jp_429_;
}
}
v___jp_461_:
{
if (lean_obj_tag(v___y_462_) == 1)
{
if (lean_obj_tag(v___y_463_) == 1)
{
lean_object* v_val_464_; lean_object* v_val_465_; lean_object* v___x_466_; 
v_val_464_ = lean_ctor_get(v___y_462_, 0);
v_val_465_ = lean_ctor_get(v___y_463_, 0);
lean_inc(v_val_465_);
lean_dec_ref(v___y_463_);
lean_inc(v_val_464_);
v___x_466_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_val_464_, v_val_465_, v_a_422_);
v___y_455_ = v___y_462_;
v___y_456_ = v___x_466_;
goto v___jp_454_;
}
else
{
lean_dec(v___y_463_);
v___y_455_ = v___y_462_;
v___y_456_ = v_a_422_;
goto v___jp_454_;
}
}
else
{
lean_dec(v___y_463_);
v___y_455_ = v___y_462_;
v___y_456_ = v_a_422_;
goto v___jp_454_;
}
}
v___jp_470_:
{
lean_object* v_cmdEnv_x3f_472_; 
v_cmdEnv_x3f_472_ = lean_ctor_get(v_toCommandContextInfo_467_, 1);
lean_inc(v_cmdEnv_x3f_472_);
lean_dec_ref(v_toCommandContextInfo_467_);
if (lean_obj_tag(v_cmdEnv_x3f_472_) == 0)
{
lean_object* v___x_473_; 
lean_dec(v_parentDecl_x3f_468_);
v___x_473_ = lean_box(0);
v___y_462_ = v___y_471_;
v___y_463_ = v___x_473_;
goto v___jp_461_;
}
else
{
if (lean_obj_tag(v_parentDecl_x3f_468_) == 0)
{
lean_object* v___x_474_; 
lean_dec_ref(v_cmdEnv_x3f_472_);
v___x_474_ = lean_box(0);
v___y_462_ = v___y_471_;
v___y_463_ = v___x_474_;
goto v___jp_461_;
}
else
{
lean_object* v_val_475_; lean_object* v_val_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; 
v_val_475_ = lean_ctor_get(v_cmdEnv_x3f_472_, 0);
lean_inc(v_val_475_);
lean_dec_ref(v_cmdEnv_x3f_472_);
v_val_476_ = lean_ctor_get(v_parentDecl_x3f_468_, 0);
lean_inc(v_val_476_);
lean_dec_ref(v_parentDecl_x3f_468_);
v___x_477_ = l_Lean_declRangeExt;
v___x_478_ = lean_box(1);
v___x_479_ = 0;
v___x_480_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_469_, v___x_477_, v_val_475_, v_val_476_, v___x_478_, v___x_479_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v___x_481_; 
v___x_481_ = lean_box(0);
v___y_462_ = v___y_471_;
v___y_463_ = v___x_481_;
goto v___jp_461_;
}
else
{
lean_object* v_val_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
v_val_482_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_490_ == 0)
{
v___x_484_ = v___x_480_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_val_482_);
lean_dec(v___x_480_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_val_482_);
lean_dec(v_val_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
v___y_462_ = v___y_471_;
v___y_463_ = v___x_488_;
goto v___jp_461_;
}
}
}
}
}
}
}
}
v___jp_429_:
{
size_t v_sz_432_; size_t v___x_433_; lean_object* v___x_434_; lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
v_sz_432_ = lean_array_size(v_usages_425_);
v___x_433_ = ((size_t)0ULL);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_RefInfo_toLspRefInfo_spec__1(v_sz_432_, v___x_433_, v_usages_425_, v_snd_431_);
v_fst_435_ = lean_ctor_get(v___x_434_, 0);
v_snd_436_ = lean_ctor_get(v___x_434_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_446_ == 0)
{
v___x_438_ = v___x_434_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_snd_436_);
lean_inc(v_fst_435_);
lean_dec(v___x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v_fst_435_);
lean_ctor_set(v___x_427_, 0, v_fst_430_);
v___x_441_ = v___x_427_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_fst_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_fst_435_);
v___x_441_ = v_reuseFailAlloc_445_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_443_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_snd_436_);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_RefInfo_toLspRefInfo___boxed(lean_object* v_i_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Server_RefInfo_toLspRefInfo(v_i_498_, v_a_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0(lean_object* v_00_u03b2_502_, lean_object* v_k_503_, lean_object* v_v_504_, lean_object* v_t_505_, lean_object* v_hl_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_503_, v_v_504_, v_t_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(lean_object* v_ref_508_, lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = ((lean_object*)(l_Lean_Server_RefInfo_empty));
v___x_511_ = l_Lean_Server_RefInfo_addRef(v___x_510_, v_ref_508_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
else
{
lean_object* v_val_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_val_513_ = lean_ctor_get(v_x_509_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_509_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v_x_509_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_val_513_);
lean_dec(v_x_509_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = l_Lean_Server_RefInfo_addRef(v_val_513_, v_ref_508_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(lean_object* v_ref_522_, lean_object* v_k_523_, lean_object* v_t_524_){
_start:
{
if (lean_obj_tag(v_t_524_) == 0)
{
lean_object* v_size_525_; lean_object* v_k_526_; lean_object* v_v_527_; lean_object* v_l_528_; lean_object* v_r_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_544_; 
v_size_525_ = lean_ctor_get(v_t_524_, 0);
v_k_526_ = lean_ctor_get(v_t_524_, 1);
v_v_527_ = lean_ctor_get(v_t_524_, 2);
v_l_528_ = lean_ctor_get(v_t_524_, 3);
v_r_529_ = lean_ctor_get(v_t_524_, 4);
v_isSharedCheck_544_ = !lean_is_exclusive(v_t_524_);
if (v_isSharedCheck_544_ == 0)
{
v___x_531_ = v_t_524_;
v_isShared_532_ = v_isSharedCheck_544_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_r_529_);
lean_inc(v_l_528_);
lean_inc(v_v_527_);
lean_inc(v_k_526_);
lean_inc(v_size_525_);
lean_dec(v_t_524_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_544_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
uint8_t v___x_533_; 
v___x_533_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_523_, v_k_526_);
switch(v___x_533_)
{
case 0:
{
lean_object* v_impl_534_; lean_object* v___x_535_; 
lean_del_object(v___x_531_);
lean_dec(v_size_525_);
v_impl_534_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_522_, v_k_523_, v_l_528_);
v___x_535_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_526_, v_v_527_, v_impl_534_, v_r_529_);
return v___x_535_;
}
case 1:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_val_538_; lean_object* v___x_540_; 
lean_dec(v_k_526_);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v_v_527_);
v___x_537_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(v_ref_522_, v___x_536_);
v_val_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_val_538_);
lean_dec(v___x_537_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 2, v_val_538_);
lean_ctor_set(v___x_531_, 1, v_k_523_);
v___x_540_ = v___x_531_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_size_525_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_k_523_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_val_538_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_l_528_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v_r_529_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
default: 
{
lean_object* v_impl_542_; lean_object* v___x_543_; 
lean_del_object(v___x_531_);
lean_dec(v_size_525_);
v_impl_542_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_522_, v_k_523_, v_r_529_);
v___x_543_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_526_, v_v_527_, v_l_528_, v_impl_542_);
return v___x_543_;
}
}
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_val_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_545_ = lean_box(0);
v___x_546_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg___lam__0(v_ref_522_, v___x_545_);
v_val_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_547_);
lean_dec(v___x_546_);
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v_k_523_);
lean_ctor_set(v___x_549_, 2, v_val_547_);
lean_ctor_set(v___x_549_, 3, v_t_524_);
lean_ctor_set(v___x_549_, 4, v_t_524_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_addRef(lean_object* v_self_550_, lean_object* v_ref_551_){
_start:
{
lean_object* v_ident_552_; lean_object* v___x_553_; 
v_ident_552_ = lean_ctor_get(v_ref_551_, 0);
lean_inc_ref(v_ident_552_);
v___x_553_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_551_, v_ident_552_, v_self_550_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0(lean_object* v_ref_554_, lean_object* v_k_555_, lean_object* v_t_556_, lean_object* v_hl_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Server_ModuleRefs_addRef_spec__0___redArg(v_ref_554_, v_k_555_, v_t_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(lean_object* v_k_559_, lean_object* v_v_560_, lean_object* v_t_561_){
_start:
{
if (lean_obj_tag(v_t_561_) == 0)
{
lean_object* v_size_562_; lean_object* v_k_563_; lean_object* v_v_564_; lean_object* v_l_565_; lean_object* v_r_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_846_; 
v_size_562_ = lean_ctor_get(v_t_561_, 0);
v_k_563_ = lean_ctor_get(v_t_561_, 1);
v_v_564_ = lean_ctor_get(v_t_561_, 2);
v_l_565_ = lean_ctor_get(v_t_561_, 3);
v_r_566_ = lean_ctor_get(v_t_561_, 4);
v_isSharedCheck_846_ = !lean_is_exclusive(v_t_561_);
if (v_isSharedCheck_846_ == 0)
{
v___x_568_ = v_t_561_;
v_isShared_569_ = v_isSharedCheck_846_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_r_566_);
lean_inc(v_l_565_);
lean_inc(v_v_564_);
lean_inc(v_k_563_);
lean_inc(v_size_562_);
lean_dec(v_t_561_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_846_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
uint8_t v___x_570_; 
v___x_570_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_559_, v_k_563_);
switch(v___x_570_)
{
case 0:
{
lean_object* v_impl_571_; lean_object* v___x_572_; 
lean_dec(v_size_562_);
v_impl_571_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_559_, v_v_560_, v_l_565_);
v___x_572_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_566_) == 0)
{
lean_object* v_size_573_; lean_object* v_size_574_; lean_object* v_k_575_; lean_object* v_v_576_; lean_object* v_l_577_; lean_object* v_r_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_size_573_ = lean_ctor_get(v_r_566_, 0);
v_size_574_ = lean_ctor_get(v_impl_571_, 0);
lean_inc(v_size_574_);
v_k_575_ = lean_ctor_get(v_impl_571_, 1);
lean_inc(v_k_575_);
v_v_576_ = lean_ctor_get(v_impl_571_, 2);
lean_inc(v_v_576_);
v_l_577_ = lean_ctor_get(v_impl_571_, 3);
lean_inc(v_l_577_);
v_r_578_ = lean_ctor_get(v_impl_571_, 4);
lean_inc(v_r_578_);
v___x_579_ = lean_unsigned_to_nat(3u);
v___x_580_ = lean_nat_mul(v___x_579_, v_size_573_);
v___x_581_ = lean_nat_dec_lt(v___x_580_, v_size_574_);
lean_dec(v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
lean_dec(v_r_578_);
lean_dec(v_l_577_);
lean_dec(v_v_576_);
lean_dec(v_k_575_);
v___x_582_ = lean_nat_add(v___x_572_, v_size_574_);
lean_dec(v_size_574_);
v___x_583_ = lean_nat_add(v___x_582_, v_size_573_);
lean_dec(v___x_582_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 3, v_impl_571_);
lean_ctor_set(v___x_568_, 0, v___x_583_);
v___x_585_ = v___x_568_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v_impl_571_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v_r_566_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
else
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_652_; 
v_isSharedCheck_652_ = !lean_is_exclusive(v_impl_571_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; lean_object* v_unused_657_; 
v_unused_653_ = lean_ctor_get(v_impl_571_, 4);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_impl_571_, 3);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_impl_571_, 2);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_impl_571_, 1);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v_impl_571_, 0);
lean_dec(v_unused_657_);
v___x_588_ = v_impl_571_;
v_isShared_589_ = v_isSharedCheck_652_;
goto v_resetjp_587_;
}
else
{
lean_dec(v_impl_571_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_652_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_size_590_; lean_object* v_size_591_; lean_object* v_k_592_; lean_object* v_v_593_; lean_object* v_l_594_; lean_object* v_r_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_size_590_ = lean_ctor_get(v_l_577_, 0);
v_size_591_ = lean_ctor_get(v_r_578_, 0);
v_k_592_ = lean_ctor_get(v_r_578_, 1);
v_v_593_ = lean_ctor_get(v_r_578_, 2);
v_l_594_ = lean_ctor_get(v_r_578_, 3);
v_r_595_ = lean_ctor_get(v_r_578_, 4);
v___x_596_ = lean_unsigned_to_nat(2u);
v___x_597_ = lean_nat_mul(v___x_596_, v_size_590_);
v___x_598_ = lean_nat_dec_lt(v_size_591_, v___x_597_);
lean_dec(v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_627_; 
lean_inc(v_r_595_);
lean_inc(v_l_594_);
lean_inc(v_v_593_);
lean_inc(v_k_592_);
v_isSharedCheck_627_ = !lean_is_exclusive(v_r_578_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; lean_object* v_unused_629_; lean_object* v_unused_630_; lean_object* v_unused_631_; lean_object* v_unused_632_; 
v_unused_628_ = lean_ctor_get(v_r_578_, 4);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_r_578_, 3);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_r_578_, 2);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_r_578_, 1);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_r_578_, 0);
lean_dec(v_unused_632_);
v___x_600_ = v_r_578_;
v_isShared_601_ = v_isSharedCheck_627_;
goto v_resetjp_599_;
}
else
{
lean_dec(v_r_578_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_627_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___x_615_; lean_object* v___y_617_; 
v___x_602_ = lean_nat_add(v___x_572_, v_size_574_);
lean_dec(v_size_574_);
v___x_603_ = lean_nat_add(v___x_602_, v_size_573_);
lean_dec(v___x_602_);
v___x_615_ = lean_nat_add(v___x_572_, v_size_590_);
if (lean_obj_tag(v_l_594_) == 0)
{
lean_object* v_size_625_; 
v_size_625_ = lean_ctor_get(v_l_594_, 0);
lean_inc(v_size_625_);
v___y_617_ = v_size_625_;
goto v___jp_616_;
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___y_617_ = v___x_626_;
goto v___jp_616_;
}
v___jp_604_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_nat_add(v___y_605_, v___y_607_);
lean_dec(v___y_607_);
lean_dec(v___y_605_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 4, v_r_566_);
lean_ctor_set(v___x_600_, 3, v_r_595_);
lean_ctor_set(v___x_600_, 2, v_v_564_);
lean_ctor_set(v___x_600_, 1, v_k_563_);
lean_ctor_set(v___x_600_, 0, v___x_608_);
v___x_610_ = v___x_600_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_r_595_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_r_566_);
v___x_610_ = v_reuseFailAlloc_614_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 4, v___x_610_);
lean_ctor_set(v___x_588_, 3, v___y_606_);
lean_ctor_set(v___x_588_, 2, v_v_593_);
lean_ctor_set(v___x_588_, 1, v_k_592_);
lean_ctor_set(v___x_588_, 0, v___x_603_);
v___x_612_ = v___x_588_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_k_592_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_v_593_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v___y_606_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
v___jp_616_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_nat_add(v___x_615_, v___y_617_);
lean_dec(v___y_617_);
lean_dec(v___x_615_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_l_594_);
lean_ctor_set(v___x_568_, 3, v_l_577_);
lean_ctor_set(v___x_568_, 2, v_v_576_);
lean_ctor_set(v___x_568_, 1, v_k_575_);
lean_ctor_set(v___x_568_, 0, v___x_618_);
v___x_620_ = v___x_568_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_k_575_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_v_576_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_l_577_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v_l_594_);
v___x_620_ = v_reuseFailAlloc_624_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_nat_add(v___x_572_, v_size_573_);
if (lean_obj_tag(v_r_595_) == 0)
{
lean_object* v_size_622_; 
v_size_622_ = lean_ctor_get(v_r_595_, 0);
lean_inc(v_size_622_);
v___y_605_ = v___x_621_;
v___y_606_ = v___x_620_;
v___y_607_ = v_size_622_;
goto v___jp_604_;
}
else
{
lean_object* v___x_623_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___y_605_ = v___x_621_;
v___y_606_ = v___x_620_;
v___y_607_ = v___x_623_;
goto v___jp_604_;
}
}
}
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
lean_del_object(v___x_568_);
v___x_633_ = lean_nat_add(v___x_572_, v_size_574_);
lean_dec(v_size_574_);
v___x_634_ = lean_nat_add(v___x_633_, v_size_573_);
lean_dec(v___x_633_);
v___x_635_ = lean_nat_add(v___x_572_, v_size_573_);
v___x_636_ = lean_nat_add(v___x_635_, v_size_591_);
lean_dec(v___x_635_);
lean_inc_ref(v_r_566_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 4, v_r_566_);
lean_ctor_set(v___x_588_, 3, v_r_578_);
lean_ctor_set(v___x_588_, 2, v_v_564_);
lean_ctor_set(v___x_588_, 1, v_k_563_);
lean_ctor_set(v___x_588_, 0, v___x_636_);
v___x_638_ = v___x_588_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_r_578_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v_r_566_);
v___x_638_ = v_reuseFailAlloc_651_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
v_isSharedCheck_645_ = !lean_is_exclusive(v_r_566_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; lean_object* v_unused_649_; lean_object* v_unused_650_; 
v_unused_646_ = lean_ctor_get(v_r_566_, 4);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_r_566_, 3);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_r_566_, 2);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v_r_566_, 1);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v_r_566_, 0);
lean_dec(v_unused_650_);
v___x_640_ = v_r_566_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_dec(v_r_566_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v___x_638_);
lean_ctor_set(v___x_640_, 3, v_l_577_);
lean_ctor_set(v___x_640_, 2, v_v_576_);
lean_ctor_set(v___x_640_, 1, v_k_575_);
lean_ctor_set(v___x_640_, 0, v___x_634_);
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_k_575_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_v_576_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_l_577_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v___x_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_658_; 
v_l_658_ = lean_ctor_get(v_impl_571_, 3);
lean_inc(v_l_658_);
if (lean_obj_tag(v_l_658_) == 0)
{
lean_object* v_r_659_; lean_object* v_k_660_; lean_object* v_v_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_672_; 
v_r_659_ = lean_ctor_get(v_impl_571_, 4);
v_k_660_ = lean_ctor_get(v_impl_571_, 1);
v_v_661_ = lean_ctor_get(v_impl_571_, 2);
v_isSharedCheck_672_ = !lean_is_exclusive(v_impl_571_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; lean_object* v_unused_674_; 
v_unused_673_ = lean_ctor_get(v_impl_571_, 3);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v_impl_571_, 0);
lean_dec(v_unused_674_);
v___x_663_ = v_impl_571_;
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_r_659_);
lean_inc(v_v_661_);
lean_inc(v_k_660_);
lean_dec(v_impl_571_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_659_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 3, v_r_659_);
lean_ctor_set(v___x_663_, 2, v_v_564_);
lean_ctor_set(v___x_663_, 1, v_k_563_);
lean_ctor_set(v___x_663_, 0, v___x_572_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_r_659_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_r_659_);
v___x_667_ = v_reuseFailAlloc_671_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v___x_667_);
lean_ctor_set(v___x_568_, 3, v_l_658_);
lean_ctor_set(v___x_568_, 2, v_v_661_);
lean_ctor_set(v___x_568_, 1, v_k_660_);
lean_ctor_set(v___x_568_, 0, v___x_665_);
v___x_669_ = v___x_568_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_k_660_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_v_661_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v_l_658_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v_r_675_; 
v_r_675_ = lean_ctor_get(v_impl_571_, 4);
lean_inc(v_r_675_);
if (lean_obj_tag(v_r_675_) == 0)
{
lean_object* v_k_676_; lean_object* v_v_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_700_; 
v_k_676_ = lean_ctor_get(v_impl_571_, 1);
v_v_677_ = lean_ctor_get(v_impl_571_, 2);
v_isSharedCheck_700_ = !lean_is_exclusive(v_impl_571_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; lean_object* v_unused_702_; lean_object* v_unused_703_; 
v_unused_701_ = lean_ctor_get(v_impl_571_, 4);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_impl_571_, 3);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_impl_571_, 0);
lean_dec(v_unused_703_);
v___x_679_ = v_impl_571_;
v_isShared_680_ = v_isSharedCheck_700_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_v_677_);
lean_inc(v_k_676_);
lean_dec(v_impl_571_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_700_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_k_681_; lean_object* v_v_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_696_; 
v_k_681_ = lean_ctor_get(v_r_675_, 1);
v_v_682_ = lean_ctor_get(v_r_675_, 2);
v_isSharedCheck_696_ = !lean_is_exclusive(v_r_675_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; 
v_unused_697_ = lean_ctor_get(v_r_675_, 4);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_r_675_, 3);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_r_675_, 0);
lean_dec(v_unused_699_);
v___x_684_ = v_r_675_;
v_isShared_685_ = v_isSharedCheck_696_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_v_682_);
lean_inc(v_k_681_);
lean_dec(v_r_675_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_696_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(3u);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 4, v_l_658_);
lean_ctor_set(v___x_684_, 3, v_l_658_);
lean_ctor_set(v___x_684_, 2, v_v_677_);
lean_ctor_set(v___x_684_, 1, v_k_676_);
lean_ctor_set(v___x_684_, 0, v___x_572_);
v___x_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_k_676_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_v_677_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_l_658_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_l_658_);
v___x_688_ = v_reuseFailAlloc_695_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 4, v_l_658_);
lean_ctor_set(v___x_679_, 2, v_v_564_);
lean_ctor_set(v___x_679_, 1, v_k_563_);
lean_ctor_set(v___x_679_, 0, v___x_572_);
v___x_690_ = v___x_679_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_l_658_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_l_658_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v___x_690_);
lean_ctor_set(v___x_568_, 3, v___x_688_);
lean_ctor_set(v___x_568_, 2, v_v_682_);
lean_ctor_set(v___x_568_, 1, v_k_681_);
lean_ctor_set(v___x_568_, 0, v___x_686_);
v___x_692_ = v___x_568_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_k_681_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_v_682_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(2u);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_r_675_);
lean_ctor_set(v___x_568_, 3, v_impl_571_);
lean_ctor_set(v___x_568_, 0, v___x_704_);
v___x_706_ = v___x_568_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_impl_571_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_r_675_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
case 1:
{
lean_object* v___x_709_; 
lean_dec(v_v_564_);
lean_dec(v_k_563_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 2, v_v_560_);
lean_ctor_set(v___x_568_, 1, v_k_559_);
v___x_709_ = v___x_568_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_size_562_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_r_566_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
default: 
{
lean_object* v_impl_711_; lean_object* v___x_712_; 
lean_dec(v_size_562_);
v_impl_711_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_559_, v_v_560_, v_r_566_);
v___x_712_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_565_) == 0)
{
lean_object* v_size_713_; lean_object* v_size_714_; lean_object* v_k_715_; lean_object* v_v_716_; lean_object* v_l_717_; lean_object* v_r_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_size_713_ = lean_ctor_get(v_l_565_, 0);
v_size_714_ = lean_ctor_get(v_impl_711_, 0);
lean_inc(v_size_714_);
v_k_715_ = lean_ctor_get(v_impl_711_, 1);
lean_inc(v_k_715_);
v_v_716_ = lean_ctor_get(v_impl_711_, 2);
lean_inc(v_v_716_);
v_l_717_ = lean_ctor_get(v_impl_711_, 3);
lean_inc(v_l_717_);
v_r_718_ = lean_ctor_get(v_impl_711_, 4);
lean_inc(v_r_718_);
v___x_719_ = lean_unsigned_to_nat(3u);
v___x_720_ = lean_nat_mul(v___x_719_, v_size_713_);
v___x_721_ = lean_nat_dec_lt(v___x_720_, v_size_714_);
lean_dec(v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec(v_r_718_);
lean_dec(v_l_717_);
lean_dec(v_v_716_);
lean_dec(v_k_715_);
v___x_722_ = lean_nat_add(v___x_712_, v_size_713_);
v___x_723_ = lean_nat_add(v___x_722_, v_size_714_);
lean_dec(v_size_714_);
lean_dec(v___x_722_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_impl_711_);
lean_ctor_set(v___x_568_, 0, v___x_723_);
v___x_725_ = v___x_568_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_impl_711_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_790_; 
v_isSharedCheck_790_ = !lean_is_exclusive(v_impl_711_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; lean_object* v_unused_792_; lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_791_ = lean_ctor_get(v_impl_711_, 4);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_impl_711_, 3);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_impl_711_, 2);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_impl_711_, 1);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_impl_711_, 0);
lean_dec(v_unused_795_);
v___x_728_ = v_impl_711_;
v_isShared_729_ = v_isSharedCheck_790_;
goto v_resetjp_727_;
}
else
{
lean_dec(v_impl_711_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_790_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_size_730_; lean_object* v_k_731_; lean_object* v_v_732_; lean_object* v_l_733_; lean_object* v_r_734_; lean_object* v_size_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_size_730_ = lean_ctor_get(v_l_717_, 0);
v_k_731_ = lean_ctor_get(v_l_717_, 1);
v_v_732_ = lean_ctor_get(v_l_717_, 2);
v_l_733_ = lean_ctor_get(v_l_717_, 3);
v_r_734_ = lean_ctor_get(v_l_717_, 4);
v_size_735_ = lean_ctor_get(v_r_718_, 0);
v___x_736_ = lean_unsigned_to_nat(2u);
v___x_737_ = lean_nat_mul(v___x_736_, v_size_735_);
v___x_738_ = lean_nat_dec_lt(v_size_730_, v___x_737_);
lean_dec(v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_766_; 
lean_inc(v_r_734_);
lean_inc(v_l_733_);
lean_inc(v_v_732_);
lean_inc(v_k_731_);
v_isSharedCheck_766_ = !lean_is_exclusive(v_l_717_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; lean_object* v_unused_770_; lean_object* v_unused_771_; 
v_unused_767_ = lean_ctor_get(v_l_717_, 4);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_l_717_, 3);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_l_717_, 2);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_l_717_, 1);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_l_717_, 0);
lean_dec(v_unused_771_);
v___x_740_ = v_l_717_;
v_isShared_741_ = v_isSharedCheck_766_;
goto v_resetjp_739_;
}
else
{
lean_dec(v_l_717_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_766_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_756_; 
v___x_742_ = lean_nat_add(v___x_712_, v_size_713_);
v___x_743_ = lean_nat_add(v___x_742_, v_size_714_);
lean_dec(v_size_714_);
if (lean_obj_tag(v_l_733_) == 0)
{
lean_object* v_size_764_; 
v_size_764_ = lean_ctor_get(v_l_733_, 0);
lean_inc(v_size_764_);
v___y_756_ = v_size_764_;
goto v___jp_755_;
}
else
{
lean_object* v___x_765_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___y_756_ = v___x_765_;
goto v___jp_755_;
}
v___jp_744_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_nat_add(v___y_745_, v___y_747_);
lean_dec(v___y_747_);
lean_dec(v___y_745_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 4, v_r_718_);
lean_ctor_set(v___x_740_, 3, v_r_734_);
lean_ctor_set(v___x_740_, 2, v_v_716_);
lean_ctor_set(v___x_740_, 1, v_k_715_);
lean_ctor_set(v___x_740_, 0, v___x_748_);
v___x_750_ = v___x_740_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_715_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_716_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_r_734_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_r_718_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v___x_750_);
lean_ctor_set(v___x_728_, 3, v___y_746_);
lean_ctor_set(v___x_728_, 2, v_v_732_);
lean_ctor_set(v___x_728_, 1, v_k_731_);
lean_ctor_set(v___x_728_, 0, v___x_743_);
v___x_752_ = v___x_728_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v___y_746_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
v___jp_755_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_nat_add(v___x_742_, v___y_756_);
lean_dec(v___y_756_);
lean_dec(v___x_742_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_l_733_);
lean_ctor_set(v___x_568_, 0, v___x_757_);
v___x_759_ = v___x_568_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_l_733_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; 
v___x_760_ = lean_nat_add(v___x_712_, v_size_735_);
if (lean_obj_tag(v_r_734_) == 0)
{
lean_object* v_size_761_; 
v_size_761_ = lean_ctor_get(v_r_734_, 0);
lean_inc(v_size_761_);
v___y_745_ = v___x_760_;
v___y_746_ = v___x_759_;
v___y_747_ = v_size_761_;
goto v___jp_744_;
}
else
{
lean_object* v___x_762_; 
v___x_762_ = lean_unsigned_to_nat(0u);
v___y_745_ = v___x_760_;
v___y_746_ = v___x_759_;
v___y_747_ = v___x_762_;
goto v___jp_744_;
}
}
}
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
lean_del_object(v___x_568_);
v___x_772_ = lean_nat_add(v___x_712_, v_size_713_);
v___x_773_ = lean_nat_add(v___x_772_, v_size_714_);
lean_dec(v_size_714_);
v___x_774_ = lean_nat_add(v___x_772_, v_size_730_);
lean_dec(v___x_772_);
lean_inc_ref(v_l_565_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v_l_717_);
lean_ctor_set(v___x_728_, 3, v_l_565_);
lean_ctor_set(v___x_728_, 2, v_v_564_);
lean_ctor_set(v___x_728_, 1, v_k_563_);
lean_ctor_set(v___x_728_, 0, v___x_774_);
v___x_776_ = v___x_728_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v_l_717_);
v___x_776_ = v_reuseFailAlloc_789_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_isSharedCheck_783_ = !lean_is_exclusive(v_l_565_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; lean_object* v_unused_785_; lean_object* v_unused_786_; lean_object* v_unused_787_; lean_object* v_unused_788_; 
v_unused_784_ = lean_ctor_get(v_l_565_, 4);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_l_565_, 3);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_l_565_, 2);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_l_565_, 1);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_l_565_, 0);
lean_dec(v_unused_788_);
v___x_778_ = v_l_565_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_l_565_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v_r_718_);
lean_ctor_set(v___x_778_, 3, v___x_776_);
lean_ctor_set(v___x_778_, 2, v_v_716_);
lean_ctor_set(v___x_778_, 1, v_k_715_);
lean_ctor_set(v___x_778_, 0, v___x_773_);
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_k_715_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_v_716_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_r_718_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_796_; 
v_l_796_ = lean_ctor_get(v_impl_711_, 3);
lean_inc(v_l_796_);
if (lean_obj_tag(v_l_796_) == 0)
{
lean_object* v_r_797_; lean_object* v_k_798_; lean_object* v_v_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_822_; 
v_r_797_ = lean_ctor_get(v_impl_711_, 4);
v_k_798_ = lean_ctor_get(v_impl_711_, 1);
v_v_799_ = lean_ctor_get(v_impl_711_, 2);
v_isSharedCheck_822_ = !lean_is_exclusive(v_impl_711_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; lean_object* v_unused_824_; 
v_unused_823_ = lean_ctor_get(v_impl_711_, 3);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_impl_711_, 0);
lean_dec(v_unused_824_);
v___x_801_ = v_impl_711_;
v_isShared_802_ = v_isSharedCheck_822_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_r_797_);
lean_inc(v_v_799_);
lean_inc(v_k_798_);
lean_dec(v_impl_711_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_822_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_k_803_; lean_object* v_v_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_818_; 
v_k_803_ = lean_ctor_get(v_l_796_, 1);
v_v_804_ = lean_ctor_get(v_l_796_, 2);
v_isSharedCheck_818_ = !lean_is_exclusive(v_l_796_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_819_ = lean_ctor_get(v_l_796_, 4);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_l_796_, 3);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_l_796_, 0);
lean_dec(v_unused_821_);
v___x_806_ = v_l_796_;
v_isShared_807_ = v_isSharedCheck_818_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_v_804_);
lean_inc(v_k_803_);
lean_dec(v_l_796_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_818_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_797_, 2);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 4, v_r_797_);
lean_ctor_set(v___x_806_, 3, v_r_797_);
lean_ctor_set(v___x_806_, 2, v_v_564_);
lean_ctor_set(v___x_806_, 1, v_k_563_);
lean_ctor_set(v___x_806_, 0, v___x_712_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_r_797_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_r_797_);
v___x_810_ = v_reuseFailAlloc_817_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
lean_inc(v_r_797_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 3, v_r_797_);
lean_ctor_set(v___x_801_, 0, v___x_712_);
v___x_812_ = v___x_801_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_k_798_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_v_799_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_r_797_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_r_797_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v___x_812_);
lean_ctor_set(v___x_568_, 3, v___x_810_);
lean_ctor_set(v___x_568_, 2, v_v_804_);
lean_ctor_set(v___x_568_, 1, v_k_803_);
lean_ctor_set(v___x_568_, 0, v___x_808_);
v___x_814_ = v___x_568_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_k_803_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_v_804_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
else
{
lean_object* v_r_825_; 
v_r_825_ = lean_ctor_get(v_impl_711_, 4);
lean_inc(v_r_825_);
if (lean_obj_tag(v_r_825_) == 0)
{
lean_object* v_k_826_; lean_object* v_v_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_838_; 
v_k_826_ = lean_ctor_get(v_impl_711_, 1);
v_v_827_ = lean_ctor_get(v_impl_711_, 2);
v_isSharedCheck_838_ = !lean_is_exclusive(v_impl_711_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; 
v_unused_839_ = lean_ctor_get(v_impl_711_, 4);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_impl_711_, 3);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_impl_711_, 0);
lean_dec(v_unused_841_);
v___x_829_ = v_impl_711_;
v_isShared_830_ = v_isSharedCheck_838_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_v_827_);
lean_inc(v_k_826_);
lean_dec(v_impl_711_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_838_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = lean_unsigned_to_nat(3u);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 4, v_l_796_);
lean_ctor_set(v___x_829_, 2, v_v_564_);
lean_ctor_set(v___x_829_, 1, v_k_563_);
lean_ctor_set(v___x_829_, 0, v___x_712_);
v___x_833_ = v___x_829_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v_l_796_);
lean_ctor_set(v_reuseFailAlloc_837_, 4, v_l_796_);
v___x_833_ = v_reuseFailAlloc_837_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_r_825_);
lean_ctor_set(v___x_568_, 3, v___x_833_);
lean_ctor_set(v___x_568_, 2, v_v_827_);
lean_ctor_set(v___x_568_, 1, v_k_826_);
lean_ctor_set(v___x_568_, 0, v___x_831_);
v___x_835_ = v___x_568_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_k_826_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_v_827_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v_r_825_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_842_ = lean_unsigned_to_nat(2u);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_impl_711_);
lean_ctor_set(v___x_568_, 3, v_r_825_);
lean_ctor_set(v___x_568_, 0, v___x_842_);
v___x_844_ = v___x_568_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_r_825_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_impl_711_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
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
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_k_559_);
lean_ctor_set(v___x_848_, 2, v_v_560_);
lean_ctor_set(v___x_848_, 3, v_t_561_);
lean_ctor_set(v___x_848_, 4, v_t_561_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(lean_object* v_init_849_, lean_object* v_x_850_, lean_object* v___y_851_){
_start:
{
if (lean_obj_tag(v_x_850_) == 0)
{
lean_object* v_k_853_; lean_object* v_v_854_; lean_object* v_l_855_; lean_object* v_r_856_; lean_object* v___x_857_; lean_object* v_fst_858_; lean_object* v_snd_859_; lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v_fst_862_; lean_object* v_snd_863_; lean_object* v___x_864_; 
v_k_853_ = lean_ctor_get(v_x_850_, 1);
lean_inc(v_k_853_);
v_v_854_ = lean_ctor_get(v_x_850_, 2);
lean_inc(v_v_854_);
v_l_855_ = lean_ctor_get(v_x_850_, 3);
lean_inc(v_l_855_);
v_r_856_ = lean_ctor_get(v_x_850_, 4);
lean_inc(v_r_856_);
lean_dec_ref(v_x_850_);
v___x_857_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(v_init_849_, v_l_855_, v___y_851_);
v_fst_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_fst_858_);
v_snd_859_ = lean_ctor_get(v___x_857_, 1);
lean_inc(v_snd_859_);
lean_dec_ref(v___x_857_);
v_a_860_ = lean_ctor_get(v_fst_858_, 0);
lean_inc(v_a_860_);
lean_dec(v_fst_858_);
v___x_861_ = l_Lean_Server_RefInfo_toLspRefInfo(v_v_854_, v_snd_859_);
v_fst_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_fst_862_);
v_snd_863_ = lean_ctor_get(v___x_861_, 1);
lean_inc(v_snd_863_);
lean_dec_ref(v___x_861_);
v___x_864_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_853_, v_fst_862_, v_a_860_);
v_init_849_ = v___x_864_;
v_x_850_ = v_r_856_;
v___y_851_ = v_snd_863_;
goto _start;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v_init_849_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___y_851_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1___boxed(lean_object* v_init_868_, lean_object* v_x_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(v_init_868_, v_x_869_, v___y_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object* v_refs_873_){
_start:
{
lean_object* v_refs_x27_875_; lean_object* v___x_876_; lean_object* v_fst_877_; lean_object* v_snd_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_888_; 
v_refs_x27_875_ = lean_box(1);
v___x_876_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__1(v_refs_x27_875_, v_refs_873_, v_refs_x27_875_);
v_fst_877_ = lean_ctor_get(v___x_876_, 0);
v_snd_878_ = lean_ctor_get(v___x_876_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_888_ == 0)
{
v___x_880_ = v___x_876_;
v_isShared_881_ = v_isSharedCheck_888_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_snd_878_);
lean_inc(v_fst_877_);
lean_dec(v___x_876_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_888_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_d_883_; lean_object* v_a_887_; 
v_a_887_ = lean_ctor_get(v_fst_877_, 0);
lean_inc(v_a_887_);
lean_dec(v_fst_877_);
v_d_883_ = v_a_887_;
goto v___jp_882_;
v___jp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v_d_883_);
v___x_885_ = v___x_880_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_d_883_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_snd_878_);
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
LEAN_EXPORT lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs___boxed(lean_object* v_refs_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v_refs_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0(lean_object* v_00_u03b2_892_, lean_object* v_k_893_, lean_object* v_v_894_, lean_object* v_t_895_, lean_object* v_hl_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_893_, v_v_894_, v_t_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_merge(lean_object* v_a_904_, lean_object* v_b_905_){
_start:
{
lean_object* v_definition_x3f_906_; lean_object* v_usages_907_; lean_object* v___y_909_; 
v_definition_x3f_906_ = lean_ctor_get(v_b_905_, 0);
lean_inc(v_definition_x3f_906_);
v_usages_907_ = lean_ctor_get(v_b_905_, 1);
lean_inc_ref(v_usages_907_);
lean_dec_ref(v_b_905_);
if (lean_obj_tag(v_definition_x3f_906_) == 0)
{
lean_object* v_definition_x3f_920_; 
v_definition_x3f_920_ = lean_ctor_get(v_a_904_, 0);
lean_inc(v_definition_x3f_920_);
v___y_909_ = v_definition_x3f_920_;
goto v___jp_908_;
}
else
{
v___y_909_ = v_definition_x3f_906_;
goto v___jp_908_;
}
v___jp_908_:
{
lean_object* v_usages_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_usages_910_ = lean_ctor_get(v_a_904_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_a_904_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_a_904_, 0);
lean_dec(v_unused_919_);
v___x_912_ = v_a_904_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_usages_910_);
lean_dec(v_a_904_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = l_Array_append___redArg(v_usages_910_, v_usages_907_);
lean_dec_ref(v_usages_907_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_914_);
lean_ctor_set(v___x_912_, 0, v___y_909_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___y_909_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_914_);
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
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(uint8_t v_includeStop_921_, lean_object* v_range_922_, lean_object* v_pos_923_){
_start:
{
lean_object* v_start_924_; lean_object* v_end_925_; uint8_t v___x_926_; 
v_start_924_ = lean_ctor_get(v_range_922_, 0);
v_end_925_ = lean_ctor_get(v_range_922_, 1);
v___x_926_ = l_Lean_Lsp_instOrdPosition_ord(v_start_924_, v_pos_923_);
if (v___x_926_ == 2)
{
uint8_t v___x_927_; 
v___x_927_ = 0;
return v___x_927_;
}
else
{
if (v_includeStop_921_ == 0)
{
uint8_t v___x_928_; 
v___x_928_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_923_, v_end_925_);
if (v___x_928_ == 0)
{
uint8_t v___x_929_; 
v___x_929_ = 1;
return v___x_929_;
}
else
{
return v_includeStop_921_;
}
}
else
{
uint8_t v___x_930_; 
v___x_930_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_923_, v_end_925_);
if (v___x_930_ == 2)
{
uint8_t v___x_931_; 
v___x_931_ = 0;
return v___x_931_;
}
else
{
return v_includeStop_921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains___boxed(lean_object* v_includeStop_932_, lean_object* v_range_933_, lean_object* v_pos_934_){
_start:
{
uint8_t v_includeStop_boxed_935_; uint8_t v_res_936_; lean_object* v_r_937_; 
v_includeStop_boxed_935_ = lean_unbox(v_includeStop_932_);
v_res_936_ = l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(v_includeStop_boxed_935_, v_range_933_, v_pos_934_);
lean_dec_ref(v_pos_934_);
lean_dec_ref(v_range_933_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(uint8_t v_includeStop_941_, lean_object* v_pos_942_, lean_object* v_as_943_, size_t v_sz_944_, size_t v_i_945_, lean_object* v_b_946_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_945_, v_sz_944_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v_b_946_);
return v___x_948_;
}
else
{
lean_object* v___x_949_; lean_object* v_a_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
lean_dec_ref(v_b_946_);
v___x_949_ = lean_box(0);
v_a_950_ = lean_array_uget_borrowed(v_as_943_, v_i_945_);
v___x_951_ = l_Lean_Lsp_RefInfo_Location_range(v_a_950_);
v___x_952_ = l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(v_includeStop_941_, v___x_951_, v_pos_942_);
lean_dec_ref(v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; size_t v___x_954_; size_t v___x_955_; 
v___x_953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___closed__0));
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_945_, v___x_954_);
v_i_945_ = v___x_955_;
v_b_946_ = v___x_953_;
goto _start;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_inc(v_a_950_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v_a_950_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_949_);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___boxed(lean_object* v_includeStop_960_, lean_object* v_pos_961_, lean_object* v_as_962_, lean_object* v_sz_963_, lean_object* v_i_964_, lean_object* v_b_965_){
_start:
{
uint8_t v_includeStop_boxed_966_; size_t v_sz_boxed_967_; size_t v_i_boxed_968_; lean_object* v_res_969_; 
v_includeStop_boxed_966_ = lean_unbox(v_includeStop_960_);
v_sz_boxed_967_ = lean_unbox_usize(v_sz_963_);
lean_dec(v_sz_963_);
v_i_boxed_968_ = lean_unbox_usize(v_i_964_);
lean_dec(v_i_964_);
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(v_includeStop_boxed_966_, v_pos_961_, v_as_962_, v_sz_boxed_967_, v_i_boxed_968_, v_b_965_);
lean_dec_ref(v_as_962_);
lean_dec_ref(v_pos_961_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(lean_object* v_self_970_, lean_object* v_pos_971_, uint8_t v_includeStop_972_){
_start:
{
lean_object* v_definition_x3f_973_; lean_object* v_usages_974_; 
v_definition_x3f_973_ = lean_ctor_get(v_self_970_, 0);
v_usages_974_ = lean_ctor_get(v_self_970_, 1);
if (lean_obj_tag(v_definition_x3f_973_) == 1)
{
lean_object* v_val_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_val_983_ = lean_ctor_get(v_definition_x3f_973_, 0);
v___x_984_ = l_Lean_Lsp_RefInfo_Location_range(v_val_983_);
v___x_985_ = l___private_Lean_Server_References_0__Lean_Lsp_RefInfo_findReferenceLocation_x3f_contains(v_includeStop_972_, v___x_984_, v_pos_971_);
lean_dec_ref(v___x_984_);
if (v___x_985_ == 0)
{
goto v___jp_975_;
}
else
{
lean_inc_ref(v_definition_x3f_973_);
return v_definition_x3f_973_;
}
}
else
{
goto v___jp_975_;
}
v___jp_975_:
{
lean_object* v___x_976_; lean_object* v___x_977_; size_t v_sz_978_; size_t v___x_979_; lean_object* v___x_980_; 
v___x_976_ = lean_box(0);
v___x_977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0___closed__0));
v_sz_978_ = lean_array_size(v_usages_974_);
v___x_979_ = ((size_t)0ULL);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_RefInfo_findReferenceLocation_x3f_spec__0(v_includeStop_972_, v_pos_971_, v_usages_974_, v_sz_978_, v___x_979_, v___x_977_);
if (lean_obj_tag(v___x_980_) == 0)
{
return v___x_976_;
}
else
{
lean_object* v_val_981_; lean_object* v_fst_982_; 
v_val_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_val_981_);
lean_dec_ref(v___x_980_);
v_fst_982_ = lean_ctor_get(v_val_981_, 0);
lean_inc(v_fst_982_);
lean_dec(v_val_981_);
if (lean_obj_tag(v_fst_982_) == 0)
{
return v___x_976_;
}
else
{
return v_fst_982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_findReferenceLocation_x3f___boxed(lean_object* v_self_986_, lean_object* v_pos_987_, lean_object* v_includeStop_988_){
_start:
{
uint8_t v_includeStop_boxed_989_; lean_object* v_res_990_; 
v_includeStop_boxed_989_ = lean_unbox(v_includeStop_988_);
v_res_990_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_self_986_, v_pos_987_, v_includeStop_boxed_989_);
lean_dec_ref(v_pos_987_);
lean_dec_ref(v_self_986_);
return v_res_990_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_RefInfo_contains(lean_object* v_self_991_, lean_object* v_pos_992_, uint8_t v_includeStop_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_self_991_, v_pos_992_, v_includeStop_993_);
if (lean_obj_tag(v___x_994_) == 0)
{
uint8_t v___x_995_; 
v___x_995_ = 0;
return v___x_995_;
}
else
{
uint8_t v___x_996_; 
lean_dec_ref(v___x_994_);
v___x_996_ = 1;
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_contains___boxed(lean_object* v_self_997_, lean_object* v_pos_998_, lean_object* v_includeStop_999_){
_start:
{
uint8_t v_includeStop_boxed_1000_; uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_includeStop_boxed_1000_ = lean_unbox(v_includeStop_999_);
v_res_1001_ = l_Lean_Lsp_RefInfo_contains(v_self_997_, v_pos_998_, v_includeStop_boxed_1000_);
lean_dec_ref(v_pos_998_);
lean_dec_ref(v_self_997_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(lean_object* v_pos_1003_, uint8_t v_includeStop_1004_, lean_object* v_init_1005_, lean_object* v_x_1006_){
_start:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_object* v_k_1007_; lean_object* v_v_1008_; lean_object* v_l_1009_; lean_object* v_r_1010_; lean_object* v___x_1011_; lean_object* v_a_1012_; uint8_t v___x_1013_; 
v_k_1007_ = lean_ctor_get(v_x_1006_, 1);
lean_inc(v_k_1007_);
v_v_1008_ = lean_ctor_get(v_x_1006_, 2);
lean_inc(v_v_1008_);
v_l_1009_ = lean_ctor_get(v_x_1006_, 3);
lean_inc(v_l_1009_);
v_r_1010_ = lean_ctor_get(v_x_1006_, 4);
lean_inc(v_r_1010_);
lean_dec_ref(v_x_1006_);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1003_, v_includeStop_1004_, v_init_1005_, v_l_1009_);
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
v___x_1013_ = l_Lean_Lsp_RefInfo_contains(v_v_1008_, v_pos_1003_, v_includeStop_1004_);
lean_dec(v_v_1008_);
if (v___x_1013_ == 0)
{
lean_object* v_a_1014_; 
lean_dec(v_a_1012_);
lean_dec(v_k_1007_);
v_a_1014_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1014_);
lean_dec_ref(v___x_1011_);
v_init_1005_ = v_a_1014_;
v_x_1006_ = v_r_1010_;
goto _start;
}
else
{
lean_object* v___x_1016_; 
lean_dec_ref(v___x_1011_);
v___x_1016_ = lean_array_push(v_a_1012_, v_k_1007_);
v_init_1005_ = v___x_1016_;
v_x_1006_ = v_r_1010_;
goto _start;
}
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_init_1005_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0___boxed(lean_object* v_pos_1019_, lean_object* v_includeStop_1020_, lean_object* v_init_1021_, lean_object* v_x_1022_){
_start:
{
uint8_t v_includeStop_boxed_1023_; lean_object* v_res_1024_; 
v_includeStop_boxed_1023_ = lean_unbox(v_includeStop_1020_);
v_res_1024_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1019_, v_includeStop_boxed_1023_, v_init_1021_, v_x_1022_);
lean_dec_ref(v_pos_1019_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt(lean_object* v_self_1027_, lean_object* v_pos_1028_, uint8_t v_includeStop_1029_){
_start:
{
lean_object* v_result_1030_; lean_object* v___x_1031_; lean_object* v_a_1032_; 
v_result_1030_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_1031_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findAt_spec__0(v_pos_1028_, v_includeStop_1029_, v_result_1030_, v_self_1027_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref(v___x_1031_);
return v_a_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findAt___boxed(lean_object* v_self_1033_, lean_object* v_pos_1034_, lean_object* v_includeStop_1035_){
_start:
{
uint8_t v_includeStop_boxed_1036_; lean_object* v_res_1037_; 
v_includeStop_boxed_1036_ = lean_unbox(v_includeStop_1035_);
v_res_1037_ = l_Lean_Lsp_ModuleRefs_findAt(v_self_1033_, v_pos_1034_, v_includeStop_boxed_1036_);
lean_dec_ref(v_pos_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(lean_object* v_pos_1041_, uint8_t v_includeStop_1042_, lean_object* v_init_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v_d_1046_; 
if (lean_obj_tag(v_x_1044_) == 0)
{
lean_object* v_v_1049_; lean_object* v_l_1050_; lean_object* v_r_1051_; lean_object* v___x_1052_; lean_object* v_val_1053_; 
v_v_1049_ = lean_ctor_get(v_x_1044_, 2);
v_l_1050_ = lean_ctor_get(v_x_1044_, 3);
v_r_1051_ = lean_ctor_get(v_x_1044_, 4);
v___x_1052_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1041_, v_includeStop_1042_, v_init_1043_, v_l_1050_);
v_val_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_val_1053_);
lean_dec(v___x_1052_);
if (lean_obj_tag(v_val_1053_) == 0)
{
lean_object* v_a_1054_; 
v_a_1054_ = lean_ctor_get(v_val_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref(v_val_1053_);
v_d_1046_ = v_a_1054_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_dec_ref(v_val_1053_);
v___x_1055_ = lean_box(0);
v___x_1056_ = l_Lean_Lsp_RefInfo_findReferenceLocation_x3f(v_v_1049_, v_pos_1041_, v_includeStop_1042_);
if (lean_obj_tag(v___x_1056_) == 1)
{
lean_object* v_val_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1066_; 
v_val_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1066_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_val_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1066_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = l_Lean_Lsp_RefInfo_Location_range(v_val_1057_);
lean_dec(v_val_1057_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1055_);
v_d_1046_ = v___x_1064_;
goto v___jp_1045_;
}
}
}
else
{
lean_object* v___x_1067_; 
lean_dec(v___x_1056_);
v___x_1067_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0));
v_init_1043_ = v___x_1067_;
v_x_1044_ = v_r_1051_;
goto _start;
}
}
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_init_1043_);
v___x_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
v___jp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_d_1046_);
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___boxed(lean_object* v_pos_1071_, lean_object* v_includeStop_1072_, lean_object* v_init_1073_, lean_object* v_x_1074_){
_start:
{
uint8_t v_includeStop_boxed_1075_; lean_object* v_res_1076_; 
v_includeStop_boxed_1075_ = lean_unbox(v_includeStop_1072_);
v_res_1076_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1071_, v_includeStop_boxed_1075_, v_init_1073_, v_x_1074_);
lean_dec(v_x_1074_);
lean_dec_ref(v_pos_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f(lean_object* v_self_1077_, lean_object* v_pos_1078_, uint8_t v_includeStop_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v_val_1082_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_val_1086_; lean_object* v_a_1087_; 
v___x_1080_ = lean_box(0);
v___x_1084_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0___closed__0));
v___x_1085_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_ModuleRefs_findRange_x3f_spec__0(v_pos_1078_, v_includeStop_1079_, v___x_1084_, v_self_1077_);
v_val_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_val_1086_);
lean_dec(v___x_1085_);
v_a_1087_ = lean_ctor_get(v_val_1086_, 0);
lean_inc(v_a_1087_);
lean_dec(v_val_1086_);
v_val_1082_ = v_a_1087_;
goto v___jp_1081_;
v___jp_1081_:
{
lean_object* v_fst_1083_; 
v_fst_1083_ = lean_ctor_get(v_val_1082_, 0);
lean_inc(v_fst_1083_);
lean_dec_ref(v_val_1082_);
if (lean_obj_tag(v_fst_1083_) == 0)
{
return v___x_1080_;
}
else
{
return v_fst_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleRefs_findRange_x3f___boxed(lean_object* v_self_1088_, lean_object* v_pos_1089_, lean_object* v_includeStop_1090_){
_start:
{
uint8_t v_includeStop_boxed_1091_; lean_object* v_res_1092_; 
v_includeStop_boxed_1091_ = lean_unbox(v_includeStop_1090_);
v_res_1092_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_self_1088_, v_pos_1089_, v_includeStop_boxed_1091_);
lean_dec_ref(v_pos_1089_);
lean_dec(v_self_1088_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(lean_object* v_j_1093_, lean_object* v_k_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = l_Lean_Json_getObjValD(v_j_1093_, v_k_1094_);
v___x_1096_ = l_Lean_Json_getNat_x3f(v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0___boxed(lean_object* v_j_1097_, lean_object* v_k_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(v_j_1097_, v_k_1098_);
lean_dec_ref(v_k_1098_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(lean_object* v_j_1100_, lean_object* v_k_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = l_Lean_Json_getObjValD(v_j_1100_, v_k_1101_);
v___x_1103_ = l_Lean_Name_fromJson_x3f(v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1___boxed(lean_object* v_j_1104_, lean_object* v_k_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(v_j_1104_, v_k_1105_);
lean_dec_ref(v_k_1105_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(lean_object* v_init_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v_k_1113_; lean_object* v_v_1114_; lean_object* v_l_1115_; lean_object* v_r_1116_; lean_object* v___x_1117_; 
v_k_1113_ = lean_ctor_get(v_x_1112_, 1);
lean_inc(v_k_1113_);
v_v_1114_ = lean_ctor_get(v_x_1112_, 2);
lean_inc(v_v_1114_);
v_l_1115_ = lean_ctor_get(v_x_1112_, 3);
lean_inc(v_l_1115_);
v_r_1116_ = lean_ctor_get(v_x_1112_, 4);
lean_inc(v_r_1116_);
lean_dec_ref(v_x_1112_);
v___x_1117_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(v_init_1111_, v_l_1115_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_dec(v_r_1116_);
lean_dec(v_v_1114_);
lean_dec(v_k_1113_);
return v___x_1117_;
}
else
{
if (lean_obj_tag(v_v_1114_) == 4)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1232_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1232_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1232_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_elems_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_elems_1122_ = lean_ctor_get(v_v_1114_, 0);
lean_inc_ref(v_elems_1122_);
lean_dec_ref(v_v_1114_);
v___x_1123_ = lean_array_get_size(v_elems_1122_);
v___x_1124_ = lean_unsigned_to_nat(8u);
v___x_1125_ = lean_nat_dec_eq(v___x_1123_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_dec_ref(v_elems_1122_);
lean_dec(v_a_1118_);
lean_dec(v_r_1116_);
lean_dec(v_k_1113_);
v___x_1126_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__0));
v___x_1127_ = l_Nat_reprFast(v___x_1123_);
v___x_1128_ = lean_string_append(v___x_1126_, v___x_1127_);
lean_dec_ref(v___x_1127_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1128_);
v___x_1130_ = v___x_1120_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_del_object(v___x_1120_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get_borrowed(v___x_1132_, v_elems_1122_, v___x_1133_);
lean_inc(v___x_1134_);
v___x_1135_ = l_Lean_Json_getNat_x3f(v___x_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v_elems_1122_);
lean_dec(v_a_1118_);
lean_dec(v_r_1116_);
lean_dec(v_k_1113_);
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_a_1144_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1144_);
lean_dec_ref(v___x_1135_);
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_array_get_borrowed(v___x_1132_, v_elems_1122_, v___x_1145_);
lean_inc(v___x_1146_);
v___x_1147_ = l_Lean_Json_getNat_x3f(v___x_1146_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_a_1144_);
lean_dec_ref(v_elems_1122_);
lean_dec(v_a_1118_);
lean_dec(v_r_1116_);
lean_dec(v_k_1113_);
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1156_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1156_);
lean_dec_ref(v___x_1147_);
v___x_1157_ = lean_unsigned_to_nat(2u);
v___x_1158_ = lean_array_get_borrowed(v___x_1132_, v_elems_1122_, v___x_1157_);
lean_inc(v___x_1158_);
v___x_1159_ = l_Lean_Json_getNat_x3f(v___x_1158_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec(v_a_1156_);
lean_dec(v_a_1144_);
lean_dec_ref(v_elems_1122_);
lean_dec(v_a_1118_);
lean_dec(v_r_1116_);
lean_dec(v_k_1113_);
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_a_1168_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1168_);
lean_dec_ref(v___x_1159_);
v___x_1169_ = lean_unsigned_to_nat(3u);
v___x_1170_ = lean_array_get_borrowed(v___x_1132_, v_elems_1122_, v___x_1169_);
lean_inc(v___x_1170_);
v___x_1171_ = l_Lean_Json_getNat_x3f(v___x_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_a_1168_);
lean_dec(v_a_1156_);
lean_dec(v_a_1144_);
lean_dec_ref(v_elems_1122_);
lean_dec(v_a_1118_);
lean_dec(v_r_1116_);
lean_dec(v_k_1113_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_a_1180_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1180_);
lean_dec_ref(v___x_1171_);
v___x_1181_ = lean_unsigned_to_nat(4u);
v___x_1182_ = lean_array_get_borrowed(v___x_1132_, v_elems_1122_, v___x_1181_);
lean_inc(v___x_1182_);
v___x_1183_ = l_Lean_Json_getNat_x3f(v___x_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_a_1180_);
lean_dec(v_a_1168_);
lean_dec(v_a_1156_);
lean_dec(v_a_1144_);
lean_dec_ref(v_elems_1122_);
lean_dec(v_a_1118_);
lean_dec(v_r_1116_);
lean_dec(v_k_1113_);
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_a_1192_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1183_);
v___x_1193_ = lean_unsigned_to_nat(5u);
v___x_1194_ = lean_array_get_borrowed(v___x_1132_, v_elems_1122_, v___x_1193_);
lean_inc(v___x_1194_);
v___x_1195_ = l_Lean_Json_getNat_x3f(v___x_1194_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_a_1192_);
lean_dec(v_a_1180_);
lean_dec(v_a_1168_);
lean_dec(v_a_1156_);
lean_dec(v_a_1144_);
lean_dec_ref(v_elems_1122_);
lean_dec(v_a_1118_);
lean_dec(v_r_1116_);
lean_dec(v_k_1113_);
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_a_1204_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1195_);
v___x_1205_ = lean_unsigned_to_nat(6u);
v___x_1206_ = lean_array_get_borrowed(v___x_1132_, v_elems_1122_, v___x_1205_);
lean_inc(v___x_1206_);
v___x_1207_ = l_Lean_Json_getNat_x3f(v___x_1206_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_a_1204_);
lean_dec(v_a_1192_);
lean_dec(v_a_1180_);
lean_dec(v_a_1168_);
lean_dec(v_a_1156_);
lean_dec(v_a_1144_);
lean_dec_ref(v_elems_1122_);
lean_dec(v_a_1118_);
lean_dec(v_r_1116_);
lean_dec(v_k_1113_);
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1207_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_a_1216_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v___x_1207_);
v___x_1217_ = lean_unsigned_to_nat(7u);
v___x_1218_ = lean_array_get(v___x_1132_, v_elems_1122_, v___x_1217_);
lean_dec_ref(v_elems_1122_);
v___x_1219_ = l_Lean_Json_getNat_x3f(v___x_1218_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_a_1216_);
lean_dec(v_a_1204_);
lean_dec(v_a_1192_);
lean_dec(v_a_1180_);
lean_dec(v_a_1168_);
lean_dec(v_a_1156_);
lean_dec(v_a_1144_);
lean_dec(v_a_1118_);
lean_dec(v_r_1116_);
lean_dec(v_k_1113_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_a_1228_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1228_);
lean_dec_ref(v___x_1219_);
v___x_1229_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1144_);
lean_ctor_set(v___x_1229_, 1, v_a_1156_);
lean_ctor_set(v___x_1229_, 2, v_a_1168_);
lean_ctor_set(v___x_1229_, 3, v_a_1180_);
lean_ctor_set(v___x_1229_, 4, v_a_1192_);
lean_ctor_set(v___x_1229_, 5, v_a_1204_);
lean_ctor_set(v___x_1229_, 6, v_a_1216_);
lean_ctor_set(v___x_1229_, 7, v_a_1228_);
v___x_1230_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_k_1113_, v___x_1229_, v_a_1118_);
v_init_1111_ = v___x_1230_;
v_x_1112_ = v_r_1116_;
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
lean_object* v___x_1233_; 
lean_dec_ref(v___x_1117_);
lean_dec(v_r_1116_);
lean_dec(v_v_1114_);
lean_dec(v_k_1113_);
v___x_1233_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9___closed__2));
return v___x_1233_;
}
}
}
else
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v_init_1111_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(lean_object* v_j_1235_, lean_object* v_k_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = l_Lean_Json_getObjValD(v_j_1235_, v_k_1236_);
v___x_1238_ = l_Lean_Json_getObj_x3f(v___x_1237_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_a_1247_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1238_);
v___x_1248_ = lean_box(1);
v___x_1249_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4_spec__9(v___x_1248_, v_a_1247_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4___boxed(lean_object* v_j_1250_, lean_object* v_k_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(v_j_1250_, v_k_1251_);
lean_dec_ref(v_k_1251_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(size_t v_sz_1253_, size_t v_i_1254_, lean_object* v_bs_1255_){
_start:
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_usize_dec_lt(v_i_1254_, v_sz_1253_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_bs_1255_);
return v___x_1257_;
}
else
{
lean_object* v_v_1258_; lean_object* v___x_1259_; lean_object* v_bs_x27_1260_; size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v_v_1258_ = lean_array_uget(v_bs_1255_, v_i_1254_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v_bs_x27_1260_ = lean_array_uset(v_bs_1255_, v_i_1254_, v___x_1259_);
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_add(v_i_1254_, v___x_1261_);
v___x_1263_ = lean_array_uset(v_bs_x27_1260_, v_i_1254_, v_v_1258_);
v_i_1254_ = v___x_1262_;
v_bs_1255_ = v___x_1263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13___boxed(lean_object* v_sz_1265_, lean_object* v_i_1266_, lean_object* v_bs_1267_){
_start:
{
size_t v_sz_boxed_1268_; size_t v_i_boxed_1269_; lean_object* v_res_1270_; 
v_sz_boxed_1268_ = lean_unbox_usize(v_sz_1265_);
lean_dec(v_sz_1265_);
v_i_boxed_1269_ = lean_unbox_usize(v_i_1266_);
lean_dec(v_i_1266_);
v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(v_sz_boxed_1268_, v_i_boxed_1269_, v_bs_1267_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(lean_object* v_x_1273_){
_start:
{
if (lean_obj_tag(v_x_1273_) == 4)
{
lean_object* v_elems_1274_; size_t v_sz_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v_elems_1274_ = lean_ctor_get(v_x_1273_, 0);
lean_inc_ref(v_elems_1274_);
lean_dec_ref(v_x_1273_);
v_sz_1275_ = lean_array_size(v_elems_1274_);
v___x_1276_ = ((size_t)0ULL);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8_spec__13(v_sz_1275_, v___x_1276_, v_elems_1274_);
return v___x_1277_;
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1278_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1279_ = lean_unsigned_to_nat(80u);
v___x_1280_ = l_Lean_Json_pretty(v_x_1273_, v___x_1279_);
v___x_1281_ = lean_string_append(v___x_1278_, v___x_1280_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1283_ = lean_string_append(v___x_1281_, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(size_t v_sz_1285_, size_t v_i_1286_, lean_object* v_bs_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_usize_dec_lt(v_i_1286_, v_sz_1285_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v_bs_1287_);
return v___x_1289_;
}
else
{
lean_object* v_v_1290_; lean_object* v___x_1291_; 
v_v_1290_ = lean_array_uget_borrowed(v_bs_1287_, v_i_1286_);
lean_inc(v_v_1290_);
v___x_1291_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(v_v_1290_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_bs_1287_);
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1301_; lean_object* v_bs_x27_1302_; size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v_a_1300_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1300_);
lean_dec_ref(v___x_1291_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v_bs_x27_1302_ = lean_array_uset(v_bs_1287_, v_i_1286_, v___x_1301_);
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_add(v_i_1286_, v___x_1303_);
v___x_1305_ = lean_array_uset(v_bs_x27_1302_, v_i_1286_, v_a_1300_);
v_i_1286_ = v___x_1304_;
v_bs_1287_ = v___x_1305_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9___boxed(lean_object* v_sz_1307_, lean_object* v_i_1308_, lean_object* v_bs_1309_){
_start:
{
size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1307_);
lean_dec(v_sz_1307_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(v_sz_boxed_1310_, v_i_boxed_1311_, v_bs_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(lean_object* v_x_1313_){
_start:
{
if (lean_obj_tag(v_x_1313_) == 4)
{
lean_object* v_elems_1314_; size_t v_sz_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v_elems_1314_ = lean_ctor_get(v_x_1313_, 0);
lean_inc_ref(v_elems_1314_);
lean_dec_ref(v_x_1313_);
v_sz_1315_ = lean_array_size(v_elems_1314_);
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__9(v_sz_1315_, v___x_1316_, v_elems_1314_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1318_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1319_ = lean_unsigned_to_nat(80u);
v___x_1320_ = l_Lean_Json_pretty(v_x_1313_, v___x_1319_);
v___x_1321_ = lean_string_append(v___x_1318_, v___x_1320_);
lean_dec_ref(v___x_1320_);
v___x_1322_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1323_ = lean_string_append(v___x_1321_, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(lean_object* v_j_1325_, lean_object* v_k_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = l_Lean_Json_getObjValD(v_j_1325_, v_k_1326_);
v___x_1328_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6(v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4___boxed(lean_object* v_j_1329_, lean_object* v_k_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(v_j_1329_, v_k_1330_);
lean_dec_ref(v_k_1330_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(size_t v_sz_1334_, size_t v_i_1335_, lean_object* v_bs_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_lt(v_i_1335_, v_sz_1334_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_bs_1336_);
return v___x_1338_;
}
else
{
lean_object* v_v_1339_; lean_object* v___x_1340_; lean_object* v_bs_x27_1341_; lean_object* v_a_1343_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1414_; 
v_v_1339_ = lean_array_uget(v_bs_1336_, v_i_1335_);
v___x_1340_ = lean_unsigned_to_nat(0u);
v_bs_x27_1341_ = lean_array_uset(v_bs_1336_, v_i_1335_, v___x_1340_);
v___x_1348_ = lean_array_get_size(v_v_1339_);
v___x_1349_ = lean_unsigned_to_nat(4u);
v___x_1414_ = lean_nat_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1414_ == 0)
{
if (v___x_1337_ == 0)
{
goto v___jp_1350_;
}
else
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = lean_unsigned_to_nat(5u);
v___x_1416_ = lean_nat_dec_eq(v___x_1348_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec_ref(v_bs_x27_1341_);
lean_dec(v_v_1339_);
v___x_1417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1418_ = l_Nat_reprFast(v___x_1348_);
v___x_1419_ = lean_string_append(v___x_1417_, v___x_1418_);
lean_dec_ref(v___x_1418_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
else
{
goto v___jp_1350_;
}
}
}
else
{
goto v___jp_1350_;
}
v___jp_1342_:
{
size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_add(v_i_1335_, v___x_1344_);
v___x_1346_ = lean_array_uset(v_bs_x27_1341_, v_i_1335_, v_a_1343_);
v_i_1335_ = v___x_1345_;
v_bs_1336_ = v___x_1346_;
goto _start;
}
v___jp_1350_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_array_fget_borrowed(v_v_1339_, v___x_1340_);
lean_inc(v___x_1351_);
v___x_1352_ = l_Lean_Json_getNat_x3f(v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_bs_x27_1341_);
lean_dec(v_v_1339_);
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
lean_dec_ref(v___x_1352_);
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_array_fget_borrowed(v_v_1339_, v___x_1362_);
lean_inc(v___x_1363_);
v___x_1364_ = l_Lean_Json_getNat_x3f(v___x_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_a_1361_);
lean_dec_ref(v_bs_x27_1341_);
lean_dec(v_v_1339_);
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
lean_dec_ref(v___x_1364_);
v___x_1374_ = lean_unsigned_to_nat(2u);
v___x_1375_ = lean_array_fget_borrowed(v_v_1339_, v___x_1374_);
lean_inc(v___x_1375_);
v___x_1376_ = l_Lean_Json_getNat_x3f(v___x_1375_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_a_1373_);
lean_dec(v_a_1361_);
lean_dec_ref(v_bs_x27_1341_);
lean_dec(v_v_1339_);
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
lean_dec_ref(v___x_1376_);
v___x_1386_ = lean_unsigned_to_nat(3u);
v___x_1387_ = lean_array_fget_borrowed(v_v_1339_, v___x_1386_);
lean_inc(v___x_1387_);
v___x_1388_ = l_Lean_Json_getNat_x3f(v___x_1387_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec(v_a_1385_);
lean_dec(v_a_1373_);
lean_dec(v_a_1361_);
lean_dec_ref(v_bs_x27_1341_);
lean_dec(v_v_1339_);
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
lean_object* v_a_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_a_1397_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1397_);
lean_dec_ref(v___x_1388_);
v___x_1398_ = lean_unsigned_to_nat(5u);
v___x_1399_ = lean_nat_dec_eq(v___x_1348_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_dec(v_v_1339_);
v___x_1400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
v___x_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1401_, 0, v_a_1361_);
lean_ctor_set(v___x_1401_, 1, v_a_1373_);
lean_ctor_set(v___x_1401_, 2, v_a_1385_);
lean_ctor_set(v___x_1401_, 3, v_a_1397_);
lean_ctor_set(v___x_1401_, 4, v___x_1400_);
v_a_1343_ = v___x_1401_;
goto v___jp_1342_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_array_fget(v_v_1339_, v___x_1349_);
lean_dec(v_v_1339_);
v___x_1403_ = l_Lean_Json_getStr_x3f(v___x_1402_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec(v_a_1397_);
lean_dec(v_a_1385_);
lean_dec(v_a_1373_);
lean_dec(v_a_1361_);
lean_dec_ref(v_bs_x27_1341_);
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1403_);
v___x_1413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1413_, 0, v_a_1361_);
lean_ctor_set(v___x_1413_, 1, v_a_1373_);
lean_ctor_set(v___x_1413_, 2, v_a_1385_);
lean_ctor_set(v___x_1413_, 3, v_a_1397_);
lean_ctor_set(v___x_1413_, 4, v_a_1412_);
v_a_1343_ = v___x_1413_;
goto v___jp_1342_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___boxed(lean_object* v_sz_1421_, lean_object* v_i_1422_, lean_object* v_bs_1423_){
_start:
{
size_t v_sz_boxed_1424_; size_t v_i_boxed_1425_; lean_object* v_res_1426_; 
v_sz_boxed_1424_ = lean_unbox_usize(v_sz_1421_);
lean_dec(v_sz_1421_);
v_i_boxed_1425_ = lean_unbox_usize(v_i_1422_);
lean_dec(v_i_1422_);
v_res_1426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_boxed_1424_, v_i_boxed_1425_, v_bs_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(lean_object* v_x_1429_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9___closed__0));
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8(v_x_1429_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v_a_1440_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1442_ = v___x_1431_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1431_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_a_1440_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(lean_object* v_j_1449_, lean_object* v_k_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = l_Lean_Json_getObjValD(v_j_1449_, v_k_1450_);
v___x_1452_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6_spec__9(v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6___boxed(lean_object* v_j_1453_, lean_object* v_k_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_j_1453_, v_k_1454_);
lean_dec_ref(v_k_1454_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(lean_object* v_init_1458_, lean_object* v_x_1459_){
_start:
{
if (lean_obj_tag(v_x_1459_) == 0)
{
lean_object* v_k_1460_; lean_object* v_v_1461_; lean_object* v_l_1462_; lean_object* v_r_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1623_; 
v_k_1460_ = lean_ctor_get(v_x_1459_, 1);
v_v_1461_ = lean_ctor_get(v_x_1459_, 2);
v_l_1462_ = lean_ctor_get(v_x_1459_, 3);
v_r_1463_ = lean_ctor_get(v_x_1459_, 4);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_x_1459_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v_x_1459_, 0);
lean_dec(v_unused_1624_);
v___x_1465_ = v_x_1459_;
v_isShared_1466_ = v_isSharedCheck_1623_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_r_1463_);
lean_inc(v_l_1462_);
lean_inc(v_v_1461_);
lean_inc(v_k_1460_);
lean_dec(v_x_1459_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1623_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v_init_1458_, v_l_1462_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
lean_dec(v_k_1460_);
return v___x_1467_;
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1622_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1622_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1622_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Json_parse(v_k_1460_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1482_; 
v_a_1481_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1481_);
lean_dec_ref(v___x_1472_);
v___x_1482_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1481_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v_definition_x3f_1493_; lean_object* v_a_1521_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_a_1491_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1491_);
lean_dec_ref(v___x_1482_);
v___x_1525_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
lean_inc(v_v_1461_);
v___x_1526_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__6(v_v_1461_, v___x_1525_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_a_1491_);
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1621_; 
v_a_1535_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1537_ = v___x_1526_;
v_isShared_1538_ = v_isSharedCheck_1621_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1526_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1621_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
if (lean_obj_tag(v_a_1535_) == 0)
{
lean_object* v___x_1539_; 
lean_del_object(v___x_1537_);
lean_del_object(v___x_1470_);
lean_del_object(v___x_1465_);
v___x_1539_ = lean_box(0);
v_definition_x3f_1493_ = v___x_1539_;
goto v___jp_1492_;
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1612_; 
v_val_1540_ = lean_ctor_get(v_a_1535_, 0);
lean_inc(v_val_1540_);
lean_dec_ref(v_a_1535_);
v___x_1541_ = lean_array_get_size(v_val_1540_);
v___x_1542_ = lean_unsigned_to_nat(4u);
v___x_1612_ = lean_nat_dec_eq(v___x_1541_, v___x_1542_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = lean_unsigned_to_nat(5u);
v___x_1614_ = lean_nat_dec_eq(v___x_1541_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_dec(v_val_1540_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
v___x_1615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__1));
v___x_1616_ = l_Nat_reprFast(v___x_1541_);
v___x_1617_ = lean_string_append(v___x_1615_, v___x_1616_);
lean_dec_ref(v___x_1616_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1617_);
v___x_1619_ = v___x_1537_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
else
{
lean_del_object(v___x_1537_);
goto v___jp_1543_;
}
}
else
{
lean_del_object(v___x_1537_);
goto v___jp_1543_;
}
v___jp_1543_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_array_fget_borrowed(v_val_1540_, v___x_1544_);
lean_inc(v___x_1545_);
v___x_1546_ = l_Lean_Json_getNat_x3f(v___x_1545_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_val_1540_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_a_1555_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1546_);
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_array_fget_borrowed(v_val_1540_, v___x_1556_);
lean_inc(v___x_1557_);
v___x_1558_ = l_Lean_Json_getNat_x3f(v___x_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1555_);
lean_dec(v_val_1540_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1567_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1558_);
v___x_1568_ = lean_unsigned_to_nat(2u);
v___x_1569_ = lean_array_fget_borrowed(v_val_1540_, v___x_1568_);
lean_inc(v___x_1569_);
v___x_1570_ = l_Lean_Json_getNat_x3f(v___x_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_a_1567_);
lean_dec(v_a_1555_);
lean_dec(v_val_1540_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_a_1579_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___x_1570_);
v___x_1580_ = lean_unsigned_to_nat(3u);
v___x_1581_ = lean_array_fget_borrowed(v_val_1540_, v___x_1580_);
lean_inc(v___x_1581_);
v___x_1582_ = l_Lean_Json_getNat_x3f(v___x_1581_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_a_1579_);
lean_dec(v_a_1567_);
lean_dec(v_a_1555_);
lean_dec(v_val_1540_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_a_1591_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1582_);
v___x_1592_ = lean_unsigned_to_nat(5u);
v___x_1593_ = lean_nat_dec_eq(v___x_1541_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
lean_dec(v_val_1540_);
v___x_1594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5___closed__0));
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v___x_1594_);
lean_ctor_set(v___x_1465_, 3, v_a_1591_);
lean_ctor_set(v___x_1465_, 2, v_a_1579_);
lean_ctor_set(v___x_1465_, 1, v_a_1567_);
lean_ctor_set(v___x_1465_, 0, v_a_1555_);
v___x_1596_ = v___x_1465_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1555_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_a_1567_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_a_1579_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_a_1591_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
v_a_1521_ = v___x_1596_;
goto v___jp_1520_;
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_array_fget(v_val_1540_, v___x_1542_);
lean_dec(v_val_1540_);
v___x_1599_ = l_Lean_Json_getStr_x3f(v___x_1598_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_a_1591_);
lean_dec(v_a_1579_);
lean_dec(v_a_1567_);
lean_dec(v_a_1555_);
lean_dec(v_a_1491_);
lean_del_object(v___x_1470_);
lean_dec(v_a_1468_);
lean_del_object(v___x_1465_);
lean_dec(v_r_1463_);
lean_dec(v_v_1461_);
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; 
v_a_1608_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1608_);
lean_dec_ref(v___x_1599_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v_a_1608_);
lean_ctor_set(v___x_1465_, 3, v_a_1591_);
lean_ctor_set(v___x_1465_, 2, v_a_1579_);
lean_ctor_set(v___x_1465_, 1, v_a_1567_);
lean_ctor_set(v___x_1465_, 0, v_a_1555_);
v___x_1610_ = v___x_1465_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1555_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1567_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_a_1579_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_a_1591_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_a_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
v_a_1521_ = v___x_1610_;
goto v___jp_1520_;
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
v___jp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v___x_1495_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4(v_v_1461_, v___x_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_definition_x3f_1493_);
lean_dec(v_a_1491_);
lean_dec(v_a_1468_);
lean_dec(v_r_1463_);
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
else
{
lean_object* v_a_1504_; size_t v_sz_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v_a_1504_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1495_);
v_sz_1505_ = lean_array_size(v_a_1504_);
v___x_1506_ = ((size_t)0ULL);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__5(v_sz_1505_, v___x_1506_, v_a_1504_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_definition_x3f_1493_);
lean_dec(v_a_1491_);
lean_dec(v_a_1468_);
lean_dec(v_r_1463_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v_a_1516_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v___x_1507_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_definition_x3f_1493_);
lean_ctor_set(v___x_1517_, 1, v_a_1516_);
v___x_1518_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_a_1491_, v___x_1517_, v_a_1468_);
v_init_1458_ = v___x_1518_;
v_x_1459_ = v_r_1463_;
goto _start;
}
}
}
v___jp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v_a_1521_);
v___x_1523_ = v___x_1470_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
v_definition_x3f_1493_ = v___x_1523_;
goto v___jp_1492_;
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
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_init_1458_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(lean_object* v_j_1626_, lean_object* v_k_1627_){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = l_Lean_Json_getObjValD(v_j_1626_, v_k_1627_);
v___x_1629_ = l_Lean_Json_getObj_x3f(v___x_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_a_1638_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1638_);
lean_dec_ref(v___x_1629_);
v___x_1639_ = lean_box(1);
v___x_1640_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7(v___x_1639_, v_a_1638_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3___boxed(lean_object* v_j_1641_, lean_object* v_k_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_j_1641_, v_k_1642_);
lean_dec_ref(v_k_1642_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1647_, size_t v_i_1648_, lean_object* v_bs_1649_){
_start:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_usize_dec_lt(v_i_1648_, v_sz_1647_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_bs_1649_);
return v___x_1653_;
}
else
{
lean_object* v_v_1654_; 
v_v_1654_ = lean_array_uget_borrowed(v_bs_1649_, v_i_1648_);
if (lean_obj_tag(v_v_1654_) == 4)
{
lean_object* v_elems_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v_elems_1655_ = lean_ctor_get(v_v_1654_, 0);
v___x_1656_ = lean_array_get_size(v_elems_1655_);
v___x_1657_ = lean_unsigned_to_nat(4u);
v___x_1658_ = lean_nat_dec_eq(v___x_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_dec_ref(v_bs_1649_);
goto v___jp_1650_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_unsigned_to_nat(0u);
v___x_1660_ = lean_array_fget_borrowed(v_elems_1655_, v___x_1659_);
lean_inc(v___x_1660_);
v___x_1661_ = l_Lean_Json_getStr_x3f(v___x_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v_bs_1649_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_a_1670_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v___x_1661_);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_array_fget_borrowed(v_elems_1655_, v___x_1671_);
v___x_1673_ = l_Lean_Json_getBool_x3f(v___x_1672_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_a_1670_);
lean_dec_ref(v_bs_1649_);
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_a_1682_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1682_);
lean_dec_ref(v___x_1673_);
v___x_1683_ = lean_unsigned_to_nat(2u);
v___x_1684_ = lean_array_fget_borrowed(v_elems_1655_, v___x_1683_);
v___x_1685_ = l_Lean_Json_getBool_x3f(v___x_1684_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_a_1682_);
lean_dec(v_a_1670_);
lean_dec_ref(v_bs_1649_);
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_a_1694_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1685_);
v___x_1695_ = lean_unsigned_to_nat(3u);
v___x_1696_ = lean_array_fget_borrowed(v_elems_1655_, v___x_1695_);
v___x_1697_ = l_Lean_Json_getBool_x3f(v___x_1696_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_a_1694_);
lean_dec(v_a_1682_);
lean_dec(v_a_1670_);
lean_dec_ref(v_bs_1649_);
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v_bs_x27_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; uint8_t v___x_1710_; uint8_t v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; lean_object* v___x_1714_; 
v_a_1706_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1697_);
v_bs_x27_1707_ = lean_array_uset(v_bs_1649_, v_i_1648_, v___x_1659_);
v___x_1708_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1708_, 0, v_a_1670_);
v___x_1709_ = lean_unbox(v_a_1682_);
lean_dec(v_a_1682_);
lean_ctor_set_uint8(v___x_1708_, sizeof(void*)*1, v___x_1709_);
v___x_1710_ = lean_unbox(v_a_1694_);
lean_dec(v_a_1694_);
lean_ctor_set_uint8(v___x_1708_, sizeof(void*)*1 + 1, v___x_1710_);
v___x_1711_ = lean_unbox(v_a_1706_);
lean_dec(v_a_1706_);
lean_ctor_set_uint8(v___x_1708_, sizeof(void*)*1 + 2, v___x_1711_);
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_add(v_i_1648_, v___x_1712_);
v___x_1714_ = lean_array_uset(v_bs_x27_1707_, v_i_1648_, v___x_1708_);
v_i_1648_ = v___x_1713_;
v_bs_1649_ = v___x_1714_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1649_);
goto v___jp_1650_;
}
}
v___jp_1650_:
{
lean_object* v___x_1651_; 
v___x_1651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___closed__1));
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1716_, lean_object* v_i_1717_, lean_object* v_bs_1718_){
_start:
{
size_t v_sz_boxed_1719_; size_t v_i_boxed_1720_; lean_object* v_res_1721_; 
v_sz_boxed_1719_ = lean_unbox_usize(v_sz_1716_);
lean_dec(v_sz_1716_);
v_i_boxed_1720_ = lean_unbox_usize(v_i_1717_);
lean_dec(v_i_1717_);
v_res_1721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1719_, v_i_boxed_1720_, v_bs_1718_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(lean_object* v_x_1722_){
_start:
{
if (lean_obj_tag(v_x_1722_) == 4)
{
lean_object* v_elems_1723_; size_t v_sz_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
v_elems_1723_ = lean_ctor_get(v_x_1722_, 0);
lean_inc_ref(v_elems_1723_);
lean_dec_ref(v_x_1722_);
v_sz_1724_ = lean_array_size(v_elems_1723_);
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2_spec__3(v_sz_1724_, v___x_1725_, v_elems_1723_);
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1727_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__0));
v___x_1728_ = lean_unsigned_to_nat(80u);
v___x_1729_ = l_Lean_Json_pretty(v_x_1722_, v___x_1728_);
v___x_1730_ = lean_string_append(v___x_1727_, v___x_1729_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__4_spec__6_spec__8___closed__1));
v___x_1732_ = lean_string_append(v___x_1730_, v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(lean_object* v_j_1734_, lean_object* v_k_1735_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = l_Lean_Json_getObjValD(v_j_1734_, v_k_1735_);
v___x_1737_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2_spec__2(v___x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2___boxed(lean_object* v_j_1738_, lean_object* v_k_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_j_1738_, v_k_1739_);
lean_dec_ref(v_k_1739_);
return v_res_1740_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = 1;
v___x_1750_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__4));
v___x_1751_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1750_, v___x_1749_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__6));
v___x_1754_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__5, &l_Lean_Server_instFromJsonIlean_fromJson___closed__5_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__5);
v___x_1755_ = lean_string_append(v___x_1754_, v___x_1753_);
return v___x_1755_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = 1;
v___x_1759_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__8));
v___x_1760_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1759_, v___x_1758_);
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__9, &l_Lean_Server_instFromJsonIlean_fromJson___closed__9_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__9);
v___x_1762_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1763_ = lean_string_append(v___x_1762_, v___x_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1766_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__10, &l_Lean_Server_instFromJsonIlean_fromJson___closed__10_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__10);
v___x_1767_ = lean_string_append(v___x_1766_, v___x_1765_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = 1;
v___x_1772_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__14));
v___x_1773_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1772_, v___x_1771_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__15, &l_Lean_Server_instFromJsonIlean_fromJson___closed__15_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__15);
v___x_1775_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1776_ = lean_string_append(v___x_1775_, v___x_1774_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1778_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__16, &l_Lean_Server_instFromJsonIlean_fromJson___closed__16_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__16);
v___x_1779_ = lean_string_append(v___x_1778_, v___x_1777_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = 1;
v___x_1784_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__19));
v___x_1785_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1784_, v___x_1783_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__20, &l_Lean_Server_instFromJsonIlean_fromJson___closed__20_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__20);
v___x_1787_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1788_ = lean_string_append(v___x_1787_, v___x_1786_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1790_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__21, &l_Lean_Server_instFromJsonIlean_fromJson___closed__21_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__21);
v___x_1791_ = lean_string_append(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = 1;
v___x_1796_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__24));
v___x_1797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1796_, v___x_1795_);
return v___x_1797_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__25, &l_Lean_Server_instFromJsonIlean_fromJson___closed__25_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__25);
v___x_1799_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1800_ = lean_string_append(v___x_1799_, v___x_1798_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1802_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__26, &l_Lean_Server_instFromJsonIlean_fromJson___closed__26_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__26);
v___x_1803_ = lean_string_append(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30(void){
_start:
{
uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = 1;
v___x_1808_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__29));
v___x_1809_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__30, &l_Lean_Server_instFromJsonIlean_fromJson___closed__30_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__30);
v___x_1811_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__7, &l_Lean_Server_instFromJsonIlean_fromJson___closed__7_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__7);
v___x_1812_ = lean_string_append(v___x_1811_, v___x_1810_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_1814_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__31, &l_Lean_Server_instFromJsonIlean_fromJson___closed__31_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__31);
v___x_1815_ = lean_string_append(v___x_1814_, v___x_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instFromJsonIlean_fromJson(lean_object* v_json_1816_){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
lean_inc(v_json_1816_);
v___x_1818_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__0(v_json_1816_, v___x_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_json_1816_);
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1828_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1828_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1823_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__12, &l_Lean_Server_instFromJsonIlean_fromJson___closed__12_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__12);
v___x_1824_ = lean_string_append(v___x_1823_, v_a_1819_);
lean_dec(v_a_1819_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1824_);
v___x_1826_ = v___x_1821_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
else
{
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec(v_json_1816_);
v_a_1829_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1818_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1818_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set_tag(v___x_1831_, 0);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v_a_1837_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1818_);
v___x_1838_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
lean_inc(v_json_1816_);
v___x_1839_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__1(v_json_1816_, v___x_1838_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v_a_1837_);
lean_dec(v_json_1816_);
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1849_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1849_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1844_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__17, &l_Lean_Server_instFromJsonIlean_fromJson___closed__17_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__17);
v___x_1845_ = lean_string_append(v___x_1844_, v_a_1840_);
lean_dec(v_a_1840_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1845_);
v___x_1847_ = v___x_1842_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec(v_a_1837_);
lean_dec(v_json_1816_);
v_a_1850_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1839_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1839_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 0);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v_a_1858_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1839_);
v___x_1859_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
lean_inc(v_json_1816_);
v___x_1860_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__2(v_json_1816_, v___x_1859_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_a_1858_);
lean_dec(v_a_1837_);
lean_dec(v_json_1816_);
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1870_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1870_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1865_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__22, &l_Lean_Server_instFromJsonIlean_fromJson___closed__22_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__22);
v___x_1866_ = lean_string_append(v___x_1865_, v_a_1861_);
lean_dec(v_a_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1866_);
v___x_1868_ = v___x_1863_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
else
{
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_a_1858_);
lean_dec(v_a_1837_);
lean_dec(v_json_1816_);
v_a_1871_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1860_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1860_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 0);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
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
lean_object* v_a_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_a_1879_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1860_);
v___x_1880_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
lean_inc(v_json_1816_);
v___x_1881_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3(v_json_1816_, v___x_1880_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_a_1879_);
lean_dec(v_a_1858_);
lean_dec(v_a_1837_);
lean_dec(v_json_1816_);
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1891_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1891_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1886_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__27, &l_Lean_Server_instFromJsonIlean_fromJson___closed__27_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__27);
v___x_1887_ = lean_string_append(v___x_1886_, v_a_1882_);
lean_dec(v_a_1882_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1887_);
v___x_1889_ = v___x_1884_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v_a_1879_);
lean_dec(v_a_1858_);
lean_dec(v_a_1837_);
lean_dec(v_json_1816_);
v_a_1892_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1881_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1881_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 0);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v_a_1900_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1881_);
v___x_1901_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_1902_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__4(v_json_1816_, v___x_1901_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_a_1900_);
lean_dec(v_a_1879_);
lean_dec(v_a_1858_);
lean_dec(v_a_1837_);
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1912_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1912_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1907_ = lean_obj_once(&l_Lean_Server_instFromJsonIlean_fromJson___closed__32, &l_Lean_Server_instFromJsonIlean_fromJson___closed__32_once, _init_l_Lean_Server_instFromJsonIlean_fromJson___closed__32);
v___x_1908_ = lean_string_append(v___x_1907_, v_a_1903_);
lean_dec(v_a_1903_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1908_);
v___x_1910_ = v___x_1905_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
else
{
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_a_1900_);
lean_dec(v_a_1879_);
lean_dec(v_a_1858_);
lean_dec(v_a_1837_);
v_a_1913_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1902_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1902_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set_tag(v___x_1915_, 0);
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
v_a_1921_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1923_ = v___x_1902_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1902_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1925_, 0, v_a_1837_);
lean_ctor_set(v___x_1925_, 1, v_a_1858_);
lean_ctor_set(v___x_1925_, 2, v_a_1879_);
lean_ctor_set(v___x_1925_, 3, v_a_1900_);
lean_ctor_set(v___x_1925_, 4, v_a_1921_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
if (lean_obj_tag(v_a_1932_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = l_List_reverse___redArg(v_a_1933_);
return v___x_1934_;
}
else
{
lean_object* v_head_1935_; lean_object* v_tail_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1946_; 
v_head_1935_ = lean_ctor_get(v_a_1932_, 0);
v_tail_1936_ = lean_ctor_get(v_a_1932_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_a_1932_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1938_ = v_a_1932_;
v_isShared_1939_ = v_isSharedCheck_1946_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_tail_1936_);
lean_inc(v_head_1935_);
lean_dec(v_a_1932_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1946_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1940_ = l_Lean_JsonNumber_fromNat(v_head_1935_);
v___x_1941_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v_a_1933_);
lean_ctor_set(v___x_1938_, 0, v___x_1941_);
v___x_1943_ = v___x_1938_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_a_1933_);
v___x_1943_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
v_a_1932_ = v_tail_1936_;
v_a_1933_ = v___x_1943_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(size_t v_sz_1947_, size_t v_i_1948_, lean_object* v_bs_1949_){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_usize_dec_lt(v_i_1948_, v_sz_1947_);
if (v___x_1950_ == 0)
{
return v_bs_1949_;
}
else
{
lean_object* v_v_1951_; lean_object* v___x_1952_; lean_object* v_bs_x27_1953_; size_t v___x_1954_; size_t v___x_1955_; lean_object* v___x_1956_; 
v_v_1951_ = lean_array_uget(v_bs_1949_, v_i_1948_);
v___x_1952_ = lean_unsigned_to_nat(0u);
v_bs_x27_1953_ = lean_array_uset(v_bs_1949_, v_i_1948_, v___x_1952_);
v___x_1954_ = ((size_t)1ULL);
v___x_1955_ = lean_usize_add(v_i_1948_, v___x_1954_);
v___x_1956_ = lean_array_uset(v_bs_x27_1953_, v_i_1948_, v_v_1951_);
v_i_1948_ = v___x_1955_;
v_bs_1949_ = v___x_1956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11___boxed(lean_object* v_sz_1958_, lean_object* v_i_1959_, lean_object* v_bs_1960_){
_start:
{
size_t v_sz_boxed_1961_; size_t v_i_boxed_1962_; lean_object* v_res_1963_; 
v_sz_boxed_1961_ = lean_unbox_usize(v_sz_1958_);
lean_dec(v_sz_1958_);
v_i_boxed_1962_ = lean_unbox_usize(v_i_1959_);
lean_dec(v_i_1959_);
v_res_1963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_boxed_1961_, v_i_boxed_1962_, v_bs_1960_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(lean_object* v_a_1964_){
_start:
{
size_t v_sz_1965_; size_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_sz_1965_ = lean_array_size(v_a_1964_);
v___x_1966_ = ((size_t)0ULL);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2_spec__11(v_sz_1965_, v___x_1966_, v_a_1964_);
v___x_1968_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(lean_object* v_a_1969_){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_array_mk(v_a_1969_);
v___x_1971_ = l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1_spec__2(v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(size_t v_sz_1972_, size_t v_i_1973_, lean_object* v_bs_1974_){
_start:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_usize_dec_lt(v_i_1973_, v_sz_1972_);
if (v___x_1975_ == 0)
{
return v_bs_1974_;
}
else
{
lean_object* v_v_1976_; lean_object* v___x_1977_; lean_object* v_bs_x27_1978_; lean_object* v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v_v_1976_ = lean_array_uget(v_bs_1974_, v_i_1973_);
v___x_1977_ = lean_unsigned_to_nat(0u);
v_bs_x27_1978_ = lean_array_uset(v_bs_1974_, v_i_1973_, v___x_1977_);
v___x_1979_ = l_List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_v_1976_);
v___x_1980_ = ((size_t)1ULL);
v___x_1981_ = lean_usize_add(v_i_1973_, v___x_1980_);
v___x_1982_ = lean_array_uset(v_bs_x27_1978_, v_i_1973_, v___x_1979_);
v_i_1973_ = v___x_1981_;
v_bs_1974_ = v___x_1982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4___boxed(lean_object* v_sz_1984_, lean_object* v_i_1985_, lean_object* v_bs_1986_){
_start:
{
size_t v_sz_boxed_1987_; size_t v_i_boxed_1988_; lean_object* v_res_1989_; 
v_sz_boxed_1987_ = lean_unbox_usize(v_sz_1984_);
lean_dec(v_sz_1984_);
v_i_boxed_1988_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_boxed_1987_, v_i_boxed_1988_, v_bs_1986_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(lean_object* v_a_1990_){
_start:
{
size_t v_sz_1991_; size_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_sz_1991_ = lean_array_size(v_a_1990_);
v___x_1992_ = ((size_t)0ULL);
v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3_spec__4(v_sz_1991_, v___x_1992_, v_a_1990_);
v___x_1994_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(lean_object* v_x_1995_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_box(0);
return v___x_1996_;
}
else
{
lean_object* v_val_1997_; lean_object* v___x_1998_; 
v_val_1997_ = lean_ctor_get(v_x_1995_, 0);
lean_inc(v_val_1997_);
lean_dec_ref(v_x_1995_);
v___x_1998_ = l_List_toJson___at___00Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1_spec__1(v_val_1997_);
return v___x_1998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(size_t v_sz_1999_, size_t v_i_2000_, lean_object* v_bs_2001_){
_start:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_usize_dec_lt(v_i_2000_, v_sz_1999_);
if (v___x_2002_ == 0)
{
return v_bs_2001_;
}
else
{
lean_object* v_v_2003_; lean_object* v_startPosLine_2004_; lean_object* v_startPosCharacter_2005_; lean_object* v_endPosLine_2006_; lean_object* v_endPosCharacter_2007_; lean_object* v___x_2008_; lean_object* v_bs_x27_2009_; lean_object* v___y_2011_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v_range_2021_; lean_object* v___x_2022_; 
v_v_2003_ = lean_array_uget(v_bs_2001_, v_i_2000_);
v_startPosLine_2004_ = lean_ctor_get(v_v_2003_, 0);
v_startPosCharacter_2005_ = lean_ctor_get(v_v_2003_, 1);
v_endPosLine_2006_ = lean_ctor_get(v_v_2003_, 2);
v_endPosCharacter_2007_ = lean_ctor_get(v_v_2003_, 3);
v___x_2008_ = lean_unsigned_to_nat(0u);
v_bs_x27_2009_ = lean_array_uset(v_bs_2001_, v_i_2000_, v___x_2008_);
v___x_2016_ = lean_box(0);
lean_inc(v_endPosCharacter_2007_);
v___x_2017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2017_, 0, v_endPosCharacter_2007_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
lean_inc(v_endPosLine_2006_);
v___x_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_endPosLine_2006_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
lean_inc(v_startPosCharacter_2005_);
v___x_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2019_, 0, v_startPosCharacter_2005_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
lean_inc(v_startPosLine_2004_);
v___x_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2020_, 0, v_startPosLine_2004_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v_range_2021_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_2020_, v___x_2016_);
v___x_2022_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_2003_);
lean_dec(v_v_2003_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = l_List_appendTR___redArg(v_range_2021_, v___x_2016_);
v___y_2011_ = v___x_2023_;
goto v___jp_2010_;
}
else
{
lean_object* v_val_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2033_; 
v_val_2024_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2026_ = v___x_2022_;
v_isShared_2027_ = v_isSharedCheck_2033_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_val_2024_);
lean_dec(v___x_2022_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2033_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set_tag(v___x_2026_, 3);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_val_2024_);
v___x_2029_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___x_2016_);
v___x_2031_ = l_List_appendTR___redArg(v_range_2021_, v___x_2030_);
v___y_2011_ = v___x_2031_;
goto v___jp_2010_;
}
}
}
v___jp_2010_:
{
size_t v___x_2012_; size_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = ((size_t)1ULL);
v___x_2013_ = lean_usize_add(v_i_2000_, v___x_2012_);
v___x_2014_ = lean_array_uset(v_bs_x27_2009_, v_i_2000_, v___y_2011_);
v_i_2000_ = v___x_2013_;
v_bs_2001_ = v___x_2014_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2___boxed(lean_object* v_sz_2034_, lean_object* v_i_2035_, lean_object* v_bs_2036_){
_start:
{
size_t v_sz_boxed_2037_; size_t v_i_boxed_2038_; lean_object* v_res_2039_; 
v_sz_boxed_2037_ = lean_unbox_usize(v_sz_2034_);
lean_dec(v_sz_2034_);
v_i_boxed_2038_ = lean_unbox_usize(v_i_2035_);
lean_dec(v_i_2035_);
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_boxed_2037_, v_i_boxed_2038_, v_bs_2036_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
if (lean_obj_tag(v_a_2040_) == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = l_List_reverse___redArg(v_a_2041_);
return v___x_2042_;
}
else
{
lean_object* v_head_2043_; lean_object* v_snd_2044_; lean_object* v_tail_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2114_; 
v_head_2043_ = lean_ctor_get(v_a_2040_, 0);
lean_inc(v_head_2043_);
v_snd_2044_ = lean_ctor_get(v_head_2043_, 1);
lean_inc(v_snd_2044_);
v_tail_2045_ = lean_ctor_get(v_a_2040_, 1);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_a_2040_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v_a_2040_, 0);
lean_dec(v_unused_2115_);
v___x_2047_ = v_a_2040_;
v_isShared_2048_ = v_isSharedCheck_2114_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_tail_2045_);
lean_dec(v_a_2040_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2114_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_fst_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2112_; 
v_fst_2049_ = lean_ctor_get(v_head_2043_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_head_2043_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; 
v_unused_2113_ = lean_ctor_get(v_head_2043_, 1);
lean_dec(v_unused_2113_);
v___x_2051_ = v_head_2043_;
v_isShared_2052_ = v_isSharedCheck_2112_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_fst_2049_);
lean_dec(v_head_2043_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2112_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_definition_x3f_2053_; lean_object* v_usages_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2111_; 
v_definition_x3f_2053_ = lean_ctor_get(v_snd_2044_, 0);
v_usages_2054_ = lean_ctor_get(v_snd_2044_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_snd_2044_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2056_ = v_snd_2044_;
v_isShared_2057_ = v_isSharedCheck_2111_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_usages_2054_);
lean_inc(v_definition_x3f_2053_);
lean_dec(v_snd_2044_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2111_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___y_2062_; lean_object* v___y_2085_; 
v___x_2058_ = l_Lean_Lsp_RefIdent_toJson(v_fst_2049_);
v___x_2059_ = l_Lean_Json_compress(v___x_2058_);
v___x_2060_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__1));
if (lean_obj_tag(v_definition_x3f_2053_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_box(0);
v___y_2062_ = v___x_2087_;
goto v___jp_2061_;
}
else
{
lean_object* v_val_2088_; lean_object* v_startPosLine_2089_; lean_object* v_startPosCharacter_2090_; lean_object* v_endPosLine_2091_; lean_object* v_endPosCharacter_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_range_2098_; lean_object* v___x_2099_; 
v_val_2088_ = lean_ctor_get(v_definition_x3f_2053_, 0);
lean_inc(v_val_2088_);
lean_dec_ref(v_definition_x3f_2053_);
v_startPosLine_2089_ = lean_ctor_get(v_val_2088_, 0);
v_startPosCharacter_2090_ = lean_ctor_get(v_val_2088_, 1);
v_endPosLine_2091_ = lean_ctor_get(v_val_2088_, 2);
v_endPosCharacter_2092_ = lean_ctor_get(v_val_2088_, 3);
v___x_2093_ = lean_box(0);
lean_inc(v_endPosCharacter_2092_);
v___x_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2094_, 0, v_endPosCharacter_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
lean_inc(v_endPosLine_2091_);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v_endPosLine_2091_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
lean_inc(v_startPosCharacter_2090_);
v___x_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2096_, 0, v_startPosCharacter_2090_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
lean_inc(v_startPosLine_2089_);
v___x_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2097_, 0, v_startPosLine_2089_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v_range_2098_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__0(v___x_2097_, v___x_2093_);
v___x_2099_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_2088_);
lean_dec(v_val_2088_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v___x_2100_; 
v___x_2100_ = l_List_appendTR___redArg(v_range_2098_, v___x_2093_);
v___y_2085_ = v___x_2100_;
goto v___jp_2084_;
}
else
{
lean_object* v_val_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2110_; 
v_val_2101_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2103_ = v___x_2099_;
v_isShared_2104_ = v_isSharedCheck_2110_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_val_2101_);
lean_dec(v___x_2099_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2110_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set_tag(v___x_2103_, 3);
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_val_2101_);
v___x_2106_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2093_);
v___x_2108_ = l_List_appendTR___redArg(v_range_2098_, v___x_2107_);
v___y_2085_ = v___x_2108_;
goto v___jp_2084_;
}
}
}
}
v___jp_2061_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = l_Option_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__1(v___y_2062_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2063_);
lean_ctor_set(v___x_2051_, 0, v___x_2060_);
v___x_2065_ = v___x_2051_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; size_t v_sz_2067_; size_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2066_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_instFromJsonIlean_fromJson_spec__3_spec__7___closed__0));
v_sz_2067_ = lean_array_size(v_usages_2054_);
v___x_2068_ = ((size_t)0ULL);
v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_instToJsonIlean_toJson_spec__2(v_sz_2067_, v___x_2068_, v_usages_2054_);
v___x_2070_ = l_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__3(v___x_2069_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v___x_2070_);
lean_ctor_set(v___x_2056_, 0, v___x_2066_);
v___x_2072_ = v___x_2056_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_box(0);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v___x_2073_);
lean_ctor_set(v___x_2047_, 0, v___x_2072_);
v___x_2075_ = v___x_2047_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2065_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = l_Lean_Json_mkObj(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2059_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v_a_2041_);
v_a_2040_ = v_tail_2045_;
v_a_2041_ = v___x_2079_;
goto _start;
}
}
}
}
v___jp_2084_:
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___y_2085_);
v___y_2062_ = v___x_2086_;
goto v___jp_2061_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(lean_object* v_init_2116_, lean_object* v_x_2117_){
_start:
{
if (lean_obj_tag(v_x_2117_) == 0)
{
lean_object* v_k_2118_; lean_object* v_v_2119_; lean_object* v_l_2120_; lean_object* v_r_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_k_2118_ = lean_ctor_get(v_x_2117_, 1);
v_v_2119_ = lean_ctor_get(v_x_2117_, 2);
v_l_2120_ = lean_ctor_get(v_x_2117_, 3);
v_r_2121_ = lean_ctor_get(v_x_2117_, 4);
v___x_2122_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2116_, v_r_2121_);
lean_inc(v_v_2119_);
lean_inc(v_k_2118_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v_k_2118_);
lean_ctor_set(v___x_2123_, 1, v_v_2119_);
v___x_2124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___x_2122_);
v_init_2116_ = v___x_2124_;
v_x_2117_ = v_l_2120_;
goto _start;
}
else
{
return v_init_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5___boxed(lean_object* v_init_2126_, lean_object* v_x_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v_init_2126_, v_x_2127_);
lean_dec(v_x_2127_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
if (lean_obj_tag(v_a_2129_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = l_List_reverse___redArg(v_a_2130_);
return v___x_2131_;
}
else
{
lean_object* v_head_2132_; lean_object* v_snd_2133_; lean_object* v_tail_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2186_; 
v_head_2132_ = lean_ctor_get(v_a_2129_, 0);
lean_inc(v_head_2132_);
v_snd_2133_ = lean_ctor_get(v_head_2132_, 1);
lean_inc(v_snd_2133_);
v_tail_2134_ = lean_ctor_get(v_a_2129_, 1);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; 
v_unused_2187_ = lean_ctor_get(v_a_2129_, 0);
lean_dec(v_unused_2187_);
v___x_2136_ = v_a_2129_;
v_isShared_2137_ = v_isSharedCheck_2186_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_tail_2134_);
lean_dec(v_a_2129_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2186_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_fst_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2184_; 
v_fst_2138_ = lean_ctor_get(v_head_2132_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_head_2132_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; 
v_unused_2185_ = lean_ctor_get(v_head_2132_, 1);
lean_dec(v_unused_2185_);
v___x_2140_ = v_head_2132_;
v_isShared_2141_ = v_isSharedCheck_2184_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_fst_2138_);
lean_dec(v_head_2132_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2184_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_rangeStartPosLine_2142_; lean_object* v_rangeStartPosCharacter_2143_; lean_object* v_rangeEndPosLine_2144_; lean_object* v_rangeEndPosCharacter_2145_; lean_object* v_selectionRangeStartPosLine_2146_; lean_object* v_selectionRangeStartPosCharacter_2147_; lean_object* v_selectionRangeEndPosLine_2148_; lean_object* v_selectionRangeEndPosCharacter_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
v_rangeStartPosLine_2142_ = lean_ctor_get(v_snd_2133_, 0);
lean_inc(v_rangeStartPosLine_2142_);
v_rangeStartPosCharacter_2143_ = lean_ctor_get(v_snd_2133_, 1);
lean_inc(v_rangeStartPosCharacter_2143_);
v_rangeEndPosLine_2144_ = lean_ctor_get(v_snd_2133_, 2);
lean_inc(v_rangeEndPosLine_2144_);
v_rangeEndPosCharacter_2145_ = lean_ctor_get(v_snd_2133_, 3);
lean_inc(v_rangeEndPosCharacter_2145_);
v_selectionRangeStartPosLine_2146_ = lean_ctor_get(v_snd_2133_, 4);
lean_inc(v_selectionRangeStartPosLine_2146_);
v_selectionRangeStartPosCharacter_2147_ = lean_ctor_get(v_snd_2133_, 5);
lean_inc(v_selectionRangeStartPosCharacter_2147_);
v_selectionRangeEndPosLine_2148_ = lean_ctor_get(v_snd_2133_, 6);
lean_inc(v_selectionRangeEndPosLine_2148_);
v_selectionRangeEndPosCharacter_2149_ = lean_ctor_get(v_snd_2133_, 7);
lean_inc(v_selectionRangeEndPosCharacter_2149_);
lean_dec(v_snd_2133_);
v___x_2150_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_2142_);
v___x_2151_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
v___x_2152_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_2143_);
v___x_2153_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
v___x_2154_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_2144_);
v___x_2155_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
v___x_2156_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_2145_);
v___x_2157_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
v___x_2158_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_2146_);
v___x_2159_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
v___x_2160_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_2147_);
v___x_2161_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
v___x_2162_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_2148_);
v___x_2163_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
v___x_2164_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_2149_);
v___x_2165_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
v___x_2166_ = lean_unsigned_to_nat(8u);
v___x_2167_ = lean_mk_empty_array_with_capacity(v___x_2166_);
v___x_2168_ = lean_array_push(v___x_2167_, v___x_2151_);
v___x_2169_ = lean_array_push(v___x_2168_, v___x_2153_);
v___x_2170_ = lean_array_push(v___x_2169_, v___x_2155_);
v___x_2171_ = lean_array_push(v___x_2170_, v___x_2157_);
v___x_2172_ = lean_array_push(v___x_2171_, v___x_2159_);
v___x_2173_ = lean_array_push(v___x_2172_, v___x_2161_);
v___x_2174_ = lean_array_push(v___x_2173_, v___x_2163_);
v___x_2175_ = lean_array_push(v___x_2174_, v___x_2165_);
v___x_2176_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 1, v___x_2176_);
v___x_2178_ = v___x_2140_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_fst_2138_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v_a_2130_);
lean_ctor_set(v___x_2136_, 0, v___x_2178_);
v___x_2180_ = v___x_2136_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_a_2130_);
v___x_2180_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
v_a_2129_ = v_tail_2134_;
v_a_2130_ = v___x_2180_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
if (lean_obj_tag(v_a_2188_) == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_array_to_list(v_a_2189_);
return v___x_2190_;
}
else
{
lean_object* v_head_2191_; lean_object* v_tail_2192_; lean_object* v___x_2193_; 
v_head_2191_ = lean_ctor_get(v_a_2188_, 0);
lean_inc(v_head_2191_);
v_tail_2192_ = lean_ctor_get(v_a_2188_, 1);
lean_inc(v_tail_2192_);
lean_dec_ref(v_a_2188_);
v___x_2193_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2189_, v_head_2191_);
v_a_2188_ = v_tail_2192_;
v_a_2189_ = v___x_2193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(size_t v_sz_2195_, size_t v_i_2196_, lean_object* v_bs_2197_){
_start:
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_usize_dec_lt(v_i_2196_, v_sz_2195_);
if (v___x_2198_ == 0)
{
return v_bs_2197_;
}
else
{
lean_object* v_v_2199_; lean_object* v_module_2200_; uint8_t v_isPrivate_2201_; uint8_t v_isAll_2202_; uint8_t v_isMeta_2203_; lean_object* v___x_2204_; lean_object* v_bs_x27_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
v_v_2199_ = lean_array_uget_borrowed(v_bs_2197_, v_i_2196_);
v_module_2200_ = lean_ctor_get(v_v_2199_, 0);
lean_inc_ref(v_module_2200_);
v_isPrivate_2201_ = lean_ctor_get_uint8(v_v_2199_, sizeof(void*)*1);
v_isAll_2202_ = lean_ctor_get_uint8(v_v_2199_, sizeof(void*)*1 + 1);
v_isMeta_2203_ = lean_ctor_get_uint8(v_v_2199_, sizeof(void*)*1 + 2);
v___x_2204_ = lean_unsigned_to_nat(0u);
v_bs_x27_2205_ = lean_array_uset(v_bs_2197_, v_i_2196_, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2206_, 0, v_module_2200_);
v___x_2207_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2207_, 0, v_isPrivate_2201_);
v___x_2208_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2208_, 0, v_isAll_2202_);
v___x_2209_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2209_, 0, v_isMeta_2203_);
v___x_2210_ = lean_unsigned_to_nat(4u);
v___x_2211_ = lean_mk_empty_array_with_capacity(v___x_2210_);
v___x_2212_ = lean_array_push(v___x_2211_, v___x_2206_);
v___x_2213_ = lean_array_push(v___x_2212_, v___x_2207_);
v___x_2214_ = lean_array_push(v___x_2213_, v___x_2208_);
v___x_2215_ = lean_array_push(v___x_2214_, v___x_2209_);
v___x_2216_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
v___x_2217_ = ((size_t)1ULL);
v___x_2218_ = lean_usize_add(v_i_2196_, v___x_2217_);
v___x_2219_ = lean_array_uset(v_bs_x27_2205_, v_i_2196_, v___x_2216_);
v_i_2196_ = v___x_2218_;
v_bs_2197_ = v___x_2219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6___boxed(lean_object* v_sz_2221_, lean_object* v_i_2222_, lean_object* v_bs_2223_){
_start:
{
size_t v_sz_boxed_2224_; size_t v_i_boxed_2225_; lean_object* v_res_2226_; 
v_sz_boxed_2224_ = lean_unbox_usize(v_sz_2221_);
lean_dec(v_sz_2221_);
v_i_boxed_2225_ = lean_unbox_usize(v_i_2222_);
lean_dec(v_i_2222_);
v_res_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_boxed_2224_, v_i_boxed_2225_, v_bs_2223_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(lean_object* v_a_2227_){
_start:
{
size_t v_sz_2228_; size_t v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v_sz_2228_ = lean_array_size(v_a_2227_);
v___x_2229_ = ((size_t)0ULL);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4_spec__6(v_sz_2228_, v___x_2229_, v_a_2227_);
v___x_2231_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(lean_object* v_init_2232_, lean_object* v_x_2233_){
_start:
{
if (lean_obj_tag(v_x_2233_) == 0)
{
lean_object* v_k_2234_; lean_object* v_v_2235_; lean_object* v_l_2236_; lean_object* v_r_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_k_2234_ = lean_ctor_get(v_x_2233_, 1);
v_v_2235_ = lean_ctor_get(v_x_2233_, 2);
v_l_2236_ = lean_ctor_get(v_x_2233_, 3);
v_r_2237_ = lean_ctor_get(v_x_2233_, 4);
v___x_2238_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2232_, v_r_2237_);
lean_inc(v_v_2235_);
lean_inc(v_k_2234_);
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_k_2234_);
lean_ctor_set(v___x_2239_, 1, v_v_2235_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___x_2238_);
v_init_2232_ = v___x_2240_;
v_x_2233_ = v_l_2236_;
goto _start;
}
else
{
return v_init_2232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7___boxed(lean_object* v_init_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v_init_2242_, v_x_2243_);
lean_dec(v_x_2243_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instToJsonIlean_toJson(lean_object* v_x_2247_){
_start:
{
lean_object* v_version_2248_; lean_object* v_module_2249_; lean_object* v_directImports_2250_; lean_object* v_references_2251_; lean_object* v_decls_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_version_2248_ = lean_ctor_get(v_x_2247_, 0);
lean_inc(v_version_2248_);
v_module_2249_ = lean_ctor_get(v_x_2247_, 1);
lean_inc(v_module_2249_);
v_directImports_2250_ = lean_ctor_get(v_x_2247_, 2);
lean_inc_ref(v_directImports_2250_);
v_references_2251_ = lean_ctor_get(v_x_2247_, 3);
lean_inc(v_references_2251_);
v_decls_2252_ = lean_ctor_get(v_x_2247_, 4);
lean_inc(v_decls_2252_);
lean_dec_ref(v_x_2247_);
v___x_2253_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__0));
v___x_2254_ = l_Lean_JsonNumber_fromNat(v_version_2248_);
v___x_2255_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2253_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_box(0);
v___x_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__13));
v___x_2260_ = 1;
v___x_2261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_2249_, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2259_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___x_2257_);
v___x_2265_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__18));
v___x_2266_ = l_Array_toJson___at___00Lean_Server_instToJsonIlean_toJson_spec__4(v_directImports_2250_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v___x_2257_);
v___x_2269_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__23));
v___x_2270_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__5(v___x_2257_, v_references_2251_);
lean_dec(v_references_2251_);
v___x_2271_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__6(v___x_2270_, v___x_2257_);
v___x_2272_ = l_Lean_Json_mkObj(v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2269_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___x_2257_);
v___x_2275_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__28));
v___x_2276_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Server_instToJsonIlean_toJson_spec__7(v___x_2257_, v_decls_2252_);
lean_dec(v_decls_2252_);
v___x_2277_ = l_List_mapTR_loop___at___00Lean_Server_instToJsonIlean_toJson_spec__8(v___x_2276_, v___x_2257_);
v___x_2278_ = l_Lean_Json_mkObj(v___x_2277_);
v___x_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2275_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___x_2257_);
v___x_2281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v___x_2257_);
v___x_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2274_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2268_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2264_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2258_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = ((lean_object*)(l_Lean_Server_instToJsonIlean_toJson___closed__0));
v___x_2287_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_instToJsonIlean_toJson_spec__9(v___x_2285_, v___x_2286_);
v___x_2288_ = l_Lean_Json_mkObj(v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load(lean_object* v_path_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_IO_FS_readFile(v_path_2292_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2316_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2316_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2316_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_a_2300_; lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_Json_parse(v_a_2295_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; 
lean_del_object(v___x_2297_);
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
v_a_2300_ = v_a_2308_;
goto v___jp_2299_;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2310_; 
v_a_2309_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2309_);
lean_dec_ref(v___x_2307_);
v___x_2310_ = l_Lean_Server_instFromJsonIlean_fromJson(v_a_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; 
lean_del_object(v___x_2297_);
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v___x_2310_);
v_a_2300_ = v_a_2311_;
goto v___jp_2299_;
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; 
v_a_2312_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2310_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v_a_2312_);
v___x_2314_ = v___x_2297_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
v___jp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = ((lean_object*)(l_Lean_Server_Ilean_load___closed__0));
v___x_2302_ = lean_string_append(v___x_2301_, v_path_2292_);
v___x_2303_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
v___x_2305_ = lean_string_append(v___x_2304_, v_a_2300_);
lean_dec_ref(v_a_2300_);
v___x_2306_ = l_IO_throwServerError___redArg(v___x_2305_);
return v___x_2306_;
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
v_a_2317_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2294_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2294_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load___boxed(lean_object* v_path_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_Server_Ilean_load(v_path_2325_);
lean_dec_ref(v_path_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f(lean_object* v_env_2328_, lean_object* v_declName_2329_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2328_, v_declName_2329_);
if (lean_obj_tag(v___x_2330_) == 1)
{
lean_object* v_val_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2343_; 
v_val_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2343_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_val_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2343_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2335_ = l_Lean_Environment_allImportedModuleNames(v_env_2328_);
v___x_2336_ = lean_array_get_size(v___x_2335_);
v___x_2337_ = lean_nat_dec_lt(v_val_2331_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
lean_dec_ref(v___x_2335_);
lean_del_object(v___x_2333_);
lean_dec(v_val_2331_);
v___x_2338_ = lean_box(0);
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2339_ = lean_array_fget(v___x_2335_, v_val_2331_);
lean_dec(v_val_2331_);
lean_dec_ref(v___x_2335_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2339_);
v___x_2341_ = v___x_2333_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v___x_2344_; lean_object* v_mainModule_2345_; lean_object* v___x_2346_; 
lean_dec(v___x_2330_);
v___x_2344_ = l_Lean_Environment_header(v_env_2328_);
v_mainModule_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_mainModule_2345_);
lean_dec_ref(v___x_2344_);
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_mainModule_2345_);
return v___x_2346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f___boxed(lean_object* v_env_2347_, lean_object* v_declName_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2347_, v_declName_2348_);
lean_dec(v_declName_2348_);
lean_dec_ref(v_env_2347_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf(lean_object* v_ci_2350_, lean_object* v_i_2351_){
_start:
{
switch(lean_obj_tag(v_i_2351_))
{
case 1:
{
lean_object* v_i_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2393_; 
v_i_2352_ = lean_ctor_get(v_i_2351_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_i_2351_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2354_ = v_i_2351_;
v_isShared_2355_ = v_isSharedCheck_2393_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_i_2352_);
lean_dec(v_i_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2393_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v_expr_2356_; 
v_expr_2356_ = lean_ctor_get(v_i_2352_, 3);
lean_inc_ref(v_expr_2356_);
switch(lean_obj_tag(v_expr_2356_))
{
case 4:
{
lean_object* v_toCommandContextInfo_2357_; uint8_t v_isBinder_2358_; lean_object* v_declName_2359_; lean_object* v_env_2360_; lean_object* v___x_2361_; 
lean_del_object(v___x_2354_);
v_toCommandContextInfo_2357_ = lean_ctor_get(v_ci_2350_, 0);
v_isBinder_2358_ = lean_ctor_get_uint8(v_i_2352_, sizeof(void*)*4);
lean_dec_ref(v_i_2352_);
v_declName_2359_ = lean_ctor_get(v_expr_2356_, 0);
lean_inc(v_declName_2359_);
lean_dec_ref(v_expr_2356_);
v_env_2360_ = lean_ctor_get(v_toCommandContextInfo_2357_, 0);
v___x_2361_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2360_, v_declName_2359_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v___x_2362_; 
lean_dec(v_declName_2359_);
v___x_2362_ = lean_box(0);
return v___x_2362_;
}
else
{
lean_object* v_val_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2376_; 
v_val_2363_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2365_ = v___x_2361_;
v_isShared_2366_ = v_isSharedCheck_2376_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_val_2363_);
lean_dec(v___x_2361_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2376_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2367_ = 1;
v___x_2368_ = l_Lean_Name_toString(v_val_2363_, v___x_2367_);
v___x_2369_ = l_Lean_Name_toString(v_declName_2359_, v___x_2367_);
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_box(v_isBinder_2358_);
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2372_);
v___x_2374_ = v___x_2365_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
case 1:
{
lean_object* v_toCommandContextInfo_2377_; uint8_t v_isBinder_2378_; lean_object* v_fvarId_2379_; lean_object* v_env_2380_; lean_object* v___x_2381_; lean_object* v_mainModule_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; 
v_toCommandContextInfo_2377_ = lean_ctor_get(v_ci_2350_, 0);
v_isBinder_2378_ = lean_ctor_get_uint8(v_i_2352_, sizeof(void*)*4);
lean_dec_ref(v_i_2352_);
v_fvarId_2379_ = lean_ctor_get(v_expr_2356_, 0);
lean_inc(v_fvarId_2379_);
lean_dec_ref(v_expr_2356_);
v_env_2380_ = lean_ctor_get(v_toCommandContextInfo_2377_, 0);
v___x_2381_ = l_Lean_Environment_header(v_env_2380_);
v_mainModule_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_mainModule_2382_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = 1;
v___x_2384_ = l_Lean_Name_toString(v_mainModule_2382_, v___x_2383_);
v___x_2385_ = l_Lean_Name_toString(v_fvarId_2379_, v___x_2383_);
v___x_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lean_box(v_isBinder_2378_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2388_);
v___x_2390_ = v___x_2354_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
default: 
{
lean_object* v___x_2392_; 
lean_dec_ref(v_expr_2356_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_i_2352_);
v___x_2392_ = lean_box(0);
return v___x_2392_;
}
}
}
}
case 7:
{
lean_object* v_toCommandContextInfo_2394_; lean_object* v_i_2395_; lean_object* v_env_2396_; lean_object* v_projName_2397_; lean_object* v___x_2398_; 
v_toCommandContextInfo_2394_ = lean_ctor_get(v_ci_2350_, 0);
v_i_2395_ = lean_ctor_get(v_i_2351_, 0);
lean_inc_ref(v_i_2395_);
lean_dec_ref(v_i_2351_);
v_env_2396_ = lean_ctor_get(v_toCommandContextInfo_2394_, 0);
v_projName_2397_ = lean_ctor_get(v_i_2395_, 0);
lean_inc(v_projName_2397_);
lean_dec_ref(v_i_2395_);
v___x_2398_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2396_, v_projName_2397_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v___x_2399_; 
lean_dec(v_projName_2397_);
v___x_2399_ = lean_box(0);
return v___x_2399_;
}
else
{
lean_object* v_val_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2414_; 
v_val_2400_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2402_ = v___x_2398_;
v_isShared_2403_ = v_isSharedCheck_2414_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_val_2400_);
lean_dec(v___x_2398_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2414_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
uint8_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2404_ = 1;
v___x_2405_ = l_Lean_Name_toString(v_val_2400_, v___x_2404_);
v___x_2406_ = l_Lean_Name_toString(v_projName_2397_, v___x_2404_);
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = 0;
v___x_2409_ = lean_box(v___x_2408_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2407_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2410_);
v___x_2412_ = v___x_2402_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
case 5:
{
lean_object* v_toCommandContextInfo_2415_; lean_object* v_i_2416_; lean_object* v_env_2417_; lean_object* v_declName_2418_; lean_object* v___x_2419_; 
v_toCommandContextInfo_2415_ = lean_ctor_get(v_ci_2350_, 0);
v_i_2416_ = lean_ctor_get(v_i_2351_, 0);
lean_inc_ref(v_i_2416_);
lean_dec_ref(v_i_2351_);
v_env_2417_ = lean_ctor_get(v_toCommandContextInfo_2415_, 0);
v_declName_2418_ = lean_ctor_get(v_i_2416_, 2);
lean_inc(v_declName_2418_);
lean_dec_ref(v_i_2416_);
v___x_2419_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2417_, v_declName_2418_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2420_; 
lean_dec(v_declName_2418_);
v___x_2420_ = lean_box(0);
return v___x_2420_;
}
else
{
lean_object* v_val_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2435_; 
v_val_2421_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2423_ = v___x_2419_;
v_isShared_2424_ = v_isSharedCheck_2435_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_val_2421_);
lean_dec(v___x_2419_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2435_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2425_ = 1;
v___x_2426_ = l_Lean_Name_toString(v_val_2421_, v___x_2425_);
v___x_2427_ = l_Lean_Name_toString(v_declName_2418_, v___x_2425_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = 0;
v___x_2430_ = lean_box(v___x_2429_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2428_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2431_);
v___x_2433_ = v___x_2423_;
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
}
}
case 16:
{
lean_object* v_toCommandContextInfo_2436_; lean_object* v_i_2437_; lean_object* v_env_2438_; lean_object* v_name_2439_; lean_object* v___x_2440_; 
v_toCommandContextInfo_2436_ = lean_ctor_get(v_ci_2350_, 0);
v_i_2437_ = lean_ctor_get(v_i_2351_, 0);
lean_inc_ref(v_i_2437_);
lean_dec_ref(v_i_2351_);
v_env_2438_ = lean_ctor_get(v_toCommandContextInfo_2436_, 0);
v_name_2439_ = lean_ctor_get(v_i_2437_, 1);
lean_inc(v_name_2439_);
lean_dec_ref(v_i_2437_);
v___x_2440_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2438_, v_name_2439_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v___x_2441_; 
lean_dec(v_name_2439_);
v___x_2441_ = lean_box(0);
return v___x_2441_;
}
else
{
lean_object* v_val_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2456_; 
v_val_2442_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2444_ = v___x_2440_;
v_isShared_2445_ = v_isSharedCheck_2456_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_val_2442_);
lean_dec(v___x_2440_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2456_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
uint8_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2446_ = 1;
v___x_2447_ = l_Lean_Name_toString(v_val_2442_, v___x_2446_);
v___x_2448_ = l_Lean_Name_toString(v_name_2439_, v___x_2446_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2447_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = 0;
v___x_2451_ = lean_box(v___x_2450_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2449_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2452_);
v___x_2454_ = v___x_2444_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
default: 
{
lean_object* v___x_2457_; 
lean_dec_ref(v_i_2351_);
v___x_2457_ = lean_box(0);
return v___x_2457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf___boxed(lean_object* v_ci_2458_, lean_object* v_i_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_Server_identOf(v_ci_2458_, v_i_2459_);
lean_dec_ref(v_ci_2458_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(uint8_t v___x_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_, lean_object* v_x_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_box(v___x_2461_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v___y_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed(lean_object* v___x_2468_, lean_object* v_x_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_, lean_object* v___y_2472_){
_start:
{
uint8_t v___x_3581__boxed_2473_; lean_object* v_res_2474_; 
v___x_3581__boxed_2473_ = lean_unbox(v___x_2468_);
v_res_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(v___x_3581__boxed_2473_, v_x_2469_, v_x_2470_, v_x_2471_, v___y_2472_);
lean_dec_ref(v_x_2471_);
lean_dec_ref(v_x_2470_);
lean_dec_ref(v_x_2469_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(lean_object* v_text_2475_, lean_object* v___x_2476_, lean_object* v_ci_2477_, lean_object* v_info_2478_, lean_object* v_x_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___x_2481_; 
lean_inc_ref(v_info_2478_);
v___x_2481_ = l_Lean_Server_identOf(v_ci_2477_, v_info_2478_);
if (lean_obj_tag(v___x_2481_) == 1)
{
lean_object* v_val_2482_; lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2506_; 
v_val_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_val_2482_);
lean_dec_ref(v___x_2481_);
v_fst_2483_ = lean_ctor_get(v_val_2482_, 0);
v_snd_2484_ = lean_ctor_get(v_val_2482_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_val_2482_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2486_ = v_val_2482_;
v_isShared_2487_ = v_isSharedCheck_2506_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_snd_2484_);
lean_inc(v_fst_2483_);
lean_dec(v_val_2482_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2506_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_Elab_Info_range_x3f(v_info_2478_);
if (lean_obj_tag(v___x_2488_) == 1)
{
lean_object* v_val_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_val_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_val_2489_);
lean_dec_ref(v___x_2488_);
v___x_2490_ = l_Lean_Elab_Info_stx(v_info_2478_);
v___x_2491_ = l_Lean_Syntax_getHeadInfo(v___x_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
lean_dec_ref(v___x_2491_);
v___x_2492_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_2493_ = l_Lean_Syntax_Range_toLspRange(v_text_2475_, v_val_2489_);
v___x_2494_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2494_, 0, v_fst_2483_);
lean_ctor_set(v___x_2494_, 1, v___x_2492_);
lean_ctor_set(v___x_2494_, 2, v___x_2493_);
lean_ctor_set(v___x_2494_, 3, v___x_2490_);
lean_ctor_set(v___x_2494_, 4, v_ci_2477_);
lean_ctor_set(v___x_2494_, 5, v_info_2478_);
v___x_2495_ = lean_unbox(v_snd_2484_);
lean_dec(v_snd_2484_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*6, v___x_2495_);
v___x_2496_ = lean_array_push(v___y_2480_, v___x_2494_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 1, v___x_2496_);
lean_ctor_set(v___x_2486_, 0, v___x_2476_);
v___x_2498_ = v___x_2486_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
else
{
lean_object* v___x_2501_; 
lean_dec(v___x_2491_);
lean_dec(v___x_2490_);
lean_dec(v_val_2489_);
lean_dec(v_snd_2484_);
lean_dec(v_fst_2483_);
lean_dec_ref(v_info_2478_);
lean_dec_ref(v_ci_2477_);
lean_dec_ref(v_text_2475_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 1, v___y_2480_);
lean_ctor_set(v___x_2486_, 0, v___x_2476_);
v___x_2501_ = v___x_2486_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___y_2480_);
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
lean_object* v___x_2504_; 
lean_dec(v___x_2488_);
lean_dec(v_snd_2484_);
lean_dec(v_fst_2483_);
lean_dec_ref(v_info_2478_);
lean_dec_ref(v_ci_2477_);
lean_dec_ref(v_text_2475_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 1, v___y_2480_);
lean_ctor_set(v___x_2486_, 0, v___x_2476_);
v___x_2504_ = v___x_2486_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v___y_2480_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v___x_2507_; 
lean_dec(v___x_2481_);
lean_dec_ref(v_info_2478_);
lean_dec_ref(v_ci_2477_);
lean_dec_ref(v_text_2475_);
v___x_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2476_);
lean_ctor_set(v___x_2507_, 1, v___y_2480_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed(lean_object* v_text_2508_, lean_object* v___x_2509_, lean_object* v_ci_2510_, lean_object* v_info_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(v_text_2508_, v___x_2509_, v_ci_2510_, v_info_2511_, v_x_2512_, v___y_2513_);
lean_dec_ref(v_x_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object* v_postNode_2515_, lean_object* v_ci_2516_, lean_object* v_i_2517_, lean_object* v_cs_2518_, lean_object* v_x_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_apply_4(v_postNode_2515_, v_ci_2516_, v_i_2517_, v_cs_2518_, v___y_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object* v_postNode_2522_, lean_object* v_ci_2523_, lean_object* v_i_2524_, lean_object* v_cs_2525_, lean_object* v_x_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(v_postNode_2522_, v_ci_2523_, v_i_2524_, v_cs_2525_, v_x_2526_, v___y_2527_);
lean_dec(v_x_2526_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___f_2538_; lean_object* v___f_2539_; lean_object* v___f_2540_; lean_object* v___f_2541_; lean_object* v___f_2542_; lean_object* v___f_2543_; lean_object* v___f_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___f_2548_; lean_object* v___f_2549_; lean_object* v___f_2550_; lean_object* v___f_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_3178__overap_2560_; lean_object* v___x_2561_; 
v___f_2538_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_2539_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_2540_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_2541_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_2542_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_2543_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_2544_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___f_2538_);
lean_ctor_set(v___x_2545_, 1, v___f_2539_);
v___x_2546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v___f_2540_);
lean_ctor_set(v___x_2546_, 2, v___f_2541_);
lean_ctor_set(v___x_2546_, 3, v___f_2542_);
lean_ctor_set(v___x_2546_, 4, v___f_2543_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
lean_ctor_set(v___x_2547_, 1, v___f_2544_);
lean_inc_ref_n(v___x_2547_, 6);
v___f_2548_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2548_, 0, v___x_2547_);
v___f_2549_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2549_, 0, v___x_2547_);
v___f_2550_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2550_, 0, v___x_2547_);
v___f_2551_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2551_, 0, v___x_2547_);
v___x_2552_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2552_, 0, lean_box(0));
lean_closure_set(v___x_2552_, 1, lean_box(0));
lean_closure_set(v___x_2552_, 2, v___x_2547_);
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
lean_ctor_set(v___x_2553_, 1, v___f_2548_);
v___x_2554_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2554_, 0, lean_box(0));
lean_closure_set(v___x_2554_, 1, lean_box(0));
lean_closure_set(v___x_2554_, 2, v___x_2547_);
v___x_2555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
lean_ctor_set(v___x_2555_, 2, v___f_2549_);
lean_ctor_set(v___x_2555_, 3, v___f_2550_);
lean_ctor_set(v___x_2555_, 4, v___f_2551_);
v___x_2556_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2556_, 0, lean_box(0));
lean_closure_set(v___x_2556_, 1, lean_box(0));
lean_closure_set(v___x_2556_, 2, v___x_2547_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_box(0);
v___x_2559_ = l_instInhabitedOfMonad___redArg(v___x_2557_, v___x_2558_);
v___x_3178__overap_2560_ = lean_panic_fn_borrowed(v___x_2559_, v_msg_2536_);
lean_dec(v___x_2559_);
v___x_2561_ = lean_apply_1(v___x_3178__overap_2560_, v___y_2537_);
return v___x_2561_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2565_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2));
v___x_2566_ = lean_unsigned_to_nat(21u);
v___x_2567_ = lean_unsigned_to_nat(65u);
v___x_2568_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1));
v___x_2569_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0));
v___x_2570_ = l_mkPanicMessageWithDecl(v___x_2569_, v___x_2568_, v___x_2567_, v___x_2566_, v___x_2565_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object* v_preNode_2571_, lean_object* v_postNode_2572_, lean_object* v_x_2573_, lean_object* v_x_2574_, lean_object* v___y_2575_){
_start:
{
switch(lean_obj_tag(v_x_2574_))
{
case 0:
{
lean_object* v_i_2576_; lean_object* v_t_2577_; lean_object* v___x_2578_; 
v_i_2576_ = lean_ctor_get(v_x_2574_, 0);
lean_inc_ref(v_i_2576_);
v_t_2577_ = lean_ctor_get(v_x_2574_, 1);
lean_inc_ref(v_t_2577_);
lean_dec_ref(v_x_2574_);
v___x_2578_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2576_, v_x_2573_);
v_x_2573_ = v___x_2578_;
v_x_2574_ = v_t_2577_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_2573_) == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref(v_x_2574_);
lean_dec_ref(v_postNode_2572_);
lean_dec_ref(v_preNode_2571_);
v___x_2580_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_2581_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v___x_2580_, v___y_2575_);
return v___x_2581_;
}
else
{
lean_object* v_i_2582_; lean_object* v_children_2583_; lean_object* v_val_2584_; lean_object* v___x_2585_; lean_object* v_fst_2586_; uint8_t v___x_2587_; 
v_i_2582_ = lean_ctor_get(v_x_2574_, 0);
lean_inc_ref_n(v_i_2582_, 2);
v_children_2583_ = lean_ctor_get(v_x_2574_, 1);
lean_inc_ref_n(v_children_2583_, 2);
lean_dec_ref(v_x_2574_);
v_val_2584_ = lean_ctor_get(v_x_2573_, 0);
lean_inc_n(v_val_2584_, 2);
lean_inc_ref(v_preNode_2571_);
v___x_2585_ = lean_apply_4(v_preNode_2571_, v_val_2584_, v_i_2582_, v_children_2583_, v___y_2575_);
v_fst_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_fst_2586_);
v___x_2587_ = lean_unbox(v_fst_2586_);
lean_dec(v_fst_2586_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2606_; 
lean_dec_ref(v_preNode_2571_);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_x_2573_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; 
v_unused_2607_ = lean_ctor_get(v_x_2573_, 0);
lean_dec(v_unused_2607_);
v___x_2589_ = v_x_2573_;
v_isShared_2590_ = v_isSharedCheck_2606_;
goto v_resetjp_2588_;
}
else
{
lean_dec(v_x_2573_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2606_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_snd_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v_fst_2594_; lean_object* v_snd_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2605_; 
v_snd_2591_ = lean_ctor_get(v___x_2585_, 1);
lean_inc(v_snd_2591_);
lean_dec_ref(v___x_2585_);
v___x_2592_ = lean_box(0);
v___x_2593_ = lean_apply_5(v_postNode_2572_, v_val_2584_, v_i_2582_, v_children_2583_, v___x_2592_, v_snd_2591_);
v_fst_2594_ = lean_ctor_get(v___x_2593_, 0);
v_snd_2595_ = lean_ctor_get(v___x_2593_, 1);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2597_ = v___x_2593_;
v_isShared_2598_ = v_isSharedCheck_2605_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_snd_2595_);
lean_inc(v_fst_2594_);
lean_dec(v___x_2593_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2605_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_fst_2594_);
v___x_2600_ = v___x_2589_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_fst_2594_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2600_);
v___x_2602_ = v___x_2597_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_snd_2595_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
else
{
lean_object* v_snd_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v_fst_2613_; lean_object* v_snd_2614_; lean_object* v___x_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2625_; 
v_snd_2608_ = lean_ctor_get(v___x_2585_, 1);
lean_inc(v_snd_2608_);
lean_dec_ref(v___x_2585_);
v___x_2609_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2573_, v_i_2582_);
v___x_2610_ = l_Lean_PersistentArray_toList___redArg(v_children_2583_);
v___x_2611_ = lean_box(0);
lean_inc_ref(v_postNode_2572_);
v___x_2612_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2571_, v_postNode_2572_, v___x_2609_, v___x_2610_, v___x_2611_, v_snd_2608_);
v_fst_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_fst_2613_);
v_snd_2614_ = lean_ctor_get(v___x_2612_, 1);
lean_inc(v_snd_2614_);
lean_dec_ref(v___x_2612_);
v___x_2615_ = lean_apply_5(v_postNode_2572_, v_val_2584_, v_i_2582_, v_children_2583_, v_fst_2613_, v_snd_2614_);
v_fst_2616_ = lean_ctor_get(v___x_2615_, 0);
v_snd_2617_ = lean_ctor_get(v___x_2615_, 1);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2619_ = v___x_2615_;
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snd_2617_);
lean_inc(v_fst_2616_);
lean_dec(v___x_2615_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_fst_2616_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2621_);
v___x_2623_ = v___x_2619_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_snd_2617_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
default: 
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v_x_2574_);
lean_dec(v_x_2573_);
lean_dec_ref(v_postNode_2572_);
lean_dec_ref(v_preNode_2571_);
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v___y_2575_);
return v___x_2627_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_2628_, lean_object* v_postNode_2629_, lean_object* v___x_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_, lean_object* v___y_2633_){
_start:
{
if (lean_obj_tag(v_x_2631_) == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec(v___x_2630_);
lean_dec_ref(v_postNode_2629_);
lean_dec_ref(v_preNode_2628_);
v___x_2634_ = l_List_reverse___redArg(v_x_2632_);
v___x_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v___y_2633_);
return v___x_2635_;
}
else
{
lean_object* v_head_2636_; lean_object* v_tail_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2648_; 
v_head_2636_ = lean_ctor_get(v_x_2631_, 0);
v_tail_2637_ = lean_ctor_get(v_x_2631_, 1);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_x_2631_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2639_ = v_x_2631_;
v_isShared_2640_ = v_isSharedCheck_2648_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_tail_2637_);
lean_inc(v_head_2636_);
lean_dec(v_x_2631_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2648_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v_fst_2642_; lean_object* v_snd_2643_; lean_object* v___x_2645_; 
lean_inc(v___x_2630_);
lean_inc_ref(v_postNode_2629_);
lean_inc_ref(v_preNode_2628_);
v___x_2641_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2628_, v_postNode_2629_, v___x_2630_, v_head_2636_, v___y_2633_);
v_fst_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_fst_2642_);
v_snd_2643_ = lean_ctor_get(v___x_2641_, 1);
lean_inc(v_snd_2643_);
lean_dec_ref(v___x_2641_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 1, v_x_2632_);
lean_ctor_set(v___x_2639_, 0, v_fst_2642_);
v___x_2645_ = v___x_2639_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_fst_2642_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_x_2632_);
v___x_2645_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
v_x_2631_ = v_tail_2637_;
v_x_2632_ = v___x_2645_;
v___y_2633_ = v_snd_2643_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object* v_preNode_2649_, lean_object* v_postNode_2650_, lean_object* v_ctx_x3f_2651_, lean_object* v_t_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___f_2654_; lean_object* v___x_2655_; lean_object* v_snd_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2664_; 
v___f_2654_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2654_, 0, v_postNode_2650_);
v___x_2655_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2649_, v___f_2654_, v_ctx_x3f_2651_, v_t_2652_, v___y_2653_);
v_snd_2656_ = lean_ctor_get(v___x_2655_, 1);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2655_, 0);
lean_dec(v_unused_2665_);
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2664_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snd_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2664_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2660_ = lean_box(0);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2660_);
v___x_2662_ = v___x_2658_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_snd_2656_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(lean_object* v_text_2666_, lean_object* v_as_2667_, size_t v_sz_2668_, size_t v_i_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_lt(v_i_2669_, v_sz_2668_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
lean_dec_ref(v_text_2666_);
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v_b_2670_);
lean_ctor_set(v___x_2673_, 1, v___y_2671_);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; lean_object* v___f_2675_; lean_object* v___x_2676_; lean_object* v___f_2677_; lean_object* v_a_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v_snd_2681_; size_t v___x_2682_; size_t v___x_2683_; 
v___x_2674_ = lean_box(v___x_2672_);
v___f_2675_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2675_, 0, v___x_2674_);
v___x_2676_ = lean_box(0);
lean_inc_ref(v_text_2666_);
v___f_2677_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2677_, 0, v_text_2666_);
lean_closure_set(v___f_2677_, 1, v___x_2676_);
v_a_2678_ = lean_array_uget_borrowed(v_as_2667_, v_i_2669_);
v___x_2679_ = lean_box(0);
lean_inc(v_a_2678_);
v___x_2680_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(v___f_2675_, v___f_2677_, v___x_2679_, v_a_2678_, v___y_2671_);
v_snd_2681_ = lean_ctor_get(v___x_2680_, 1);
lean_inc(v_snd_2681_);
lean_dec_ref(v___x_2680_);
v___x_2682_ = ((size_t)1ULL);
v___x_2683_ = lean_usize_add(v_i_2669_, v___x_2682_);
v_i_2669_ = v___x_2683_;
v_b_2670_ = v___x_2676_;
v___y_2671_ = v_snd_2681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___boxed(lean_object* v_text_2685_, lean_object* v_as_2686_, lean_object* v_sz_2687_, lean_object* v_i_2688_, lean_object* v_b_2689_, lean_object* v___y_2690_){
_start:
{
size_t v_sz_boxed_2691_; size_t v_i_boxed_2692_; lean_object* v_res_2693_; 
v_sz_boxed_2691_ = lean_unbox_usize(v_sz_2687_);
lean_dec(v_sz_2687_);
v_i_boxed_2692_ = lean_unbox_usize(v_i_2688_);
lean_dec(v_i_2688_);
v_res_2693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2685_, v_as_2686_, v_sz_boxed_2691_, v_i_boxed_2692_, v_b_2689_, v___y_2690_);
lean_dec_ref(v_as_2686_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences(lean_object* v_text_2694_, lean_object* v_trees_2695_){
_start:
{
lean_object* v___x_2696_; size_t v_sz_2697_; size_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v_snd_2701_; 
v___x_2696_ = lean_box(0);
v_sz_2697_ = lean_array_size(v_trees_2695_);
v___x_2698_ = ((size_t)0ULL);
v___x_2699_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2694_, v_trees_2695_, v_sz_2697_, v___x_2698_, v___x_2696_, v___x_2699_);
v_snd_2701_ = lean_ctor_get(v___x_2700_, 1);
lean_inc(v_snd_2701_);
lean_dec_ref(v___x_2700_);
return v_snd_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences___boxed(lean_object* v_text_2702_, lean_object* v_trees_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_Server_findReferences(v_text_2702_, v_trees_2703_);
lean_dec_ref(v_trees_2703_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2705_, lean_object* v_msg_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v_msg_2706_, v___y_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object* v_00_u03b1_2709_, lean_object* v_preNode_2710_, lean_object* v_postNode_2711_, lean_object* v_x_2712_, lean_object* v_x_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2710_, v_postNode_2711_, v_x_2712_, v_x_2713_, v___y_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2716_, lean_object* v_preNode_2717_, lean_object* v_postNode_2718_, lean_object* v___x_2719_, lean_object* v_x_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2717_, v_postNode_2718_, v___x_2719_, v_x_2720_, v_x_2721_, v___y_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(lean_object* v_a_2724_, lean_object* v_x_2725_){
_start:
{
lean_object* v_key_2726_; lean_object* v_value_2727_; lean_object* v_tail_2728_; uint8_t v___x_2729_; 
v_key_2726_ = lean_ctor_get(v_x_2725_, 0);
v_value_2727_ = lean_ctor_get(v_x_2725_, 1);
v_tail_2728_ = lean_ctor_get(v_x_2725_, 2);
v___x_2729_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2726_, v_a_2724_);
if (v___x_2729_ == 0)
{
v_x_2725_ = v_tail_2728_;
goto _start;
}
else
{
lean_inc(v_value_2727_);
return v_value_2727_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg___boxed(lean_object* v_a_2731_, lean_object* v_x_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2731_, v_x_2732_);
lean_dec(v_x_2732_);
lean_dec_ref(v_a_2731_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(lean_object* v_m_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_buckets_2736_; lean_object* v___x_2737_; uint64_t v___x_2738_; uint64_t v___x_2739_; uint64_t v___x_2740_; uint64_t v_fold_2741_; uint64_t v___x_2742_; uint64_t v___x_2743_; uint64_t v___x_2744_; size_t v___x_2745_; size_t v___x_2746_; size_t v___x_2747_; size_t v___x_2748_; size_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_buckets_2736_ = lean_ctor_get(v_m_2734_, 1);
v___x_2737_ = lean_array_get_size(v_buckets_2736_);
v___x_2738_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2735_);
v___x_2739_ = 32ULL;
v___x_2740_ = lean_uint64_shift_right(v___x_2738_, v___x_2739_);
v_fold_2741_ = lean_uint64_xor(v___x_2738_, v___x_2740_);
v___x_2742_ = 16ULL;
v___x_2743_ = lean_uint64_shift_right(v_fold_2741_, v___x_2742_);
v___x_2744_ = lean_uint64_xor(v_fold_2741_, v___x_2743_);
v___x_2745_ = lean_uint64_to_usize(v___x_2744_);
v___x_2746_ = lean_usize_of_nat(v___x_2737_);
v___x_2747_ = ((size_t)1ULL);
v___x_2748_ = lean_usize_sub(v___x_2746_, v___x_2747_);
v___x_2749_ = lean_usize_land(v___x_2745_, v___x_2748_);
v___x_2750_ = lean_array_uget_borrowed(v_buckets_2736_, v___x_2749_);
v___x_2751_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2735_, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg___boxed(lean_object* v_m_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2752_, v_a_2753_);
lean_dec_ref(v_a_2753_);
lean_dec_ref(v_m_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(lean_object* v_a_2755_, lean_object* v_x_2756_){
_start:
{
if (lean_obj_tag(v_x_2756_) == 0)
{
uint8_t v___x_2757_; 
v___x_2757_ = 0;
return v___x_2757_;
}
else
{
lean_object* v_key_2758_; lean_object* v_tail_2759_; uint8_t v___x_2760_; 
v_key_2758_ = lean_ctor_get(v_x_2756_, 0);
v_tail_2759_ = lean_ctor_get(v_x_2756_, 2);
v___x_2760_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2758_, v_a_2755_);
if (v___x_2760_ == 0)
{
v_x_2756_ = v_tail_2759_;
goto _start;
}
else
{
return v___x_2760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg___boxed(lean_object* v_a_2762_, lean_object* v_x_2763_){
_start:
{
uint8_t v_res_2764_; lean_object* v_r_2765_; 
v_res_2764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2762_, v_x_2763_);
lean_dec(v_x_2763_);
lean_dec_ref(v_a_2762_);
v_r_2765_ = lean_box(v_res_2764_);
return v_r_2765_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(lean_object* v_m_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v_buckets_2768_; lean_object* v___x_2769_; uint64_t v___x_2770_; uint64_t v___x_2771_; uint64_t v___x_2772_; uint64_t v_fold_2773_; uint64_t v___x_2774_; uint64_t v___x_2775_; uint64_t v___x_2776_; size_t v___x_2777_; size_t v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; size_t v___x_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v_buckets_2768_ = lean_ctor_get(v_m_2766_, 1);
v___x_2769_ = lean_array_get_size(v_buckets_2768_);
v___x_2770_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2767_);
v___x_2771_ = 32ULL;
v___x_2772_ = lean_uint64_shift_right(v___x_2770_, v___x_2771_);
v_fold_2773_ = lean_uint64_xor(v___x_2770_, v___x_2772_);
v___x_2774_ = 16ULL;
v___x_2775_ = lean_uint64_shift_right(v_fold_2773_, v___x_2774_);
v___x_2776_ = lean_uint64_xor(v_fold_2773_, v___x_2775_);
v___x_2777_ = lean_uint64_to_usize(v___x_2776_);
v___x_2778_ = lean_usize_of_nat(v___x_2769_);
v___x_2779_ = ((size_t)1ULL);
v___x_2780_ = lean_usize_sub(v___x_2778_, v___x_2779_);
v___x_2781_ = lean_usize_land(v___x_2777_, v___x_2780_);
v___x_2782_ = lean_array_uget_borrowed(v_buckets_2768_, v___x_2781_);
v___x_2783_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2767_, v___x_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg___boxed(lean_object* v_m_2784_, lean_object* v_a_2785_){
_start:
{
uint8_t v_res_2786_; lean_object* v_r_2787_; 
v_res_2786_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2784_, v_a_2785_);
lean_dec_ref(v_a_2785_);
lean_dec_ref(v_m_2784_);
v_r_2787_ = lean_box(v_res_2786_);
return v_r_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object* v_idMap_2788_, lean_object* v_b_2789_){
_start:
{
uint8_t v___x_2790_; 
v___x_2790_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_idMap_2788_, v_b_2789_);
if (v___x_2790_ == 0)
{
return v_b_2789_;
}
else
{
lean_object* v_canonicalRepresentative_2791_; 
v_canonicalRepresentative_2791_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_idMap_2788_, v_b_2789_);
lean_dec_ref(v_b_2789_);
v_b_2789_ = v_canonicalRepresentative_2791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object* v_idMap_2793_, lean_object* v_b_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2793_, v_b_2794_);
lean_dec_ref(v_idMap_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object* v_idMap_2796_, lean_object* v_id_2797_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2796_, v_id_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object* v_idMap_2799_, lean_object* v_id_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(v_idMap_2799_, v_id_2800_);
lean_dec_ref(v_idMap_2799_);
return v_res_2801_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object* v_00_u03b2_2802_, lean_object* v_m_2803_, lean_object* v_a_2804_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2803_, v_a_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object* v_00_u03b2_2806_, lean_object* v_m_2807_, lean_object* v_a_2808_){
_start:
{
uint8_t v_res_2809_; lean_object* v_r_2810_; 
v_res_2809_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(v_00_u03b2_2806_, v_m_2807_, v_a_2808_);
lean_dec_ref(v_a_2808_);
lean_dec_ref(v_m_2807_);
v_r_2810_ = lean_box(v_res_2809_);
return v_r_2810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object* v_00_u03b2_2811_, lean_object* v_m_2812_, lean_object* v_a_2813_, lean_object* v_hma_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2812_, v_a_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object* v_00_u03b2_2816_, lean_object* v_m_2817_, lean_object* v_a_2818_, lean_object* v_hma_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(v_00_u03b2_2816_, v_m_2817_, v_a_2818_, v_hma_2819_);
lean_dec_ref(v_a_2818_);
lean_dec_ref(v_m_2817_);
return v_res_2820_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(lean_object* v_00_u03b2_2821_, lean_object* v_a_2822_, lean_object* v_x_2823_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2822_, v_x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2825_, lean_object* v_a_2826_, lean_object* v_x_2827_){
_start:
{
uint8_t v_res_2828_; lean_object* v_r_2829_; 
v_res_2828_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(v_00_u03b2_2825_, v_a_2826_, v_x_2827_);
lean_dec(v_x_2827_);
lean_dec_ref(v_a_2826_);
v_r_2829_ = lean_box(v_res_2828_);
return v_r_2829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(lean_object* v_00_u03b2_2830_, lean_object* v_a_2831_, lean_object* v_x_2832_, lean_object* v_x_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2831_, v_x_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2835_, lean_object* v_a_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(v_00_u03b2_2835_, v_a_2836_, v_x_2837_, v_x_2838_);
lean_dec(v_x_2837_);
lean_dec_ref(v_a_2836_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
if (lean_obj_tag(v_a_2840_) == 0)
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_a_2841_);
return v___x_2842_;
}
else
{
if (lean_obj_tag(v_a_2841_) == 0)
{
lean_object* v_tail_2843_; 
v_tail_2843_ = lean_ctor_get(v_a_2840_, 2);
lean_inc(v_tail_2843_);
lean_dec_ref(v_a_2840_);
v_a_2840_ = v_tail_2843_;
goto _start;
}
else
{
lean_object* v_key_2845_; 
v_key_2845_ = lean_ctor_get(v_a_2840_, 0);
if (lean_obj_tag(v_key_2845_) == 0)
{
lean_object* v_tail_2846_; 
lean_inc_ref(v_key_2845_);
lean_dec_ref(v_a_2841_);
v_tail_2846_ = lean_ctor_get(v_a_2840_, 2);
lean_inc(v_tail_2846_);
lean_dec_ref(v_a_2840_);
v_a_2840_ = v_tail_2846_;
v_a_2841_ = v_key_2845_;
goto _start;
}
else
{
lean_object* v_tail_2848_; 
v_tail_2848_ = lean_ctor_get(v_a_2840_, 2);
lean_inc(v_tail_2848_);
lean_dec_ref(v_a_2840_);
v_a_2840_ = v_tail_2848_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(lean_object* v_as_2850_, size_t v_sz_2851_, size_t v_i_2852_, lean_object* v_b_2853_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_usize_dec_lt(v_i_2852_, v_sz_2851_);
if (v___x_2854_ == 0)
{
return v_b_2853_;
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2856_; 
v_a_2855_ = lean_array_uget_borrowed(v_as_2850_, v_i_2852_);
lean_inc(v_a_2855_);
v___x_2856_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(v_a_2855_, v_b_2853_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref(v___x_2856_);
return v_a_2857_;
}
else
{
lean_object* v_a_2858_; size_t v___x_2859_; size_t v___x_2860_; 
v_a_2858_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2856_);
v___x_2859_ = ((size_t)1ULL);
v___x_2860_ = lean_usize_add(v_i_2852_, v___x_2859_);
v_i_2852_ = v___x_2860_;
v_b_2853_ = v_a_2858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5___boxed(lean_object* v_as_2862_, lean_object* v_sz_2863_, lean_object* v_i_2864_, lean_object* v_b_2865_){
_start:
{
size_t v_sz_boxed_2866_; size_t v_i_boxed_2867_; lean_object* v_res_2868_; 
v_sz_boxed_2866_ = lean_unbox_usize(v_sz_2863_);
lean_dec(v_sz_2863_);
v_i_boxed_2867_ = lean_unbox_usize(v_i_2864_);
lean_dec(v_i_2864_);
v_res_2868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_as_2862_, v_sz_boxed_2866_, v_i_boxed_2867_, v_b_2865_);
lean_dec_ref(v_as_2862_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(lean_object* v_a_2869_, lean_object* v_b_2870_, lean_object* v_x_2871_){
_start:
{
if (lean_obj_tag(v_x_2871_) == 0)
{
lean_dec(v_b_2870_);
lean_dec_ref(v_a_2869_);
return v_x_2871_;
}
else
{
lean_object* v_key_2872_; lean_object* v_value_2873_; lean_object* v_tail_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2886_; 
v_key_2872_ = lean_ctor_get(v_x_2871_, 0);
v_value_2873_ = lean_ctor_get(v_x_2871_, 1);
v_tail_2874_ = lean_ctor_get(v_x_2871_, 2);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_x_2871_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2876_ = v_x_2871_;
v_isShared_2877_ = v_isSharedCheck_2886_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_tail_2874_);
lean_inc(v_value_2873_);
lean_inc(v_key_2872_);
lean_dec(v_x_2871_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2886_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
uint8_t v___x_2878_; 
v___x_2878_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2872_, v_a_2869_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2869_, v_b_2870_, v_tail_2874_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 2, v___x_2879_);
v___x_2881_ = v___x_2876_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_key_2872_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_value_2873_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
else
{
lean_object* v___x_2884_; 
lean_dec(v_value_2873_);
lean_dec(v_key_2872_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 1, v_b_2870_);
lean_ctor_set(v___x_2876_, 0, v_a_2869_);
v___x_2884_ = v___x_2876_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2869_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_b_2870_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_tail_2874_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(lean_object* v_x_2887_, lean_object* v_x_2888_){
_start:
{
if (lean_obj_tag(v_x_2888_) == 0)
{
return v_x_2887_;
}
else
{
lean_object* v_key_2889_; lean_object* v_value_2890_; lean_object* v_tail_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2914_; 
v_key_2889_ = lean_ctor_get(v_x_2888_, 0);
v_value_2890_ = lean_ctor_get(v_x_2888_, 1);
v_tail_2891_ = lean_ctor_get(v_x_2888_, 2);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_x_2888_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2893_ = v_x_2888_;
v_isShared_2894_ = v_isSharedCheck_2914_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_tail_2891_);
lean_inc(v_value_2890_);
lean_inc(v_key_2889_);
lean_dec(v_x_2888_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2914_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; uint64_t v___x_2896_; uint64_t v___x_2897_; uint64_t v___x_2898_; uint64_t v_fold_2899_; uint64_t v___x_2900_; uint64_t v___x_2901_; uint64_t v___x_2902_; size_t v___x_2903_; size_t v___x_2904_; size_t v___x_2905_; size_t v___x_2906_; size_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2895_ = lean_array_get_size(v_x_2887_);
v___x_2896_ = l_Lean_Lsp_instHashableRefIdent_hash(v_key_2889_);
v___x_2897_ = 32ULL;
v___x_2898_ = lean_uint64_shift_right(v___x_2896_, v___x_2897_);
v_fold_2899_ = lean_uint64_xor(v___x_2896_, v___x_2898_);
v___x_2900_ = 16ULL;
v___x_2901_ = lean_uint64_shift_right(v_fold_2899_, v___x_2900_);
v___x_2902_ = lean_uint64_xor(v_fold_2899_, v___x_2901_);
v___x_2903_ = lean_uint64_to_usize(v___x_2902_);
v___x_2904_ = lean_usize_of_nat(v___x_2895_);
v___x_2905_ = ((size_t)1ULL);
v___x_2906_ = lean_usize_sub(v___x_2904_, v___x_2905_);
v___x_2907_ = lean_usize_land(v___x_2903_, v___x_2906_);
v___x_2908_ = lean_array_uget_borrowed(v_x_2887_, v___x_2907_);
lean_inc(v___x_2908_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 2, v___x_2908_);
v___x_2910_ = v___x_2893_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_key_2889_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_value_2890_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_array_uset(v_x_2887_, v___x_2907_, v___x_2910_);
v_x_2887_ = v___x_2911_;
v_x_2888_ = v_tail_2891_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(lean_object* v_i_2915_, lean_object* v_source_2916_, lean_object* v_target_2917_){
_start:
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = lean_array_get_size(v_source_2916_);
v___x_2919_ = lean_nat_dec_lt(v_i_2915_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_dec_ref(v_source_2916_);
lean_dec(v_i_2915_);
return v_target_2917_;
}
else
{
lean_object* v_es_2920_; lean_object* v___x_2921_; lean_object* v_source_2922_; lean_object* v_target_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_es_2920_ = lean_array_fget(v_source_2916_, v_i_2915_);
v___x_2921_ = lean_box(0);
v_source_2922_ = lean_array_fset(v_source_2916_, v_i_2915_, v___x_2921_);
v_target_2923_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_target_2917_, v_es_2920_);
v___x_2924_ = lean_unsigned_to_nat(1u);
v___x_2925_ = lean_nat_add(v_i_2915_, v___x_2924_);
lean_dec(v_i_2915_);
v_i_2915_ = v___x_2925_;
v_source_2916_ = v_source_2922_;
v_target_2917_ = v_target_2923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(lean_object* v_data_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v_nbuckets_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2928_ = lean_array_get_size(v_data_2927_);
v___x_2929_ = lean_unsigned_to_nat(2u);
v_nbuckets_2930_ = lean_nat_mul(v___x_2928_, v___x_2929_);
v___x_2931_ = lean_unsigned_to_nat(0u);
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_mk_array(v_nbuckets_2930_, v___x_2932_);
v___x_2934_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2931_, v_data_2927_, v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object* v_m_2935_, lean_object* v_a_2936_, lean_object* v_b_2937_){
_start:
{
lean_object* v_size_2938_; lean_object* v_buckets_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2982_; 
v_size_2938_ = lean_ctor_get(v_m_2935_, 0);
v_buckets_2939_ = lean_ctor_get(v_m_2935_, 1);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_m_2935_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2941_ = v_m_2935_;
v_isShared_2942_ = v_isSharedCheck_2982_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_buckets_2939_);
lean_inc(v_size_2938_);
lean_dec(v_m_2935_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2982_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; uint64_t v___x_2944_; uint64_t v___x_2945_; uint64_t v___x_2946_; uint64_t v_fold_2947_; uint64_t v___x_2948_; uint64_t v___x_2949_; uint64_t v___x_2950_; size_t v___x_2951_; size_t v___x_2952_; size_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; lean_object* v_bkt_2956_; uint8_t v___x_2957_; 
v___x_2943_ = lean_array_get_size(v_buckets_2939_);
v___x_2944_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2936_);
v___x_2945_ = 32ULL;
v___x_2946_ = lean_uint64_shift_right(v___x_2944_, v___x_2945_);
v_fold_2947_ = lean_uint64_xor(v___x_2944_, v___x_2946_);
v___x_2948_ = 16ULL;
v___x_2949_ = lean_uint64_shift_right(v_fold_2947_, v___x_2948_);
v___x_2950_ = lean_uint64_xor(v_fold_2947_, v___x_2949_);
v___x_2951_ = lean_uint64_to_usize(v___x_2950_);
v___x_2952_ = lean_usize_of_nat(v___x_2943_);
v___x_2953_ = ((size_t)1ULL);
v___x_2954_ = lean_usize_sub(v___x_2952_, v___x_2953_);
v___x_2955_ = lean_usize_land(v___x_2951_, v___x_2954_);
v_bkt_2956_ = lean_array_uget_borrowed(v_buckets_2939_, v___x_2955_);
v___x_2957_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2936_, v_bkt_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v_size_x27_2959_; lean_object* v___x_2960_; lean_object* v_buckets_x27_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2958_ = lean_unsigned_to_nat(1u);
v_size_x27_2959_ = lean_nat_add(v_size_2938_, v___x_2958_);
lean_dec(v_size_2938_);
lean_inc(v_bkt_2956_);
v___x_2960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2960_, 0, v_a_2936_);
lean_ctor_set(v___x_2960_, 1, v_b_2937_);
lean_ctor_set(v___x_2960_, 2, v_bkt_2956_);
v_buckets_x27_2961_ = lean_array_uset(v_buckets_2939_, v___x_2955_, v___x_2960_);
v___x_2962_ = lean_unsigned_to_nat(4u);
v___x_2963_ = lean_nat_mul(v_size_x27_2959_, v___x_2962_);
v___x_2964_ = lean_unsigned_to_nat(3u);
v___x_2965_ = lean_nat_div(v___x_2963_, v___x_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_array_get_size(v_buckets_x27_2961_);
v___x_2967_ = lean_nat_dec_le(v___x_2965_, v___x_2966_);
lean_dec(v___x_2965_);
if (v___x_2967_ == 0)
{
lean_object* v_val_2968_; lean_object* v___x_2970_; 
v_val_2968_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_2961_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v_val_2968_);
lean_ctor_set(v___x_2941_, 0, v_size_x27_2959_);
v___x_2970_ = v___x_2941_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_size_x27_2959_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_val_2968_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
else
{
lean_object* v___x_2973_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v_buckets_x27_2961_);
lean_ctor_set(v___x_2941_, 0, v_size_x27_2959_);
v___x_2973_ = v___x_2941_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_size_x27_2959_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_buckets_x27_2961_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
else
{
lean_object* v___x_2975_; lean_object* v_buckets_x27_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
lean_inc(v_bkt_2956_);
v___x_2975_ = lean_box(0);
v_buckets_x27_2976_ = lean_array_uset(v_buckets_2939_, v___x_2955_, v___x_2975_);
v___x_2977_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2936_, v_b_2937_, v_bkt_2956_);
v___x_2978_ = lean_array_uset(v_buckets_x27_2976_, v___x_2955_, v___x_2977_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2978_);
v___x_2980_ = v___x_2941_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_size_2938_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object* v___x_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
if (lean_obj_tag(v_a_2984_) == 0)
{
lean_object* v___x_2986_; 
lean_dec_ref(v___x_2983_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_a_2985_);
return v___x_2986_;
}
else
{
lean_object* v_key_2987_; lean_object* v_tail_2988_; uint8_t v___x_2989_; 
v_key_2987_ = lean_ctor_get(v_a_2984_, 0);
lean_inc(v_key_2987_);
v_tail_2988_ = lean_ctor_get(v_a_2984_, 2);
lean_inc(v_tail_2988_);
lean_dec_ref(v_a_2984_);
v___x_2989_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2987_, v___x_2983_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_inc_ref(v___x_2983_);
v___x_2990_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_2985_, v_key_2987_, v___x_2983_);
v_a_2984_ = v_tail_2988_;
v_a_2985_ = v___x_2990_;
goto _start;
}
else
{
lean_dec(v_key_2987_);
v_a_2984_ = v_tail_2988_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object* v___x_2993_, lean_object* v_as_2994_, size_t v_sz_2995_, size_t v_i_2996_, lean_object* v_b_2997_){
_start:
{
uint8_t v___x_2998_; 
v___x_2998_ = lean_usize_dec_lt(v_i_2996_, v_sz_2995_);
if (v___x_2998_ == 0)
{
lean_dec_ref(v___x_2993_);
return v_b_2997_;
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3000_; 
v_a_2999_ = lean_array_uget_borrowed(v_as_2994_, v_i_2996_);
lean_inc(v_a_2999_);
lean_inc_ref(v___x_2993_);
v___x_3000_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(v___x_2993_, v_a_2999_, v_b_2997_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; 
lean_dec_ref(v___x_2993_);
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref(v___x_3000_);
return v_a_3001_;
}
else
{
lean_object* v_a_3002_; size_t v___x_3003_; size_t v___x_3004_; 
v_a_3002_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3002_);
lean_dec_ref(v___x_3000_);
v___x_3003_ = ((size_t)1ULL);
v___x_3004_ = lean_usize_add(v_i_2996_, v___x_3003_);
v_i_2996_ = v___x_3004_;
v_b_2997_ = v_a_3002_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object* v___x_3006_, lean_object* v_as_3007_, lean_object* v_sz_3008_, lean_object* v_i_3009_, lean_object* v_b_3010_){
_start:
{
size_t v_sz_boxed_3011_; size_t v_i_boxed_3012_; lean_object* v_res_3013_; 
v_sz_boxed_3011_ = lean_unbox_usize(v_sz_3008_);
lean_dec(v_sz_3008_);
v_i_boxed_3012_ = lean_unbox_usize(v_i_3009_);
lean_dec(v_i_3009_);
v_res_3013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3006_, v_as_3007_, v_sz_boxed_3011_, v_i_boxed_3012_, v_b_3010_);
lean_dec_ref(v_as_3007_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
if (lean_obj_tag(v_a_3014_) == 0)
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3016_, 0, v_a_3015_);
return v___x_3016_;
}
else
{
lean_object* v_value_3017_; lean_object* v_key_3018_; lean_object* v_tail_3019_; lean_object* v_buckets_3020_; size_t v_sz_3021_; size_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_value_3017_ = lean_ctor_get(v_a_3014_, 1);
lean_inc(v_value_3017_);
v_key_3018_ = lean_ctor_get(v_a_3014_, 0);
lean_inc(v_key_3018_);
v_tail_3019_ = lean_ctor_get(v_a_3014_, 2);
lean_inc(v_tail_3019_);
lean_dec_ref(v_a_3014_);
v_buckets_3020_ = lean_ctor_get(v_value_3017_, 1);
lean_inc_ref(v_buckets_3020_);
lean_dec(v_value_3017_);
v_sz_3021_ = lean_array_size(v_buckets_3020_);
v___x_3022_ = ((size_t)0ULL);
v___x_3023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_buckets_3020_, v_sz_3021_, v___x_3022_, v_key_3018_);
v___x_3024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3023_, v_buckets_3020_, v_sz_3021_, v___x_3022_, v_a_3015_);
lean_dec_ref(v_buckets_3020_);
v_a_3014_ = v_tail_3019_;
v_a_3015_ = v___x_3024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object* v_as_3026_, size_t v_sz_3027_, size_t v_i_3028_, lean_object* v_b_3029_){
_start:
{
uint8_t v___x_3030_; 
v___x_3030_ = lean_usize_dec_lt(v_i_3028_, v_sz_3027_);
if (v___x_3030_ == 0)
{
return v_b_3029_;
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_array_uget_borrowed(v_as_3026_, v_i_3028_);
lean_inc(v_a_3031_);
v___x_3032_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(v_a_3031_, v_b_3029_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref(v___x_3032_);
return v_a_3033_;
}
else
{
lean_object* v_a_3034_; size_t v___x_3035_; size_t v___x_3036_; 
v_a_3034_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3034_);
lean_dec_ref(v___x_3032_);
v___x_3035_ = ((size_t)1ULL);
v___x_3036_ = lean_usize_add(v_i_3028_, v___x_3035_);
v_i_3028_ = v___x_3036_;
v_b_3029_ = v_a_3034_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object* v_as_3038_, lean_object* v_sz_3039_, lean_object* v_i_3040_, lean_object* v_b_3041_){
_start:
{
size_t v_sz_boxed_3042_; size_t v_i_boxed_3043_; lean_object* v_res_3044_; 
v_sz_boxed_3042_ = lean_unbox_usize(v_sz_3039_);
lean_dec(v_sz_3039_);
v_i_boxed_3043_ = lean_unbox_usize(v_i_3040_);
lean_dec(v_i_3040_);
v_res_3044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_as_3038_, v_sz_boxed_3042_, v_i_boxed_3043_, v_b_3041_);
lean_dec_ref(v_as_3038_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object* v_a_3045_, lean_object* v_x_3046_){
_start:
{
if (lean_obj_tag(v_x_3046_) == 0)
{
return v_x_3046_;
}
else
{
lean_object* v_key_3047_; lean_object* v_value_3048_; lean_object* v_tail_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3058_; 
v_key_3047_ = lean_ctor_get(v_x_3046_, 0);
v_value_3048_ = lean_ctor_get(v_x_3046_, 1);
v_tail_3049_ = lean_ctor_get(v_x_3046_, 2);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_x_3046_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3051_ = v_x_3046_;
v_isShared_3052_ = v_isSharedCheck_3058_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_tail_3049_);
lean_inc(v_value_3048_);
lean_inc(v_key_3047_);
lean_dec(v_x_3046_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3058_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
uint8_t v___x_3053_; 
v___x_3053_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3047_, v_a_3045_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3045_, v_tail_3049_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 2, v___x_3054_);
v___x_3056_ = v___x_3051_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_key_3047_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_value_3048_);
lean_ctor_set(v_reuseFailAlloc_3057_, 2, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
else
{
lean_del_object(v___x_3051_);
lean_dec(v_value_3048_);
lean_dec(v_key_3047_);
return v_tail_3049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object* v_a_3059_, lean_object* v_x_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3059_, v_x_3060_);
lean_dec_ref(v_a_3059_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object* v_m_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v_size_3064_; lean_object* v_buckets_3065_; lean_object* v___x_3066_; uint64_t v___x_3067_; uint64_t v___x_3068_; uint64_t v___x_3069_; uint64_t v_fold_3070_; uint64_t v___x_3071_; uint64_t v___x_3072_; uint64_t v___x_3073_; size_t v___x_3074_; size_t v___x_3075_; size_t v___x_3076_; size_t v___x_3077_; size_t v___x_3078_; lean_object* v_bkt_3079_; uint8_t v___x_3080_; 
v_size_3064_ = lean_ctor_get(v_m_3062_, 0);
v_buckets_3065_ = lean_ctor_get(v_m_3062_, 1);
v___x_3066_ = lean_array_get_size(v_buckets_3065_);
v___x_3067_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3063_);
v___x_3068_ = 32ULL;
v___x_3069_ = lean_uint64_shift_right(v___x_3067_, v___x_3068_);
v_fold_3070_ = lean_uint64_xor(v___x_3067_, v___x_3069_);
v___x_3071_ = 16ULL;
v___x_3072_ = lean_uint64_shift_right(v_fold_3070_, v___x_3071_);
v___x_3073_ = lean_uint64_xor(v_fold_3070_, v___x_3072_);
v___x_3074_ = lean_uint64_to_usize(v___x_3073_);
v___x_3075_ = lean_usize_of_nat(v___x_3066_);
v___x_3076_ = ((size_t)1ULL);
v___x_3077_ = lean_usize_sub(v___x_3075_, v___x_3076_);
v___x_3078_ = lean_usize_land(v___x_3074_, v___x_3077_);
v_bkt_3079_ = lean_array_uget_borrowed(v_buckets_3065_, v___x_3078_);
v___x_3080_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3063_, v_bkt_3079_);
if (v___x_3080_ == 0)
{
return v_m_3062_;
}
else
{
lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3093_; 
lean_inc(v_bkt_3079_);
lean_inc_ref(v_buckets_3065_);
lean_inc(v_size_3064_);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_m_3062_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; lean_object* v_unused_3095_; 
v_unused_3094_ = lean_ctor_get(v_m_3062_, 1);
lean_dec(v_unused_3094_);
v_unused_3095_ = lean_ctor_get(v_m_3062_, 0);
lean_dec(v_unused_3095_);
v___x_3082_ = v_m_3062_;
v_isShared_3083_ = v_isSharedCheck_3093_;
goto v_resetjp_3081_;
}
else
{
lean_dec(v_m_3062_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3093_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3084_; lean_object* v_buckets_x27_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3084_ = lean_box(0);
v_buckets_x27_3085_ = lean_array_uset(v_buckets_3065_, v___x_3078_, v___x_3084_);
v___x_3086_ = lean_unsigned_to_nat(1u);
v___x_3087_ = lean_nat_sub(v_size_3064_, v___x_3086_);
lean_dec(v_size_3064_);
v___x_3088_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3063_, v_bkt_3079_);
v___x_3089_ = lean_array_uset(v_buckets_x27_3085_, v___x_3078_, v___x_3088_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 1, v___x_3089_);
lean_ctor_set(v___x_3082_, 0, v___x_3087_);
v___x_3091_ = v___x_3082_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object* v_m_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3096_, v_a_3097_);
lean_dec_ref(v_a_3097_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object* v_m_3099_, lean_object* v_a_3100_, lean_object* v_b_3101_){
_start:
{
lean_object* v_size_3102_; lean_object* v_buckets_3103_; lean_object* v___x_3104_; uint64_t v___x_3105_; uint64_t v___x_3106_; uint64_t v___x_3107_; uint64_t v_fold_3108_; uint64_t v___x_3109_; uint64_t v___x_3110_; uint64_t v___x_3111_; size_t v___x_3112_; size_t v___x_3113_; size_t v___x_3114_; size_t v___x_3115_; size_t v___x_3116_; lean_object* v_bkt_3117_; uint8_t v___x_3118_; 
v_size_3102_ = lean_ctor_get(v_m_3099_, 0);
v_buckets_3103_ = lean_ctor_get(v_m_3099_, 1);
v___x_3104_ = lean_array_get_size(v_buckets_3103_);
v___x_3105_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3100_);
v___x_3106_ = 32ULL;
v___x_3107_ = lean_uint64_shift_right(v___x_3105_, v___x_3106_);
v_fold_3108_ = lean_uint64_xor(v___x_3105_, v___x_3107_);
v___x_3109_ = 16ULL;
v___x_3110_ = lean_uint64_shift_right(v_fold_3108_, v___x_3109_);
v___x_3111_ = lean_uint64_xor(v_fold_3108_, v___x_3110_);
v___x_3112_ = lean_uint64_to_usize(v___x_3111_);
v___x_3113_ = lean_usize_of_nat(v___x_3104_);
v___x_3114_ = ((size_t)1ULL);
v___x_3115_ = lean_usize_sub(v___x_3113_, v___x_3114_);
v___x_3116_ = lean_usize_land(v___x_3112_, v___x_3115_);
v_bkt_3117_ = lean_array_uget_borrowed(v_buckets_3103_, v___x_3116_);
v___x_3118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3100_, v_bkt_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3139_; 
lean_inc_ref(v_buckets_3103_);
lean_inc(v_size_3102_);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_m_3099_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; lean_object* v_unused_3141_; 
v_unused_3140_ = lean_ctor_get(v_m_3099_, 1);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v_m_3099_, 0);
lean_dec(v_unused_3141_);
v___x_3120_ = v_m_3099_;
v_isShared_3121_ = v_isSharedCheck_3139_;
goto v_resetjp_3119_;
}
else
{
lean_dec(v_m_3099_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3139_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v_size_x27_3123_; lean_object* v___x_3124_; lean_object* v_buckets_x27_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3122_ = lean_unsigned_to_nat(1u);
v_size_x27_3123_ = lean_nat_add(v_size_3102_, v___x_3122_);
lean_dec(v_size_3102_);
lean_inc(v_bkt_3117_);
v___x_3124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3124_, 0, v_a_3100_);
lean_ctor_set(v___x_3124_, 1, v_b_3101_);
lean_ctor_set(v___x_3124_, 2, v_bkt_3117_);
v_buckets_x27_3125_ = lean_array_uset(v_buckets_3103_, v___x_3116_, v___x_3124_);
v___x_3126_ = lean_unsigned_to_nat(4u);
v___x_3127_ = lean_nat_mul(v_size_x27_3123_, v___x_3126_);
v___x_3128_ = lean_unsigned_to_nat(3u);
v___x_3129_ = lean_nat_div(v___x_3127_, v___x_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_array_get_size(v_buckets_x27_3125_);
v___x_3131_ = lean_nat_dec_le(v___x_3129_, v___x_3130_);
lean_dec(v___x_3129_);
if (v___x_3131_ == 0)
{
lean_object* v_val_3132_; lean_object* v___x_3134_; 
v_val_3132_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3125_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v_val_3132_);
lean_ctor_set(v___x_3120_, 0, v_size_x27_3123_);
v___x_3134_ = v___x_3120_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_size_x27_3123_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_val_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
else
{
lean_object* v___x_3137_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v_buckets_x27_3125_);
lean_ctor_set(v___x_3120_, 0, v_size_x27_3123_);
v___x_3137_ = v___x_3120_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_size_x27_3123_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_buckets_x27_3125_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_dec(v_b_3101_);
lean_dec_ref(v_a_3100_);
return v_m_3099_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object* v_a_3142_, lean_object* v_fallback_3143_, lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3144_) == 0)
{
lean_inc(v_fallback_3143_);
return v_fallback_3143_;
}
else
{
lean_object* v_key_3145_; lean_object* v_value_3146_; lean_object* v_tail_3147_; uint8_t v___x_3148_; 
v_key_3145_ = lean_ctor_get(v_x_3144_, 0);
v_value_3146_ = lean_ctor_get(v_x_3144_, 1);
v_tail_3147_ = lean_ctor_get(v_x_3144_, 2);
v___x_3148_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3145_, v_a_3142_);
if (v___x_3148_ == 0)
{
v_x_3144_ = v_tail_3147_;
goto _start;
}
else
{
lean_inc(v_value_3146_);
return v_value_3146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object* v_a_3150_, lean_object* v_fallback_3151_, lean_object* v_x_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3150_, v_fallback_3151_, v_x_3152_);
lean_dec(v_x_3152_);
lean_dec(v_fallback_3151_);
lean_dec_ref(v_a_3150_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object* v_m_3154_, lean_object* v_a_3155_, lean_object* v_fallback_3156_){
_start:
{
lean_object* v_buckets_3157_; lean_object* v___x_3158_; uint64_t v___x_3159_; uint64_t v___x_3160_; uint64_t v___x_3161_; uint64_t v_fold_3162_; uint64_t v___x_3163_; uint64_t v___x_3164_; uint64_t v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; size_t v___x_3168_; size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_buckets_3157_ = lean_ctor_get(v_m_3154_, 1);
v___x_3158_ = lean_array_get_size(v_buckets_3157_);
v___x_3159_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3155_);
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
v___x_3171_ = lean_array_uget_borrowed(v_buckets_3157_, v___x_3170_);
v___x_3172_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3155_, v_fallback_3156_, v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object* v_m_3173_, lean_object* v_a_3174_, lean_object* v_fallback_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3173_, v_a_3174_, v_fallback_3175_);
lean_dec(v_fallback_3175_);
lean_dec_ref(v_a_3174_);
lean_dec_ref(v_m_3173_);
return v_res_3176_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_unsigned_to_nat(16u);
v___x_3179_ = lean_mk_array(v___x_3178_, v___x_3177_);
return v___x_3179_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3180_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0);
v___x_3181_ = lean_unsigned_to_nat(0u);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v___x_3180_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object* v_idMap_3183_, lean_object* v_classesById_3184_, lean_object* v_id_3185_){
_start:
{
lean_object* v_representative_3186_; lean_object* v___x_3187_; lean_object* v_class_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v_class_3191_; lean_object* v___x_3192_; 
lean_inc_ref(v_id_3185_);
v_representative_3186_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_3183_, v_id_3185_);
v___x_3187_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_class_3188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_classesById_3184_, v_representative_3186_, v___x_3187_);
v___x_3189_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_classesById_3184_, v_representative_3186_);
v___x_3190_ = lean_box(0);
v_class_3191_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_class_3188_, v_id_3185_, v___x_3190_);
v___x_3192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v___x_3189_, v_representative_3186_, v_class_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object* v_idMap_3193_, lean_object* v_classesById_3194_, lean_object* v_id_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3193_, v_classesById_3194_, v_id_3195_);
lean_dec_ref(v_idMap_3193_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object* v_idMap_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
if (lean_obj_tag(v_a_3198_) == 0)
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3200_, 0, v_a_3199_);
return v___x_3200_;
}
else
{
lean_object* v_key_3201_; lean_object* v_value_3202_; lean_object* v_tail_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_key_3201_ = lean_ctor_get(v_a_3198_, 0);
lean_inc(v_key_3201_);
v_value_3202_ = lean_ctor_get(v_a_3198_, 1);
lean_inc(v_value_3202_);
v_tail_3203_ = lean_ctor_get(v_a_3198_, 2);
lean_inc(v_tail_3203_);
lean_dec_ref(v_a_3198_);
v___x_3204_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3197_, v_a_3199_, v_key_3201_);
v___x_3205_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3197_, v___x_3204_, v_value_3202_);
v_a_3198_ = v_tail_3203_;
v_a_3199_ = v___x_3205_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object* v_idMap_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3207_, v_a_3208_, v_a_3209_);
lean_dec_ref(v_idMap_3207_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object* v_idMap_3211_, lean_object* v_as_3212_, size_t v_sz_3213_, size_t v_i_3214_, lean_object* v_b_3215_){
_start:
{
uint8_t v___x_3216_; 
v___x_3216_ = lean_usize_dec_lt(v_i_3214_, v_sz_3213_);
if (v___x_3216_ == 0)
{
return v_b_3215_;
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3218_; 
v_a_3217_ = lean_array_uget_borrowed(v_as_3212_, v_i_3214_);
lean_inc(v_a_3217_);
v___x_3218_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3211_, v_a_3217_, v_b_3215_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref(v___x_3218_);
return v_a_3219_;
}
else
{
lean_object* v_a_3220_; size_t v___x_3221_; size_t v___x_3222_; 
v_a_3220_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3220_);
lean_dec_ref(v___x_3218_);
v___x_3221_ = ((size_t)1ULL);
v___x_3222_ = lean_usize_add(v_i_3214_, v___x_3221_);
v_i_3214_ = v___x_3222_;
v_b_3215_ = v_a_3220_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object* v_idMap_3224_, lean_object* v_as_3225_, lean_object* v_sz_3226_, lean_object* v_i_3227_, lean_object* v_b_3228_){
_start:
{
size_t v_sz_boxed_3229_; size_t v_i_boxed_3230_; lean_object* v_res_3231_; 
v_sz_boxed_3229_ = lean_unbox_usize(v_sz_3226_);
lean_dec(v_sz_3226_);
v_i_boxed_3230_ = lean_unbox_usize(v_i_3227_);
lean_dec(v_i_3227_);
v_res_3231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3224_, v_as_3225_, v_sz_boxed_3229_, v_i_boxed_3230_, v_b_3228_);
lean_dec_ref(v_as_3225_);
lean_dec_ref(v_idMap_3224_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object* v_idMap_3232_){
_start:
{
lean_object* v_buckets_3233_; lean_object* v_classesById_3234_; size_t v_sz_3235_; size_t v___x_3236_; lean_object* v___x_3237_; lean_object* v_buckets_3238_; size_t v_sz_3239_; lean_object* v___x_3240_; 
v_buckets_3233_ = lean_ctor_get(v_idMap_3232_, 1);
v_classesById_3234_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_sz_3235_ = lean_array_size(v_buckets_3233_);
v___x_3236_ = ((size_t)0ULL);
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3232_, v_buckets_3233_, v_sz_3235_, v___x_3236_, v_classesById_3234_);
v_buckets_3238_ = lean_ctor_get(v___x_3237_, 1);
lean_inc_ref(v_buckets_3238_);
lean_dec_ref(v___x_3237_);
v_sz_3239_ = lean_array_size(v_buckets_3238_);
v___x_3240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_buckets_3238_, v_sz_3239_, v___x_3236_, v_classesById_3234_);
lean_dec_ref(v_buckets_3238_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object* v_idMap_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v_idMap_3241_);
lean_dec_ref(v_idMap_3241_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object* v_00_u03b2_3243_, lean_object* v_m_3244_, lean_object* v_a_3245_, lean_object* v_fallback_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3244_, v_a_3245_, v_fallback_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object* v_00_u03b2_3248_, lean_object* v_m_3249_, lean_object* v_a_3250_, lean_object* v_fallback_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(v_00_u03b2_3248_, v_m_3249_, v_a_3250_, v_fallback_3251_);
lean_dec(v_fallback_3251_);
lean_dec_ref(v_a_3250_);
lean_dec_ref(v_m_3249_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object* v_00_u03b2_3253_, lean_object* v_m_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3254_, v_a_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object* v_00_u03b2_3257_, lean_object* v_m_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(v_00_u03b2_3257_, v_m_3258_, v_a_3259_);
lean_dec_ref(v_a_3259_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object* v_00_u03b2_3261_, lean_object* v_m_3262_, lean_object* v_a_3263_, lean_object* v_b_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_m_3262_, v_a_3263_, v_b_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object* v_00_u03b2_3266_, lean_object* v_m_3267_, lean_object* v_a_3268_, lean_object* v_b_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_m_3267_, v_a_3268_, v_b_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object* v_00_u03b2_3271_, lean_object* v_a_3272_, lean_object* v_fallback_3273_, lean_object* v_x_3274_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3272_, v_fallback_3273_, v_x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3276_, lean_object* v_a_3277_, lean_object* v_fallback_3278_, lean_object* v_x_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(v_00_u03b2_3276_, v_a_3277_, v_fallback_3278_, v_x_3279_);
lean_dec(v_x_3279_);
lean_dec(v_fallback_3278_);
lean_dec_ref(v_a_3277_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object* v_00_u03b2_3281_, lean_object* v_a_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3282_, v_x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3285_, lean_object* v_a_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(v_00_u03b2_3285_, v_a_3286_, v_x_3287_);
lean_dec_ref(v_a_3286_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object* v_00_u03b2_3289_, lean_object* v_data_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_data_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object* v_00_u03b2_3292_, lean_object* v_a_3293_, lean_object* v_b_3294_, lean_object* v_x_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_3293_, v_b_3294_, v_x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3297_, lean_object* v_i_3298_, lean_object* v_source_3299_, lean_object* v_target_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v_i_3298_, v_source_3299_, v_target_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object* v_00_u03b2_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_x_3303_, v_x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object* v_id_3306_, lean_object* v_baseId_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3309_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_a_3308_, v_id_3306_);
v___x_3310_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_a_3308_, v_baseId_3307_);
v___x_3311_ = l_Lean_Lsp_instBEqRefIdent_beq(v___x_3310_, v___x_3309_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = lean_box(0);
v___x_3313_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3308_, v___x_3309_, v___x_3310_);
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
return v___x_3314_;
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v___x_3310_);
lean_dec_ref(v___x_3309_);
v___x_3315_ = lean_box(0);
v___x_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
lean_ctor_set(v___x_3316_, 1, v_a_3308_);
return v___x_3316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object* v___x_3317_, lean_object* v_ci_3318_, lean_object* v_info_3319_, lean_object* v_x_3320_, lean_object* v___y_3321_){
_start:
{
if (lean_obj_tag(v_info_3319_) == 11)
{
lean_object* v_toCommandContextInfo_3322_; lean_object* v_i_3323_; lean_object* v_env_3324_; lean_object* v___x_3325_; lean_object* v_mainModule_3326_; lean_object* v_id_3327_; lean_object* v_baseId_3328_; uint8_t v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_toCommandContextInfo_3322_ = lean_ctor_get(v_ci_3318_, 0);
v_i_3323_ = lean_ctor_get(v_info_3319_, 0);
lean_inc_ref(v_i_3323_);
lean_dec_ref(v_info_3319_);
v_env_3324_ = lean_ctor_get(v_toCommandContextInfo_3322_, 0);
v___x_3325_ = l_Lean_Environment_header(v_env_3324_);
v_mainModule_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_mainModule_3326_);
lean_dec_ref(v___x_3325_);
v_id_3327_ = lean_ctor_get(v_i_3323_, 1);
lean_inc(v_id_3327_);
v_baseId_3328_ = lean_ctor_get(v_i_3323_, 2);
lean_inc(v_baseId_3328_);
lean_dec_ref(v_i_3323_);
v___x_3329_ = 1;
v___x_3330_ = l_Lean_Name_toString(v_mainModule_3326_, v___x_3329_);
v___x_3331_ = l_Lean_Name_toString(v_id_3327_, v___x_3329_);
lean_inc_ref(v___x_3330_);
v___x_3332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3330_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_Name_toString(v_baseId_3328_, v___x_3329_);
v___x_3334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3330_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v___x_3332_, v___x_3334_, v___y_3321_);
return v___x_3335_;
}
else
{
lean_object* v___x_3336_; 
lean_dec_ref(v_info_3319_);
v___x_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3317_);
lean_ctor_set(v___x_3336_, 1, v___y_3321_);
return v___x_3336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object* v___x_3337_, lean_object* v_ci_3338_, lean_object* v_info_3339_, lean_object* v_x_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(v___x_3337_, v_ci_3338_, v_info_3339_, v_x_3340_, v___y_3341_);
lean_dec_ref(v_x_3340_);
lean_dec_ref(v_ci_3338_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object* v_x_3343_, lean_object* v_x_3344_, lean_object* v_x_3345_, lean_object* v___y_3346_){
_start:
{
uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = 1;
v___x_3348_ = lean_box(v___x_3347_);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
lean_ctor_set(v___x_3349_, 1, v___y_3346_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object* v_x_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(v_x_3350_, v_x_3351_, v_x_3352_, v___y_3353_);
lean_dec_ref(v_x_3352_);
lean_dec_ref(v_x_3351_);
lean_dec_ref(v_x_3350_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3355_, lean_object* v_ci_3356_, lean_object* v_i_3357_, lean_object* v_cs_3358_, lean_object* v_x_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_apply_4(v_postNode_3355_, v_ci_3356_, v_i_3357_, v_cs_3358_, v___y_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3362_, lean_object* v_ci_3363_, lean_object* v_i_3364_, lean_object* v_cs_3365_, lean_object* v_x_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3362_, v_ci_3363_, v_i_3364_, v_cs_3365_, v_x_3366_, v___y_3367_);
lean_dec(v_x_3366_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___f_3371_; lean_object* v___f_3372_; lean_object* v___f_3373_; lean_object* v___f_3374_; lean_object* v___f_3375_; lean_object* v___f_3376_; lean_object* v___f_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___f_3381_; lean_object* v___f_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3773__overap_3393_; lean_object* v___x_3394_; 
v___f_3371_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3372_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3373_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3374_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3375_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3376_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3377_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___f_3371_);
lean_ctor_set(v___x_3378_, 1, v___f_3372_);
v___x_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
lean_ctor_set(v___x_3379_, 1, v___f_3373_);
lean_ctor_set(v___x_3379_, 2, v___f_3374_);
lean_ctor_set(v___x_3379_, 3, v___f_3375_);
lean_ctor_set(v___x_3379_, 4, v___f_3376_);
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
lean_ctor_set(v___x_3380_, 1, v___f_3377_);
lean_inc_ref_n(v___x_3380_, 6);
v___f_3381_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3381_, 0, v___x_3380_);
v___f_3382_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3382_, 0, v___x_3380_);
v___f_3383_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3383_, 0, v___x_3380_);
v___f_3384_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3384_, 0, v___x_3380_);
v___x_3385_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3385_, 0, lean_box(0));
lean_closure_set(v___x_3385_, 1, lean_box(0));
lean_closure_set(v___x_3385_, 2, v___x_3380_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v___f_3381_);
v___x_3387_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3387_, 0, lean_box(0));
lean_closure_set(v___x_3387_, 1, lean_box(0));
lean_closure_set(v___x_3387_, 2, v___x_3380_);
v___x_3388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
lean_ctor_set(v___x_3388_, 2, v___f_3382_);
lean_ctor_set(v___x_3388_, 3, v___f_3383_);
lean_ctor_set(v___x_3388_, 4, v___f_3384_);
v___x_3389_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3389_, 0, lean_box(0));
lean_closure_set(v___x_3389_, 1, lean_box(0));
lean_closure_set(v___x_3389_, 2, v___x_3380_);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_box(0);
v___x_3392_ = l_instInhabitedOfMonad___redArg(v___x_3390_, v___x_3391_);
v___x_3773__overap_3393_ = lean_panic_fn_borrowed(v___x_3392_, v_msg_3369_);
lean_dec(v___x_3392_);
v___x_3394_ = lean_apply_1(v___x_3773__overap_3393_, v___y_3370_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3395_, lean_object* v_postNode_3396_, lean_object* v_x_3397_, lean_object* v_x_3398_, lean_object* v___y_3399_){
_start:
{
switch(lean_obj_tag(v_x_3398_))
{
case 0:
{
lean_object* v_i_3400_; lean_object* v_t_3401_; lean_object* v___x_3402_; 
v_i_3400_ = lean_ctor_get(v_x_3398_, 0);
lean_inc_ref(v_i_3400_);
v_t_3401_ = lean_ctor_get(v_x_3398_, 1);
lean_inc_ref(v_t_3401_);
lean_dec_ref(v_x_3398_);
v___x_3402_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3400_, v_x_3397_);
v_x_3397_ = v___x_3402_;
v_x_3398_ = v_t_3401_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3397_) == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec_ref(v_x_3398_);
lean_dec_ref(v_postNode_3396_);
lean_dec_ref(v_preNode_3395_);
v___x_3404_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3405_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3404_, v___y_3399_);
return v___x_3405_;
}
else
{
lean_object* v_i_3406_; lean_object* v_children_3407_; lean_object* v_val_3408_; lean_object* v___x_3409_; lean_object* v_fst_3410_; uint8_t v___x_3411_; 
v_i_3406_ = lean_ctor_get(v_x_3398_, 0);
lean_inc_ref_n(v_i_3406_, 2);
v_children_3407_ = lean_ctor_get(v_x_3398_, 1);
lean_inc_ref_n(v_children_3407_, 2);
lean_dec_ref(v_x_3398_);
v_val_3408_ = lean_ctor_get(v_x_3397_, 0);
lean_inc_n(v_val_3408_, 2);
lean_inc_ref(v_preNode_3395_);
v___x_3409_ = lean_apply_4(v_preNode_3395_, v_val_3408_, v_i_3406_, v_children_3407_, v___y_3399_);
v_fst_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_fst_3410_);
v___x_3411_ = lean_unbox(v_fst_3410_);
lean_dec(v_fst_3410_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_preNode_3395_);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_x_3397_);
if (v_isSharedCheck_3430_ == 0)
{
lean_object* v_unused_3431_; 
v_unused_3431_ = lean_ctor_get(v_x_3397_, 0);
lean_dec(v_unused_3431_);
v___x_3413_ = v_x_3397_;
v_isShared_3414_ = v_isSharedCheck_3430_;
goto v_resetjp_3412_;
}
else
{
lean_dec(v_x_3397_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3430_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v_snd_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v_fst_3418_; lean_object* v_snd_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3429_; 
v_snd_3415_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_snd_3415_);
lean_dec_ref(v___x_3409_);
v___x_3416_ = lean_box(0);
v___x_3417_ = lean_apply_5(v_postNode_3396_, v_val_3408_, v_i_3406_, v_children_3407_, v___x_3416_, v_snd_3415_);
v_fst_3418_ = lean_ctor_get(v___x_3417_, 0);
v_snd_3419_ = lean_ctor_get(v___x_3417_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3421_ = v___x_3417_;
v_isShared_3422_ = v_isSharedCheck_3429_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_snd_3419_);
lean_inc(v_fst_3418_);
lean_dec(v___x_3417_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3429_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v_fst_3418_);
v___x_3424_ = v___x_3413_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_fst_3418_);
v___x_3424_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v___x_3424_);
v___x_3426_ = v___x_3421_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_snd_3419_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
else
{
lean_object* v_snd_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v_fst_3437_; lean_object* v_snd_3438_; lean_object* v___x_3439_; lean_object* v_fst_3440_; lean_object* v_snd_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3449_; 
v_snd_3432_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_snd_3432_);
lean_dec_ref(v___x_3409_);
v___x_3433_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3397_, v_i_3406_);
v___x_3434_ = l_Lean_PersistentArray_toList___redArg(v_children_3407_);
v___x_3435_ = lean_box(0);
lean_inc_ref(v_postNode_3396_);
v___x_3436_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3395_, v_postNode_3396_, v___x_3433_, v___x_3434_, v___x_3435_, v_snd_3432_);
v_fst_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_fst_3437_);
v_snd_3438_ = lean_ctor_get(v___x_3436_, 1);
lean_inc(v_snd_3438_);
lean_dec_ref(v___x_3436_);
v___x_3439_ = lean_apply_5(v_postNode_3396_, v_val_3408_, v_i_3406_, v_children_3407_, v_fst_3437_, v_snd_3438_);
v_fst_3440_ = lean_ctor_get(v___x_3439_, 0);
v_snd_3441_ = lean_ctor_get(v___x_3439_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3443_ = v___x_3439_;
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_snd_3441_);
lean_inc(v_fst_3440_);
lean_dec(v___x_3439_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v_fst_3440_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3445_);
v___x_3447_ = v___x_3443_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_snd_3441_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
default: 
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_dec_ref(v_x_3398_);
lean_dec(v_x_3397_);
lean_dec_ref(v_postNode_3396_);
lean_dec_ref(v_preNode_3395_);
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
lean_ctor_set(v___x_3451_, 1, v___y_3399_);
return v___x_3451_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3452_, lean_object* v_postNode_3453_, lean_object* v___x_3454_, lean_object* v_x_3455_, lean_object* v_x_3456_, lean_object* v___y_3457_){
_start:
{
if (lean_obj_tag(v_x_3455_) == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_dec(v___x_3454_);
lean_dec_ref(v_postNode_3453_);
lean_dec_ref(v_preNode_3452_);
v___x_3458_ = l_List_reverse___redArg(v_x_3456_);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v___y_3457_);
return v___x_3459_;
}
else
{
lean_object* v_head_3460_; lean_object* v_tail_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3472_; 
v_head_3460_ = lean_ctor_get(v_x_3455_, 0);
v_tail_3461_ = lean_ctor_get(v_x_3455_, 1);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_x_3455_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3463_ = v_x_3455_;
v_isShared_3464_ = v_isSharedCheck_3472_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_tail_3461_);
lean_inc(v_head_3460_);
lean_dec(v_x_3455_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3472_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v_fst_3466_; lean_object* v_snd_3467_; lean_object* v___x_3469_; 
lean_inc(v___x_3454_);
lean_inc_ref(v_postNode_3453_);
lean_inc_ref(v_preNode_3452_);
v___x_3465_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3452_, v_postNode_3453_, v___x_3454_, v_head_3460_, v___y_3457_);
v_fst_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_fst_3466_);
v_snd_3467_ = lean_ctor_get(v___x_3465_, 1);
lean_inc(v_snd_3467_);
lean_dec_ref(v___x_3465_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v_x_3456_);
lean_ctor_set(v___x_3463_, 0, v_fst_3466_);
v___x_3469_ = v___x_3463_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_fst_3466_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_x_3456_);
v___x_3469_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
v_x_3455_ = v_tail_3461_;
v_x_3456_ = v___x_3469_;
v___y_3457_ = v_snd_3467_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3473_, lean_object* v_postNode_3474_, lean_object* v_ctx_x3f_3475_, lean_object* v_t_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v___f_3478_; lean_object* v___x_3479_; lean_object* v_snd_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3488_; 
v___f_3478_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3478_, 0, v_postNode_3474_);
v___x_3479_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3473_, v___f_3478_, v_ctx_x3f_3475_, v_t_3476_, v___y_3477_);
v_snd_3480_ = lean_ctor_get(v___x_3479_, 1);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3479_, 0);
lean_dec(v_unused_3489_);
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_snd_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = lean_box(0);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(lean_object* v_as_3493_, size_t v_i_3494_, size_t v_stop_3495_, lean_object* v_b_3496_, lean_object* v___y_3497_){
_start:
{
uint8_t v___x_3498_; 
v___x_3498_ = lean_usize_dec_eq(v_i_3494_, v_stop_3495_);
if (v___x_3498_ == 0)
{
lean_object* v___f_3499_; lean_object* v___f_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v_fst_3504_; lean_object* v_snd_3505_; size_t v___x_3506_; size_t v___x_3507_; 
v___f_3499_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0));
v___f_3500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1));
v___x_3501_ = lean_array_uget_borrowed(v_as_3493_, v_i_3494_);
v___x_3502_ = lean_box(0);
lean_inc(v___x_3501_);
v___x_3503_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(v___f_3499_, v___f_3500_, v___x_3502_, v___x_3501_, v___y_3497_);
v_fst_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_fst_3504_);
v_snd_3505_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_snd_3505_);
lean_dec_ref(v___x_3503_);
v___x_3506_ = ((size_t)1ULL);
v___x_3507_ = lean_usize_add(v_i_3494_, v___x_3506_);
v_i_3494_ = v___x_3507_;
v_b_3496_ = v_fst_3504_;
v___y_3497_ = v_snd_3505_;
goto _start;
}
else
{
lean_object* v___x_3509_; 
v___x_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3509_, 0, v_b_3496_);
lean_ctor_set(v___x_3509_, 1, v___y_3497_);
return v___x_3509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___boxed(lean_object* v_as_3510_, lean_object* v_i_3511_, lean_object* v_stop_3512_, lean_object* v_b_3513_, lean_object* v___y_3514_){
_start:
{
size_t v_i_boxed_3515_; size_t v_stop_boxed_3516_; lean_object* v_res_3517_; 
v_i_boxed_3515_ = lean_unbox_usize(v_i_3511_);
lean_dec(v_i_3511_);
v_stop_boxed_3516_ = lean_unbox_usize(v_stop_3512_);
lean_dec(v_stop_3512_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_as_3510_, v_i_boxed_3515_, v_stop_boxed_3516_, v_b_3513_, v___y_3514_);
lean_dec_ref(v_as_3510_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(lean_object* v_a_3518_, lean_object* v_x_3519_){
_start:
{
if (lean_obj_tag(v_x_3519_) == 0)
{
lean_object* v___x_3520_; 
v___x_3520_ = lean_box(0);
return v___x_3520_;
}
else
{
lean_object* v_key_3521_; lean_object* v_value_3522_; lean_object* v_tail_3523_; uint8_t v___x_3524_; 
v_key_3521_ = lean_ctor_get(v_x_3519_, 0);
v_value_3522_ = lean_ctor_get(v_x_3519_, 1);
v_tail_3523_ = lean_ctor_get(v_x_3519_, 2);
v___x_3524_ = l_Lean_Lsp_instBEqRange_beq(v_key_3521_, v_a_3518_);
if (v___x_3524_ == 0)
{
v_x_3519_ = v_tail_3523_;
goto _start;
}
else
{
lean_object* v___x_3526_; 
lean_inc(v_value_3522_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_value_3522_);
return v___x_3526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_3527_, lean_object* v_x_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3527_, v_x_3528_);
lean_dec(v_x_3528_);
lean_dec_ref(v_a_3527_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(lean_object* v_m_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v_buckets_3532_; lean_object* v___x_3533_; uint64_t v___x_3534_; uint64_t v___x_3535_; uint64_t v___x_3536_; uint64_t v_fold_3537_; uint64_t v___x_3538_; uint64_t v___x_3539_; uint64_t v___x_3540_; size_t v___x_3541_; size_t v___x_3542_; size_t v___x_3543_; size_t v___x_3544_; size_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v_buckets_3532_ = lean_ctor_get(v_m_3530_, 1);
v___x_3533_ = lean_array_get_size(v_buckets_3532_);
v___x_3534_ = l_Lean_Lsp_instHashableRange_hash(v_a_3531_);
v___x_3535_ = 32ULL;
v___x_3536_ = lean_uint64_shift_right(v___x_3534_, v___x_3535_);
v_fold_3537_ = lean_uint64_xor(v___x_3534_, v___x_3536_);
v___x_3538_ = 16ULL;
v___x_3539_ = lean_uint64_shift_right(v_fold_3537_, v___x_3538_);
v___x_3540_ = lean_uint64_xor(v_fold_3537_, v___x_3539_);
v___x_3541_ = lean_uint64_to_usize(v___x_3540_);
v___x_3542_ = lean_usize_of_nat(v___x_3533_);
v___x_3543_ = ((size_t)1ULL);
v___x_3544_ = lean_usize_sub(v___x_3542_, v___x_3543_);
v___x_3545_ = lean_usize_land(v___x_3541_, v___x_3544_);
v___x_3546_ = lean_array_uget_borrowed(v_buckets_3532_, v___x_3545_);
v___x_3547_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3531_, v___x_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg___boxed(lean_object* v_m_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3548_, v_a_3549_);
lean_dec_ref(v_a_3549_);
lean_dec_ref(v_m_3548_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(lean_object* v_posMap_3551_, lean_object* v_as_3552_, size_t v_sz_3553_, size_t v_i_3554_, lean_object* v_b_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_a_3558_; lean_object* v_snd_3559_; uint8_t v___x_3563_; 
v___x_3563_ = lean_usize_dec_lt(v_i_3554_, v_sz_3553_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v_b_3555_);
lean_ctor_set(v___x_3564_, 1, v___y_3556_);
return v___x_3564_;
}
else
{
lean_object* v_a_3565_; lean_object* v_ident_3566_; lean_object* v_range_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_a_3565_ = lean_array_uget_borrowed(v_as_3552_, v_i_3554_);
v_ident_3566_ = lean_ctor_get(v_a_3565_, 0);
v_range_3567_ = lean_ctor_get(v_a_3565_, 2);
v___x_3568_ = lean_box(0);
v___x_3569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_posMap_3551_, v_range_3567_);
if (lean_obj_tag(v___x_3569_) == 1)
{
lean_object* v_val_3570_; lean_object* v___x_3571_; lean_object* v_snd_3572_; 
v_val_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_val_3570_);
lean_dec_ref(v___x_3569_);
lean_inc_ref(v_ident_3566_);
v___x_3571_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v_val_3570_, v_ident_3566_, v___y_3556_);
v_snd_3572_ = lean_ctor_get(v___x_3571_, 1);
lean_inc(v_snd_3572_);
lean_dec_ref(v___x_3571_);
v_a_3558_ = v___x_3568_;
v_snd_3559_ = v_snd_3572_;
goto v___jp_3557_;
}
else
{
lean_dec(v___x_3569_);
v_a_3558_ = v___x_3568_;
v_snd_3559_ = v___y_3556_;
goto v___jp_3557_;
}
}
v___jp_3557_:
{
size_t v___x_3560_; size_t v___x_3561_; 
v___x_3560_ = ((size_t)1ULL);
v___x_3561_ = lean_usize_add(v_i_3554_, v___x_3560_);
v_i_3554_ = v___x_3561_;
v_b_3555_ = v_a_3558_;
v___y_3556_ = v_snd_3559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2___boxed(lean_object* v_posMap_3573_, lean_object* v_as_3574_, lean_object* v_sz_3575_, lean_object* v_i_3576_, lean_object* v_b_3577_, lean_object* v___y_3578_){
_start:
{
size_t v_sz_boxed_3579_; size_t v_i_boxed_3580_; lean_object* v_res_3581_; 
v_sz_boxed_3579_ = lean_unbox_usize(v_sz_3575_);
lean_dec(v_sz_3575_);
v_i_boxed_3580_ = lean_unbox_usize(v_i_3576_);
lean_dec(v_i_3576_);
v_res_3581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3573_, v_as_3574_, v_sz_boxed_3579_, v_i_boxed_3580_, v_b_3577_, v___y_3578_);
lean_dec_ref(v_as_3574_);
lean_dec_ref(v_posMap_3573_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(lean_object* v_trees_3582_, lean_object* v_refs_3583_, lean_object* v_posMap_3584_){
_start:
{
lean_object* v___x_3585_; size_t v_sz_3586_; size_t v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v_snd_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v___x_3585_ = lean_box(0);
v_sz_3586_ = lean_array_size(v_refs_3583_);
v___x_3587_ = ((size_t)0ULL);
v___x_3588_ = lean_unsigned_to_nat(0u);
v___x_3589_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v___x_3590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3584_, v_refs_3583_, v_sz_3586_, v___x_3587_, v___x_3585_, v___x_3589_);
v_snd_3591_ = lean_ctor_get(v___x_3590_, 1);
lean_inc(v_snd_3591_);
lean_dec_ref(v___x_3590_);
v___x_3592_ = lean_array_get_size(v_trees_3582_);
v___x_3593_ = lean_nat_dec_lt(v___x_3588_, v___x_3592_);
if (v___x_3593_ == 0)
{
return v_snd_3591_;
}
else
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_nat_dec_le(v___x_3592_, v___x_3592_);
if (v___x_3594_ == 0)
{
if (v___x_3593_ == 0)
{
return v_snd_3591_;
}
else
{
size_t v___x_3595_; lean_object* v___x_3596_; lean_object* v_snd_3597_; 
v___x_3595_ = lean_usize_of_nat(v___x_3592_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3582_, v___x_3587_, v___x_3595_, v___x_3585_, v_snd_3591_);
v_snd_3597_ = lean_ctor_get(v___x_3596_, 1);
lean_inc(v_snd_3597_);
lean_dec_ref(v___x_3596_);
return v_snd_3597_;
}
}
else
{
size_t v___x_3598_; lean_object* v___x_3599_; lean_object* v_snd_3600_; 
v___x_3598_ = lean_usize_of_nat(v___x_3592_);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3582_, v___x_3587_, v___x_3598_, v___x_3585_, v_snd_3591_);
v_snd_3600_ = lean_ctor_get(v___x_3599_, 1);
lean_inc(v_snd_3600_);
lean_dec_ref(v___x_3599_);
return v_snd_3600_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap___boxed(lean_object* v_trees_3601_, lean_object* v_refs_3602_, lean_object* v_posMap_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3601_, v_refs_3602_, v_posMap_3603_);
lean_dec_ref(v_posMap_3603_);
lean_dec_ref(v_refs_3602_);
lean_dec_ref(v_trees_3601_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(lean_object* v_00_u03b2_3605_, lean_object* v_m_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3606_, v_a_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___boxed(lean_object* v_00_u03b2_3609_, lean_object* v_m_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(v_00_u03b2_3609_, v_m_3610_, v_a_3611_);
lean_dec_ref(v_a_3611_);
lean_dec_ref(v_m_3610_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3613_, lean_object* v_msg_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v_msg_3614_, v___y_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object* v_00_u03b1_3617_, lean_object* v_preNode_3618_, lean_object* v_postNode_3619_, lean_object* v_x_3620_, lean_object* v_x_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3618_, v_postNode_3619_, v_x_3620_, v_x_3621_, v___y_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object* v_00_u03b2_3624_, lean_object* v_a_3625_, lean_object* v_x_3626_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3625_, v_x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3628_, lean_object* v_a_3629_, lean_object* v_x_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(v_00_u03b2_3628_, v_a_3629_, v_x_3630_);
lean_dec(v_x_3630_);
lean_dec_ref(v_a_3629_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3632_, lean_object* v_preNode_3633_, lean_object* v_postNode_3634_, lean_object* v___x_3635_, lean_object* v_x_3636_, lean_object* v_x_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3633_, v_postNode_3634_, v___x_3635_, v_x_3636_, v_x_3637_, v___y_3638_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(lean_object* v_a_3640_, lean_object* v_b_3641_, lean_object* v_x_3642_){
_start:
{
if (lean_obj_tag(v_x_3642_) == 0)
{
lean_dec(v_b_3641_);
lean_dec_ref(v_a_3640_);
return v_x_3642_;
}
else
{
lean_object* v_key_3643_; lean_object* v_value_3644_; lean_object* v_tail_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3657_; 
v_key_3643_ = lean_ctor_get(v_x_3642_, 0);
v_value_3644_ = lean_ctor_get(v_x_3642_, 1);
v_tail_3645_ = lean_ctor_get(v_x_3642_, 2);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_x_3642_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3647_ = v_x_3642_;
v_isShared_3648_ = v_isSharedCheck_3657_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_tail_3645_);
lean_inc(v_value_3644_);
lean_inc(v_key_3643_);
lean_dec(v_x_3642_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3657_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
uint8_t v___x_3649_; 
v___x_3649_ = l_Lean_Lsp_instBEqRange_beq(v_key_3643_, v_a_3640_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3650_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3640_, v_b_3641_, v_tail_3645_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 2, v___x_3650_);
v___x_3652_ = v___x_3647_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_key_3643_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_value_3644_);
lean_ctor_set(v_reuseFailAlloc_3653_, 2, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
else
{
lean_object* v___x_3655_; 
lean_dec(v_value_3644_);
lean_dec(v_key_3643_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 1, v_b_3641_);
lean_ctor_set(v___x_3647_, 0, v_a_3640_);
v___x_3655_ = v___x_3647_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3640_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_b_3641_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v_tail_3645_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_3658_, lean_object* v_x_3659_){
_start:
{
if (lean_obj_tag(v_x_3659_) == 0)
{
return v_x_3658_;
}
else
{
lean_object* v_key_3660_; lean_object* v_value_3661_; lean_object* v_tail_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3685_; 
v_key_3660_ = lean_ctor_get(v_x_3659_, 0);
v_value_3661_ = lean_ctor_get(v_x_3659_, 1);
v_tail_3662_ = lean_ctor_get(v_x_3659_, 2);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_x_3659_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3664_ = v_x_3659_;
v_isShared_3665_ = v_isSharedCheck_3685_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_tail_3662_);
lean_inc(v_value_3661_);
lean_inc(v_key_3660_);
lean_dec(v_x_3659_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3685_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; uint64_t v___x_3667_; uint64_t v___x_3668_; uint64_t v___x_3669_; uint64_t v_fold_3670_; uint64_t v___x_3671_; uint64_t v___x_3672_; uint64_t v___x_3673_; size_t v___x_3674_; size_t v___x_3675_; size_t v___x_3676_; size_t v___x_3677_; size_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3666_ = lean_array_get_size(v_x_3658_);
v___x_3667_ = l_Lean_Lsp_instHashableRange_hash(v_key_3660_);
v___x_3668_ = 32ULL;
v___x_3669_ = lean_uint64_shift_right(v___x_3667_, v___x_3668_);
v_fold_3670_ = lean_uint64_xor(v___x_3667_, v___x_3669_);
v___x_3671_ = 16ULL;
v___x_3672_ = lean_uint64_shift_right(v_fold_3670_, v___x_3671_);
v___x_3673_ = lean_uint64_xor(v_fold_3670_, v___x_3672_);
v___x_3674_ = lean_uint64_to_usize(v___x_3673_);
v___x_3675_ = lean_usize_of_nat(v___x_3666_);
v___x_3676_ = ((size_t)1ULL);
v___x_3677_ = lean_usize_sub(v___x_3675_, v___x_3676_);
v___x_3678_ = lean_usize_land(v___x_3674_, v___x_3677_);
v___x_3679_ = lean_array_uget_borrowed(v_x_3658_, v___x_3678_);
lean_inc(v___x_3679_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 2, v___x_3679_);
v___x_3681_ = v___x_3664_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_key_3660_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_value_3661_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; 
v___x_3682_ = lean_array_uset(v_x_3658_, v___x_3678_, v___x_3681_);
v_x_3658_ = v___x_3682_;
v_x_3659_ = v_tail_3662_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3686_, lean_object* v_source_3687_, lean_object* v_target_3688_){
_start:
{
lean_object* v___x_3689_; uint8_t v___x_3690_; 
v___x_3689_ = lean_array_get_size(v_source_3687_);
v___x_3690_ = lean_nat_dec_lt(v_i_3686_, v___x_3689_);
if (v___x_3690_ == 0)
{
lean_dec_ref(v_source_3687_);
lean_dec(v_i_3686_);
return v_target_3688_;
}
else
{
lean_object* v_es_3691_; lean_object* v___x_3692_; lean_object* v_source_3693_; lean_object* v_target_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_es_3691_ = lean_array_fget(v_source_3687_, v_i_3686_);
v___x_3692_ = lean_box(0);
v_source_3693_ = lean_array_fset(v_source_3687_, v_i_3686_, v___x_3692_);
v_target_3694_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3688_, v_es_3691_);
v___x_3695_ = lean_unsigned_to_nat(1u);
v___x_3696_ = lean_nat_add(v_i_3686_, v___x_3695_);
lean_dec(v_i_3686_);
v_i_3686_ = v___x_3696_;
v_source_3687_ = v_source_3693_;
v_target_3688_ = v_target_3694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(lean_object* v_data_3698_){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_nbuckets_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3699_ = lean_array_get_size(v_data_3698_);
v___x_3700_ = lean_unsigned_to_nat(2u);
v_nbuckets_3701_ = lean_nat_mul(v___x_3699_, v___x_3700_);
v___x_3702_ = lean_unsigned_to_nat(0u);
v___x_3703_ = lean_box(0);
v___x_3704_ = lean_mk_array(v_nbuckets_3701_, v___x_3703_);
v___x_3705_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v___x_3702_, v_data_3698_, v___x_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object* v_a_3706_, lean_object* v_x_3707_){
_start:
{
if (lean_obj_tag(v_x_3707_) == 0)
{
uint8_t v___x_3708_; 
v___x_3708_ = 0;
return v___x_3708_;
}
else
{
lean_object* v_key_3709_; lean_object* v_tail_3710_; uint8_t v___x_3711_; 
v_key_3709_ = lean_ctor_get(v_x_3707_, 0);
v_tail_3710_ = lean_ctor_get(v_x_3707_, 2);
v___x_3711_ = l_Lean_Lsp_instBEqRange_beq(v_key_3709_, v_a_3706_);
if (v___x_3711_ == 0)
{
v_x_3707_ = v_tail_3710_;
goto _start;
}
else
{
return v___x_3711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object* v_a_3713_, lean_object* v_x_3714_){
_start:
{
uint8_t v_res_3715_; lean_object* v_r_3716_; 
v_res_3715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3713_, v_x_3714_);
lean_dec(v_x_3714_);
lean_dec_ref(v_a_3713_);
v_r_3716_ = lean_box(v_res_3715_);
return v_r_3716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object* v_m_3717_, lean_object* v_a_3718_, lean_object* v_b_3719_){
_start:
{
lean_object* v_size_3720_; lean_object* v_buckets_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3764_; 
v_size_3720_ = lean_ctor_get(v_m_3717_, 0);
v_buckets_3721_ = lean_ctor_get(v_m_3717_, 1);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_m_3717_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3723_ = v_m_3717_;
v_isShared_3724_ = v_isSharedCheck_3764_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_buckets_3721_);
lean_inc(v_size_3720_);
lean_dec(v_m_3717_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3764_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; uint64_t v___x_3726_; uint64_t v___x_3727_; uint64_t v___x_3728_; uint64_t v_fold_3729_; uint64_t v___x_3730_; uint64_t v___x_3731_; uint64_t v___x_3732_; size_t v___x_3733_; size_t v___x_3734_; size_t v___x_3735_; size_t v___x_3736_; size_t v___x_3737_; lean_object* v_bkt_3738_; uint8_t v___x_3739_; 
v___x_3725_ = lean_array_get_size(v_buckets_3721_);
v___x_3726_ = l_Lean_Lsp_instHashableRange_hash(v_a_3718_);
v___x_3727_ = 32ULL;
v___x_3728_ = lean_uint64_shift_right(v___x_3726_, v___x_3727_);
v_fold_3729_ = lean_uint64_xor(v___x_3726_, v___x_3728_);
v___x_3730_ = 16ULL;
v___x_3731_ = lean_uint64_shift_right(v_fold_3729_, v___x_3730_);
v___x_3732_ = lean_uint64_xor(v_fold_3729_, v___x_3731_);
v___x_3733_ = lean_uint64_to_usize(v___x_3732_);
v___x_3734_ = lean_usize_of_nat(v___x_3725_);
v___x_3735_ = ((size_t)1ULL);
v___x_3736_ = lean_usize_sub(v___x_3734_, v___x_3735_);
v___x_3737_ = lean_usize_land(v___x_3733_, v___x_3736_);
v_bkt_3738_ = lean_array_uget_borrowed(v_buckets_3721_, v___x_3737_);
v___x_3739_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3718_, v_bkt_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; lean_object* v_size_x27_3741_; lean_object* v___x_3742_; lean_object* v_buckets_x27_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; 
v___x_3740_ = lean_unsigned_to_nat(1u);
v_size_x27_3741_ = lean_nat_add(v_size_3720_, v___x_3740_);
lean_dec(v_size_3720_);
lean_inc(v_bkt_3738_);
v___x_3742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3742_, 0, v_a_3718_);
lean_ctor_set(v___x_3742_, 1, v_b_3719_);
lean_ctor_set(v___x_3742_, 2, v_bkt_3738_);
v_buckets_x27_3743_ = lean_array_uset(v_buckets_3721_, v___x_3737_, v___x_3742_);
v___x_3744_ = lean_unsigned_to_nat(4u);
v___x_3745_ = lean_nat_mul(v_size_x27_3741_, v___x_3744_);
v___x_3746_ = lean_unsigned_to_nat(3u);
v___x_3747_ = lean_nat_div(v___x_3745_, v___x_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_array_get_size(v_buckets_x27_3743_);
v___x_3749_ = lean_nat_dec_le(v___x_3747_, v___x_3748_);
lean_dec(v___x_3747_);
if (v___x_3749_ == 0)
{
lean_object* v_val_3750_; lean_object* v___x_3752_; 
v_val_3750_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_buckets_x27_3743_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 1, v_val_3750_);
lean_ctor_set(v___x_3723_, 0, v_size_x27_3741_);
v___x_3752_ = v___x_3723_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_size_x27_3741_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_val_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
else
{
lean_object* v___x_3755_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 1, v_buckets_x27_3743_);
lean_ctor_set(v___x_3723_, 0, v_size_x27_3741_);
v___x_3755_ = v___x_3723_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_size_x27_3741_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_buckets_x27_3743_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
else
{
lean_object* v___x_3757_; lean_object* v_buckets_x27_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3762_; 
lean_inc(v_bkt_3738_);
v___x_3757_ = lean_box(0);
v_buckets_x27_3758_ = lean_array_uset(v_buckets_3721_, v___x_3737_, v___x_3757_);
v___x_3759_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3718_, v_b_3719_, v_bkt_3738_);
v___x_3760_ = lean_array_uset(v_buckets_x27_3758_, v___x_3737_, v___x_3759_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 1, v___x_3760_);
v___x_3762_ = v___x_3723_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_size_3720_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object* v_as_3765_, size_t v_sz_3766_, size_t v_i_3767_, lean_object* v_b_3768_){
_start:
{
lean_object* v_a_3770_; uint8_t v___x_3774_; 
v___x_3774_ = lean_usize_dec_lt(v_i_3767_, v_sz_3766_);
if (v___x_3774_ == 0)
{
return v_b_3768_;
}
else
{
lean_object* v_a_3775_; uint8_t v_isBinder_3776_; 
v_a_3775_ = lean_array_uget_borrowed(v_as_3765_, v_i_3767_);
v_isBinder_3776_ = lean_ctor_get_uint8(v_a_3775_, sizeof(void*)*6);
if (v_isBinder_3776_ == 1)
{
lean_object* v_ident_3777_; lean_object* v_range_3778_; lean_object* v___x_3779_; 
v_ident_3777_ = lean_ctor_get(v_a_3775_, 0);
v_range_3778_ = lean_ctor_get(v_a_3775_, 2);
lean_inc_ref(v_ident_3777_);
lean_inc_ref(v_range_3778_);
v___x_3779_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_b_3768_, v_range_3778_, v_ident_3777_);
v_a_3770_ = v___x_3779_;
goto v___jp_3769_;
}
else
{
v_a_3770_ = v_b_3768_;
goto v___jp_3769_;
}
}
v___jp_3769_:
{
size_t v___x_3771_; size_t v___x_3772_; 
v___x_3771_ = ((size_t)1ULL);
v___x_3772_ = lean_usize_add(v_i_3767_, v___x_3771_);
v_i_3767_ = v___x_3772_;
v_b_3768_ = v_a_3770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object* v_as_3780_, lean_object* v_sz_3781_, lean_object* v_i_3782_, lean_object* v_b_3783_){
_start:
{
size_t v_sz_boxed_3784_; size_t v_i_boxed_3785_; lean_object* v_res_3786_; 
v_sz_boxed_3784_ = lean_unbox_usize(v_sz_3781_);
lean_dec(v_sz_3781_);
v_i_boxed_3785_ = lean_unbox_usize(v_i_3782_);
lean_dec(v_i_3782_);
v_res_3786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_as_3780_, v_sz_boxed_3784_, v_i_boxed_3785_, v_b_3783_);
lean_dec_ref(v_as_3780_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object* v___x_3787_, lean_object* v_as_3788_, size_t v_sz_3789_, size_t v_i_3790_, lean_object* v_b_3791_){
_start:
{
lean_object* v_a_3793_; uint8_t v___x_3797_; 
v___x_3797_ = lean_usize_dec_lt(v_i_3790_, v_sz_3789_);
if (v___x_3797_ == 0)
{
return v_b_3791_;
}
else
{
lean_object* v_a_3798_; lean_object* v_ident_3801_; lean_object* v_range_3802_; lean_object* v_stx_3803_; lean_object* v_ci_3804_; lean_object* v_info_3805_; uint8_t v_isBinder_3806_; uint8_t v___x_3807_; 
v_a_3798_ = lean_array_uget(v_as_3788_, v_i_3790_);
v_ident_3801_ = lean_ctor_get(v_a_3798_, 0);
v_range_3802_ = lean_ctor_get(v_a_3798_, 2);
v_stx_3803_ = lean_ctor_get(v_a_3798_, 3);
v_ci_3804_ = lean_ctor_get(v_a_3798_, 4);
v_info_3805_ = lean_ctor_get(v_a_3798_, 5);
v_isBinder_3806_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*6);
v___x_3807_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v___x_3787_, v_ident_3801_);
if (v___x_3807_ == 0)
{
if (v___x_3807_ == 0)
{
goto v___jp_3799_;
}
else
{
if (v___x_3807_ == 0)
{
lean_dec(v_a_3798_);
v_a_3793_ = v_b_3791_;
goto v___jp_3792_;
}
else
{
goto v___jp_3799_;
}
}
}
else
{
lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3819_; 
lean_inc_ref(v_info_3805_);
lean_inc_ref(v_ci_3804_);
lean_inc(v_stx_3803_);
lean_inc_ref(v_range_3802_);
lean_inc_ref(v_ident_3801_);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_a_3798_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; lean_object* v_unused_3821_; lean_object* v_unused_3822_; lean_object* v_unused_3823_; lean_object* v_unused_3824_; lean_object* v_unused_3825_; 
v_unused_3820_ = lean_ctor_get(v_a_3798_, 5);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_a_3798_, 4);
lean_dec(v_unused_3821_);
v_unused_3822_ = lean_ctor_get(v_a_3798_, 3);
lean_dec(v_unused_3822_);
v_unused_3823_ = lean_ctor_get(v_a_3798_, 2);
lean_dec(v_unused_3823_);
v_unused_3824_ = lean_ctor_get(v_a_3798_, 1);
lean_dec(v_unused_3824_);
v_unused_3825_ = lean_ctor_get(v_a_3798_, 0);
lean_dec(v_unused_3825_);
v___x_3809_ = v_a_3798_;
v_isShared_3810_ = v_isSharedCheck_3819_;
goto v_resetjp_3808_;
}
else
{
lean_dec(v_a_3798_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3819_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3816_; 
lean_inc_ref(v_ident_3801_);
v___x_3811_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v___x_3787_, v_ident_3801_);
v___x_3812_ = lean_unsigned_to_nat(1u);
v___x_3813_ = lean_mk_empty_array_with_capacity(v___x_3812_);
v___x_3814_ = lean_array_push(v___x_3813_, v_ident_3801_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 1, v___x_3814_);
lean_ctor_set(v___x_3809_, 0, v___x_3811_);
v___x_3816_ = v___x_3809_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_range_3802_);
lean_ctor_set(v_reuseFailAlloc_3818_, 3, v_stx_3803_);
lean_ctor_set(v_reuseFailAlloc_3818_, 4, v_ci_3804_);
lean_ctor_set(v_reuseFailAlloc_3818_, 5, v_info_3805_);
lean_ctor_set_uint8(v_reuseFailAlloc_3818_, sizeof(void*)*6, v_isBinder_3806_);
v___x_3816_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3817_; 
v___x_3817_ = lean_array_push(v_b_3791_, v___x_3816_);
v_a_3793_ = v___x_3817_;
goto v___jp_3792_;
}
}
}
v___jp_3799_:
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_array_push(v_b_3791_, v_a_3798_);
v_a_3793_ = v___x_3800_;
goto v___jp_3792_;
}
}
v___jp_3792_:
{
size_t v___x_3794_; size_t v___x_3795_; 
v___x_3794_ = ((size_t)1ULL);
v___x_3795_ = lean_usize_add(v_i_3790_, v___x_3794_);
v_i_3790_ = v___x_3795_;
v_b_3791_ = v_a_3793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object* v___x_3826_, lean_object* v_as_3827_, lean_object* v_sz_3828_, lean_object* v_i_3829_, lean_object* v_b_3830_){
_start:
{
size_t v_sz_boxed_3831_; size_t v_i_boxed_3832_; lean_object* v_res_3833_; 
v_sz_boxed_3831_ = lean_unbox_usize(v_sz_3828_);
lean_dec(v_sz_3828_);
v_i_boxed_3832_ = lean_unbox_usize(v_i_3829_);
lean_dec(v_i_3829_);
v_res_3833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3826_, v_as_3827_, v_sz_boxed_3831_, v_i_boxed_3832_, v_b_3830_);
lean_dec_ref(v_as_3827_);
lean_dec_ref(v___x_3826_);
return v_res_3833_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__0(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = lean_box(0);
v___x_3835_ = lean_unsigned_to_nat(16u);
v___x_3836_ = lean_mk_array(v___x_3835_, v___x_3834_);
return v___x_3836_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__1(void){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v_posMap_3839_; 
v___x_3837_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__0, &l_Lean_Server_combineIdents___closed__0_once, _init_l_Lean_Server_combineIdents___closed__0);
v___x_3838_ = lean_unsigned_to_nat(0u);
v_posMap_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_posMap_3839_, 0, v___x_3838_);
lean_ctor_set(v_posMap_3839_, 1, v___x_3837_);
return v_posMap_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object* v_trees_3840_, lean_object* v_refs_3841_){
_start:
{
lean_object* v_posMap_3842_; size_t v_sz_3843_; size_t v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_posMap_3842_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__1, &l_Lean_Server_combineIdents___closed__1_once, _init_l_Lean_Server_combineIdents___closed__1);
v_sz_3843_ = lean_array_size(v_refs_3841_);
v___x_3844_ = ((size_t)0ULL);
v___x_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_refs_3841_, v_sz_3843_, v___x_3844_, v_posMap_3842_);
v___x_3846_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3840_, v_refs_3841_, v___x_3845_);
lean_dec_ref(v___x_3845_);
v___x_3847_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v___x_3846_);
lean_dec_ref(v___x_3846_);
v___x_3848_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_3849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3847_, v_refs_3841_, v_sz_3843_, v___x_3844_, v___x_3848_);
lean_dec_ref(v___x_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object* v_trees_3850_, lean_object* v_refs_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_Server_combineIdents(v_trees_3850_, v_refs_3851_);
lean_dec_ref(v_refs_3851_);
lean_dec_ref(v_trees_3850_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object* v_00_u03b2_3853_, lean_object* v_m_3854_, lean_object* v_a_3855_, lean_object* v_b_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_m_3854_, v_a_3855_, v_b_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object* v_00_u03b2_3858_, lean_object* v_a_3859_, lean_object* v_x_3860_){
_start:
{
uint8_t v___x_3861_; 
v___x_3861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3859_, v_x_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3862_, lean_object* v_a_3863_, lean_object* v_x_3864_){
_start:
{
uint8_t v_res_3865_; lean_object* v_r_3866_; 
v_res_3865_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(v_00_u03b2_3862_, v_a_3863_, v_x_3864_);
lean_dec(v_x_3864_);
lean_dec_ref(v_a_3863_);
v_r_3866_ = lean_box(v_res_3865_);
return v_r_3866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object* v_00_u03b2_3867_, lean_object* v_data_3868_){
_start:
{
lean_object* v___x_3869_; 
v___x_3869_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_data_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object* v_00_u03b2_3870_, lean_object* v_a_3871_, lean_object* v_b_3872_, lean_object* v_x_3873_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3871_, v_b_3872_, v_x_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3875_, lean_object* v_i_3876_, lean_object* v_source_3877_, lean_object* v_target_3878_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v_i_3876_, v_source_3877_, v_target_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3880_, lean_object* v_x_3881_, lean_object* v_x_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3881_, v_x_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3884_, lean_object* v_x1_3885_, lean_object* v_x2_3886_){
_start:
{
lean_object* v_range_3887_; lean_object* v_range_3888_; uint8_t v___x_3889_; 
v_range_3887_ = lean_ctor_get(v_x1_3885_, 2);
v_range_3888_ = lean_ctor_get(v_x2_3886_, 2);
v___x_3889_ = l_Lean_Lsp_instOrdRange_ord(v_range_3887_, v_range_3888_);
if (v___x_3889_ == 0)
{
return v___x_3884_;
}
else
{
uint8_t v___x_3890_; 
v___x_3890_ = 0;
return v___x_3890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3891_, lean_object* v_x1_3892_, lean_object* v_x2_3893_){
_start:
{
uint8_t v___x_1916__boxed_3894_; uint8_t v_res_3895_; lean_object* v_r_3896_; 
v___x_1916__boxed_3894_ = lean_unbox(v___x_3891_);
v_res_3895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_1916__boxed_3894_, v_x1_3892_, v_x2_3893_);
lean_dec_ref(v_x2_3893_);
lean_dec_ref(v_x1_3892_);
v_r_3896_ = lean_box(v_res_3895_);
return v_r_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_as_3897_, lean_object* v_lo_3898_, lean_object* v_hi_3899_){
_start:
{
uint8_t v___x_3900_; 
v___x_3900_ = lean_nat_dec_lt(v_lo_3898_, v_hi_3899_);
if (v___x_3900_ == 0)
{
lean_dec(v_lo_3898_);
return v_as_3897_;
}
else
{
lean_object* v___x_3901_; lean_object* v___f_3902_; lean_object* v___x_3903_; lean_object* v_fst_3904_; lean_object* v_snd_3905_; uint8_t v___x_3906_; 
v___x_3901_ = lean_box(v___x_3900_);
v___f_3902_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3902_, 0, v___x_3901_);
lean_inc(v_lo_3898_);
v___x_3903_ = l_Array_qpartition___redArg(v_as_3897_, v___f_3902_, v_lo_3898_, v_hi_3899_);
v_fst_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_fst_3904_);
v_snd_3905_ = lean_ctor_get(v___x_3903_, 1);
lean_inc(v_snd_3905_);
lean_dec_ref(v___x_3903_);
v___x_3906_ = lean_nat_dec_le(v_hi_3899_, v_fst_3904_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_snd_3905_, v_lo_3898_, v_fst_3904_);
v___x_3908_ = lean_unsigned_to_nat(1u);
v___x_3909_ = lean_nat_add(v_fst_3904_, v___x_3908_);
lean_dec(v_fst_3904_);
v_as_3897_ = v___x_3907_;
v_lo_3898_ = v___x_3909_;
goto _start;
}
else
{
lean_dec(v_fst_3904_);
lean_dec(v_lo_3898_);
return v_snd_3905_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_as_3911_, lean_object* v_lo_3912_, lean_object* v_hi_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_as_3911_, v_lo_3912_, v_hi_3913_);
lean_dec(v_hi_3913_);
return v_res_3914_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1_spec__2(lean_object* v_x_3915_, lean_object* v_x_3916_){
_start:
{
if (lean_obj_tag(v_x_3915_) == 0)
{
if (lean_obj_tag(v_x_3916_) == 0)
{
uint8_t v___x_3917_; 
v___x_3917_ = 1;
return v___x_3917_;
}
else
{
uint8_t v___x_3918_; 
v___x_3918_ = 0;
return v___x_3918_;
}
}
else
{
if (lean_obj_tag(v_x_3916_) == 0)
{
uint8_t v___x_3919_; 
v___x_3919_ = 0;
return v___x_3919_;
}
else
{
lean_object* v_val_3920_; uint8_t v___x_3921_; 
v_val_3920_ = lean_ctor_get(v_x_3915_, 0);
v___x_3921_ = lean_unbox(v_val_3920_);
if (v___x_3921_ == 0)
{
lean_object* v_val_3922_; uint8_t v___x_3923_; 
v_val_3922_ = lean_ctor_get(v_x_3916_, 0);
v___x_3923_ = lean_unbox(v_val_3922_);
if (v___x_3923_ == 0)
{
uint8_t v___x_3924_; 
v___x_3924_ = 1;
return v___x_3924_;
}
else
{
uint8_t v___x_3925_; 
v___x_3925_ = lean_unbox(v_val_3920_);
return v___x_3925_;
}
}
else
{
lean_object* v_val_3926_; uint8_t v___x_3927_; 
v_val_3926_ = lean_ctor_get(v_x_3916_, 0);
v___x_3927_ = lean_unbox(v_val_3926_);
return v___x_3927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1_spec__2___boxed(lean_object* v_x_3928_, lean_object* v_x_3929_){
_start:
{
uint8_t v_res_3930_; lean_object* v_r_3931_; 
v_res_3930_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1_spec__2(v_x_3928_, v_x_3929_);
lean_dec(v_x_3929_);
lean_dec(v_x_3928_);
v_r_3931_ = lean_box(v_res_3930_);
return v_r_3931_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___redArg(lean_object* v_a_3932_, lean_object* v_x_3933_){
_start:
{
if (lean_obj_tag(v_x_3933_) == 0)
{
uint8_t v___x_3934_; 
v___x_3934_ = 0;
return v___x_3934_;
}
else
{
lean_object* v_key_3935_; lean_object* v_tail_3936_; uint8_t v___y_3938_; lean_object* v_fst_3940_; lean_object* v_snd_3941_; lean_object* v_fst_3942_; lean_object* v_snd_3943_; uint8_t v___x_3944_; 
v_key_3935_ = lean_ctor_get(v_x_3933_, 0);
v_tail_3936_ = lean_ctor_get(v_x_3933_, 2);
v_fst_3940_ = lean_ctor_get(v_key_3935_, 0);
v_snd_3941_ = lean_ctor_get(v_key_3935_, 1);
v_fst_3942_ = lean_ctor_get(v_a_3932_, 0);
v_snd_3943_ = lean_ctor_get(v_a_3932_, 1);
v___x_3944_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_3940_, v_fst_3942_);
if (v___x_3944_ == 0)
{
v___y_3938_ = v___x_3944_;
goto v___jp_3937_;
}
else
{
lean_object* v_fst_3945_; lean_object* v_snd_3946_; lean_object* v_fst_3947_; lean_object* v_snd_3948_; uint8_t v___x_3949_; 
v_fst_3945_ = lean_ctor_get(v_snd_3941_, 0);
v_snd_3946_ = lean_ctor_get(v_snd_3941_, 1);
v_fst_3947_ = lean_ctor_get(v_snd_3943_, 0);
v_snd_3948_ = lean_ctor_get(v_snd_3943_, 1);
v___x_3949_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1_spec__2(v_fst_3945_, v_fst_3947_);
if (v___x_3949_ == 0)
{
v___y_3938_ = v___x_3949_;
goto v___jp_3937_;
}
else
{
uint8_t v___x_3950_; 
v___x_3950_ = l_Lean_Lsp_instBEqRange_beq(v_snd_3946_, v_snd_3948_);
v___y_3938_ = v___x_3950_;
goto v___jp_3937_;
}
}
v___jp_3937_:
{
if (v___y_3938_ == 0)
{
v_x_3933_ = v_tail_3936_;
goto _start;
}
else
{
return v___y_3938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___redArg___boxed(lean_object* v_a_3951_, lean_object* v_x_3952_){
_start:
{
uint8_t v_res_3953_; lean_object* v_r_3954_; 
v_res_3953_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___redArg(v_a_3951_, v_x_3952_);
lean_dec(v_x_3952_);
lean_dec_ref(v_a_3951_);
v_r_3954_ = lean_box(v_res_3953_);
return v_r_3954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___lam__0(lean_object* v_a_3955_, lean_object* v_x_3956_){
_start:
{
if (lean_obj_tag(v_x_3956_) == 0)
{
lean_object* v___x_3957_; 
v___x_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3957_, 0, v_a_3955_);
return v___x_3957_;
}
else
{
lean_object* v_val_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3986_; 
v_val_3958_ = lean_ctor_get(v_x_3956_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_x_3956_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3960_ = v_x_3956_;
v_isShared_3961_ = v_isSharedCheck_3986_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_val_3958_);
lean_dec(v_x_3956_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3986_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v_ident_3962_; lean_object* v_aliases_3963_; lean_object* v_range_3964_; lean_object* v_stx_3965_; lean_object* v_ci_3966_; lean_object* v_info_3967_; uint8_t v_isBinder_3968_; lean_object* v_aliases_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3980_; 
v_ident_3962_ = lean_ctor_get(v_val_3958_, 0);
lean_inc_ref(v_ident_3962_);
v_aliases_3963_ = lean_ctor_get(v_val_3958_, 1);
lean_inc_ref(v_aliases_3963_);
v_range_3964_ = lean_ctor_get(v_val_3958_, 2);
lean_inc_ref(v_range_3964_);
v_stx_3965_ = lean_ctor_get(v_val_3958_, 3);
lean_inc(v_stx_3965_);
v_ci_3966_ = lean_ctor_get(v_val_3958_, 4);
lean_inc_ref(v_ci_3966_);
v_info_3967_ = lean_ctor_get(v_val_3958_, 5);
lean_inc_ref(v_info_3967_);
v_isBinder_3968_ = lean_ctor_get_uint8(v_val_3958_, sizeof(void*)*6);
lean_dec(v_val_3958_);
v_aliases_3969_ = lean_ctor_get(v_a_3955_, 1);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_a_3955_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; lean_object* v_unused_3984_; lean_object* v_unused_3985_; 
v_unused_3981_ = lean_ctor_get(v_a_3955_, 5);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_a_3955_, 4);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_a_3955_, 3);
lean_dec(v_unused_3983_);
v_unused_3984_ = lean_ctor_get(v_a_3955_, 2);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_a_3955_, 0);
lean_dec(v_unused_3985_);
v___x_3971_ = v_a_3955_;
v_isShared_3972_ = v_isSharedCheck_3980_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_aliases_3969_);
lean_dec(v_a_3955_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3980_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3973_ = l_Array_append___redArg(v_aliases_3963_, v_aliases_3969_);
lean_dec_ref(v_aliases_3969_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 5, v_info_3967_);
lean_ctor_set(v___x_3971_, 4, v_ci_3966_);
lean_ctor_set(v___x_3971_, 3, v_stx_3965_);
lean_ctor_set(v___x_3971_, 2, v_range_3964_);
lean_ctor_set(v___x_3971_, 1, v___x_3973_);
lean_ctor_set(v___x_3971_, 0, v_ident_3962_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_ident_3962_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v___x_3973_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_range_3964_);
lean_ctor_set(v_reuseFailAlloc_3979_, 3, v_stx_3965_);
lean_ctor_set(v_reuseFailAlloc_3979_, 4, v_ci_3966_);
lean_ctor_set(v_reuseFailAlloc_3979_, 5, v_info_3967_);
v___x_3975_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3977_; 
lean_ctor_set_uint8(v___x_3975_, sizeof(void*)*6, v_isBinder_3968_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3975_);
v___x_3977_ = v___x_3960_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_x_3989_){
_start:
{
if (lean_obj_tag(v_x_3989_) == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v_val_3992_; lean_object* v___x_3993_; 
v___x_3990_ = lean_box(0);
v___x_3991_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___lam__0(v_a_3987_, v___x_3990_);
v_val_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_val_3992_);
lean_dec(v___x_3991_);
v___x_3993_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3993_, 0, v_a_3988_);
lean_ctor_set(v___x_3993_, 1, v_val_3992_);
lean_ctor_set(v___x_3993_, 2, v_x_3989_);
return v___x_3993_;
}
else
{
lean_object* v_key_3994_; lean_object* v_value_3995_; lean_object* v_tail_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4023_; 
v_key_3994_ = lean_ctor_get(v_x_3989_, 0);
v_value_3995_ = lean_ctor_get(v_x_3989_, 1);
v_tail_3996_ = lean_ctor_get(v_x_3989_, 2);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_x_3989_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_3998_ = v_x_3989_;
v_isShared_3999_ = v_isSharedCheck_4023_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_tail_3996_);
lean_inc(v_value_3995_);
lean_inc(v_key_3994_);
lean_dec(v_x_3989_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4023_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
uint8_t v___y_4001_; lean_object* v_fst_4012_; lean_object* v_snd_4013_; lean_object* v_fst_4014_; lean_object* v_snd_4015_; uint8_t v___x_4016_; 
v_fst_4012_ = lean_ctor_get(v_key_3994_, 0);
v_snd_4013_ = lean_ctor_get(v_key_3994_, 1);
v_fst_4014_ = lean_ctor_get(v_a_3988_, 0);
v_snd_4015_ = lean_ctor_get(v_a_3988_, 1);
v___x_4016_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4012_, v_fst_4014_);
if (v___x_4016_ == 0)
{
v___y_4001_ = v___x_4016_;
goto v___jp_4000_;
}
else
{
lean_object* v_fst_4017_; lean_object* v_snd_4018_; lean_object* v_fst_4019_; lean_object* v_snd_4020_; uint8_t v___x_4021_; 
v_fst_4017_ = lean_ctor_get(v_snd_4013_, 0);
v_snd_4018_ = lean_ctor_get(v_snd_4013_, 1);
v_fst_4019_ = lean_ctor_get(v_snd_4015_, 0);
v_snd_4020_ = lean_ctor_get(v_snd_4015_, 1);
v___x_4021_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1_spec__2(v_fst_4017_, v_fst_4019_);
if (v___x_4021_ == 0)
{
v___y_4001_ = v___x_4021_;
goto v___jp_4000_;
}
else
{
uint8_t v___x_4022_; 
v___x_4022_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4018_, v_snd_4020_);
v___y_4001_ = v___x_4022_;
goto v___jp_4000_;
}
}
v___jp_4000_:
{
if (v___y_4001_ == 0)
{
lean_object* v_tail_4002_; lean_object* v___x_4004_; 
v_tail_4002_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(v_a_3987_, v_a_3988_, v_tail_3996_);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 2, v_tail_4002_);
v___x_4004_ = v___x_3998_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_key_3994_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_value_3995_);
lean_ctor_set(v_reuseFailAlloc_4005_, 2, v_tail_4002_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v_val_4008_; lean_object* v___x_4010_; 
lean_dec(v_key_3994_);
v___x_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4006_, 0, v_value_3995_);
v___x_4007_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___lam__0(v_a_3987_, v___x_4006_);
v_val_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_val_4008_);
lean_dec(v___x_4007_);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 1, v_val_4008_);
lean_ctor_set(v___x_3998_, 0, v_a_3988_);
v___x_4010_ = v___x_3998_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_3988_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_val_4008_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_tail_3996_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_4024_, lean_object* v_x_4025_){
_start:
{
if (lean_obj_tag(v_x_4025_) == 0)
{
return v_x_4024_;
}
else
{
lean_object* v_key_4026_; lean_object* v_snd_4027_; lean_object* v_value_4028_; lean_object* v_tail_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4069_; 
v_key_4026_ = lean_ctor_get(v_x_4025_, 0);
lean_inc(v_key_4026_);
v_snd_4027_ = lean_ctor_get(v_key_4026_, 1);
v_value_4028_ = lean_ctor_get(v_x_4025_, 1);
v_tail_4029_ = lean_ctor_get(v_x_4025_, 2);
v_isSharedCheck_4069_ = !lean_is_exclusive(v_x_4025_);
if (v_isSharedCheck_4069_ == 0)
{
lean_object* v_unused_4070_; 
v_unused_4070_ = lean_ctor_get(v_x_4025_, 0);
lean_dec(v_unused_4070_);
v___x_4031_ = v_x_4025_;
v_isShared_4032_ = v_isSharedCheck_4069_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_tail_4029_);
lean_inc(v_value_4028_);
lean_dec(v_x_4025_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4069_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v_fst_4033_; lean_object* v_fst_4034_; lean_object* v_snd_4035_; lean_object* v___x_4036_; uint64_t v___x_4037_; uint64_t v___y_4039_; uint64_t v___y_4061_; 
v_fst_4033_ = lean_ctor_get(v_key_4026_, 0);
v_fst_4034_ = lean_ctor_get(v_snd_4027_, 0);
v_snd_4035_ = lean_ctor_get(v_snd_4027_, 1);
v___x_4036_ = lean_array_get_size(v_x_4024_);
v___x_4037_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4033_);
if (lean_obj_tag(v_fst_4034_) == 0)
{
uint64_t v___x_4064_; 
v___x_4064_ = 11ULL;
v___y_4039_ = v___x_4064_;
goto v___jp_4038_;
}
else
{
lean_object* v_val_4065_; uint8_t v___x_4066_; 
v_val_4065_ = lean_ctor_get(v_fst_4034_, 0);
v___x_4066_ = lean_unbox(v_val_4065_);
if (v___x_4066_ == 0)
{
uint64_t v___x_4067_; 
v___x_4067_ = 13ULL;
v___y_4061_ = v___x_4067_;
goto v___jp_4060_;
}
else
{
uint64_t v___x_4068_; 
v___x_4068_ = 11ULL;
v___y_4061_ = v___x_4068_;
goto v___jp_4060_;
}
}
v___jp_4038_:
{
uint64_t v___x_4040_; uint64_t v___x_4041_; uint64_t v___x_4042_; uint64_t v___x_4043_; uint64_t v___x_4044_; uint64_t v_fold_4045_; uint64_t v___x_4046_; uint64_t v___x_4047_; uint64_t v___x_4048_; size_t v___x_4049_; size_t v___x_4050_; size_t v___x_4051_; size_t v___x_4052_; size_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4056_; 
v___x_4040_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4035_);
v___x_4041_ = lean_uint64_mix_hash(v___y_4039_, v___x_4040_);
v___x_4042_ = lean_uint64_mix_hash(v___x_4037_, v___x_4041_);
v___x_4043_ = 32ULL;
v___x_4044_ = lean_uint64_shift_right(v___x_4042_, v___x_4043_);
v_fold_4045_ = lean_uint64_xor(v___x_4042_, v___x_4044_);
v___x_4046_ = 16ULL;
v___x_4047_ = lean_uint64_shift_right(v_fold_4045_, v___x_4046_);
v___x_4048_ = lean_uint64_xor(v_fold_4045_, v___x_4047_);
v___x_4049_ = lean_uint64_to_usize(v___x_4048_);
v___x_4050_ = lean_usize_of_nat(v___x_4036_);
v___x_4051_ = ((size_t)1ULL);
v___x_4052_ = lean_usize_sub(v___x_4050_, v___x_4051_);
v___x_4053_ = lean_usize_land(v___x_4049_, v___x_4052_);
v___x_4054_ = lean_array_uget_borrowed(v_x_4024_, v___x_4053_);
lean_inc(v___x_4054_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 2, v___x_4054_);
v___x_4056_ = v___x_4031_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_key_4026_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_value_4028_);
lean_ctor_set(v_reuseFailAlloc_4059_, 2, v___x_4054_);
v___x_4056_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4057_; 
v___x_4057_ = lean_array_uset(v_x_4024_, v___x_4053_, v___x_4056_);
v_x_4024_ = v___x_4057_;
v_x_4025_ = v_tail_4029_;
goto _start;
}
}
v___jp_4060_:
{
uint64_t v___x_4062_; uint64_t v___x_4063_; 
v___x_4062_ = 13ULL;
v___x_4063_ = lean_uint64_mix_hash(v___y_4061_, v___x_4062_);
v___y_4039_ = v___x_4063_;
goto v___jp_4038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4___redArg(lean_object* v_i_4071_, lean_object* v_source_4072_, lean_object* v_target_4073_){
_start:
{
lean_object* v___x_4074_; uint8_t v___x_4075_; 
v___x_4074_ = lean_array_get_size(v_source_4072_);
v___x_4075_ = lean_nat_dec_lt(v_i_4071_, v___x_4074_);
if (v___x_4075_ == 0)
{
lean_dec_ref(v_source_4072_);
lean_dec(v_i_4071_);
return v_target_4073_;
}
else
{
lean_object* v_es_4076_; lean_object* v___x_4077_; lean_object* v_source_4078_; lean_object* v_target_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v_es_4076_ = lean_array_fget(v_source_4072_, v_i_4071_);
v___x_4077_ = lean_box(0);
v_source_4078_ = lean_array_fset(v_source_4072_, v_i_4071_, v___x_4077_);
v_target_4079_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4_spec__8___redArg(v_target_4073_, v_es_4076_);
v___x_4080_ = lean_unsigned_to_nat(1u);
v___x_4081_ = lean_nat_add(v_i_4071_, v___x_4080_);
lean_dec(v_i_4071_);
v_i_4071_ = v___x_4081_;
v_source_4072_ = v_source_4078_;
v_target_4073_ = v_target_4079_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_data_4083_){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v_nbuckets_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4084_ = lean_array_get_size(v_data_4083_);
v___x_4085_ = lean_unsigned_to_nat(2u);
v_nbuckets_4086_ = lean_nat_mul(v___x_4084_, v___x_4085_);
v___x_4087_ = lean_unsigned_to_nat(0u);
v___x_4088_ = lean_box(0);
v___x_4089_ = lean_mk_array(v_nbuckets_4086_, v___x_4088_);
v___x_4090_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4___redArg(v___x_4087_, v_data_4083_, v___x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4091_, lean_object* v_m_4092_, lean_object* v_a_4093_){
_start:
{
size_t v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v_snd_4101_; lean_object* v_size_4102_; lean_object* v_buckets_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4162_; 
v_snd_4101_ = lean_ctor_get(v_a_4093_, 1);
v_size_4102_ = lean_ctor_get(v_m_4092_, 0);
v_buckets_4103_ = lean_ctor_get(v_m_4092_, 1);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_m_4092_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4105_ = v_m_4092_;
v_isShared_4106_ = v_isSharedCheck_4162_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_buckets_4103_);
lean_inc(v_size_4102_);
lean_dec(v_m_4092_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4162_;
goto v_resetjp_4104_;
}
v___jp_4094_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = lean_array_uset(v___y_4096_, v___y_4095_, v___y_4097_);
v___x_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___y_4098_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
return v___x_4100_;
}
v_resetjp_4104_:
{
lean_object* v_fst_4107_; lean_object* v_fst_4108_; lean_object* v_snd_4109_; lean_object* v___x_4110_; uint64_t v___x_4111_; uint64_t v___y_4113_; uint64_t v___y_4154_; 
v_fst_4107_ = lean_ctor_get(v_a_4093_, 0);
v_fst_4108_ = lean_ctor_get(v_snd_4101_, 0);
v_snd_4109_ = lean_ctor_get(v_snd_4101_, 1);
v___x_4110_ = lean_array_get_size(v_buckets_4103_);
v___x_4111_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4107_);
if (lean_obj_tag(v_fst_4108_) == 0)
{
uint64_t v___x_4157_; 
v___x_4157_ = 11ULL;
v___y_4113_ = v___x_4157_;
goto v___jp_4112_;
}
else
{
lean_object* v_val_4158_; uint8_t v___x_4159_; 
v_val_4158_ = lean_ctor_get(v_fst_4108_, 0);
v___x_4159_ = lean_unbox(v_val_4158_);
if (v___x_4159_ == 0)
{
uint64_t v___x_4160_; 
v___x_4160_ = 13ULL;
v___y_4154_ = v___x_4160_;
goto v___jp_4153_;
}
else
{
uint64_t v___x_4161_; 
v___x_4161_ = 11ULL;
v___y_4154_ = v___x_4161_;
goto v___jp_4153_;
}
}
v___jp_4112_:
{
uint64_t v___x_4114_; uint64_t v___x_4115_; uint64_t v___x_4116_; uint64_t v___x_4117_; uint64_t v___x_4118_; uint64_t v_fold_4119_; uint64_t v___x_4120_; uint64_t v___x_4121_; uint64_t v___x_4122_; size_t v___x_4123_; size_t v___x_4124_; size_t v___x_4125_; size_t v___x_4126_; size_t v___x_4127_; lean_object* v_bkt_4128_; uint8_t v___x_4129_; 
v___x_4114_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4109_);
v___x_4115_ = lean_uint64_mix_hash(v___y_4113_, v___x_4114_);
v___x_4116_ = lean_uint64_mix_hash(v___x_4111_, v___x_4115_);
v___x_4117_ = 32ULL;
v___x_4118_ = lean_uint64_shift_right(v___x_4116_, v___x_4117_);
v_fold_4119_ = lean_uint64_xor(v___x_4116_, v___x_4118_);
v___x_4120_ = 16ULL;
v___x_4121_ = lean_uint64_shift_right(v_fold_4119_, v___x_4120_);
v___x_4122_ = lean_uint64_xor(v_fold_4119_, v___x_4121_);
v___x_4123_ = lean_uint64_to_usize(v___x_4122_);
v___x_4124_ = lean_usize_of_nat(v___x_4110_);
v___x_4125_ = ((size_t)1ULL);
v___x_4126_ = lean_usize_sub(v___x_4124_, v___x_4125_);
v___x_4127_ = lean_usize_land(v___x_4123_, v___x_4126_);
v_bkt_4128_ = lean_array_uget_borrowed(v_buckets_4103_, v___x_4127_);
v___x_4129_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___redArg(v_a_4093_, v_bkt_4128_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v_size_x27_4131_; lean_object* v___x_4132_; lean_object* v_buckets_x27_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v___x_4130_ = lean_unsigned_to_nat(1u);
v_size_x27_4131_ = lean_nat_add(v_size_4102_, v___x_4130_);
lean_dec(v_size_4102_);
lean_inc(v_bkt_4128_);
v___x_4132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4132_, 0, v_a_4093_);
lean_ctor_set(v___x_4132_, 1, v_a_4091_);
lean_ctor_set(v___x_4132_, 2, v_bkt_4128_);
v_buckets_x27_4133_ = lean_array_uset(v_buckets_4103_, v___x_4127_, v___x_4132_);
v___x_4134_ = lean_unsigned_to_nat(4u);
v___x_4135_ = lean_nat_mul(v_size_x27_4131_, v___x_4134_);
v___x_4136_ = lean_unsigned_to_nat(3u);
v___x_4137_ = lean_nat_div(v___x_4135_, v___x_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_array_get_size(v_buckets_x27_4133_);
v___x_4139_ = lean_nat_dec_le(v___x_4137_, v___x_4138_);
lean_dec(v___x_4137_);
if (v___x_4139_ == 0)
{
lean_object* v_val_4140_; lean_object* v___x_4142_; 
v_val_4140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_buckets_x27_4133_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 1, v_val_4140_);
lean_ctor_set(v___x_4105_, 0, v_size_x27_4131_);
v___x_4142_ = v___x_4105_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_size_x27_4131_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v_val_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
else
{
lean_object* v___x_4145_; 
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 1, v_buckets_x27_4133_);
lean_ctor_set(v___x_4105_, 0, v_size_x27_4131_);
v___x_4145_ = v___x_4105_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_size_x27_4131_);
lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_buckets_x27_4133_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
else
{
lean_object* v___x_4147_; lean_object* v_buckets_x27_4148_; lean_object* v_bkt_x27_4149_; uint8_t v___x_4150_; 
lean_inc(v_bkt_4128_);
lean_del_object(v___x_4105_);
v___x_4147_ = lean_box(0);
v_buckets_x27_4148_ = lean_array_uset(v_buckets_4103_, v___x_4127_, v___x_4147_);
lean_inc_ref(v_a_4093_);
v_bkt_x27_4149_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(v_a_4091_, v_a_4093_, v_bkt_4128_);
v___x_4150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___redArg(v_a_4093_, v_bkt_x27_4149_);
lean_dec_ref(v_a_4093_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = lean_unsigned_to_nat(1u);
v___x_4152_ = lean_nat_sub(v_size_4102_, v___x_4151_);
lean_dec(v_size_4102_);
v___y_4095_ = v___x_4127_;
v___y_4096_ = v_buckets_x27_4148_;
v___y_4097_ = v_bkt_x27_4149_;
v___y_4098_ = v___x_4152_;
goto v___jp_4094_;
}
else
{
v___y_4095_ = v___x_4127_;
v___y_4096_ = v_buckets_x27_4148_;
v___y_4097_ = v_bkt_x27_4149_;
v___y_4098_ = v_size_4102_;
goto v___jp_4094_;
}
}
}
v___jp_4153_:
{
uint64_t v___x_4155_; uint64_t v___x_4156_; 
v___x_4155_ = 13ULL;
v___x_4156_ = lean_uint64_mix_hash(v___y_4154_, v___x_4155_);
v___y_4113_ = v___x_4156_;
goto v___jp_4112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4163_, lean_object* v_as_4164_, size_t v_sz_4165_, size_t v_i_4166_, lean_object* v_b_4167_){
_start:
{
uint8_t v___x_4168_; 
v___x_4168_ = lean_usize_dec_lt(v_i_4166_, v_sz_4165_);
if (v___x_4168_ == 0)
{
return v_b_4167_;
}
else
{
lean_object* v_a_4169_; lean_object* v___y_4171_; 
v_a_4169_ = lean_array_uget_borrowed(v_as_4164_, v_i_4166_);
if (v_allowSimultaneousBinderUse_4163_ == 0)
{
lean_object* v___x_4180_; 
v___x_4180_ = lean_box(0);
v___y_4171_ = v___x_4180_;
goto v___jp_4170_;
}
else
{
uint8_t v_isBinder_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v_isBinder_4181_ = lean_ctor_get_uint8(v_a_4169_, sizeof(void*)*6);
v___x_4182_ = lean_box(v_isBinder_4181_);
v___x_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
v___y_4171_ = v___x_4183_;
goto v___jp_4170_;
}
v___jp_4170_:
{
lean_object* v_ident_4172_; lean_object* v_range_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; size_t v___x_4177_; size_t v___x_4178_; 
v_ident_4172_ = lean_ctor_get(v_a_4169_, 0);
v_range_4173_ = lean_ctor_get(v_a_4169_, 2);
lean_inc_ref(v_range_4173_);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___y_4171_);
lean_ctor_set(v___x_4174_, 1, v_range_4173_);
lean_inc_ref(v_ident_4172_);
v___x_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4175_, 0, v_ident_4172_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
lean_inc(v_a_4169_);
v___x_4176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4169_, v_b_4167_, v___x_4175_);
v___x_4177_ = ((size_t)1ULL);
v___x_4178_ = lean_usize_add(v_i_4166_, v___x_4177_);
v_i_4166_ = v___x_4178_;
v_b_4167_ = v___x_4176_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4184_, lean_object* v_as_4185_, lean_object* v_sz_4186_, lean_object* v_i_4187_, lean_object* v_b_4188_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4189_; size_t v_sz_boxed_4190_; size_t v_i_boxed_4191_; lean_object* v_res_4192_; 
v_allowSimultaneousBinderUse_boxed_4189_ = lean_unbox(v_allowSimultaneousBinderUse_4184_);
v_sz_boxed_4190_ = lean_unbox_usize(v_sz_4186_);
lean_dec(v_sz_4186_);
v_i_boxed_4191_ = lean_unbox_usize(v_i_4187_);
lean_dec(v_i_4187_);
v_res_4192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4189_, v_as_4185_, v_sz_boxed_4190_, v_i_boxed_4191_, v_b_4188_);
lean_dec_ref(v_as_4185_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4193_, lean_object* v_x_4194_){
_start:
{
if (lean_obj_tag(v_x_4194_) == 0)
{
return v_x_4193_;
}
else
{
lean_object* v_value_4195_; lean_object* v_tail_4196_; lean_object* v___x_4197_; 
v_value_4195_ = lean_ctor_get(v_x_4194_, 1);
lean_inc(v_value_4195_);
v_tail_4196_ = lean_ctor_get(v_x_4194_, 2);
lean_inc(v_tail_4196_);
lean_dec_ref(v_x_4194_);
v___x_4197_ = lean_array_push(v_x_4193_, v_value_4195_);
v_x_4193_ = v___x_4197_;
v_x_4194_ = v_tail_4196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4199_, size_t v_i_4200_, size_t v_stop_4201_, lean_object* v_b_4202_){
_start:
{
uint8_t v___x_4203_; 
v___x_4203_ = lean_usize_dec_eq(v_i_4200_, v_stop_4201_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; lean_object* v___x_4205_; size_t v___x_4206_; size_t v___x_4207_; 
v___x_4204_ = lean_array_uget_borrowed(v_as_4199_, v_i_4200_);
lean_inc(v___x_4204_);
v___x_4205_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4202_, v___x_4204_);
v___x_4206_ = ((size_t)1ULL);
v___x_4207_ = lean_usize_add(v_i_4200_, v___x_4206_);
v_i_4200_ = v___x_4207_;
v_b_4202_ = v___x_4205_;
goto _start;
}
else
{
return v_b_4202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4209_, lean_object* v_i_4210_, lean_object* v_stop_4211_, lean_object* v_b_4212_){
_start:
{
size_t v_i_boxed_4213_; size_t v_stop_boxed_4214_; lean_object* v_res_4215_; 
v_i_boxed_4213_ = lean_unbox_usize(v_i_4210_);
lean_dec(v_i_4210_);
v_stop_boxed_4214_ = lean_unbox_usize(v_stop_4211_);
lean_dec(v_stop_4211_);
v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4209_, v_i_boxed_4213_, v_stop_boxed_4214_, v_b_4212_);
lean_dec_ref(v_as_4209_);
return v_res_4215_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4216_ = lean_box(0);
v___x_4217_ = lean_unsigned_to_nat(16u);
v___x_4218_ = lean_mk_array(v___x_4217_, v___x_4216_);
return v___x_4218_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v_refsByIdAndRange_4221_; 
v___x_4219_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4220_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4221_, 0, v___x_4220_);
lean_ctor_set(v_refsByIdAndRange_4221_, 1, v___x_4219_);
return v_refsByIdAndRange_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4222_, uint8_t v_allowSimultaneousBinderUse_4223_){
_start:
{
lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4233_; lean_object* v___x_4240_; lean_object* v_refsByIdAndRange_4241_; size_t v_sz_4242_; size_t v___x_4243_; lean_object* v___x_4244_; lean_object* v_buckets_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; uint8_t v___x_4248_; 
v___x_4240_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4241_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4242_ = lean_array_size(v_refs_4222_);
v___x_4243_ = ((size_t)0ULL);
v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4223_, v_refs_4222_, v_sz_4242_, v___x_4243_, v_refsByIdAndRange_4241_);
v_buckets_4245_ = lean_ctor_get(v___x_4244_, 1);
lean_inc_ref(v_buckets_4245_);
lean_dec_ref(v___x_4244_);
v___x_4246_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4247_ = lean_array_get_size(v_buckets_4245_);
v___x_4248_ = lean_nat_dec_lt(v___x_4240_, v___x_4247_);
if (v___x_4248_ == 0)
{
lean_dec_ref(v_buckets_4245_);
v___y_4233_ = v___x_4246_;
goto v___jp_4232_;
}
else
{
uint8_t v___x_4249_; 
v___x_4249_ = lean_nat_dec_le(v___x_4247_, v___x_4247_);
if (v___x_4249_ == 0)
{
if (v___x_4248_ == 0)
{
lean_dec_ref(v_buckets_4245_);
v___y_4233_ = v___x_4246_;
goto v___jp_4232_;
}
else
{
size_t v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = lean_usize_of_nat(v___x_4247_);
v___x_4251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4245_, v___x_4243_, v___x_4250_, v___x_4246_);
lean_dec_ref(v_buckets_4245_);
v___y_4233_ = v___x_4251_;
goto v___jp_4232_;
}
}
else
{
size_t v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_usize_of_nat(v___x_4247_);
v___x_4253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4245_, v___x_4243_, v___x_4252_, v___x_4246_);
lean_dec_ref(v_buckets_4245_);
v___y_4233_ = v___x_4253_;
goto v___jp_4232_;
}
}
v___jp_4224_:
{
uint8_t v___x_4229_; 
lean_dec(v___y_4225_);
v___x_4229_ = lean_nat_dec_le(v___y_4228_, v___y_4226_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; 
lean_dec(v___y_4226_);
lean_inc(v___y_4228_);
v___x_4230_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4227_, v___y_4228_, v___y_4228_);
lean_dec(v___y_4228_);
return v___x_4230_;
}
else
{
lean_object* v___x_4231_; 
v___x_4231_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4227_, v___y_4228_, v___y_4226_);
lean_dec(v___y_4226_);
return v___x_4231_;
}
}
v___jp_4232_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; uint8_t v___x_4236_; 
v___x_4234_ = lean_array_get_size(v___y_4233_);
v___x_4235_ = lean_unsigned_to_nat(0u);
v___x_4236_ = lean_nat_dec_eq(v___x_4234_, v___x_4235_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4237_ = lean_unsigned_to_nat(1u);
v___x_4238_ = lean_nat_sub(v___x_4234_, v___x_4237_);
v___x_4239_ = lean_nat_dec_le(v___x_4235_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_inc(v___x_4238_);
v___y_4225_ = v___x_4234_;
v___y_4226_ = v___x_4238_;
v___y_4227_ = v___y_4233_;
v___y_4228_ = v___x_4238_;
goto v___jp_4224_;
}
else
{
v___y_4225_ = v___x_4234_;
v___y_4226_ = v___x_4238_;
v___y_4227_ = v___y_4233_;
v___y_4228_ = v___x_4235_;
goto v___jp_4224_;
}
}
else
{
return v___y_4233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object* v_refs_4254_, lean_object* v_allowSimultaneousBinderUse_4255_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4256_; lean_object* v_res_4257_; 
v_allowSimultaneousBinderUse_boxed_4256_ = lean_unbox(v_allowSimultaneousBinderUse_4255_);
v_res_4257_ = l_Lean_Server_dedupReferences(v_refs_4254_, v_allowSimultaneousBinderUse_boxed_4256_);
lean_dec_ref(v_refs_4254_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object* v_n_4258_, lean_object* v_as_4259_, lean_object* v_lo_4260_, lean_object* v_hi_4261_, lean_object* v_w_4262_, lean_object* v_hlo_4263_, lean_object* v_hhi_4264_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_as_4259_, v_lo_4260_, v_hi_4261_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object* v_n_4266_, lean_object* v_as_4267_, lean_object* v_lo_4268_, lean_object* v_hi_4269_, lean_object* v_w_4270_, lean_object* v_hlo_4271_, lean_object* v_hhi_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(v_n_4266_, v_as_4267_, v_lo_4268_, v_hi_4269_, v_w_4270_, v_hlo_4271_, v_hhi_4272_);
lean_dec(v_hi_4269_);
lean_dec(v_n_4266_);
return v_res_4273_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1(lean_object* v_00_u03b2_4274_, lean_object* v_a_4275_, lean_object* v_x_4276_){
_start:
{
uint8_t v___x_4277_; 
v___x_4277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___redArg(v_a_4275_, v_x_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4278_, lean_object* v_a_4279_, lean_object* v_x_4280_){
_start:
{
uint8_t v_res_4281_; lean_object* v_r_4282_; 
v_res_4281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__1(v_00_u03b2_4278_, v_a_4279_, v_x_4280_);
lean_dec(v_x_4280_);
lean_dec_ref(v_a_4279_);
v_r_4282_ = lean_box(v_res_4281_);
return v_r_4282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object* v_00_u03b2_4283_, lean_object* v_data_4284_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_data_4284_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4286_, lean_object* v_i_4287_, lean_object* v_source_4288_, lean_object* v_target_4289_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4___redArg(v_i_4287_, v_source_4288_, v_target_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4291_, lean_object* v_x_4292_, lean_object* v_x_4293_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__4_spec__8___redArg(v_x_4292_, v_x_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object* v_as_4295_, size_t v_i_4296_, size_t v_stop_4297_, lean_object* v_b_4298_){
_start:
{
uint8_t v___x_4299_; 
v___x_4299_ = lean_usize_dec_eq(v_i_4296_, v_stop_4297_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; lean_object* v___x_4301_; size_t v___x_4302_; size_t v___x_4303_; 
v___x_4300_ = lean_array_uget_borrowed(v_as_4295_, v_i_4296_);
lean_inc(v___x_4300_);
v___x_4301_ = l_Lean_Server_ModuleRefs_addRef(v_b_4298_, v___x_4300_);
v___x_4302_ = ((size_t)1ULL);
v___x_4303_ = lean_usize_add(v_i_4296_, v___x_4302_);
v_i_4296_ = v___x_4303_;
v_b_4298_ = v___x_4301_;
goto _start;
}
else
{
return v_b_4298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object* v_as_4305_, lean_object* v_i_4306_, lean_object* v_stop_4307_, lean_object* v_b_4308_){
_start:
{
size_t v_i_boxed_4309_; size_t v_stop_boxed_4310_; lean_object* v_res_4311_; 
v_i_boxed_4309_ = lean_unbox_usize(v_i_4306_);
lean_dec(v_i_4306_);
v_stop_boxed_4310_ = lean_unbox_usize(v_stop_4307_);
lean_dec(v_stop_4307_);
v_res_4311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_as_4305_, v_i_boxed_4309_, v_stop_boxed_4310_, v_b_4308_);
lean_dec_ref(v_as_4305_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object* v_as_4312_, size_t v_i_4313_, size_t v_stop_4314_, lean_object* v_b_4315_){
_start:
{
lean_object* v___y_4317_; uint8_t v___x_4321_; 
v___x_4321_ = lean_usize_dec_eq(v_i_4313_, v_stop_4314_);
if (v___x_4321_ == 0)
{
lean_object* v___x_4322_; lean_object* v_ident_4323_; 
v___x_4322_ = lean_array_uget_borrowed(v_as_4312_, v_i_4313_);
v_ident_4323_ = lean_ctor_get(v___x_4322_, 0);
if (lean_obj_tag(v_ident_4323_) == 1)
{
v___y_4317_ = v_b_4315_;
goto v___jp_4316_;
}
else
{
lean_object* v___x_4324_; 
lean_inc(v___x_4322_);
v___x_4324_ = lean_array_push(v_b_4315_, v___x_4322_);
v___y_4317_ = v___x_4324_;
goto v___jp_4316_;
}
}
else
{
return v_b_4315_;
}
v___jp_4316_:
{
size_t v___x_4318_; size_t v___x_4319_; 
v___x_4318_ = ((size_t)1ULL);
v___x_4319_ = lean_usize_add(v_i_4313_, v___x_4318_);
v_i_4313_ = v___x_4319_;
v_b_4315_ = v___y_4317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object* v_as_4325_, lean_object* v_i_4326_, lean_object* v_stop_4327_, lean_object* v_b_4328_){
_start:
{
size_t v_i_boxed_4329_; size_t v_stop_boxed_4330_; lean_object* v_res_4331_; 
v_i_boxed_4329_ = lean_unbox_usize(v_i_4326_);
lean_dec(v_i_4326_);
v_stop_boxed_4330_ = lean_unbox_usize(v_stop_4327_);
lean_dec(v_stop_4327_);
v_res_4331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_as_4325_, v_i_boxed_4329_, v_stop_boxed_4330_, v_b_4328_);
lean_dec_ref(v_as_4325_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object* v_text_4332_, lean_object* v_trees_4333_, uint8_t v_localVars_4334_, uint8_t v_allowSimultaneousBinderUse_4335_){
_start:
{
lean_object* v_refs_4337_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v_refs_4351_; 
v___x_4349_ = l_Lean_Server_findReferences(v_text_4332_, v_trees_4333_);
v___x_4350_ = l_Lean_Server_combineIdents(v_trees_4333_, v___x_4349_);
lean_dec_ref(v___x_4349_);
v_refs_4351_ = l_Lean_Server_dedupReferences(v___x_4350_, v_allowSimultaneousBinderUse_4335_);
lean_dec_ref(v___x_4350_);
if (v_localVars_4334_ == 0)
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; uint8_t v___x_4355_; 
v___x_4352_ = lean_unsigned_to_nat(0u);
v___x_4353_ = lean_array_get_size(v_refs_4351_);
v___x_4354_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4355_ = lean_nat_dec_lt(v___x_4352_, v___x_4353_);
if (v___x_4355_ == 0)
{
lean_dec_ref(v_refs_4351_);
v_refs_4337_ = v___x_4354_;
goto v___jp_4336_;
}
else
{
uint8_t v___x_4356_; 
v___x_4356_ = lean_nat_dec_le(v___x_4353_, v___x_4353_);
if (v___x_4356_ == 0)
{
if (v___x_4355_ == 0)
{
lean_dec_ref(v_refs_4351_);
v_refs_4337_ = v___x_4354_;
goto v___jp_4336_;
}
else
{
size_t v___x_4357_; size_t v___x_4358_; lean_object* v___x_4359_; 
v___x_4357_ = ((size_t)0ULL);
v___x_4358_ = lean_usize_of_nat(v___x_4353_);
v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4351_, v___x_4357_, v___x_4358_, v___x_4354_);
lean_dec_ref(v_refs_4351_);
v_refs_4337_ = v___x_4359_;
goto v___jp_4336_;
}
}
else
{
size_t v___x_4360_; size_t v___x_4361_; lean_object* v___x_4362_; 
v___x_4360_ = ((size_t)0ULL);
v___x_4361_ = lean_usize_of_nat(v___x_4353_);
v___x_4362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4351_, v___x_4360_, v___x_4361_, v___x_4354_);
lean_dec_ref(v_refs_4351_);
v_refs_4337_ = v___x_4362_;
goto v___jp_4336_;
}
}
}
else
{
v_refs_4337_ = v_refs_4351_;
goto v___jp_4336_;
}
v___jp_4336_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4338_ = lean_box(1);
v___x_4339_ = lean_unsigned_to_nat(0u);
v___x_4340_ = lean_array_get_size(v_refs_4337_);
v___x_4341_ = lean_nat_dec_lt(v___x_4339_, v___x_4340_);
if (v___x_4341_ == 0)
{
lean_dec_ref(v_refs_4337_);
return v___x_4338_;
}
else
{
uint8_t v___x_4342_; 
v___x_4342_ = lean_nat_dec_le(v___x_4340_, v___x_4340_);
if (v___x_4342_ == 0)
{
if (v___x_4341_ == 0)
{
lean_dec_ref(v_refs_4337_);
return v___x_4338_;
}
else
{
size_t v___x_4343_; size_t v___x_4344_; lean_object* v___x_4345_; 
v___x_4343_ = ((size_t)0ULL);
v___x_4344_ = lean_usize_of_nat(v___x_4340_);
v___x_4345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4337_, v___x_4343_, v___x_4344_, v___x_4338_);
lean_dec_ref(v_refs_4337_);
return v___x_4345_;
}
}
else
{
size_t v___x_4346_; size_t v___x_4347_; lean_object* v___x_4348_; 
v___x_4346_ = ((size_t)0ULL);
v___x_4347_ = lean_usize_of_nat(v___x_4340_);
v___x_4348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4337_, v___x_4346_, v___x_4347_, v___x_4338_);
lean_dec_ref(v_refs_4337_);
return v___x_4348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object* v_text_4363_, lean_object* v_trees_4364_, lean_object* v_localVars_4365_, lean_object* v_allowSimultaneousBinderUse_4366_){
_start:
{
uint8_t v_localVars_boxed_4367_; uint8_t v_allowSimultaneousBinderUse_boxed_4368_; lean_object* v_res_4369_; 
v_localVars_boxed_4367_ = lean_unbox(v_localVars_4365_);
v_allowSimultaneousBinderUse_boxed_4368_ = lean_unbox(v_allowSimultaneousBinderUse_4366_);
v_res_4369_ = l_Lean_Server_findModuleRefs(v_text_4363_, v_trees_4364_, v_localVars_boxed_4367_, v_allowSimultaneousBinderUse_boxed_4368_);
lean_dec_ref(v_trees_4364_);
return v_res_4369_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t v_a_4377_, uint8_t v_a_4378_){
_start:
{
switch(v_a_4377_)
{
case 0:
{
if (v_a_4378_ == 1)
{
uint8_t v___x_4379_; 
v___x_4379_ = 2;
return v___x_4379_;
}
else
{
return v_a_4378_;
}
}
case 1:
{
if (v_a_4378_ == 0)
{
uint8_t v___x_4380_; 
v___x_4380_ = 2;
return v___x_4380_;
}
else
{
return v_a_4378_;
}
}
default: 
{
return v_a_4377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
uint8_t v_a_46__boxed_4383_; uint8_t v_a_47__boxed_4384_; uint8_t v_res_4385_; lean_object* v_r_4386_; 
v_a_46__boxed_4383_ = lean_unbox(v_a_4381_);
v_a_47__boxed_4384_ = lean_unbox(v_a_4382_);
v_res_4385_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_a_46__boxed_4383_, v_a_47__boxed_4384_);
v_r_4386_ = lean_box(v_res_4385_);
return v_r_4386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object* v_upperBound_4387_, lean_object* v_identicalImports_4388_, lean_object* v_a_4389_, lean_object* v_b_4390_){
_start:
{
uint8_t v___x_4391_; 
v___x_4391_ = lean_nat_dec_lt(v_a_4389_, v_upperBound_4387_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4392_; 
lean_dec(v_a_4389_);
v___x_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4392_, 0, v_b_4390_);
return v___x_4392_;
}
else
{
lean_object* v_module_4393_; lean_object* v_uri_4394_; uint8_t v_isAll_4395_; uint8_t v_isPrivate_4396_; uint8_t v_metaKind_4397_; lean_object* v___x_4398_; lean_object* v_module_4399_; lean_object* v_uri_4400_; uint8_t v_isAll_4401_; uint8_t v_isPrivate_4402_; uint8_t v_metaKind_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4423_; 
v_module_4393_ = lean_ctor_get(v_b_4390_, 0);
lean_inc(v_module_4393_);
v_uri_4394_ = lean_ctor_get(v_b_4390_, 1);
lean_inc_ref(v_uri_4394_);
v_isAll_4395_ = lean_ctor_get_uint8(v_b_4390_, sizeof(void*)*2);
v_isPrivate_4396_ = lean_ctor_get_uint8(v_b_4390_, sizeof(void*)*2 + 1);
v_metaKind_4397_ = lean_ctor_get_uint8(v_b_4390_, sizeof(void*)*2 + 2);
lean_dec_ref(v_b_4390_);
v___x_4398_ = lean_array_fget(v_identicalImports_4388_, v_a_4389_);
v_module_4399_ = lean_ctor_get(v___x_4398_, 0);
v_uri_4400_ = lean_ctor_get(v___x_4398_, 1);
v_isAll_4401_ = lean_ctor_get_uint8(v___x_4398_, sizeof(void*)*2);
v_isPrivate_4402_ = lean_ctor_get_uint8(v___x_4398_, sizeof(void*)*2 + 1);
v_metaKind_4403_ = lean_ctor_get_uint8(v___x_4398_, sizeof(void*)*2 + 2);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4405_ = v___x_4398_;
v_isShared_4406_ = v_isSharedCheck_4423_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_uri_4400_);
lean_inc(v_module_4399_);
lean_dec(v___x_4398_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4423_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
uint8_t v___y_4408_; uint8_t v___y_4409_; uint8_t v___y_4418_; uint8_t v___x_4419_; 
v___x_4419_ = lean_name_eq(v_module_4393_, v_module_4399_);
lean_dec(v_module_4399_);
if (v___x_4419_ == 0)
{
lean_object* v___x_4420_; 
lean_del_object(v___x_4405_);
lean_dec_ref(v_uri_4400_);
lean_dec_ref(v_uri_4394_);
lean_dec(v_module_4393_);
lean_dec(v_a_4389_);
v___x_4420_ = lean_box(0);
return v___x_4420_;
}
else
{
uint8_t v___x_4421_; 
v___x_4421_ = lean_string_dec_eq(v_uri_4394_, v_uri_4400_);
lean_dec_ref(v_uri_4400_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; 
lean_del_object(v___x_4405_);
lean_dec_ref(v_uri_4394_);
lean_dec(v_module_4393_);
lean_dec(v_a_4389_);
v___x_4422_ = lean_box(0);
return v___x_4422_;
}
else
{
if (v_isAll_4395_ == 0)
{
v___y_4418_ = v_isAll_4401_;
goto v___jp_4417_;
}
else
{
v___y_4418_ = v_isAll_4395_;
goto v___jp_4417_;
}
}
}
v___jp_4407_:
{
uint8_t v___x_4410_; lean_object* v___x_4412_; 
v___x_4410_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_metaKind_4397_, v_metaKind_4403_);
if (v_isShared_4406_ == 0)
{
lean_ctor_set(v___x_4405_, 1, v_uri_4394_);
lean_ctor_set(v___x_4405_, 0, v_module_4393_);
v___x_4412_ = v___x_4405_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_module_4393_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_uri_4394_);
v___x_4412_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*2, v___y_4408_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*2 + 1, v___y_4409_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*2 + 2, v___x_4410_);
v___x_4413_ = lean_unsigned_to_nat(1u);
v___x_4414_ = lean_nat_add(v_a_4389_, v___x_4413_);
lean_dec(v_a_4389_);
v_a_4389_ = v___x_4414_;
v_b_4390_ = v___x_4412_;
goto _start;
}
}
v___jp_4417_:
{
if (v_isPrivate_4396_ == 0)
{
v___y_4408_ = v___y_4418_;
v___y_4409_ = v_isPrivate_4396_;
goto v___jp_4407_;
}
else
{
v___y_4408_ = v___y_4418_;
v___y_4409_ = v_isPrivate_4402_;
goto v___jp_4407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_4424_, lean_object* v_identicalImports_4425_, lean_object* v_a_4426_, lean_object* v_b_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4424_, v_identicalImports_4425_, v_a_4426_, v_b_4427_);
lean_dec_ref(v_identicalImports_4425_);
lean_dec(v_upperBound_4424_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object* v_identicalImports_4429_){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; uint8_t v___x_4432_; 
v___x_4430_ = lean_unsigned_to_nat(0u);
v___x_4431_ = lean_array_get_size(v_identicalImports_4429_);
v___x_4432_ = lean_nat_dec_lt(v___x_4430_, v___x_4431_);
if (v___x_4432_ == 0)
{
lean_object* v___x_4433_; 
v___x_4433_ = lean_box(0);
return v___x_4433_;
}
else
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = lean_unsigned_to_nat(1u);
v___x_4435_ = lean_array_fget_borrowed(v_identicalImports_4429_, v___x_4430_);
lean_inc(v___x_4435_);
v___x_4436_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v___x_4431_, v_identicalImports_4429_, v___x_4434_, v___x_4435_);
return v___x_4436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object* v_identicalImports_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_identicalImports_4437_);
lean_dec_ref(v_identicalImports_4437_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object* v_upperBound_4439_, lean_object* v_identicalImports_4440_, lean_object* v_inst_4441_, lean_object* v_R_4442_, lean_object* v_a_4443_, lean_object* v_b_4444_, lean_object* v_c_4445_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4439_, v_identicalImports_4440_, v_a_4443_, v_b_4444_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object* v_upperBound_4447_, lean_object* v_identicalImports_4448_, lean_object* v_inst_4449_, lean_object* v_R_4450_, lean_object* v_a_4451_, lean_object* v_b_4452_, lean_object* v_c_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(v_upperBound_4447_, v_identicalImports_4448_, v_inst_4449_, v_R_4450_, v_a_4451_, v_b_4452_, v_c_4453_);
lean_dec_ref(v_identicalImports_4448_);
lean_dec(v_upperBound_4447_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object* v_x_4461_){
_start:
{
lean_object* v_module_4462_; 
v_module_4462_ = lean_ctor_get(v_x_4461_, 0);
lean_inc(v_module_4462_);
return v_module_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object* v_x_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Lean_Server_DirectImports_convertImportInfos___lam__0(v_x_4463_);
lean_dec_ref(v_x_4463_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object* v_x_4465_, lean_object* v_x_4466_){
_start:
{
if (lean_obj_tag(v_x_4466_) == 0)
{
return v_x_4465_;
}
else
{
lean_object* v_key_4467_; lean_object* v_value_4468_; lean_object* v_tail_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v_key_4467_ = lean_ctor_get(v_x_4466_, 0);
v_value_4468_ = lean_ctor_get(v_x_4466_, 1);
v_tail_4469_ = lean_ctor_get(v_x_4466_, 2);
lean_inc(v_value_4468_);
lean_inc(v_key_4467_);
v___x_4470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4470_, 0, v_key_4467_);
lean_ctor_set(v___x_4470_, 1, v_value_4468_);
v___x_4471_ = lean_array_push(v_x_4465_, v___x_4470_);
v_x_4465_ = v___x_4471_;
v_x_4466_ = v_tail_4469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object* v_x_4473_, lean_object* v_x_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_x_4473_, v_x_4474_);
lean_dec(v_x_4474_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object* v_as_4476_, size_t v_i_4477_, size_t v_stop_4478_, lean_object* v_b_4479_){
_start:
{
uint8_t v___x_4480_; 
v___x_4480_ = lean_usize_dec_eq(v_i_4477_, v_stop_4478_);
if (v___x_4480_ == 0)
{
lean_object* v___x_4481_; lean_object* v___x_4482_; size_t v___x_4483_; size_t v___x_4484_; 
v___x_4481_ = lean_array_uget_borrowed(v_as_4476_, v_i_4477_);
v___x_4482_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_b_4479_, v___x_4481_);
v___x_4483_ = ((size_t)1ULL);
v___x_4484_ = lean_usize_add(v_i_4477_, v___x_4483_);
v_i_4477_ = v___x_4484_;
v_b_4479_ = v___x_4482_;
goto _start;
}
else
{
return v_b_4479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object* v_as_4486_, lean_object* v_i_4487_, lean_object* v_stop_4488_, lean_object* v_b_4489_){
_start:
{
size_t v_i_boxed_4490_; size_t v_stop_boxed_4491_; lean_object* v_res_4492_; 
v_i_boxed_4490_ = lean_unbox_usize(v_i_4487_);
lean_dec(v_i_4487_);
v_stop_boxed_4491_ = lean_unbox_usize(v_stop_4488_);
lean_dec(v_stop_4488_);
v_res_4492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_as_4486_, v_i_boxed_4490_, v_stop_boxed_4491_, v_b_4489_);
lean_dec_ref(v_as_4486_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object* v_as_4493_, size_t v_i_4494_, size_t v_stop_4495_, lean_object* v_b_4496_){
_start:
{
uint8_t v___x_4498_; 
v___x_4498_ = lean_usize_dec_eq(v_i_4494_, v_stop_4495_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4499_; lean_object* v_module_4500_; uint8_t v_isPrivate_4501_; uint8_t v_isAll_4502_; uint8_t v_isMeta_4503_; lean_object* v_module_4504_; lean_object* v___x_4505_; 
v___x_4499_ = lean_array_uget_borrowed(v_as_4493_, v_i_4494_);
v_module_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isPrivate_4501_ = lean_ctor_get_uint8(v___x_4499_, sizeof(void*)*1);
v_isAll_4502_ = lean_ctor_get_uint8(v___x_4499_, sizeof(void*)*1 + 1);
v_isMeta_4503_ = lean_ctor_get_uint8(v___x_4499_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4500_);
v_module_4504_ = l_String_toName(v_module_4500_);
lean_inc(v_module_4504_);
v___x_4505_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4504_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; lean_object* v_a_4508_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4506_);
lean_dec_ref(v___x_4505_);
if (lean_obj_tag(v_a_4506_) == 1)
{
lean_object* v_val_4512_; uint8_t v___y_4514_; 
v_val_4512_ = lean_ctor_get(v_a_4506_, 0);
lean_inc(v_val_4512_);
lean_dec_ref(v_a_4506_);
if (v_isMeta_4503_ == 0)
{
uint8_t v___x_4517_; 
v___x_4517_ = 0;
v___y_4514_ = v___x_4517_;
goto v___jp_4513_;
}
else
{
uint8_t v___x_4518_; 
v___x_4518_ = 1;
v___y_4514_ = v___x_4518_;
goto v___jp_4513_;
}
v___jp_4513_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4515_, 0, v_module_4504_);
lean_ctor_set(v___x_4515_, 1, v_val_4512_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*2, v_isAll_4502_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*2 + 1, v_isPrivate_4501_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*2 + 2, v___y_4514_);
v___x_4516_ = lean_array_push(v_b_4496_, v___x_4515_);
v_a_4508_ = v___x_4516_;
goto v___jp_4507_;
}
}
else
{
lean_dec(v_a_4506_);
lean_dec(v_module_4504_);
v_a_4508_ = v_b_4496_;
goto v___jp_4507_;
}
v___jp_4507_:
{
size_t v___x_4509_; size_t v___x_4510_; 
v___x_4509_ = ((size_t)1ULL);
v___x_4510_ = lean_usize_add(v_i_4494_, v___x_4509_);
v_i_4494_ = v___x_4510_;
v_b_4496_ = v_a_4508_;
goto _start;
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec(v_module_4504_);
lean_dec_ref(v_b_4496_);
v_a_4519_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4505_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4505_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_object* v___x_4527_; 
v___x_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4527_, 0, v_b_4496_);
return v___x_4527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object* v_as_4528_, lean_object* v_i_4529_, lean_object* v_stop_4530_, lean_object* v_b_4531_, lean_object* v___y_4532_){
_start:
{
size_t v_i_boxed_4533_; size_t v_stop_boxed_4534_; lean_object* v_res_4535_; 
v_i_boxed_4533_ = lean_unbox_usize(v_i_4529_);
lean_dec(v_i_4529_);
v_stop_boxed_4534_ = lean_unbox_usize(v_stop_4530_);
lean_dec(v_stop_4530_);
v_res_4535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4528_, v_i_boxed_4533_, v_stop_boxed_4534_, v_b_4531_);
lean_dec_ref(v_as_4528_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object* v_as_4536_, lean_object* v_start_4537_, lean_object* v_stop_4538_){
_start:
{
lean_object* v___x_4540_; uint8_t v___x_4541_; 
v___x_4540_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_4541_ = lean_nat_dec_lt(v_start_4537_, v_stop_4538_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; 
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4540_);
return v___x_4542_;
}
else
{
lean_object* v___x_4543_; uint8_t v___x_4544_; 
v___x_4543_ = lean_array_get_size(v_as_4536_);
v___x_4544_ = lean_nat_dec_le(v_stop_4538_, v___x_4543_);
if (v___x_4544_ == 0)
{
uint8_t v___x_4545_; 
v___x_4545_ = lean_nat_dec_lt(v_start_4537_, v___x_4543_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; 
v___x_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4540_);
return v___x_4546_;
}
else
{
size_t v___x_4547_; size_t v___x_4548_; lean_object* v___x_4549_; 
v___x_4547_ = lean_usize_of_nat(v_start_4537_);
v___x_4548_ = lean_usize_of_nat(v___x_4543_);
v___x_4549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4536_, v___x_4547_, v___x_4548_, v___x_4540_);
return v___x_4549_;
}
}
else
{
size_t v___x_4550_; size_t v___x_4551_; lean_object* v___x_4552_; 
v___x_4550_ = lean_usize_of_nat(v_start_4537_);
v___x_4551_ = lean_usize_of_nat(v_stop_4538_);
v___x_4552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4536_, v___x_4550_, v___x_4551_, v___x_4540_);
return v___x_4552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object* v_as_4553_, lean_object* v_start_4554_, lean_object* v_stop_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_as_4553_, v_start_4554_, v_stop_4555_);
lean_dec(v_stop_4555_);
lean_dec(v_start_4554_);
lean_dec_ref(v_as_4553_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object* v_k_4558_, lean_object* v_v_4559_, lean_object* v_t_4560_){
_start:
{
if (lean_obj_tag(v_t_4560_) == 0)
{
lean_object* v_size_4561_; lean_object* v_k_4562_; lean_object* v_v_4563_; lean_object* v_l_4564_; lean_object* v_r_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4845_; 
v_size_4561_ = lean_ctor_get(v_t_4560_, 0);
v_k_4562_ = lean_ctor_get(v_t_4560_, 1);
v_v_4563_ = lean_ctor_get(v_t_4560_, 2);
v_l_4564_ = lean_ctor_get(v_t_4560_, 3);
v_r_4565_ = lean_ctor_get(v_t_4560_, 4);
v_isSharedCheck_4845_ = !lean_is_exclusive(v_t_4560_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4567_ = v_t_4560_;
v_isShared_4568_ = v_isSharedCheck_4845_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_r_4565_);
lean_inc(v_l_4564_);
lean_inc(v_v_4563_);
lean_inc(v_k_4562_);
lean_inc(v_size_4561_);
lean_dec(v_t_4560_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4845_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
uint8_t v___x_4569_; 
v___x_4569_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4558_, v_k_4562_);
switch(v___x_4569_)
{
case 0:
{
lean_object* v_impl_4570_; lean_object* v___x_4571_; 
lean_dec(v_size_4561_);
v_impl_4570_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4558_, v_v_4559_, v_l_4564_);
v___x_4571_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4565_) == 0)
{
lean_object* v_size_4572_; lean_object* v_size_4573_; lean_object* v_k_4574_; lean_object* v_v_4575_; lean_object* v_l_4576_; lean_object* v_r_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; uint8_t v___x_4580_; 
v_size_4572_ = lean_ctor_get(v_r_4565_, 0);
v_size_4573_ = lean_ctor_get(v_impl_4570_, 0);
lean_inc(v_size_4573_);
v_k_4574_ = lean_ctor_get(v_impl_4570_, 1);
lean_inc(v_k_4574_);
v_v_4575_ = lean_ctor_get(v_impl_4570_, 2);
lean_inc(v_v_4575_);
v_l_4576_ = lean_ctor_get(v_impl_4570_, 3);
lean_inc(v_l_4576_);
v_r_4577_ = lean_ctor_get(v_impl_4570_, 4);
lean_inc(v_r_4577_);
v___x_4578_ = lean_unsigned_to_nat(3u);
v___x_4579_ = lean_nat_mul(v___x_4578_, v_size_4572_);
v___x_4580_ = lean_nat_dec_lt(v___x_4579_, v_size_4573_);
lean_dec(v___x_4579_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4584_; 
lean_dec(v_r_4577_);
lean_dec(v_l_4576_);
lean_dec(v_v_4575_);
lean_dec(v_k_4574_);
v___x_4581_ = lean_nat_add(v___x_4571_, v_size_4573_);
lean_dec(v_size_4573_);
v___x_4582_ = lean_nat_add(v___x_4581_, v_size_4572_);
lean_dec(v___x_4581_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 3, v_impl_4570_);
lean_ctor_set(v___x_4567_, 0, v___x_4582_);
v___x_4584_ = v___x_4567_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4585_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4585_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4585_, 3, v_impl_4570_);
lean_ctor_set(v_reuseFailAlloc_4585_, 4, v_r_4565_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
else
{
lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4651_; 
v_isSharedCheck_4651_ = !lean_is_exclusive(v_impl_4570_);
if (v_isSharedCheck_4651_ == 0)
{
lean_object* v_unused_4652_; lean_object* v_unused_4653_; lean_object* v_unused_4654_; lean_object* v_unused_4655_; lean_object* v_unused_4656_; 
v_unused_4652_ = lean_ctor_get(v_impl_4570_, 4);
lean_dec(v_unused_4652_);
v_unused_4653_ = lean_ctor_get(v_impl_4570_, 3);
lean_dec(v_unused_4653_);
v_unused_4654_ = lean_ctor_get(v_impl_4570_, 2);
lean_dec(v_unused_4654_);
v_unused_4655_ = lean_ctor_get(v_impl_4570_, 1);
lean_dec(v_unused_4655_);
v_unused_4656_ = lean_ctor_get(v_impl_4570_, 0);
lean_dec(v_unused_4656_);
v___x_4587_ = v_impl_4570_;
v_isShared_4588_ = v_isSharedCheck_4651_;
goto v_resetjp_4586_;
}
else
{
lean_dec(v_impl_4570_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4651_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v_size_4589_; lean_object* v_size_4590_; lean_object* v_k_4591_; lean_object* v_v_4592_; lean_object* v_l_4593_; lean_object* v_r_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; uint8_t v___x_4597_; 
v_size_4589_ = lean_ctor_get(v_l_4576_, 0);
v_size_4590_ = lean_ctor_get(v_r_4577_, 0);
v_k_4591_ = lean_ctor_get(v_r_4577_, 1);
v_v_4592_ = lean_ctor_get(v_r_4577_, 2);
v_l_4593_ = lean_ctor_get(v_r_4577_, 3);
v_r_4594_ = lean_ctor_get(v_r_4577_, 4);
v___x_4595_ = lean_unsigned_to_nat(2u);
v___x_4596_ = lean_nat_mul(v___x_4595_, v_size_4589_);
v___x_4597_ = lean_nat_dec_lt(v_size_4590_, v___x_4596_);
lean_dec(v___x_4596_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4626_; 
lean_inc(v_r_4594_);
lean_inc(v_l_4593_);
lean_inc(v_v_4592_);
lean_inc(v_k_4591_);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_r_4577_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; lean_object* v_unused_4628_; lean_object* v_unused_4629_; lean_object* v_unused_4630_; lean_object* v_unused_4631_; 
v_unused_4627_ = lean_ctor_get(v_r_4577_, 4);
lean_dec(v_unused_4627_);
v_unused_4628_ = lean_ctor_get(v_r_4577_, 3);
lean_dec(v_unused_4628_);
v_unused_4629_ = lean_ctor_get(v_r_4577_, 2);
lean_dec(v_unused_4629_);
v_unused_4630_ = lean_ctor_get(v_r_4577_, 1);
lean_dec(v_unused_4630_);
v_unused_4631_ = lean_ctor_get(v_r_4577_, 0);
lean_dec(v_unused_4631_);
v___x_4599_ = v_r_4577_;
v_isShared_4600_ = v_isSharedCheck_4626_;
goto v_resetjp_4598_;
}
else
{
lean_dec(v_r_4577_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4626_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v___x_4614_; lean_object* v___y_4616_; 
v___x_4601_ = lean_nat_add(v___x_4571_, v_size_4573_);
lean_dec(v_size_4573_);
v___x_4602_ = lean_nat_add(v___x_4601_, v_size_4572_);
lean_dec(v___x_4601_);
v___x_4614_ = lean_nat_add(v___x_4571_, v_size_4589_);
if (lean_obj_tag(v_l_4593_) == 0)
{
lean_object* v_size_4624_; 
v_size_4624_ = lean_ctor_get(v_l_4593_, 0);
lean_inc(v_size_4624_);
v___y_4616_ = v_size_4624_;
goto v___jp_4615_;
}
else
{
lean_object* v___x_4625_; 
v___x_4625_ = lean_unsigned_to_nat(0u);
v___y_4616_ = v___x_4625_;
goto v___jp_4615_;
}
v___jp_4603_:
{
lean_object* v___x_4607_; lean_object* v___x_4609_; 
v___x_4607_ = lean_nat_add(v___y_4605_, v___y_4606_);
lean_dec(v___y_4606_);
lean_dec(v___y_4605_);
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 4, v_r_4565_);
lean_ctor_set(v___x_4599_, 3, v_r_4594_);
lean_ctor_set(v___x_4599_, 2, v_v_4563_);
lean_ctor_set(v___x_4599_, 1, v_k_4562_);
lean_ctor_set(v___x_4599_, 0, v___x_4607_);
v___x_4609_ = v___x_4599_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4607_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4613_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4613_, 3, v_r_4594_);
lean_ctor_set(v_reuseFailAlloc_4613_, 4, v_r_4565_);
v___x_4609_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4611_; 
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 4, v___x_4609_);
lean_ctor_set(v___x_4587_, 3, v___y_4604_);
lean_ctor_set(v___x_4587_, 2, v_v_4592_);
lean_ctor_set(v___x_4587_, 1, v_k_4591_);
lean_ctor_set(v___x_4587_, 0, v___x_4602_);
v___x_4611_ = v___x_4587_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4602_);
lean_ctor_set(v_reuseFailAlloc_4612_, 1, v_k_4591_);
lean_ctor_set(v_reuseFailAlloc_4612_, 2, v_v_4592_);
lean_ctor_set(v_reuseFailAlloc_4612_, 3, v___y_4604_);
lean_ctor_set(v_reuseFailAlloc_4612_, 4, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
v___jp_4615_:
{
lean_object* v___x_4617_; lean_object* v___x_4619_; 
v___x_4617_ = lean_nat_add(v___x_4614_, v___y_4616_);
lean_dec(v___y_4616_);
lean_dec(v___x_4614_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v_l_4593_);
lean_ctor_set(v___x_4567_, 3, v_l_4576_);
lean_ctor_set(v___x_4567_, 2, v_v_4575_);
lean_ctor_set(v___x_4567_, 1, v_k_4574_);
lean_ctor_set(v___x_4567_, 0, v___x_4617_);
v___x_4619_ = v___x_4567_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4617_);
lean_ctor_set(v_reuseFailAlloc_4623_, 1, v_k_4574_);
lean_ctor_set(v_reuseFailAlloc_4623_, 2, v_v_4575_);
lean_ctor_set(v_reuseFailAlloc_4623_, 3, v_l_4576_);
lean_ctor_set(v_reuseFailAlloc_4623_, 4, v_l_4593_);
v___x_4619_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
lean_object* v___x_4620_; 
v___x_4620_ = lean_nat_add(v___x_4571_, v_size_4572_);
if (lean_obj_tag(v_r_4594_) == 0)
{
lean_object* v_size_4621_; 
v_size_4621_ = lean_ctor_get(v_r_4594_, 0);
lean_inc(v_size_4621_);
v___y_4604_ = v___x_4619_;
v___y_4605_ = v___x_4620_;
v___y_4606_ = v_size_4621_;
goto v___jp_4603_;
}
else
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_unsigned_to_nat(0u);
v___y_4604_ = v___x_4619_;
v___y_4605_ = v___x_4620_;
v___y_4606_ = v___x_4622_;
goto v___jp_4603_;
}
}
}
}
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4637_; 
lean_del_object(v___x_4567_);
v___x_4632_ = lean_nat_add(v___x_4571_, v_size_4573_);
lean_dec(v_size_4573_);
v___x_4633_ = lean_nat_add(v___x_4632_, v_size_4572_);
lean_dec(v___x_4632_);
v___x_4634_ = lean_nat_add(v___x_4571_, v_size_4572_);
v___x_4635_ = lean_nat_add(v___x_4634_, v_size_4590_);
lean_dec(v___x_4634_);
lean_inc_ref(v_r_4565_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 4, v_r_4565_);
lean_ctor_set(v___x_4587_, 3, v_r_4577_);
lean_ctor_set(v___x_4587_, 2, v_v_4563_);
lean_ctor_set(v___x_4587_, 1, v_k_4562_);
lean_ctor_set(v___x_4587_, 0, v___x_4635_);
v___x_4637_ = v___x_4587_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4635_);
lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4650_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4650_, 3, v_r_4577_);
lean_ctor_set(v_reuseFailAlloc_4650_, 4, v_r_4565_);
v___x_4637_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
v_isSharedCheck_4644_ = !lean_is_exclusive(v_r_4565_);
if (v_isSharedCheck_4644_ == 0)
{
lean_object* v_unused_4645_; lean_object* v_unused_4646_; lean_object* v_unused_4647_; lean_object* v_unused_4648_; lean_object* v_unused_4649_; 
v_unused_4645_ = lean_ctor_get(v_r_4565_, 4);
lean_dec(v_unused_4645_);
v_unused_4646_ = lean_ctor_get(v_r_4565_, 3);
lean_dec(v_unused_4646_);
v_unused_4647_ = lean_ctor_get(v_r_4565_, 2);
lean_dec(v_unused_4647_);
v_unused_4648_ = lean_ctor_get(v_r_4565_, 1);
lean_dec(v_unused_4648_);
v_unused_4649_ = lean_ctor_get(v_r_4565_, 0);
lean_dec(v_unused_4649_);
v___x_4639_ = v_r_4565_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_dec(v_r_4565_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 4, v___x_4637_);
lean_ctor_set(v___x_4639_, 3, v_l_4576_);
lean_ctor_set(v___x_4639_, 2, v_v_4575_);
lean_ctor_set(v___x_4639_, 1, v_k_4574_);
lean_ctor_set(v___x_4639_, 0, v___x_4633_);
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v___x_4633_);
lean_ctor_set(v_reuseFailAlloc_4643_, 1, v_k_4574_);
lean_ctor_set(v_reuseFailAlloc_4643_, 2, v_v_4575_);
lean_ctor_set(v_reuseFailAlloc_4643_, 3, v_l_4576_);
lean_ctor_set(v_reuseFailAlloc_4643_, 4, v___x_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4657_; 
v_l_4657_ = lean_ctor_get(v_impl_4570_, 3);
lean_inc(v_l_4657_);
if (lean_obj_tag(v_l_4657_) == 0)
{
lean_object* v_r_4658_; lean_object* v_k_4659_; lean_object* v_v_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4671_; 
v_r_4658_ = lean_ctor_get(v_impl_4570_, 4);
v_k_4659_ = lean_ctor_get(v_impl_4570_, 1);
v_v_4660_ = lean_ctor_get(v_impl_4570_, 2);
v_isSharedCheck_4671_ = !lean_is_exclusive(v_impl_4570_);
if (v_isSharedCheck_4671_ == 0)
{
lean_object* v_unused_4672_; lean_object* v_unused_4673_; 
v_unused_4672_ = lean_ctor_get(v_impl_4570_, 3);
lean_dec(v_unused_4672_);
v_unused_4673_ = lean_ctor_get(v_impl_4570_, 0);
lean_dec(v_unused_4673_);
v___x_4662_ = v_impl_4570_;
v_isShared_4663_ = v_isSharedCheck_4671_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_r_4658_);
lean_inc(v_v_4660_);
lean_inc(v_k_4659_);
lean_dec(v_impl_4570_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4671_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4664_; lean_object* v___x_4666_; 
v___x_4664_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4658_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 3, v_r_4658_);
lean_ctor_set(v___x_4662_, 2, v_v_4563_);
lean_ctor_set(v___x_4662_, 1, v_k_4562_);
lean_ctor_set(v___x_4662_, 0, v___x_4571_);
v___x_4666_ = v___x_4662_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4571_);
lean_ctor_set(v_reuseFailAlloc_4670_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4670_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4670_, 3, v_r_4658_);
lean_ctor_set(v_reuseFailAlloc_4670_, 4, v_r_4658_);
v___x_4666_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
lean_object* v___x_4668_; 
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v___x_4666_);
lean_ctor_set(v___x_4567_, 3, v_l_4657_);
lean_ctor_set(v___x_4567_, 2, v_v_4660_);
lean_ctor_set(v___x_4567_, 1, v_k_4659_);
lean_ctor_set(v___x_4567_, 0, v___x_4664_);
v___x_4668_ = v___x_4567_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v___x_4664_);
lean_ctor_set(v_reuseFailAlloc_4669_, 1, v_k_4659_);
lean_ctor_set(v_reuseFailAlloc_4669_, 2, v_v_4660_);
lean_ctor_set(v_reuseFailAlloc_4669_, 3, v_l_4657_);
lean_ctor_set(v_reuseFailAlloc_4669_, 4, v___x_4666_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
else
{
lean_object* v_r_4674_; 
v_r_4674_ = lean_ctor_get(v_impl_4570_, 4);
lean_inc(v_r_4674_);
if (lean_obj_tag(v_r_4674_) == 0)
{
lean_object* v_k_4675_; lean_object* v_v_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4699_; 
v_k_4675_ = lean_ctor_get(v_impl_4570_, 1);
v_v_4676_ = lean_ctor_get(v_impl_4570_, 2);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_impl_4570_);
if (v_isSharedCheck_4699_ == 0)
{
lean_object* v_unused_4700_; lean_object* v_unused_4701_; lean_object* v_unused_4702_; 
v_unused_4700_ = lean_ctor_get(v_impl_4570_, 4);
lean_dec(v_unused_4700_);
v_unused_4701_ = lean_ctor_get(v_impl_4570_, 3);
lean_dec(v_unused_4701_);
v_unused_4702_ = lean_ctor_get(v_impl_4570_, 0);
lean_dec(v_unused_4702_);
v___x_4678_ = v_impl_4570_;
v_isShared_4679_ = v_isSharedCheck_4699_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_v_4676_);
lean_inc(v_k_4675_);
lean_dec(v_impl_4570_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4699_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v_k_4680_; lean_object* v_v_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4695_; 
v_k_4680_ = lean_ctor_get(v_r_4674_, 1);
v_v_4681_ = lean_ctor_get(v_r_4674_, 2);
v_isSharedCheck_4695_ = !lean_is_exclusive(v_r_4674_);
if (v_isSharedCheck_4695_ == 0)
{
lean_object* v_unused_4696_; lean_object* v_unused_4697_; lean_object* v_unused_4698_; 
v_unused_4696_ = lean_ctor_get(v_r_4674_, 4);
lean_dec(v_unused_4696_);
v_unused_4697_ = lean_ctor_get(v_r_4674_, 3);
lean_dec(v_unused_4697_);
v_unused_4698_ = lean_ctor_get(v_r_4674_, 0);
lean_dec(v_unused_4698_);
v___x_4683_ = v_r_4674_;
v_isShared_4684_ = v_isSharedCheck_4695_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_v_4681_);
lean_inc(v_k_4680_);
lean_dec(v_r_4674_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4695_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4685_; lean_object* v___x_4687_; 
v___x_4685_ = lean_unsigned_to_nat(3u);
if (v_isShared_4684_ == 0)
{
lean_ctor_set(v___x_4683_, 4, v_l_4657_);
lean_ctor_set(v___x_4683_, 3, v_l_4657_);
lean_ctor_set(v___x_4683_, 2, v_v_4676_);
lean_ctor_set(v___x_4683_, 1, v_k_4675_);
lean_ctor_set(v___x_4683_, 0, v___x_4571_);
v___x_4687_ = v___x_4683_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4571_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v_k_4675_);
lean_ctor_set(v_reuseFailAlloc_4694_, 2, v_v_4676_);
lean_ctor_set(v_reuseFailAlloc_4694_, 3, v_l_4657_);
lean_ctor_set(v_reuseFailAlloc_4694_, 4, v_l_4657_);
v___x_4687_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
lean_object* v___x_4689_; 
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 4, v_l_4657_);
lean_ctor_set(v___x_4678_, 2, v_v_4563_);
lean_ctor_set(v___x_4678_, 1, v_k_4562_);
lean_ctor_set(v___x_4678_, 0, v___x_4571_);
v___x_4689_ = v___x_4678_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4571_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4693_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4693_, 3, v_l_4657_);
lean_ctor_set(v_reuseFailAlloc_4693_, 4, v_l_4657_);
v___x_4689_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4691_; 
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v___x_4689_);
lean_ctor_set(v___x_4567_, 3, v___x_4687_);
lean_ctor_set(v___x_4567_, 2, v_v_4681_);
lean_ctor_set(v___x_4567_, 1, v_k_4680_);
lean_ctor_set(v___x_4567_, 0, v___x_4685_);
v___x_4691_ = v___x_4567_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4685_);
lean_ctor_set(v_reuseFailAlloc_4692_, 1, v_k_4680_);
lean_ctor_set(v_reuseFailAlloc_4692_, 2, v_v_4681_);
lean_ctor_set(v_reuseFailAlloc_4692_, 3, v___x_4687_);
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
}
}
}
else
{
lean_object* v___x_4703_; lean_object* v___x_4705_; 
v___x_4703_ = lean_unsigned_to_nat(2u);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v_r_4674_);
lean_ctor_set(v___x_4567_, 3, v_impl_4570_);
lean_ctor_set(v___x_4567_, 0, v___x_4703_);
v___x_4705_ = v___x_4567_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v___x_4703_);
lean_ctor_set(v_reuseFailAlloc_4706_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4706_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4706_, 3, v_impl_4570_);
lean_ctor_set(v_reuseFailAlloc_4706_, 4, v_r_4674_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4708_; 
lean_dec(v_v_4563_);
lean_dec(v_k_4562_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 2, v_v_4559_);
lean_ctor_set(v___x_4567_, 1, v_k_4558_);
v___x_4708_ = v___x_4567_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_size_4561_);
lean_ctor_set(v_reuseFailAlloc_4709_, 1, v_k_4558_);
lean_ctor_set(v_reuseFailAlloc_4709_, 2, v_v_4559_);
lean_ctor_set(v_reuseFailAlloc_4709_, 3, v_l_4564_);
lean_ctor_set(v_reuseFailAlloc_4709_, 4, v_r_4565_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
default: 
{
lean_object* v_impl_4710_; lean_object* v___x_4711_; 
lean_dec(v_size_4561_);
v_impl_4710_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4558_, v_v_4559_, v_r_4565_);
v___x_4711_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4564_) == 0)
{
lean_object* v_size_4712_; lean_object* v_size_4713_; lean_object* v_k_4714_; lean_object* v_v_4715_; lean_object* v_l_4716_; lean_object* v_r_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; uint8_t v___x_4720_; 
v_size_4712_ = lean_ctor_get(v_l_4564_, 0);
v_size_4713_ = lean_ctor_get(v_impl_4710_, 0);
lean_inc(v_size_4713_);
v_k_4714_ = lean_ctor_get(v_impl_4710_, 1);
lean_inc(v_k_4714_);
v_v_4715_ = lean_ctor_get(v_impl_4710_, 2);
lean_inc(v_v_4715_);
v_l_4716_ = lean_ctor_get(v_impl_4710_, 3);
lean_inc(v_l_4716_);
v_r_4717_ = lean_ctor_get(v_impl_4710_, 4);
lean_inc(v_r_4717_);
v___x_4718_ = lean_unsigned_to_nat(3u);
v___x_4719_ = lean_nat_mul(v___x_4718_, v_size_4712_);
v___x_4720_ = lean_nat_dec_lt(v___x_4719_, v_size_4713_);
lean_dec(v___x_4719_);
if (v___x_4720_ == 0)
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4724_; 
lean_dec(v_r_4717_);
lean_dec(v_l_4716_);
lean_dec(v_v_4715_);
lean_dec(v_k_4714_);
v___x_4721_ = lean_nat_add(v___x_4711_, v_size_4712_);
v___x_4722_ = lean_nat_add(v___x_4721_, v_size_4713_);
lean_dec(v_size_4713_);
lean_dec(v___x_4721_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v_impl_4710_);
lean_ctor_set(v___x_4567_, 0, v___x_4722_);
v___x_4724_ = v___x_4567_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4725_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4725_, 3, v_l_4564_);
lean_ctor_set(v_reuseFailAlloc_4725_, 4, v_impl_4710_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
else
{
lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4789_; 
v_isSharedCheck_4789_ = !lean_is_exclusive(v_impl_4710_);
if (v_isSharedCheck_4789_ == 0)
{
lean_object* v_unused_4790_; lean_object* v_unused_4791_; lean_object* v_unused_4792_; lean_object* v_unused_4793_; lean_object* v_unused_4794_; 
v_unused_4790_ = lean_ctor_get(v_impl_4710_, 4);
lean_dec(v_unused_4790_);
v_unused_4791_ = lean_ctor_get(v_impl_4710_, 3);
lean_dec(v_unused_4791_);
v_unused_4792_ = lean_ctor_get(v_impl_4710_, 2);
lean_dec(v_unused_4792_);
v_unused_4793_ = lean_ctor_get(v_impl_4710_, 1);
lean_dec(v_unused_4793_);
v_unused_4794_ = lean_ctor_get(v_impl_4710_, 0);
lean_dec(v_unused_4794_);
v___x_4727_ = v_impl_4710_;
v_isShared_4728_ = v_isSharedCheck_4789_;
goto v_resetjp_4726_;
}
else
{
lean_dec(v_impl_4710_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4789_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v_size_4729_; lean_object* v_k_4730_; lean_object* v_v_4731_; lean_object* v_l_4732_; lean_object* v_r_4733_; lean_object* v_size_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; 
v_size_4729_ = lean_ctor_get(v_l_4716_, 0);
v_k_4730_ = lean_ctor_get(v_l_4716_, 1);
v_v_4731_ = lean_ctor_get(v_l_4716_, 2);
v_l_4732_ = lean_ctor_get(v_l_4716_, 3);
v_r_4733_ = lean_ctor_get(v_l_4716_, 4);
v_size_4734_ = lean_ctor_get(v_r_4717_, 0);
v___x_4735_ = lean_unsigned_to_nat(2u);
v___x_4736_ = lean_nat_mul(v___x_4735_, v_size_4734_);
v___x_4737_ = lean_nat_dec_lt(v_size_4729_, v___x_4736_);
lean_dec(v___x_4736_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4765_; 
lean_inc(v_r_4733_);
lean_inc(v_l_4732_);
lean_inc(v_v_4731_);
lean_inc(v_k_4730_);
v_isSharedCheck_4765_ = !lean_is_exclusive(v_l_4716_);
if (v_isSharedCheck_4765_ == 0)
{
lean_object* v_unused_4766_; lean_object* v_unused_4767_; lean_object* v_unused_4768_; lean_object* v_unused_4769_; lean_object* v_unused_4770_; 
v_unused_4766_ = lean_ctor_get(v_l_4716_, 4);
lean_dec(v_unused_4766_);
v_unused_4767_ = lean_ctor_get(v_l_4716_, 3);
lean_dec(v_unused_4767_);
v_unused_4768_ = lean_ctor_get(v_l_4716_, 2);
lean_dec(v_unused_4768_);
v_unused_4769_ = lean_ctor_get(v_l_4716_, 1);
lean_dec(v_unused_4769_);
v_unused_4770_ = lean_ctor_get(v_l_4716_, 0);
lean_dec(v_unused_4770_);
v___x_4739_ = v_l_4716_;
v_isShared_4740_ = v_isSharedCheck_4765_;
goto v_resetjp_4738_;
}
else
{
lean_dec(v_l_4716_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4765_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___y_4744_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4755_; 
v___x_4741_ = lean_nat_add(v___x_4711_, v_size_4712_);
v___x_4742_ = lean_nat_add(v___x_4741_, v_size_4713_);
lean_dec(v_size_4713_);
if (lean_obj_tag(v_l_4732_) == 0)
{
lean_object* v_size_4763_; 
v_size_4763_ = lean_ctor_get(v_l_4732_, 0);
lean_inc(v_size_4763_);
v___y_4755_ = v_size_4763_;
goto v___jp_4754_;
}
else
{
lean_object* v___x_4764_; 
v___x_4764_ = lean_unsigned_to_nat(0u);
v___y_4755_ = v___x_4764_;
goto v___jp_4754_;
}
v___jp_4743_:
{
lean_object* v___x_4747_; lean_object* v___x_4749_; 
v___x_4747_ = lean_nat_add(v___y_4745_, v___y_4746_);
lean_dec(v___y_4746_);
lean_dec(v___y_4745_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 4, v_r_4717_);
lean_ctor_set(v___x_4739_, 3, v_r_4733_);
lean_ctor_set(v___x_4739_, 2, v_v_4715_);
lean_ctor_set(v___x_4739_, 1, v_k_4714_);
lean_ctor_set(v___x_4739_, 0, v___x_4747_);
v___x_4749_ = v___x_4739_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4747_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_k_4714_);
lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_v_4715_);
lean_ctor_set(v_reuseFailAlloc_4753_, 3, v_r_4733_);
lean_ctor_set(v_reuseFailAlloc_4753_, 4, v_r_4717_);
v___x_4749_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4751_; 
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 4, v___x_4749_);
lean_ctor_set(v___x_4727_, 3, v___y_4744_);
lean_ctor_set(v___x_4727_, 2, v_v_4731_);
lean_ctor_set(v___x_4727_, 1, v_k_4730_);
lean_ctor_set(v___x_4727_, 0, v___x_4742_);
v___x_4751_ = v___x_4727_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4742_);
lean_ctor_set(v_reuseFailAlloc_4752_, 1, v_k_4730_);
lean_ctor_set(v_reuseFailAlloc_4752_, 2, v_v_4731_);
lean_ctor_set(v_reuseFailAlloc_4752_, 3, v___y_4744_);
lean_ctor_set(v_reuseFailAlloc_4752_, 4, v___x_4749_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
v___jp_4754_:
{
lean_object* v___x_4756_; lean_object* v___x_4758_; 
v___x_4756_ = lean_nat_add(v___x_4741_, v___y_4755_);
lean_dec(v___y_4755_);
lean_dec(v___x_4741_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v_l_4732_);
lean_ctor_set(v___x_4567_, 0, v___x_4756_);
v___x_4758_ = v___x_4567_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4756_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4762_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4762_, 3, v_l_4564_);
lean_ctor_set(v_reuseFailAlloc_4762_, 4, v_l_4732_);
v___x_4758_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
lean_object* v___x_4759_; 
v___x_4759_ = lean_nat_add(v___x_4711_, v_size_4734_);
if (lean_obj_tag(v_r_4733_) == 0)
{
lean_object* v_size_4760_; 
v_size_4760_ = lean_ctor_get(v_r_4733_, 0);
lean_inc(v_size_4760_);
v___y_4744_ = v___x_4758_;
v___y_4745_ = v___x_4759_;
v___y_4746_ = v_size_4760_;
goto v___jp_4743_;
}
else
{
lean_object* v___x_4761_; 
v___x_4761_ = lean_unsigned_to_nat(0u);
v___y_4744_ = v___x_4758_;
v___y_4745_ = v___x_4759_;
v___y_4746_ = v___x_4761_;
goto v___jp_4743_;
}
}
}
}
}
else
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4775_; 
lean_del_object(v___x_4567_);
v___x_4771_ = lean_nat_add(v___x_4711_, v_size_4712_);
v___x_4772_ = lean_nat_add(v___x_4771_, v_size_4713_);
lean_dec(v_size_4713_);
v___x_4773_ = lean_nat_add(v___x_4771_, v_size_4729_);
lean_dec(v___x_4771_);
lean_inc_ref(v_l_4564_);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 4, v_l_4716_);
lean_ctor_set(v___x_4727_, 3, v_l_4564_);
lean_ctor_set(v___x_4727_, 2, v_v_4563_);
lean_ctor_set(v___x_4727_, 1, v_k_4562_);
lean_ctor_set(v___x_4727_, 0, v___x_4773_);
v___x_4775_ = v___x_4727_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4773_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4788_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4788_, 3, v_l_4564_);
lean_ctor_set(v_reuseFailAlloc_4788_, 4, v_l_4716_);
v___x_4775_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4782_; 
v_isSharedCheck_4782_ = !lean_is_exclusive(v_l_4564_);
if (v_isSharedCheck_4782_ == 0)
{
lean_object* v_unused_4783_; lean_object* v_unused_4784_; lean_object* v_unused_4785_; lean_object* v_unused_4786_; lean_object* v_unused_4787_; 
v_unused_4783_ = lean_ctor_get(v_l_4564_, 4);
lean_dec(v_unused_4783_);
v_unused_4784_ = lean_ctor_get(v_l_4564_, 3);
lean_dec(v_unused_4784_);
v_unused_4785_ = lean_ctor_get(v_l_4564_, 2);
lean_dec(v_unused_4785_);
v_unused_4786_ = lean_ctor_get(v_l_4564_, 1);
lean_dec(v_unused_4786_);
v_unused_4787_ = lean_ctor_get(v_l_4564_, 0);
lean_dec(v_unused_4787_);
v___x_4777_ = v_l_4564_;
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
else
{
lean_dec(v_l_4564_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 4, v_r_4717_);
lean_ctor_set(v___x_4777_, 3, v___x_4775_);
lean_ctor_set(v___x_4777_, 2, v_v_4715_);
lean_ctor_set(v___x_4777_, 1, v_k_4714_);
lean_ctor_set(v___x_4777_, 0, v___x_4772_);
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4772_);
lean_ctor_set(v_reuseFailAlloc_4781_, 1, v_k_4714_);
lean_ctor_set(v_reuseFailAlloc_4781_, 2, v_v_4715_);
lean_ctor_set(v_reuseFailAlloc_4781_, 3, v___x_4775_);
lean_ctor_set(v_reuseFailAlloc_4781_, 4, v_r_4717_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4795_; 
v_l_4795_ = lean_ctor_get(v_impl_4710_, 3);
lean_inc(v_l_4795_);
if (lean_obj_tag(v_l_4795_) == 0)
{
lean_object* v_r_4796_; lean_object* v_k_4797_; lean_object* v_v_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4821_; 
v_r_4796_ = lean_ctor_get(v_impl_4710_, 4);
v_k_4797_ = lean_ctor_get(v_impl_4710_, 1);
v_v_4798_ = lean_ctor_get(v_impl_4710_, 2);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_impl_4710_);
if (v_isSharedCheck_4821_ == 0)
{
lean_object* v_unused_4822_; lean_object* v_unused_4823_; 
v_unused_4822_ = lean_ctor_get(v_impl_4710_, 3);
lean_dec(v_unused_4822_);
v_unused_4823_ = lean_ctor_get(v_impl_4710_, 0);
lean_dec(v_unused_4823_);
v___x_4800_ = v_impl_4710_;
v_isShared_4801_ = v_isSharedCheck_4821_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_r_4796_);
lean_inc(v_v_4798_);
lean_inc(v_k_4797_);
lean_dec(v_impl_4710_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4821_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v_k_4802_; lean_object* v_v_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4817_; 
v_k_4802_ = lean_ctor_get(v_l_4795_, 1);
v_v_4803_ = lean_ctor_get(v_l_4795_, 2);
v_isSharedCheck_4817_ = !lean_is_exclusive(v_l_4795_);
if (v_isSharedCheck_4817_ == 0)
{
lean_object* v_unused_4818_; lean_object* v_unused_4819_; lean_object* v_unused_4820_; 
v_unused_4818_ = lean_ctor_get(v_l_4795_, 4);
lean_dec(v_unused_4818_);
v_unused_4819_ = lean_ctor_get(v_l_4795_, 3);
lean_dec(v_unused_4819_);
v_unused_4820_ = lean_ctor_get(v_l_4795_, 0);
lean_dec(v_unused_4820_);
v___x_4805_ = v_l_4795_;
v_isShared_4806_ = v_isSharedCheck_4817_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_v_4803_);
lean_inc(v_k_4802_);
lean_dec(v_l_4795_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4817_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4807_; lean_object* v___x_4809_; 
v___x_4807_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4796_, 2);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 4, v_r_4796_);
lean_ctor_set(v___x_4805_, 3, v_r_4796_);
lean_ctor_set(v___x_4805_, 2, v_v_4563_);
lean_ctor_set(v___x_4805_, 1, v_k_4562_);
lean_ctor_set(v___x_4805_, 0, v___x_4711_);
v___x_4809_ = v___x_4805_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4711_);
lean_ctor_set(v_reuseFailAlloc_4816_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4816_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4816_, 3, v_r_4796_);
lean_ctor_set(v_reuseFailAlloc_4816_, 4, v_r_4796_);
v___x_4809_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
lean_object* v___x_4811_; 
lean_inc(v_r_4796_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 3, v_r_4796_);
lean_ctor_set(v___x_4800_, 0, v___x_4711_);
v___x_4811_ = v___x_4800_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4711_);
lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_k_4797_);
lean_ctor_set(v_reuseFailAlloc_4815_, 2, v_v_4798_);
lean_ctor_set(v_reuseFailAlloc_4815_, 3, v_r_4796_);
lean_ctor_set(v_reuseFailAlloc_4815_, 4, v_r_4796_);
v___x_4811_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
lean_object* v___x_4813_; 
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v___x_4811_);
lean_ctor_set(v___x_4567_, 3, v___x_4809_);
lean_ctor_set(v___x_4567_, 2, v_v_4803_);
lean_ctor_set(v___x_4567_, 1, v_k_4802_);
lean_ctor_set(v___x_4567_, 0, v___x_4807_);
v___x_4813_ = v___x_4567_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4807_);
lean_ctor_set(v_reuseFailAlloc_4814_, 1, v_k_4802_);
lean_ctor_set(v_reuseFailAlloc_4814_, 2, v_v_4803_);
lean_ctor_set(v_reuseFailAlloc_4814_, 3, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4814_, 4, v___x_4811_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
}
}
else
{
lean_object* v_r_4824_; 
v_r_4824_ = lean_ctor_get(v_impl_4710_, 4);
lean_inc(v_r_4824_);
if (lean_obj_tag(v_r_4824_) == 0)
{
lean_object* v_k_4825_; lean_object* v_v_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4837_; 
v_k_4825_ = lean_ctor_get(v_impl_4710_, 1);
v_v_4826_ = lean_ctor_get(v_impl_4710_, 2);
v_isSharedCheck_4837_ = !lean_is_exclusive(v_impl_4710_);
if (v_isSharedCheck_4837_ == 0)
{
lean_object* v_unused_4838_; lean_object* v_unused_4839_; lean_object* v_unused_4840_; 
v_unused_4838_ = lean_ctor_get(v_impl_4710_, 4);
lean_dec(v_unused_4838_);
v_unused_4839_ = lean_ctor_get(v_impl_4710_, 3);
lean_dec(v_unused_4839_);
v_unused_4840_ = lean_ctor_get(v_impl_4710_, 0);
lean_dec(v_unused_4840_);
v___x_4828_ = v_impl_4710_;
v_isShared_4829_ = v_isSharedCheck_4837_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_v_4826_);
lean_inc(v_k_4825_);
lean_dec(v_impl_4710_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4837_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4830_; lean_object* v___x_4832_; 
v___x_4830_ = lean_unsigned_to_nat(3u);
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 4, v_l_4795_);
lean_ctor_set(v___x_4828_, 2, v_v_4563_);
lean_ctor_set(v___x_4828_, 1, v_k_4562_);
lean_ctor_set(v___x_4828_, 0, v___x_4711_);
v___x_4832_ = v___x_4828_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4711_);
lean_ctor_set(v_reuseFailAlloc_4836_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4836_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4836_, 3, v_l_4795_);
lean_ctor_set(v_reuseFailAlloc_4836_, 4, v_l_4795_);
v___x_4832_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
lean_object* v___x_4834_; 
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v_r_4824_);
lean_ctor_set(v___x_4567_, 3, v___x_4832_);
lean_ctor_set(v___x_4567_, 2, v_v_4826_);
lean_ctor_set(v___x_4567_, 1, v_k_4825_);
lean_ctor_set(v___x_4567_, 0, v___x_4830_);
v___x_4834_ = v___x_4567_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4830_);
lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_k_4825_);
lean_ctor_set(v_reuseFailAlloc_4835_, 2, v_v_4826_);
lean_ctor_set(v_reuseFailAlloc_4835_, 3, v___x_4832_);
lean_ctor_set(v_reuseFailAlloc_4835_, 4, v_r_4824_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
else
{
lean_object* v___x_4841_; lean_object* v___x_4843_; 
v___x_4841_ = lean_unsigned_to_nat(2u);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 4, v_impl_4710_);
lean_ctor_set(v___x_4567_, 3, v_r_4824_);
lean_ctor_set(v___x_4567_, 0, v___x_4841_);
v___x_4843_ = v___x_4567_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v___x_4841_);
lean_ctor_set(v_reuseFailAlloc_4844_, 1, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4844_, 2, v_v_4563_);
lean_ctor_set(v_reuseFailAlloc_4844_, 3, v_r_4824_);
lean_ctor_set(v_reuseFailAlloc_4844_, 4, v_impl_4710_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
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
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = lean_unsigned_to_nat(1u);
v___x_4847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
lean_ctor_set(v___x_4847_, 1, v_k_4558_);
lean_ctor_set(v___x_4847_, 2, v_v_4559_);
lean_ctor_set(v___x_4847_, 3, v_t_4560_);
lean_ctor_set(v___x_4847_, 4, v_t_4560_);
return v___x_4847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object* v_as_4848_, size_t v_sz_4849_, size_t v_i_4850_, lean_object* v_b_4851_){
_start:
{
uint8_t v___x_4852_; 
v___x_4852_ = lean_usize_dec_lt(v_i_4850_, v_sz_4849_);
if (v___x_4852_ == 0)
{
return v_b_4851_;
}
else
{
lean_object* v_a_4853_; lean_object* v_fst_4854_; lean_object* v_snd_4855_; lean_object* v_r_4856_; size_t v___x_4857_; size_t v___x_4858_; 
v_a_4853_ = lean_array_uget_borrowed(v_as_4848_, v_i_4850_);
v_fst_4854_ = lean_ctor_get(v_a_4853_, 0);
v_snd_4855_ = lean_ctor_get(v_a_4853_, 1);
lean_inc(v_snd_4855_);
lean_inc(v_fst_4854_);
v_r_4856_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_fst_4854_, v_snd_4855_, v_b_4851_);
v___x_4857_ = ((size_t)1ULL);
v___x_4858_ = lean_usize_add(v_i_4850_, v___x_4857_);
v_i_4850_ = v___x_4858_;
v_b_4851_ = v_r_4856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object* v_as_4860_, lean_object* v_sz_4861_, lean_object* v_i_4862_, lean_object* v_b_4863_){
_start:
{
size_t v_sz_boxed_4864_; size_t v_i_boxed_4865_; lean_object* v_res_4866_; 
v_sz_boxed_4864_ = lean_unbox_usize(v_sz_4861_);
lean_dec(v_sz_4861_);
v_i_boxed_4865_ = lean_unbox_usize(v_i_4862_);
lean_dec(v_i_4862_);
v_res_4866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v_as_4860_, v_sz_boxed_4864_, v_i_boxed_4865_, v_b_4863_);
lean_dec_ref(v_as_4860_);
return v_res_4866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object* v_a_4869_, lean_object* v_x_4870_){
_start:
{
lean_object* v___y_4872_; 
if (lean_obj_tag(v_x_4870_) == 0)
{
lean_object* v___x_4875_; 
v___x_4875_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___y_4872_ = v___x_4875_;
goto v___jp_4871_;
}
else
{
lean_object* v_val_4876_; 
v_val_4876_ = lean_ctor_get(v_x_4870_, 0);
lean_inc(v_val_4876_);
lean_dec_ref(v_x_4870_);
v___y_4872_ = v_val_4876_;
goto v___jp_4871_;
}
v___jp_4871_:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_array_push(v___y_4872_, v_a_4869_);
v___x_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
return v___x_4874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_x_4879_){
_start:
{
if (lean_obj_tag(v_x_4879_) == 0)
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v_val_4882_; lean_object* v___x_4883_; 
v___x_4880_ = lean_box(0);
v___x_4881_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4877_, v___x_4880_);
v_val_4882_ = lean_ctor_get(v___x_4881_, 0);
lean_inc(v_val_4882_);
lean_dec(v___x_4881_);
v___x_4883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4883_, 0, v_a_4878_);
lean_ctor_set(v___x_4883_, 1, v_val_4882_);
lean_ctor_set(v___x_4883_, 2, v_x_4879_);
return v___x_4883_;
}
else
{
lean_object* v_key_4884_; lean_object* v_value_4885_; lean_object* v_tail_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4901_; 
v_key_4884_ = lean_ctor_get(v_x_4879_, 0);
v_value_4885_ = lean_ctor_get(v_x_4879_, 1);
v_tail_4886_ = lean_ctor_get(v_x_4879_, 2);
v_isSharedCheck_4901_ = !lean_is_exclusive(v_x_4879_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4888_ = v_x_4879_;
v_isShared_4889_ = v_isSharedCheck_4901_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_tail_4886_);
lean_inc(v_value_4885_);
lean_inc(v_key_4884_);
lean_dec(v_x_4879_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4901_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
uint8_t v___x_4890_; 
v___x_4890_ = lean_name_eq(v_key_4884_, v_a_4878_);
if (v___x_4890_ == 0)
{
lean_object* v_tail_4891_; lean_object* v___x_4893_; 
v_tail_4891_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4877_, v_a_4878_, v_tail_4886_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 2, v_tail_4891_);
v___x_4893_ = v___x_4888_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_key_4884_);
lean_ctor_set(v_reuseFailAlloc_4894_, 1, v_value_4885_);
lean_ctor_set(v_reuseFailAlloc_4894_, 2, v_tail_4891_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
else
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v_val_4897_; lean_object* v___x_4899_; 
lean_dec(v_key_4884_);
v___x_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4895_, 0, v_value_4885_);
v___x_4896_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4877_, v___x_4895_);
v_val_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc(v_val_4897_);
lean_dec(v___x_4896_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 1, v_val_4897_);
lean_ctor_set(v___x_4888_, 0, v_a_4878_);
v___x_4899_ = v___x_4888_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v_a_4878_);
lean_ctor_set(v_reuseFailAlloc_4900_, 1, v_val_4897_);
lean_ctor_set(v_reuseFailAlloc_4900_, 2, v_tail_4886_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_4902_; uint64_t v___x_4903_; 
v___x_4902_ = lean_unsigned_to_nat(1723u);
v___x_4903_ = lean_uint64_of_nat(v___x_4902_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_4904_, lean_object* v_x_4905_){
_start:
{
if (lean_obj_tag(v_x_4905_) == 0)
{
return v_x_4904_;
}
else
{
lean_object* v_key_4906_; lean_object* v_value_4907_; lean_object* v_tail_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4934_; 
v_key_4906_ = lean_ctor_get(v_x_4905_, 0);
v_value_4907_ = lean_ctor_get(v_x_4905_, 1);
v_tail_4908_ = lean_ctor_get(v_x_4905_, 2);
v_isSharedCheck_4934_ = !lean_is_exclusive(v_x_4905_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4910_ = v_x_4905_;
v_isShared_4911_ = v_isSharedCheck_4934_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_tail_4908_);
lean_inc(v_value_4907_);
lean_inc(v_key_4906_);
lean_dec(v_x_4905_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4934_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4912_; uint64_t v___y_4914_; 
v___x_4912_ = lean_array_get_size(v_x_4904_);
if (lean_obj_tag(v_key_4906_) == 0)
{
uint64_t v___x_4932_; 
v___x_4932_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0);
v___y_4914_ = v___x_4932_;
goto v___jp_4913_;
}
else
{
uint64_t v_hash_4933_; 
v_hash_4933_ = lean_ctor_get_uint64(v_key_4906_, sizeof(void*)*2);
v___y_4914_ = v_hash_4933_;
goto v___jp_4913_;
}
v___jp_4913_:
{
uint64_t v___x_4915_; uint64_t v___x_4916_; uint64_t v_fold_4917_; uint64_t v___x_4918_; uint64_t v___x_4919_; uint64_t v___x_4920_; size_t v___x_4921_; size_t v___x_4922_; size_t v___x_4923_; size_t v___x_4924_; size_t v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4928_; 
v___x_4915_ = 32ULL;
v___x_4916_ = lean_uint64_shift_right(v___y_4914_, v___x_4915_);
v_fold_4917_ = lean_uint64_xor(v___y_4914_, v___x_4916_);
v___x_4918_ = 16ULL;
v___x_4919_ = lean_uint64_shift_right(v_fold_4917_, v___x_4918_);
v___x_4920_ = lean_uint64_xor(v_fold_4917_, v___x_4919_);
v___x_4921_ = lean_uint64_to_usize(v___x_4920_);
v___x_4922_ = lean_usize_of_nat(v___x_4912_);
v___x_4923_ = ((size_t)1ULL);
v___x_4924_ = lean_usize_sub(v___x_4922_, v___x_4923_);
v___x_4925_ = lean_usize_land(v___x_4921_, v___x_4924_);
v___x_4926_ = lean_array_uget_borrowed(v_x_4904_, v___x_4925_);
lean_inc(v___x_4926_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 2, v___x_4926_);
v___x_4928_ = v___x_4910_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_key_4906_);
lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_value_4907_);
lean_ctor_set(v_reuseFailAlloc_4931_, 2, v___x_4926_);
v___x_4928_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
lean_object* v___x_4929_; 
v___x_4929_ = lean_array_uset(v_x_4904_, v___x_4925_, v___x_4928_);
v_x_4904_ = v___x_4929_;
v_x_4905_ = v_tail_4908_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object* v_i_4935_, lean_object* v_source_4936_, lean_object* v_target_4937_){
_start:
{
lean_object* v___x_4938_; uint8_t v___x_4939_; 
v___x_4938_ = lean_array_get_size(v_source_4936_);
v___x_4939_ = lean_nat_dec_lt(v_i_4935_, v___x_4938_);
if (v___x_4939_ == 0)
{
lean_dec_ref(v_source_4936_);
lean_dec(v_i_4935_);
return v_target_4937_;
}
else
{
lean_object* v_es_4940_; lean_object* v___x_4941_; lean_object* v_source_4942_; lean_object* v_target_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
v_es_4940_ = lean_array_fget(v_source_4936_, v_i_4935_);
v___x_4941_ = lean_box(0);
v_source_4942_ = lean_array_fset(v_source_4936_, v_i_4935_, v___x_4941_);
v_target_4943_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_target_4937_, v_es_4940_);
v___x_4944_ = lean_unsigned_to_nat(1u);
v___x_4945_ = lean_nat_add(v_i_4935_, v___x_4944_);
lean_dec(v_i_4935_);
v_i_4935_ = v___x_4945_;
v_source_4936_ = v_source_4942_;
v_target_4937_ = v_target_4943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object* v_data_4947_){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v_nbuckets_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4948_ = lean_array_get_size(v_data_4947_);
v___x_4949_ = lean_unsigned_to_nat(2u);
v_nbuckets_4950_ = lean_nat_mul(v___x_4948_, v___x_4949_);
v___x_4951_ = lean_unsigned_to_nat(0u);
v___x_4952_ = lean_box(0);
v___x_4953_ = lean_mk_array(v_nbuckets_4950_, v___x_4952_);
v___x_4954_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_4951_, v_data_4947_, v___x_4953_);
return v___x_4954_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_4955_, lean_object* v_x_4956_){
_start:
{
if (lean_obj_tag(v_x_4956_) == 0)
{
uint8_t v___x_4957_; 
v___x_4957_ = 0;
return v___x_4957_;
}
else
{
lean_object* v_key_4958_; lean_object* v_tail_4959_; uint8_t v___x_4960_; 
v_key_4958_ = lean_ctor_get(v_x_4956_, 0);
v_tail_4959_ = lean_ctor_get(v_x_4956_, 2);
v___x_4960_ = lean_name_eq(v_key_4958_, v_a_4955_);
if (v___x_4960_ == 0)
{
v_x_4956_ = v_tail_4959_;
goto _start;
}
else
{
return v___x_4960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_4962_, lean_object* v_x_4963_){
_start:
{
uint8_t v_res_4964_; lean_object* v_r_4965_; 
v_res_4964_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_4962_, v_x_4963_);
lean_dec(v_x_4963_);
lean_dec(v_a_4962_);
v_r_4965_ = lean_box(v_res_4964_);
return v_r_4965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_4966_, lean_object* v_m_4967_, lean_object* v_a_4968_){
_start:
{
lean_object* v___y_4970_; size_t v___y_4971_; lean_object* v___y_4972_; lean_object* v___y_4973_; lean_object* v_size_4976_; lean_object* v_buckets_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_5024_; 
v_size_4976_ = lean_ctor_get(v_m_4967_, 0);
v_buckets_4977_ = lean_ctor_get(v_m_4967_, 1);
v_isSharedCheck_5024_ = !lean_is_exclusive(v_m_4967_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_4979_ = v_m_4967_;
v_isShared_4980_ = v_isSharedCheck_5024_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_buckets_4977_);
lean_inc(v_size_4976_);
lean_dec(v_m_4967_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_5024_;
goto v_resetjp_4978_;
}
v___jp_4969_:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4974_ = lean_array_uset(v___y_4970_, v___y_4971_, v___y_4972_);
v___x_4975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4975_, 0, v___y_4973_);
lean_ctor_set(v___x_4975_, 1, v___x_4974_);
return v___x_4975_;
}
v_resetjp_4978_:
{
lean_object* v___x_4981_; uint64_t v___y_4983_; 
v___x_4981_ = lean_array_get_size(v_buckets_4977_);
if (lean_obj_tag(v_a_4968_) == 0)
{
uint64_t v___x_5022_; 
v___x_5022_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0);
v___y_4983_ = v___x_5022_;
goto v___jp_4982_;
}
else
{
uint64_t v_hash_5023_; 
v_hash_5023_ = lean_ctor_get_uint64(v_a_4968_, sizeof(void*)*2);
v___y_4983_ = v_hash_5023_;
goto v___jp_4982_;
}
v___jp_4982_:
{
uint64_t v___x_4984_; uint64_t v___x_4985_; uint64_t v_fold_4986_; uint64_t v___x_4987_; uint64_t v___x_4988_; uint64_t v___x_4989_; size_t v___x_4990_; size_t v___x_4991_; size_t v___x_4992_; size_t v___x_4993_; size_t v___x_4994_; lean_object* v_bkt_4995_; uint8_t v___x_4996_; 
v___x_4984_ = 32ULL;
v___x_4985_ = lean_uint64_shift_right(v___y_4983_, v___x_4984_);
v_fold_4986_ = lean_uint64_xor(v___y_4983_, v___x_4985_);
v___x_4987_ = 16ULL;
v___x_4988_ = lean_uint64_shift_right(v_fold_4986_, v___x_4987_);
v___x_4989_ = lean_uint64_xor(v_fold_4986_, v___x_4988_);
v___x_4990_ = lean_uint64_to_usize(v___x_4989_);
v___x_4991_ = lean_usize_of_nat(v___x_4981_);
v___x_4992_ = ((size_t)1ULL);
v___x_4993_ = lean_usize_sub(v___x_4991_, v___x_4992_);
v___x_4994_ = lean_usize_land(v___x_4990_, v___x_4993_);
v_bkt_4995_ = lean_array_uget_borrowed(v_buckets_4977_, v___x_4994_);
v___x_4996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_4968_, v_bkt_4995_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v_size_x27_5000_; lean_object* v___x_5001_; lean_object* v_buckets_x27_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; uint8_t v___x_5008_; 
v___x_4997_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_4998_ = lean_array_push(v___x_4997_, v_a_4966_);
v___x_4999_ = lean_unsigned_to_nat(1u);
v_size_x27_5000_ = lean_nat_add(v_size_4976_, v___x_4999_);
lean_dec(v_size_4976_);
lean_inc(v_bkt_4995_);
v___x_5001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5001_, 0, v_a_4968_);
lean_ctor_set(v___x_5001_, 1, v___x_4998_);
lean_ctor_set(v___x_5001_, 2, v_bkt_4995_);
v_buckets_x27_5002_ = lean_array_uset(v_buckets_4977_, v___x_4994_, v___x_5001_);
v___x_5003_ = lean_unsigned_to_nat(4u);
v___x_5004_ = lean_nat_mul(v_size_x27_5000_, v___x_5003_);
v___x_5005_ = lean_unsigned_to_nat(3u);
v___x_5006_ = lean_nat_div(v___x_5004_, v___x_5005_);
lean_dec(v___x_5004_);
v___x_5007_ = lean_array_get_size(v_buckets_x27_5002_);
v___x_5008_ = lean_nat_dec_le(v___x_5006_, v___x_5007_);
lean_dec(v___x_5006_);
if (v___x_5008_ == 0)
{
lean_object* v_val_5009_; lean_object* v___x_5011_; 
v_val_5009_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5002_);
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 1, v_val_5009_);
lean_ctor_set(v___x_4979_, 0, v_size_x27_5000_);
v___x_5011_ = v___x_4979_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_size_x27_5000_);
lean_ctor_set(v_reuseFailAlloc_5012_, 1, v_val_5009_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
else
{
lean_object* v___x_5014_; 
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 1, v_buckets_x27_5002_);
lean_ctor_set(v___x_4979_, 0, v_size_x27_5000_);
v___x_5014_ = v___x_4979_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_size_x27_5000_);
lean_ctor_set(v_reuseFailAlloc_5015_, 1, v_buckets_x27_5002_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
else
{
lean_object* v___x_5016_; lean_object* v_buckets_x27_5017_; lean_object* v_bkt_x27_5018_; uint8_t v___x_5019_; 
lean_inc(v_bkt_4995_);
lean_del_object(v___x_4979_);
v___x_5016_ = lean_box(0);
v_buckets_x27_5017_ = lean_array_uset(v_buckets_4977_, v___x_4994_, v___x_5016_);
lean_inc(v_a_4968_);
v_bkt_x27_5018_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4966_, v_a_4968_, v_bkt_4995_);
v___x_5019_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_4968_, v_bkt_x27_5018_);
lean_dec(v_a_4968_);
if (v___x_5019_ == 0)
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = lean_unsigned_to_nat(1u);
v___x_5021_ = lean_nat_sub(v_size_4976_, v___x_5020_);
lean_dec(v_size_4976_);
v___y_4970_ = v_buckets_x27_5017_;
v___y_4971_ = v___x_4994_;
v___y_4972_ = v_bkt_x27_5018_;
v___y_4973_ = v___x_5021_;
goto v___jp_4969_;
}
else
{
v___y_4970_ = v_buckets_x27_5017_;
v___y_4971_ = v___x_4994_;
v___y_4972_ = v_bkt_x27_5018_;
v___y_4973_ = v_size_4976_;
goto v___jp_4969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5025_, lean_object* v_as_5026_, size_t v_sz_5027_, size_t v_i_5028_, lean_object* v_b_5029_){
_start:
{
uint8_t v___x_5030_; 
v___x_5030_ = lean_usize_dec_lt(v_i_5028_, v_sz_5027_);
if (v___x_5030_ == 0)
{
lean_dec_ref(v_key_5025_);
return v_b_5029_;
}
else
{
lean_object* v_a_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; size_t v___x_5034_; size_t v___x_5035_; 
v_a_5031_ = lean_array_uget_borrowed(v_as_5026_, v_i_5028_);
lean_inc_ref(v_key_5025_);
lean_inc_n(v_a_5031_, 2);
v___x_5032_ = lean_apply_1(v_key_5025_, v_a_5031_);
v___x_5033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5031_, v_b_5029_, v___x_5032_);
v___x_5034_ = ((size_t)1ULL);
v___x_5035_ = lean_usize_add(v_i_5028_, v___x_5034_);
v_i_5028_ = v___x_5035_;
v_b_5029_ = v___x_5033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5037_, lean_object* v_as_5038_, lean_object* v_sz_5039_, lean_object* v_i_5040_, lean_object* v_b_5041_){
_start:
{
size_t v_sz_boxed_5042_; size_t v_i_boxed_5043_; lean_object* v_res_5044_; 
v_sz_boxed_5042_ = lean_unbox_usize(v_sz_5039_);
lean_dec(v_sz_5039_);
v_i_boxed_5043_ = lean_unbox_usize(v_i_5040_);
lean_dec(v_i_5040_);
v_res_5044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5037_, v_as_5038_, v_sz_boxed_5042_, v_i_boxed_5043_, v_b_5041_);
lean_dec_ref(v_as_5038_);
return v_res_5044_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5045_ = lean_box(0);
v___x_5046_ = lean_unsigned_to_nat(16u);
v___x_5047_ = lean_mk_array(v___x_5046_, v___x_5045_);
return v___x_5047_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v_groups_5050_; 
v___x_5048_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5049_ = lean_unsigned_to_nat(0u);
v_groups_5050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5050_, 0, v___x_5049_);
lean_ctor_set(v_groups_5050_, 1, v___x_5048_);
return v_groups_5050_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5051_, lean_object* v_xs_5052_){
_start:
{
lean_object* v_groups_5053_; size_t v_sz_5054_; size_t v___x_5055_; lean_object* v___x_5056_; 
v_groups_5053_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5054_ = lean_array_size(v_xs_5052_);
v___x_5055_ = ((size_t)0ULL);
v___x_5056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5051_, v_xs_5052_, v_sz_5054_, v___x_5055_, v_groups_5053_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5057_, lean_object* v_xs_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5057_, v_xs_5058_);
lean_dec_ref(v_xs_5058_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5061_){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5063_ = lean_unsigned_to_nat(0u);
v___x_5064_ = lean_array_get_size(v_infos_5061_);
v___x_5065_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5061_, v___x_5063_, v___x_5064_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5094_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5068_ = v___x_5065_;
v_isShared_5069_ = v_isSharedCheck_5094_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_a_5066_);
lean_dec(v___x_5065_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5094_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___y_5071_; lean_object* v___f_5080_; lean_object* v___x_5081_; lean_object* v_size_5082_; lean_object* v_buckets_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; uint8_t v___x_5086_; 
v___f_5080_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5081_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5080_, v_a_5066_);
v_size_5082_ = lean_ctor_get(v___x_5081_, 0);
lean_inc(v_size_5082_);
v_buckets_5083_ = lean_ctor_get(v___x_5081_, 1);
lean_inc_ref(v_buckets_5083_);
lean_dec_ref(v___x_5081_);
v___x_5084_ = lean_mk_empty_array_with_capacity(v_size_5082_);
lean_dec(v_size_5082_);
v___x_5085_ = lean_array_get_size(v_buckets_5083_);
v___x_5086_ = lean_nat_dec_lt(v___x_5063_, v___x_5085_);
if (v___x_5086_ == 0)
{
lean_dec_ref(v_buckets_5083_);
v___y_5071_ = v___x_5084_;
goto v___jp_5070_;
}
else
{
uint8_t v___x_5087_; 
v___x_5087_ = lean_nat_dec_le(v___x_5085_, v___x_5085_);
if (v___x_5087_ == 0)
{
if (v___x_5086_ == 0)
{
lean_dec_ref(v_buckets_5083_);
v___y_5071_ = v___x_5084_;
goto v___jp_5070_;
}
else
{
size_t v___x_5088_; size_t v___x_5089_; lean_object* v___x_5090_; 
v___x_5088_ = ((size_t)0ULL);
v___x_5089_ = lean_usize_of_nat(v___x_5085_);
v___x_5090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5083_, v___x_5088_, v___x_5089_, v___x_5084_);
lean_dec_ref(v_buckets_5083_);
v___y_5071_ = v___x_5090_;
goto v___jp_5070_;
}
}
else
{
size_t v___x_5091_; size_t v___x_5092_; lean_object* v___x_5093_; 
v___x_5091_ = ((size_t)0ULL);
v___x_5092_ = lean_usize_of_nat(v___x_5085_);
v___x_5093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5083_, v___x_5091_, v___x_5092_, v___x_5084_);
lean_dec_ref(v_buckets_5083_);
v___y_5071_ = v___x_5093_;
goto v___jp_5070_;
}
}
v___jp_5070_:
{
lean_object* v_r_5072_; size_t v_sz_5073_; size_t v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5078_; 
v_r_5072_ = lean_box(1);
v_sz_5073_ = lean_array_size(v___y_5071_);
v___x_5074_ = ((size_t)0ULL);
v___x_5075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5071_, v_sz_5073_, v___x_5074_, v_r_5072_);
lean_dec_ref(v___y_5071_);
v___x_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5076_, 0, v_a_5066_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
if (v_isShared_5069_ == 0)
{
lean_ctor_set(v___x_5068_, 0, v___x_5076_);
v___x_5078_ = v___x_5068_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5076_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
v_a_5095_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_5065_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5065_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5103_);
lean_dec_ref(v_infos_5103_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5106_, lean_object* v_k_5107_, lean_object* v_v_5108_, lean_object* v_t_5109_, lean_object* v_hl_5110_){
_start:
{
lean_object* v___x_5111_; 
v___x_5111_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5107_, v_v_5108_, v_t_5109_);
return v___x_5111_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5112_, lean_object* v_key_5113_, lean_object* v_xs_5114_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5113_, v_xs_5114_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5116_, lean_object* v_key_5117_, lean_object* v_xs_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5116_, v_key_5117_, v_xs_5118_);
lean_dec_ref(v_xs_5118_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5120_, lean_object* v_a_5121_, lean_object* v_m_5122_, lean_object* v_a_5123_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5121_, v_m_5122_, v_a_5123_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5125_, lean_object* v_key_5126_, lean_object* v_as_5127_, size_t v_sz_5128_, size_t v_i_5129_, lean_object* v_b_5130_){
_start:
{
lean_object* v___x_5131_; 
v___x_5131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5126_, v_as_5127_, v_sz_5128_, v_i_5129_, v_b_5130_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5132_, lean_object* v_key_5133_, lean_object* v_as_5134_, lean_object* v_sz_5135_, lean_object* v_i_5136_, lean_object* v_b_5137_){
_start:
{
size_t v_sz_boxed_5138_; size_t v_i_boxed_5139_; lean_object* v_res_5140_; 
v_sz_boxed_5138_ = lean_unbox_usize(v_sz_5135_);
lean_dec(v_sz_5135_);
v_i_boxed_5139_ = lean_unbox_usize(v_i_5136_);
lean_dec(v_i_5136_);
v_res_5140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5132_, v_key_5133_, v_as_5134_, v_sz_boxed_5138_, v_i_boxed_5139_, v_b_5137_);
lean_dec_ref(v_as_5134_);
return v_res_5140_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5141_, lean_object* v_a_5142_, lean_object* v_x_5143_){
_start:
{
uint8_t v___x_5144_; 
v___x_5144_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5142_, v_x_5143_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5145_, lean_object* v_a_5146_, lean_object* v_x_5147_){
_start:
{
uint8_t v_res_5148_; lean_object* v_r_5149_; 
v_res_5148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5145_, v_a_5146_, v_x_5147_);
lean_dec(v_x_5147_);
lean_dec(v_a_5146_);
v_r_5149_ = lean_box(v_res_5148_);
return v_r_5149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5150_, lean_object* v_data_5151_){
_start:
{
lean_object* v___x_5152_; 
v___x_5152_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5151_);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_x_5156_){
_start:
{
lean_object* v___x_5157_; 
v___x_5157_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5154_, v_a_5155_, v_x_5156_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5158_, lean_object* v_i_5159_, lean_object* v_source_5160_, lean_object* v_target_5161_){
_start:
{
lean_object* v___x_5162_; 
v___x_5162_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5159_, v_source_5160_, v_target_5161_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5163_, lean_object* v_x_5164_, lean_object* v_x_5165_){
_start:
{
lean_object* v___x_5166_; 
v___x_5166_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5164_, v_x_5165_);
return v___x_5166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5167_){
_start:
{
lean_object* v_isSetupFailure_x3f_5168_; 
v_isSetupFailure_x3f_5168_ = lean_ctor_get(v_i_5167_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5168_) == 0)
{
uint8_t v___x_5169_; 
v___x_5169_ = 0;
return v___x_5169_;
}
else
{
lean_object* v_val_5170_; uint8_t v___x_5171_; 
v_val_5170_ = lean_ctor_get(v_isSetupFailure_x3f_5168_, 0);
v___x_5171_ = lean_unbox(v_val_5170_);
if (v___x_5171_ == 0)
{
uint8_t v___x_5172_; 
v___x_5172_ = 1;
return v___x_5172_;
}
else
{
uint8_t v___x_5173_; 
v___x_5173_ = 0;
return v___x_5173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5174_){
_start:
{
uint8_t v_res_5175_; lean_object* v_r_5176_; 
v_res_5175_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5174_);
lean_dec_ref(v_i_5174_);
v_r_5176_ = lean_box(v_res_5175_);
return v_r_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5182_, lean_object* v_path_5183_, lean_object* v_ilean_5184_){
_start:
{
lean_object* v_module_5186_; lean_object* v_directImports_5187_; lean_object* v_references_5188_; lean_object* v_decls_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5241_; 
v_module_5186_ = lean_ctor_get(v_ilean_5184_, 1);
v_directImports_5187_ = lean_ctor_get(v_ilean_5184_, 2);
v_references_5188_ = lean_ctor_get(v_ilean_5184_, 3);
v_decls_5189_ = lean_ctor_get(v_ilean_5184_, 4);
v_isSharedCheck_5241_ = !lean_is_exclusive(v_ilean_5184_);
if (v_isSharedCheck_5241_ == 0)
{
lean_object* v_unused_5242_; 
v_unused_5242_ = lean_ctor_get(v_ilean_5184_, 0);
lean_dec(v_unused_5242_);
v___x_5191_ = v_ilean_5184_;
v_isShared_5192_ = v_isSharedCheck_5241_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_decls_5189_);
lean_inc(v_references_5188_);
lean_inc(v_directImports_5187_);
lean_inc(v_module_5186_);
lean_dec(v_ilean_5184_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5241_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5193_; 
lean_inc(v_module_5186_);
v___x_5193_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5186_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5232_; 
v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5196_ = v___x_5193_;
v_isShared_5197_ = v_isSharedCheck_5232_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5193_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5232_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
if (lean_obj_tag(v_a_5194_) == 1)
{
lean_object* v_val_5198_; lean_object* v___x_5199_; 
lean_del_object(v___x_5196_);
v_val_5198_ = lean_ctor_get(v_a_5194_, 0);
lean_inc(v_val_5198_);
lean_dec_ref(v_a_5194_);
v___x_5199_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5187_);
lean_dec_ref(v_directImports_5187_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5220_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5202_ = v___x_5199_;
v_isShared_5203_ = v_isSharedCheck_5220_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5199_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5220_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v_ileans_5204_; lean_object* v_workers_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5219_; 
v_ileans_5204_ = lean_ctor_get(v_self_5182_, 0);
v_workers_5205_ = lean_ctor_get(v_self_5182_, 1);
v_isSharedCheck_5219_ = !lean_is_exclusive(v_self_5182_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5207_ = v_self_5182_;
v_isShared_5208_ = v_isSharedCheck_5219_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_workers_5205_);
lean_inc(v_ileans_5204_);
lean_dec(v_self_5182_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5219_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5192_ == 0)
{
lean_ctor_set(v___x_5191_, 2, v_a_5200_);
lean_ctor_set(v___x_5191_, 1, v_path_5183_);
lean_ctor_set(v___x_5191_, 0, v_val_5198_);
v___x_5210_ = v___x_5191_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_val_5198_);
lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_path_5183_);
lean_ctor_set(v_reuseFailAlloc_5218_, 2, v_a_5200_);
lean_ctor_set(v_reuseFailAlloc_5218_, 3, v_references_5188_);
lean_ctor_set(v_reuseFailAlloc_5218_, 4, v_decls_5189_);
v___x_5210_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
lean_object* v___x_5211_; lean_object* v___x_5213_; 
v___x_5211_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5186_, v___x_5210_, v_ileans_5204_);
if (v_isShared_5208_ == 0)
{
lean_ctor_set(v___x_5207_, 0, v___x_5211_);
v___x_5213_ = v___x_5207_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v___x_5211_);
lean_ctor_set(v_reuseFailAlloc_5217_, 1, v_workers_5205_);
v___x_5213_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
lean_object* v___x_5215_; 
if (v_isShared_5203_ == 0)
{
lean_ctor_set(v___x_5202_, 0, v___x_5213_);
v___x_5215_ = v___x_5202_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v___x_5213_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
lean_dec(v_val_5198_);
lean_del_object(v___x_5191_);
lean_dec(v_decls_5189_);
lean_dec(v_references_5188_);
lean_dec(v_module_5186_);
lean_dec_ref(v_path_5183_);
lean_dec_ref(v_self_5182_);
v_a_5221_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5199_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5199_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
}
else
{
lean_object* v___x_5230_; 
lean_dec(v_a_5194_);
lean_del_object(v___x_5191_);
lean_dec(v_decls_5189_);
lean_dec(v_references_5188_);
lean_dec_ref(v_directImports_5187_);
lean_dec(v_module_5186_);
lean_dec_ref(v_path_5183_);
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v_self_5182_);
v___x_5230_ = v___x_5196_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_self_5182_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5240_; 
lean_del_object(v___x_5191_);
lean_dec(v_decls_5189_);
lean_dec(v_references_5188_);
lean_dec_ref(v_directImports_5187_);
lean_dec(v_module_5186_);
lean_dec_ref(v_path_5183_);
lean_dec_ref(v_self_5182_);
v_a_5233_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5235_ = v___x_5193_;
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5193_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5236_ == 0)
{
v___x_5238_ = v___x_5235_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5243_, lean_object* v_path_5244_, lean_object* v_ilean_5245_, lean_object* v_a_5246_){
_start:
{
lean_object* v_res_5247_; 
v_res_5247_ = l_Lean_Server_References_addIlean(v_self_5243_, v_path_5244_, v_ilean_5245_);
return v_res_5247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5248_, lean_object* v_t_5249_){
_start:
{
if (lean_obj_tag(v_t_5249_) == 0)
{
lean_object* v_v_5250_; lean_object* v_k_5251_; lean_object* v_l_5252_; lean_object* v_r_5253_; lean_object* v_ileanPath_5254_; uint8_t v___x_5255_; 
v_v_5250_ = lean_ctor_get(v_t_5249_, 2);
lean_inc(v_v_5250_);
v_k_5251_ = lean_ctor_get(v_t_5249_, 1);
lean_inc(v_k_5251_);
v_l_5252_ = lean_ctor_get(v_t_5249_, 3);
lean_inc(v_l_5252_);
v_r_5253_ = lean_ctor_get(v_t_5249_, 4);
lean_inc(v_r_5253_);
lean_dec_ref(v_t_5249_);
v_ileanPath_5254_ = lean_ctor_get(v_v_5250_, 1);
v___x_5255_ = lean_string_dec_eq(v_ileanPath_5254_, v_path_5248_);
if (v___x_5255_ == 0)
{
lean_object* v_impl_5256_; lean_object* v_impl_5257_; lean_object* v___x_5258_; 
lean_dec(v_k_5251_);
lean_dec(v_v_5250_);
v_impl_5256_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5248_, v_l_5252_);
v_impl_5257_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5248_, v_r_5253_);
v___x_5258_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5256_, v_impl_5257_);
return v___x_5258_;
}
else
{
lean_object* v_impl_5259_; lean_object* v_impl_5260_; lean_object* v___x_5261_; 
v_impl_5259_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5248_, v_l_5252_);
v_impl_5260_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5248_, v_r_5253_);
v___x_5261_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5251_, v_v_5250_, v_impl_5259_, v_impl_5260_);
return v___x_5261_;
}
}
else
{
return v_t_5249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5262_, lean_object* v_t_5263_){
_start:
{
lean_object* v_res_5264_; 
v_res_5264_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5262_, v_t_5263_);
lean_dec_ref(v_path_5262_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5265_, lean_object* v_t_5266_){
_start:
{
if (lean_obj_tag(v_t_5266_) == 0)
{
lean_object* v_k_5267_; lean_object* v_v_5268_; lean_object* v_l_5269_; lean_object* v_r_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5924_; 
v_k_5267_ = lean_ctor_get(v_t_5266_, 1);
v_v_5268_ = lean_ctor_get(v_t_5266_, 2);
v_l_5269_ = lean_ctor_get(v_t_5266_, 3);
v_r_5270_ = lean_ctor_get(v_t_5266_, 4);
v_isSharedCheck_5924_ = !lean_is_exclusive(v_t_5266_);
if (v_isSharedCheck_5924_ == 0)
{
lean_object* v_unused_5925_; 
v_unused_5925_ = lean_ctor_get(v_t_5266_, 0);
lean_dec(v_unused_5925_);
v___x_5272_ = v_t_5266_;
v_isShared_5273_ = v_isSharedCheck_5924_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_r_5270_);
lean_inc(v_l_5269_);
lean_inc(v_v_5268_);
lean_inc(v_k_5267_);
lean_dec(v_t_5266_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5924_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
uint8_t v___x_5274_; 
v___x_5274_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5265_, v_k_5267_);
switch(v___x_5274_)
{
case 0:
{
lean_object* v_impl_5275_; lean_object* v___x_5276_; 
v_impl_5275_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5265_, v_l_5269_);
v___x_5276_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5275_) == 0)
{
if (lean_obj_tag(v_r_5270_) == 0)
{
lean_object* v_size_5277_; lean_object* v_size_5278_; lean_object* v_k_5279_; lean_object* v_v_5280_; lean_object* v_l_5281_; lean_object* v_r_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; uint8_t v___x_5285_; 
v_size_5277_ = lean_ctor_get(v_impl_5275_, 0);
lean_inc(v_size_5277_);
v_size_5278_ = lean_ctor_get(v_r_5270_, 0);
v_k_5279_ = lean_ctor_get(v_r_5270_, 1);
v_v_5280_ = lean_ctor_get(v_r_5270_, 2);
v_l_5281_ = lean_ctor_get(v_r_5270_, 3);
lean_inc(v_l_5281_);
v_r_5282_ = lean_ctor_get(v_r_5270_, 4);
v___x_5283_ = lean_unsigned_to_nat(3u);
v___x_5284_ = lean_nat_mul(v___x_5283_, v_size_5277_);
v___x_5285_ = lean_nat_dec_lt(v___x_5284_, v_size_5278_);
lean_dec(v___x_5284_);
if (v___x_5285_ == 0)
{
lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5289_; 
lean_dec(v_l_5281_);
v___x_5286_ = lean_nat_add(v___x_5276_, v_size_5277_);
lean_dec(v_size_5277_);
v___x_5287_ = lean_nat_add(v___x_5286_, v_size_5278_);
lean_dec(v___x_5286_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 3, v_impl_5275_);
lean_ctor_set(v___x_5272_, 0, v___x_5287_);
v___x_5289_ = v___x_5272_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v___x_5287_);
lean_ctor_set(v_reuseFailAlloc_5290_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5290_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5290_, 3, v_impl_5275_);
lean_ctor_set(v_reuseFailAlloc_5290_, 4, v_r_5270_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
else
{
lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5354_; 
lean_inc(v_r_5282_);
lean_inc(v_v_5280_);
lean_inc(v_k_5279_);
lean_inc(v_size_5278_);
v_isSharedCheck_5354_ = !lean_is_exclusive(v_r_5270_);
if (v_isSharedCheck_5354_ == 0)
{
lean_object* v_unused_5355_; lean_object* v_unused_5356_; lean_object* v_unused_5357_; lean_object* v_unused_5358_; lean_object* v_unused_5359_; 
v_unused_5355_ = lean_ctor_get(v_r_5270_, 4);
lean_dec(v_unused_5355_);
v_unused_5356_ = lean_ctor_get(v_r_5270_, 3);
lean_dec(v_unused_5356_);
v_unused_5357_ = lean_ctor_get(v_r_5270_, 2);
lean_dec(v_unused_5357_);
v_unused_5358_ = lean_ctor_get(v_r_5270_, 1);
lean_dec(v_unused_5358_);
v_unused_5359_ = lean_ctor_get(v_r_5270_, 0);
lean_dec(v_unused_5359_);
v___x_5292_ = v_r_5270_;
v_isShared_5293_ = v_isSharedCheck_5354_;
goto v_resetjp_5291_;
}
else
{
lean_dec(v_r_5270_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5354_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v_size_5294_; lean_object* v_k_5295_; lean_object* v_v_5296_; lean_object* v_l_5297_; lean_object* v_r_5298_; lean_object* v_size_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; uint8_t v___x_5302_; 
v_size_5294_ = lean_ctor_get(v_l_5281_, 0);
v_k_5295_ = lean_ctor_get(v_l_5281_, 1);
v_v_5296_ = lean_ctor_get(v_l_5281_, 2);
v_l_5297_ = lean_ctor_get(v_l_5281_, 3);
v_r_5298_ = lean_ctor_get(v_l_5281_, 4);
v_size_5299_ = lean_ctor_get(v_r_5282_, 0);
v___x_5300_ = lean_unsigned_to_nat(2u);
v___x_5301_ = lean_nat_mul(v___x_5300_, v_size_5299_);
v___x_5302_ = lean_nat_dec_lt(v_size_5294_, v___x_5301_);
lean_dec(v___x_5301_);
if (v___x_5302_ == 0)
{
lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5330_; 
lean_inc(v_r_5298_);
lean_inc(v_l_5297_);
lean_inc(v_v_5296_);
lean_inc(v_k_5295_);
v_isSharedCheck_5330_ = !lean_is_exclusive(v_l_5281_);
if (v_isSharedCheck_5330_ == 0)
{
lean_object* v_unused_5331_; lean_object* v_unused_5332_; lean_object* v_unused_5333_; lean_object* v_unused_5334_; lean_object* v_unused_5335_; 
v_unused_5331_ = lean_ctor_get(v_l_5281_, 4);
lean_dec(v_unused_5331_);
v_unused_5332_ = lean_ctor_get(v_l_5281_, 3);
lean_dec(v_unused_5332_);
v_unused_5333_ = lean_ctor_get(v_l_5281_, 2);
lean_dec(v_unused_5333_);
v_unused_5334_ = lean_ctor_get(v_l_5281_, 1);
lean_dec(v_unused_5334_);
v_unused_5335_ = lean_ctor_get(v_l_5281_, 0);
lean_dec(v_unused_5335_);
v___x_5304_ = v_l_5281_;
v_isShared_5305_ = v_isSharedCheck_5330_;
goto v_resetjp_5303_;
}
else
{
lean_dec(v_l_5281_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5330_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___y_5309_; lean_object* v___y_5310_; lean_object* v___y_5311_; lean_object* v___y_5320_; 
v___x_5306_ = lean_nat_add(v___x_5276_, v_size_5277_);
lean_dec(v_size_5277_);
v___x_5307_ = lean_nat_add(v___x_5306_, v_size_5278_);
lean_dec(v_size_5278_);
if (lean_obj_tag(v_l_5297_) == 0)
{
lean_object* v_size_5328_; 
v_size_5328_ = lean_ctor_get(v_l_5297_, 0);
lean_inc(v_size_5328_);
v___y_5320_ = v_size_5328_;
goto v___jp_5319_;
}
else
{
lean_object* v___x_5329_; 
v___x_5329_ = lean_unsigned_to_nat(0u);
v___y_5320_ = v___x_5329_;
goto v___jp_5319_;
}
v___jp_5308_:
{
lean_object* v___x_5312_; lean_object* v___x_5314_; 
v___x_5312_ = lean_nat_add(v___y_5309_, v___y_5311_);
lean_dec(v___y_5311_);
lean_dec(v___y_5309_);
if (v_isShared_5305_ == 0)
{
lean_ctor_set(v___x_5304_, 4, v_r_5282_);
lean_ctor_set(v___x_5304_, 3, v_r_5298_);
lean_ctor_set(v___x_5304_, 2, v_v_5280_);
lean_ctor_set(v___x_5304_, 1, v_k_5279_);
lean_ctor_set(v___x_5304_, 0, v___x_5312_);
v___x_5314_ = v___x_5304_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5312_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_k_5279_);
lean_ctor_set(v_reuseFailAlloc_5318_, 2, v_v_5280_);
lean_ctor_set(v_reuseFailAlloc_5318_, 3, v_r_5298_);
lean_ctor_set(v_reuseFailAlloc_5318_, 4, v_r_5282_);
v___x_5314_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
lean_object* v___x_5316_; 
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 4, v___x_5314_);
lean_ctor_set(v___x_5292_, 3, v___y_5310_);
lean_ctor_set(v___x_5292_, 2, v_v_5296_);
lean_ctor_set(v___x_5292_, 1, v_k_5295_);
lean_ctor_set(v___x_5292_, 0, v___x_5307_);
v___x_5316_ = v___x_5292_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v___x_5307_);
lean_ctor_set(v_reuseFailAlloc_5317_, 1, v_k_5295_);
lean_ctor_set(v_reuseFailAlloc_5317_, 2, v_v_5296_);
lean_ctor_set(v_reuseFailAlloc_5317_, 3, v___y_5310_);
lean_ctor_set(v_reuseFailAlloc_5317_, 4, v___x_5314_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
v___jp_5319_:
{
lean_object* v___x_5321_; lean_object* v___x_5323_; 
v___x_5321_ = lean_nat_add(v___x_5306_, v___y_5320_);
lean_dec(v___y_5320_);
lean_dec(v___x_5306_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v_l_5297_);
lean_ctor_set(v___x_5272_, 3, v_impl_5275_);
lean_ctor_set(v___x_5272_, 0, v___x_5321_);
v___x_5323_ = v___x_5272_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5321_);
lean_ctor_set(v_reuseFailAlloc_5327_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5327_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5327_, 3, v_impl_5275_);
lean_ctor_set(v_reuseFailAlloc_5327_, 4, v_l_5297_);
v___x_5323_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
lean_object* v___x_5324_; 
v___x_5324_ = lean_nat_add(v___x_5276_, v_size_5299_);
if (lean_obj_tag(v_r_5298_) == 0)
{
lean_object* v_size_5325_; 
v_size_5325_ = lean_ctor_get(v_r_5298_, 0);
lean_inc(v_size_5325_);
v___y_5309_ = v___x_5324_;
v___y_5310_ = v___x_5323_;
v___y_5311_ = v_size_5325_;
goto v___jp_5308_;
}
else
{
lean_object* v___x_5326_; 
v___x_5326_ = lean_unsigned_to_nat(0u);
v___y_5309_ = v___x_5324_;
v___y_5310_ = v___x_5323_;
v___y_5311_ = v___x_5326_;
goto v___jp_5308_;
}
}
}
}
}
else
{
lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5340_; 
lean_del_object(v___x_5272_);
v___x_5336_ = lean_nat_add(v___x_5276_, v_size_5277_);
lean_dec(v_size_5277_);
v___x_5337_ = lean_nat_add(v___x_5336_, v_size_5278_);
lean_dec(v_size_5278_);
v___x_5338_ = lean_nat_add(v___x_5336_, v_size_5294_);
lean_dec(v___x_5336_);
lean_inc_ref(v_impl_5275_);
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 4, v_l_5281_);
lean_ctor_set(v___x_5292_, 3, v_impl_5275_);
lean_ctor_set(v___x_5292_, 2, v_v_5268_);
lean_ctor_set(v___x_5292_, 1, v_k_5267_);
lean_ctor_set(v___x_5292_, 0, v___x_5338_);
v___x_5340_ = v___x_5292_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v___x_5338_);
lean_ctor_set(v_reuseFailAlloc_5353_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5353_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5353_, 3, v_impl_5275_);
lean_ctor_set(v_reuseFailAlloc_5353_, 4, v_l_5281_);
v___x_5340_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5347_; 
v_isSharedCheck_5347_ = !lean_is_exclusive(v_impl_5275_);
if (v_isSharedCheck_5347_ == 0)
{
lean_object* v_unused_5348_; lean_object* v_unused_5349_; lean_object* v_unused_5350_; lean_object* v_unused_5351_; lean_object* v_unused_5352_; 
v_unused_5348_ = lean_ctor_get(v_impl_5275_, 4);
lean_dec(v_unused_5348_);
v_unused_5349_ = lean_ctor_get(v_impl_5275_, 3);
lean_dec(v_unused_5349_);
v_unused_5350_ = lean_ctor_get(v_impl_5275_, 2);
lean_dec(v_unused_5350_);
v_unused_5351_ = lean_ctor_get(v_impl_5275_, 1);
lean_dec(v_unused_5351_);
v_unused_5352_ = lean_ctor_get(v_impl_5275_, 0);
lean_dec(v_unused_5352_);
v___x_5342_ = v_impl_5275_;
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
else
{
lean_dec(v_impl_5275_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5345_; 
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 4, v_r_5282_);
lean_ctor_set(v___x_5342_, 3, v___x_5340_);
lean_ctor_set(v___x_5342_, 2, v_v_5280_);
lean_ctor_set(v___x_5342_, 1, v_k_5279_);
lean_ctor_set(v___x_5342_, 0, v___x_5337_);
v___x_5345_ = v___x_5342_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5337_);
lean_ctor_set(v_reuseFailAlloc_5346_, 1, v_k_5279_);
lean_ctor_set(v_reuseFailAlloc_5346_, 2, v_v_5280_);
lean_ctor_set(v_reuseFailAlloc_5346_, 3, v___x_5340_);
lean_ctor_set(v_reuseFailAlloc_5346_, 4, v_r_5282_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5360_; lean_object* v___x_5361_; lean_object* v___x_5363_; 
v_size_5360_ = lean_ctor_get(v_impl_5275_, 0);
lean_inc(v_size_5360_);
v___x_5361_ = lean_nat_add(v___x_5276_, v_size_5360_);
lean_dec(v_size_5360_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 3, v_impl_5275_);
lean_ctor_set(v___x_5272_, 0, v___x_5361_);
v___x_5363_ = v___x_5272_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v___x_5361_);
lean_ctor_set(v_reuseFailAlloc_5364_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5364_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5364_, 3, v_impl_5275_);
lean_ctor_set(v_reuseFailAlloc_5364_, 4, v_r_5270_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
else
{
if (lean_obj_tag(v_r_5270_) == 0)
{
lean_object* v_l_5365_; 
v_l_5365_ = lean_ctor_get(v_r_5270_, 3);
lean_inc(v_l_5365_);
if (lean_obj_tag(v_l_5365_) == 0)
{
lean_object* v_r_5366_; 
v_r_5366_ = lean_ctor_get(v_r_5270_, 4);
lean_inc(v_r_5366_);
if (lean_obj_tag(v_r_5366_) == 0)
{
lean_object* v_size_5367_; lean_object* v_k_5368_; lean_object* v_v_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5382_; 
v_size_5367_ = lean_ctor_get(v_r_5270_, 0);
v_k_5368_ = lean_ctor_get(v_r_5270_, 1);
v_v_5369_ = lean_ctor_get(v_r_5270_, 2);
v_isSharedCheck_5382_ = !lean_is_exclusive(v_r_5270_);
if (v_isSharedCheck_5382_ == 0)
{
lean_object* v_unused_5383_; lean_object* v_unused_5384_; 
v_unused_5383_ = lean_ctor_get(v_r_5270_, 4);
lean_dec(v_unused_5383_);
v_unused_5384_ = lean_ctor_get(v_r_5270_, 3);
lean_dec(v_unused_5384_);
v___x_5371_ = v_r_5270_;
v_isShared_5372_ = v_isSharedCheck_5382_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_v_5369_);
lean_inc(v_k_5368_);
lean_inc(v_size_5367_);
lean_dec(v_r_5270_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5382_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v_size_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5377_; 
v_size_5373_ = lean_ctor_get(v_l_5365_, 0);
v___x_5374_ = lean_nat_add(v___x_5276_, v_size_5367_);
lean_dec(v_size_5367_);
v___x_5375_ = lean_nat_add(v___x_5276_, v_size_5373_);
if (v_isShared_5372_ == 0)
{
lean_ctor_set(v___x_5371_, 4, v_l_5365_);
lean_ctor_set(v___x_5371_, 3, v_impl_5275_);
lean_ctor_set(v___x_5371_, 2, v_v_5268_);
lean_ctor_set(v___x_5371_, 1, v_k_5267_);
lean_ctor_set(v___x_5371_, 0, v___x_5375_);
v___x_5377_ = v___x_5371_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5375_);
lean_ctor_set(v_reuseFailAlloc_5381_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5381_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5381_, 3, v_impl_5275_);
lean_ctor_set(v_reuseFailAlloc_5381_, 4, v_l_5365_);
v___x_5377_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
lean_object* v___x_5379_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v_r_5366_);
lean_ctor_set(v___x_5272_, 3, v___x_5377_);
lean_ctor_set(v___x_5272_, 2, v_v_5369_);
lean_ctor_set(v___x_5272_, 1, v_k_5368_);
lean_ctor_set(v___x_5272_, 0, v___x_5374_);
v___x_5379_ = v___x_5272_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5374_);
lean_ctor_set(v_reuseFailAlloc_5380_, 1, v_k_5368_);
lean_ctor_set(v_reuseFailAlloc_5380_, 2, v_v_5369_);
lean_ctor_set(v_reuseFailAlloc_5380_, 3, v___x_5377_);
lean_ctor_set(v_reuseFailAlloc_5380_, 4, v_r_5366_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
else
{
lean_object* v_k_5385_; lean_object* v_v_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5409_; 
v_k_5385_ = lean_ctor_get(v_r_5270_, 1);
v_v_5386_ = lean_ctor_get(v_r_5270_, 2);
v_isSharedCheck_5409_ = !lean_is_exclusive(v_r_5270_);
if (v_isSharedCheck_5409_ == 0)
{
lean_object* v_unused_5410_; lean_object* v_unused_5411_; lean_object* v_unused_5412_; 
v_unused_5410_ = lean_ctor_get(v_r_5270_, 4);
lean_dec(v_unused_5410_);
v_unused_5411_ = lean_ctor_get(v_r_5270_, 3);
lean_dec(v_unused_5411_);
v_unused_5412_ = lean_ctor_get(v_r_5270_, 0);
lean_dec(v_unused_5412_);
v___x_5388_ = v_r_5270_;
v_isShared_5389_ = v_isSharedCheck_5409_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_v_5386_);
lean_inc(v_k_5385_);
lean_dec(v_r_5270_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5409_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v_k_5390_; lean_object* v_v_5391_; lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5405_; 
v_k_5390_ = lean_ctor_get(v_l_5365_, 1);
v_v_5391_ = lean_ctor_get(v_l_5365_, 2);
v_isSharedCheck_5405_ = !lean_is_exclusive(v_l_5365_);
if (v_isSharedCheck_5405_ == 0)
{
lean_object* v_unused_5406_; lean_object* v_unused_5407_; lean_object* v_unused_5408_; 
v_unused_5406_ = lean_ctor_get(v_l_5365_, 4);
lean_dec(v_unused_5406_);
v_unused_5407_ = lean_ctor_get(v_l_5365_, 3);
lean_dec(v_unused_5407_);
v_unused_5408_ = lean_ctor_get(v_l_5365_, 0);
lean_dec(v_unused_5408_);
v___x_5393_ = v_l_5365_;
v_isShared_5394_ = v_isSharedCheck_5405_;
goto v_resetjp_5392_;
}
else
{
lean_inc(v_v_5391_);
lean_inc(v_k_5390_);
lean_dec(v_l_5365_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5405_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
lean_object* v___x_5395_; lean_object* v___x_5397_; 
v___x_5395_ = lean_unsigned_to_nat(3u);
if (v_isShared_5394_ == 0)
{
lean_ctor_set(v___x_5393_, 4, v_r_5366_);
lean_ctor_set(v___x_5393_, 3, v_r_5366_);
lean_ctor_set(v___x_5393_, 2, v_v_5268_);
lean_ctor_set(v___x_5393_, 1, v_k_5267_);
lean_ctor_set(v___x_5393_, 0, v___x_5276_);
v___x_5397_ = v___x_5393_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v___x_5276_);
lean_ctor_set(v_reuseFailAlloc_5404_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5404_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5404_, 3, v_r_5366_);
lean_ctor_set(v_reuseFailAlloc_5404_, 4, v_r_5366_);
v___x_5397_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
lean_object* v___x_5399_; 
if (v_isShared_5389_ == 0)
{
lean_ctor_set(v___x_5388_, 3, v_r_5366_);
lean_ctor_set(v___x_5388_, 0, v___x_5276_);
v___x_5399_ = v___x_5388_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v___x_5276_);
lean_ctor_set(v_reuseFailAlloc_5403_, 1, v_k_5385_);
lean_ctor_set(v_reuseFailAlloc_5403_, 2, v_v_5386_);
lean_ctor_set(v_reuseFailAlloc_5403_, 3, v_r_5366_);
lean_ctor_set(v_reuseFailAlloc_5403_, 4, v_r_5366_);
v___x_5399_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
lean_object* v___x_5401_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v___x_5399_);
lean_ctor_set(v___x_5272_, 3, v___x_5397_);
lean_ctor_set(v___x_5272_, 2, v_v_5391_);
lean_ctor_set(v___x_5272_, 1, v_k_5390_);
lean_ctor_set(v___x_5272_, 0, v___x_5395_);
v___x_5401_ = v___x_5272_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5395_);
lean_ctor_set(v_reuseFailAlloc_5402_, 1, v_k_5390_);
lean_ctor_set(v_reuseFailAlloc_5402_, 2, v_v_5391_);
lean_ctor_set(v_reuseFailAlloc_5402_, 3, v___x_5397_);
lean_ctor_set(v_reuseFailAlloc_5402_, 4, v___x_5399_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_5413_; 
v_r_5413_ = lean_ctor_get(v_r_5270_, 4);
lean_inc(v_r_5413_);
if (lean_obj_tag(v_r_5413_) == 0)
{
lean_object* v_k_5414_; lean_object* v_v_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5426_; 
v_k_5414_ = lean_ctor_get(v_r_5270_, 1);
v_v_5415_ = lean_ctor_get(v_r_5270_, 2);
v_isSharedCheck_5426_ = !lean_is_exclusive(v_r_5270_);
if (v_isSharedCheck_5426_ == 0)
{
lean_object* v_unused_5427_; lean_object* v_unused_5428_; lean_object* v_unused_5429_; 
v_unused_5427_ = lean_ctor_get(v_r_5270_, 4);
lean_dec(v_unused_5427_);
v_unused_5428_ = lean_ctor_get(v_r_5270_, 3);
lean_dec(v_unused_5428_);
v_unused_5429_ = lean_ctor_get(v_r_5270_, 0);
lean_dec(v_unused_5429_);
v___x_5417_ = v_r_5270_;
v_isShared_5418_ = v_isSharedCheck_5426_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_v_5415_);
lean_inc(v_k_5414_);
lean_dec(v_r_5270_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5426_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5419_; lean_object* v___x_5421_; 
v___x_5419_ = lean_unsigned_to_nat(3u);
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 4, v_l_5365_);
lean_ctor_set(v___x_5417_, 2, v_v_5268_);
lean_ctor_set(v___x_5417_, 1, v_k_5267_);
lean_ctor_set(v___x_5417_, 0, v___x_5276_);
v___x_5421_ = v___x_5417_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5276_);
lean_ctor_set(v_reuseFailAlloc_5425_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5425_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5425_, 3, v_l_5365_);
lean_ctor_set(v_reuseFailAlloc_5425_, 4, v_l_5365_);
v___x_5421_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5423_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v_r_5413_);
lean_ctor_set(v___x_5272_, 3, v___x_5421_);
lean_ctor_set(v___x_5272_, 2, v_v_5415_);
lean_ctor_set(v___x_5272_, 1, v_k_5414_);
lean_ctor_set(v___x_5272_, 0, v___x_5419_);
v___x_5423_ = v___x_5272_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v___x_5419_);
lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_k_5414_);
lean_ctor_set(v_reuseFailAlloc_5424_, 2, v_v_5415_);
lean_ctor_set(v_reuseFailAlloc_5424_, 3, v___x_5421_);
lean_ctor_set(v_reuseFailAlloc_5424_, 4, v_r_5413_);
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
else
{
lean_object* v_size_5430_; lean_object* v_k_5431_; lean_object* v_v_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5443_; 
v_size_5430_ = lean_ctor_get(v_r_5270_, 0);
v_k_5431_ = lean_ctor_get(v_r_5270_, 1);
v_v_5432_ = lean_ctor_get(v_r_5270_, 2);
v_isSharedCheck_5443_ = !lean_is_exclusive(v_r_5270_);
if (v_isSharedCheck_5443_ == 0)
{
lean_object* v_unused_5444_; lean_object* v_unused_5445_; 
v_unused_5444_ = lean_ctor_get(v_r_5270_, 4);
lean_dec(v_unused_5444_);
v_unused_5445_ = lean_ctor_get(v_r_5270_, 3);
lean_dec(v_unused_5445_);
v___x_5434_ = v_r_5270_;
v_isShared_5435_ = v_isSharedCheck_5443_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_v_5432_);
lean_inc(v_k_5431_);
lean_inc(v_size_5430_);
lean_dec(v_r_5270_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5443_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 3, v_r_5413_);
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_size_5430_);
lean_ctor_set(v_reuseFailAlloc_5442_, 1, v_k_5431_);
lean_ctor_set(v_reuseFailAlloc_5442_, 2, v_v_5432_);
lean_ctor_set(v_reuseFailAlloc_5442_, 3, v_r_5413_);
lean_ctor_set(v_reuseFailAlloc_5442_, 4, v_r_5413_);
v___x_5437_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
lean_object* v___x_5438_; lean_object* v___x_5440_; 
v___x_5438_ = lean_unsigned_to_nat(2u);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v___x_5437_);
lean_ctor_set(v___x_5272_, 3, v_r_5413_);
lean_ctor_set(v___x_5272_, 0, v___x_5438_);
v___x_5440_ = v___x_5272_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5438_);
lean_ctor_set(v_reuseFailAlloc_5441_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5441_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5441_, 3, v_r_5413_);
lean_ctor_set(v_reuseFailAlloc_5441_, 4, v___x_5437_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
}
}
}
else
{
lean_object* v___x_5447_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 3, v_r_5270_);
lean_ctor_set(v___x_5272_, 0, v___x_5276_);
v___x_5447_ = v___x_5272_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5276_);
lean_ctor_set(v_reuseFailAlloc_5448_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5448_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5448_, 3, v_r_5270_);
lean_ctor_set(v_reuseFailAlloc_5448_, 4, v_r_5270_);
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
case 1:
{
lean_del_object(v___x_5272_);
lean_dec(v_v_5268_);
lean_dec(v_k_5267_);
if (lean_obj_tag(v_l_5269_) == 0)
{
if (lean_obj_tag(v_r_5270_) == 0)
{
lean_object* v_size_5449_; lean_object* v_k_5450_; lean_object* v_v_5451_; lean_object* v_l_5452_; lean_object* v_r_5453_; lean_object* v_size_5454_; lean_object* v_k_5455_; lean_object* v_v_5456_; lean_object* v_l_5457_; lean_object* v_r_5458_; lean_object* v___x_5459_; uint8_t v___x_5460_; 
v_size_5449_ = lean_ctor_get(v_l_5269_, 0);
v_k_5450_ = lean_ctor_get(v_l_5269_, 1);
v_v_5451_ = lean_ctor_get(v_l_5269_, 2);
v_l_5452_ = lean_ctor_get(v_l_5269_, 3);
v_r_5453_ = lean_ctor_get(v_l_5269_, 4);
lean_inc(v_r_5453_);
v_size_5454_ = lean_ctor_get(v_r_5270_, 0);
v_k_5455_ = lean_ctor_get(v_r_5270_, 1);
v_v_5456_ = lean_ctor_get(v_r_5270_, 2);
v_l_5457_ = lean_ctor_get(v_r_5270_, 3);
lean_inc(v_l_5457_);
v_r_5458_ = lean_ctor_get(v_r_5270_, 4);
v___x_5459_ = lean_unsigned_to_nat(1u);
v___x_5460_ = lean_nat_dec_lt(v_size_5449_, v_size_5454_);
if (v___x_5460_ == 0)
{
lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5596_; 
lean_inc(v_l_5452_);
lean_inc(v_v_5451_);
lean_inc(v_k_5450_);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_l_5269_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; lean_object* v_unused_5598_; lean_object* v_unused_5599_; lean_object* v_unused_5600_; lean_object* v_unused_5601_; 
v_unused_5597_ = lean_ctor_get(v_l_5269_, 4);
lean_dec(v_unused_5597_);
v_unused_5598_ = lean_ctor_get(v_l_5269_, 3);
lean_dec(v_unused_5598_);
v_unused_5599_ = lean_ctor_get(v_l_5269_, 2);
lean_dec(v_unused_5599_);
v_unused_5600_ = lean_ctor_get(v_l_5269_, 1);
lean_dec(v_unused_5600_);
v_unused_5601_ = lean_ctor_get(v_l_5269_, 0);
lean_dec(v_unused_5601_);
v___x_5462_ = v_l_5269_;
v_isShared_5463_ = v_isSharedCheck_5596_;
goto v_resetjp_5461_;
}
else
{
lean_dec(v_l_5269_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5596_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v___x_5464_; lean_object* v_tree_5465_; 
v___x_5464_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5450_, v_v_5451_, v_l_5452_, v_r_5453_);
v_tree_5465_ = lean_ctor_get(v___x_5464_, 2);
lean_inc(v_tree_5465_);
if (lean_obj_tag(v_tree_5465_) == 0)
{
lean_object* v_k_5466_; lean_object* v_v_5467_; lean_object* v_size_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; uint8_t v___x_5471_; 
v_k_5466_ = lean_ctor_get(v___x_5464_, 0);
lean_inc(v_k_5466_);
v_v_5467_ = lean_ctor_get(v___x_5464_, 1);
lean_inc(v_v_5467_);
lean_dec_ref(v___x_5464_);
v_size_5468_ = lean_ctor_get(v_tree_5465_, 0);
v___x_5469_ = lean_unsigned_to_nat(3u);
v___x_5470_ = lean_nat_mul(v___x_5469_, v_size_5468_);
v___x_5471_ = lean_nat_dec_lt(v___x_5470_, v_size_5454_);
lean_dec(v___x_5470_);
if (v___x_5471_ == 0)
{
lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5475_; 
lean_dec(v_l_5457_);
v___x_5472_ = lean_nat_add(v___x_5459_, v_size_5468_);
v___x_5473_ = lean_nat_add(v___x_5472_, v_size_5454_);
lean_dec(v___x_5472_);
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 4, v_r_5270_);
lean_ctor_set(v___x_5462_, 3, v_tree_5465_);
lean_ctor_set(v___x_5462_, 2, v_v_5467_);
lean_ctor_set(v___x_5462_, 1, v_k_5466_);
lean_ctor_set(v___x_5462_, 0, v___x_5473_);
v___x_5475_ = v___x_5462_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v___x_5473_);
lean_ctor_set(v_reuseFailAlloc_5476_, 1, v_k_5466_);
lean_ctor_set(v_reuseFailAlloc_5476_, 2, v_v_5467_);
lean_ctor_set(v_reuseFailAlloc_5476_, 3, v_tree_5465_);
lean_ctor_set(v_reuseFailAlloc_5476_, 4, v_r_5270_);
v___x_5475_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
return v___x_5475_;
}
}
else
{
lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5531_; 
lean_inc(v_r_5458_);
lean_inc(v_v_5456_);
lean_inc(v_k_5455_);
lean_inc(v_size_5454_);
v_isSharedCheck_5531_ = !lean_is_exclusive(v_r_5270_);
if (v_isSharedCheck_5531_ == 0)
{
lean_object* v_unused_5532_; lean_object* v_unused_5533_; lean_object* v_unused_5534_; lean_object* v_unused_5535_; lean_object* v_unused_5536_; 
v_unused_5532_ = lean_ctor_get(v_r_5270_, 4);
lean_dec(v_unused_5532_);
v_unused_5533_ = lean_ctor_get(v_r_5270_, 3);
lean_dec(v_unused_5533_);
v_unused_5534_ = lean_ctor_get(v_r_5270_, 2);
lean_dec(v_unused_5534_);
v_unused_5535_ = lean_ctor_get(v_r_5270_, 1);
lean_dec(v_unused_5535_);
v_unused_5536_ = lean_ctor_get(v_r_5270_, 0);
lean_dec(v_unused_5536_);
v___x_5478_ = v_r_5270_;
v_isShared_5479_ = v_isSharedCheck_5531_;
goto v_resetjp_5477_;
}
else
{
lean_dec(v_r_5270_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5531_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v_size_5480_; lean_object* v_k_5481_; lean_object* v_v_5482_; lean_object* v_l_5483_; lean_object* v_r_5484_; lean_object* v_size_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; uint8_t v___x_5488_; 
v_size_5480_ = lean_ctor_get(v_l_5457_, 0);
v_k_5481_ = lean_ctor_get(v_l_5457_, 1);
v_v_5482_ = lean_ctor_get(v_l_5457_, 2);
v_l_5483_ = lean_ctor_get(v_l_5457_, 3);
v_r_5484_ = lean_ctor_get(v_l_5457_, 4);
v_size_5485_ = lean_ctor_get(v_r_5458_, 0);
v___x_5486_ = lean_unsigned_to_nat(2u);
v___x_5487_ = lean_nat_mul(v___x_5486_, v_size_5485_);
v___x_5488_ = lean_nat_dec_lt(v_size_5480_, v___x_5487_);
lean_dec(v___x_5487_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5516_; 
lean_inc(v_r_5484_);
lean_inc(v_l_5483_);
lean_inc(v_v_5482_);
lean_inc(v_k_5481_);
v_isSharedCheck_5516_ = !lean_is_exclusive(v_l_5457_);
if (v_isSharedCheck_5516_ == 0)
{
lean_object* v_unused_5517_; lean_object* v_unused_5518_; lean_object* v_unused_5519_; lean_object* v_unused_5520_; lean_object* v_unused_5521_; 
v_unused_5517_ = lean_ctor_get(v_l_5457_, 4);
lean_dec(v_unused_5517_);
v_unused_5518_ = lean_ctor_get(v_l_5457_, 3);
lean_dec(v_unused_5518_);
v_unused_5519_ = lean_ctor_get(v_l_5457_, 2);
lean_dec(v_unused_5519_);
v_unused_5520_ = lean_ctor_get(v_l_5457_, 1);
lean_dec(v_unused_5520_);
v_unused_5521_ = lean_ctor_get(v_l_5457_, 0);
lean_dec(v_unused_5521_);
v___x_5490_ = v_l_5457_;
v_isShared_5491_ = v_isSharedCheck_5516_;
goto v_resetjp_5489_;
}
else
{
lean_dec(v_l_5457_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5516_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___y_5495_; lean_object* v___y_5496_; lean_object* v___y_5497_; lean_object* v___y_5506_; 
v___x_5492_ = lean_nat_add(v___x_5459_, v_size_5468_);
v___x_5493_ = lean_nat_add(v___x_5492_, v_size_5454_);
lean_dec(v_size_5454_);
if (lean_obj_tag(v_l_5483_) == 0)
{
lean_object* v_size_5514_; 
v_size_5514_ = lean_ctor_get(v_l_5483_, 0);
lean_inc(v_size_5514_);
v___y_5506_ = v_size_5514_;
goto v___jp_5505_;
}
else
{
lean_object* v___x_5515_; 
v___x_5515_ = lean_unsigned_to_nat(0u);
v___y_5506_ = v___x_5515_;
goto v___jp_5505_;
}
v___jp_5494_:
{
lean_object* v___x_5498_; lean_object* v___x_5500_; 
v___x_5498_ = lean_nat_add(v___y_5496_, v___y_5497_);
lean_dec(v___y_5497_);
lean_dec(v___y_5496_);
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 4, v_r_5458_);
lean_ctor_set(v___x_5490_, 3, v_r_5484_);
lean_ctor_set(v___x_5490_, 2, v_v_5456_);
lean_ctor_set(v___x_5490_, 1, v_k_5455_);
lean_ctor_set(v___x_5490_, 0, v___x_5498_);
v___x_5500_ = v___x_5490_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5498_);
lean_ctor_set(v_reuseFailAlloc_5504_, 1, v_k_5455_);
lean_ctor_set(v_reuseFailAlloc_5504_, 2, v_v_5456_);
lean_ctor_set(v_reuseFailAlloc_5504_, 3, v_r_5484_);
lean_ctor_set(v_reuseFailAlloc_5504_, 4, v_r_5458_);
v___x_5500_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
lean_object* v___x_5502_; 
if (v_isShared_5479_ == 0)
{
lean_ctor_set(v___x_5478_, 4, v___x_5500_);
lean_ctor_set(v___x_5478_, 3, v___y_5495_);
lean_ctor_set(v___x_5478_, 2, v_v_5482_);
lean_ctor_set(v___x_5478_, 1, v_k_5481_);
lean_ctor_set(v___x_5478_, 0, v___x_5493_);
v___x_5502_ = v___x_5478_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5493_);
lean_ctor_set(v_reuseFailAlloc_5503_, 1, v_k_5481_);
lean_ctor_set(v_reuseFailAlloc_5503_, 2, v_v_5482_);
lean_ctor_set(v_reuseFailAlloc_5503_, 3, v___y_5495_);
lean_ctor_set(v_reuseFailAlloc_5503_, 4, v___x_5500_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
v___jp_5505_:
{
lean_object* v___x_5507_; lean_object* v___x_5509_; 
v___x_5507_ = lean_nat_add(v___x_5492_, v___y_5506_);
lean_dec(v___y_5506_);
lean_dec(v___x_5492_);
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 4, v_l_5483_);
lean_ctor_set(v___x_5462_, 3, v_tree_5465_);
lean_ctor_set(v___x_5462_, 2, v_v_5467_);
lean_ctor_set(v___x_5462_, 1, v_k_5466_);
lean_ctor_set(v___x_5462_, 0, v___x_5507_);
v___x_5509_ = v___x_5462_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v___x_5507_);
lean_ctor_set(v_reuseFailAlloc_5513_, 1, v_k_5466_);
lean_ctor_set(v_reuseFailAlloc_5513_, 2, v_v_5467_);
lean_ctor_set(v_reuseFailAlloc_5513_, 3, v_tree_5465_);
lean_ctor_set(v_reuseFailAlloc_5513_, 4, v_l_5483_);
v___x_5509_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5510_; 
v___x_5510_ = lean_nat_add(v___x_5459_, v_size_5485_);
if (lean_obj_tag(v_r_5484_) == 0)
{
lean_object* v_size_5511_; 
v_size_5511_ = lean_ctor_get(v_r_5484_, 0);
lean_inc(v_size_5511_);
v___y_5495_ = v___x_5509_;
v___y_5496_ = v___x_5510_;
v___y_5497_ = v_size_5511_;
goto v___jp_5494_;
}
else
{
lean_object* v___x_5512_; 
v___x_5512_ = lean_unsigned_to_nat(0u);
v___y_5495_ = v___x_5509_;
v___y_5496_ = v___x_5510_;
v___y_5497_ = v___x_5512_;
goto v___jp_5494_;
}
}
}
}
}
else
{
lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5526_; 
v___x_5522_ = lean_nat_add(v___x_5459_, v_size_5468_);
v___x_5523_ = lean_nat_add(v___x_5522_, v_size_5454_);
lean_dec(v_size_5454_);
v___x_5524_ = lean_nat_add(v___x_5522_, v_size_5480_);
lean_dec(v___x_5522_);
if (v_isShared_5479_ == 0)
{
lean_ctor_set(v___x_5478_, 4, v_l_5457_);
lean_ctor_set(v___x_5478_, 3, v_tree_5465_);
lean_ctor_set(v___x_5478_, 2, v_v_5467_);
lean_ctor_set(v___x_5478_, 1, v_k_5466_);
lean_ctor_set(v___x_5478_, 0, v___x_5524_);
v___x_5526_ = v___x_5478_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5524_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_k_5466_);
lean_ctor_set(v_reuseFailAlloc_5530_, 2, v_v_5467_);
lean_ctor_set(v_reuseFailAlloc_5530_, 3, v_tree_5465_);
lean_ctor_set(v_reuseFailAlloc_5530_, 4, v_l_5457_);
v___x_5526_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5528_; 
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 4, v_r_5458_);
lean_ctor_set(v___x_5462_, 3, v___x_5526_);
lean_ctor_set(v___x_5462_, 2, v_v_5456_);
lean_ctor_set(v___x_5462_, 1, v_k_5455_);
lean_ctor_set(v___x_5462_, 0, v___x_5523_);
v___x_5528_ = v___x_5462_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5523_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_k_5455_);
lean_ctor_set(v_reuseFailAlloc_5529_, 2, v_v_5456_);
lean_ctor_set(v_reuseFailAlloc_5529_, 3, v___x_5526_);
lean_ctor_set(v_reuseFailAlloc_5529_, 4, v_r_5458_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
}
}
else
{
lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5590_; 
lean_inc(v_r_5458_);
lean_inc(v_v_5456_);
lean_inc(v_k_5455_);
lean_inc(v_size_5454_);
v_isSharedCheck_5590_ = !lean_is_exclusive(v_r_5270_);
if (v_isSharedCheck_5590_ == 0)
{
lean_object* v_unused_5591_; lean_object* v_unused_5592_; lean_object* v_unused_5593_; lean_object* v_unused_5594_; lean_object* v_unused_5595_; 
v_unused_5591_ = lean_ctor_get(v_r_5270_, 4);
lean_dec(v_unused_5591_);
v_unused_5592_ = lean_ctor_get(v_r_5270_, 3);
lean_dec(v_unused_5592_);
v_unused_5593_ = lean_ctor_get(v_r_5270_, 2);
lean_dec(v_unused_5593_);
v_unused_5594_ = lean_ctor_get(v_r_5270_, 1);
lean_dec(v_unused_5594_);
v_unused_5595_ = lean_ctor_get(v_r_5270_, 0);
lean_dec(v_unused_5595_);
v___x_5538_ = v_r_5270_;
v_isShared_5539_ = v_isSharedCheck_5590_;
goto v_resetjp_5537_;
}
else
{
lean_dec(v_r_5270_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5590_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
if (lean_obj_tag(v_l_5457_) == 0)
{
if (lean_obj_tag(v_r_5458_) == 0)
{
lean_object* v_k_5540_; lean_object* v_v_5541_; lean_object* v_size_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5546_; 
v_k_5540_ = lean_ctor_get(v___x_5464_, 0);
lean_inc(v_k_5540_);
v_v_5541_ = lean_ctor_get(v___x_5464_, 1);
lean_inc(v_v_5541_);
lean_dec_ref(v___x_5464_);
v_size_5542_ = lean_ctor_get(v_l_5457_, 0);
v___x_5543_ = lean_nat_add(v___x_5459_, v_size_5454_);
lean_dec(v_size_5454_);
v___x_5544_ = lean_nat_add(v___x_5459_, v_size_5542_);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 4, v_l_5457_);
lean_ctor_set(v___x_5538_, 3, v_tree_5465_);
lean_ctor_set(v___x_5538_, 2, v_v_5541_);
lean_ctor_set(v___x_5538_, 1, v_k_5540_);
lean_ctor_set(v___x_5538_, 0, v___x_5544_);
v___x_5546_ = v___x_5538_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v___x_5544_);
lean_ctor_set(v_reuseFailAlloc_5550_, 1, v_k_5540_);
lean_ctor_set(v_reuseFailAlloc_5550_, 2, v_v_5541_);
lean_ctor_set(v_reuseFailAlloc_5550_, 3, v_tree_5465_);
lean_ctor_set(v_reuseFailAlloc_5550_, 4, v_l_5457_);
v___x_5546_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
lean_object* v___x_5548_; 
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 4, v_r_5458_);
lean_ctor_set(v___x_5462_, 3, v___x_5546_);
lean_ctor_set(v___x_5462_, 2, v_v_5456_);
lean_ctor_set(v___x_5462_, 1, v_k_5455_);
lean_ctor_set(v___x_5462_, 0, v___x_5543_);
v___x_5548_ = v___x_5462_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5543_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v_k_5455_);
lean_ctor_set(v_reuseFailAlloc_5549_, 2, v_v_5456_);
lean_ctor_set(v_reuseFailAlloc_5549_, 3, v___x_5546_);
lean_ctor_set(v_reuseFailAlloc_5549_, 4, v_r_5458_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
return v___x_5548_;
}
}
}
else
{
lean_object* v_k_5551_; lean_object* v_v_5552_; lean_object* v_k_5553_; lean_object* v_v_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5568_; 
lean_dec(v_size_5454_);
v_k_5551_ = lean_ctor_get(v___x_5464_, 0);
lean_inc(v_k_5551_);
v_v_5552_ = lean_ctor_get(v___x_5464_, 1);
lean_inc(v_v_5552_);
lean_dec_ref(v___x_5464_);
v_k_5553_ = lean_ctor_get(v_l_5457_, 1);
v_v_5554_ = lean_ctor_get(v_l_5457_, 2);
v_isSharedCheck_5568_ = !lean_is_exclusive(v_l_5457_);
if (v_isSharedCheck_5568_ == 0)
{
lean_object* v_unused_5569_; lean_object* v_unused_5570_; lean_object* v_unused_5571_; 
v_unused_5569_ = lean_ctor_get(v_l_5457_, 4);
lean_dec(v_unused_5569_);
v_unused_5570_ = lean_ctor_get(v_l_5457_, 3);
lean_dec(v_unused_5570_);
v_unused_5571_ = lean_ctor_get(v_l_5457_, 0);
lean_dec(v_unused_5571_);
v___x_5556_ = v_l_5457_;
v_isShared_5557_ = v_isSharedCheck_5568_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_v_5554_);
lean_inc(v_k_5553_);
lean_dec(v_l_5457_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5568_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5558_; lean_object* v___x_5560_; 
v___x_5558_ = lean_unsigned_to_nat(3u);
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 4, v_r_5458_);
lean_ctor_set(v___x_5556_, 3, v_r_5458_);
lean_ctor_set(v___x_5556_, 2, v_v_5552_);
lean_ctor_set(v___x_5556_, 1, v_k_5551_);
lean_ctor_set(v___x_5556_, 0, v___x_5459_);
v___x_5560_ = v___x_5556_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v_k_5551_);
lean_ctor_set(v_reuseFailAlloc_5567_, 2, v_v_5552_);
lean_ctor_set(v_reuseFailAlloc_5567_, 3, v_r_5458_);
lean_ctor_set(v_reuseFailAlloc_5567_, 4, v_r_5458_);
v___x_5560_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
lean_object* v___x_5562_; 
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 3, v_r_5458_);
lean_ctor_set(v___x_5538_, 0, v___x_5459_);
v___x_5562_ = v___x_5538_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v_k_5455_);
lean_ctor_set(v_reuseFailAlloc_5566_, 2, v_v_5456_);
lean_ctor_set(v_reuseFailAlloc_5566_, 3, v_r_5458_);
lean_ctor_set(v_reuseFailAlloc_5566_, 4, v_r_5458_);
v___x_5562_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
lean_object* v___x_5564_; 
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 4, v___x_5562_);
lean_ctor_set(v___x_5462_, 3, v___x_5560_);
lean_ctor_set(v___x_5462_, 2, v_v_5554_);
lean_ctor_set(v___x_5462_, 1, v_k_5553_);
lean_ctor_set(v___x_5462_, 0, v___x_5558_);
v___x_5564_ = v___x_5462_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5558_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v_k_5553_);
lean_ctor_set(v_reuseFailAlloc_5565_, 2, v_v_5554_);
lean_ctor_set(v_reuseFailAlloc_5565_, 3, v___x_5560_);
lean_ctor_set(v_reuseFailAlloc_5565_, 4, v___x_5562_);
v___x_5564_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
return v___x_5564_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5458_) == 0)
{
lean_object* v_k_5572_; lean_object* v_v_5573_; lean_object* v___x_5574_; lean_object* v___x_5576_; 
lean_dec(v_size_5454_);
v_k_5572_ = lean_ctor_get(v___x_5464_, 0);
lean_inc(v_k_5572_);
v_v_5573_ = lean_ctor_get(v___x_5464_, 1);
lean_inc(v_v_5573_);
lean_dec_ref(v___x_5464_);
v___x_5574_ = lean_unsigned_to_nat(3u);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 4, v_l_5457_);
lean_ctor_set(v___x_5538_, 2, v_v_5573_);
lean_ctor_set(v___x_5538_, 1, v_k_5572_);
lean_ctor_set(v___x_5538_, 0, v___x_5459_);
v___x_5576_ = v___x_5538_;
goto v_reusejp_5575_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5580_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5580_, 3, v_l_5457_);
lean_ctor_set(v_reuseFailAlloc_5580_, 4, v_l_5457_);
v___x_5576_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5575_;
}
v_reusejp_5575_:
{
lean_object* v___x_5578_; 
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 4, v_r_5458_);
lean_ctor_set(v___x_5462_, 3, v___x_5576_);
lean_ctor_set(v___x_5462_, 2, v_v_5456_);
lean_ctor_set(v___x_5462_, 1, v_k_5455_);
lean_ctor_set(v___x_5462_, 0, v___x_5574_);
v___x_5578_ = v___x_5462_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5574_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v_k_5455_);
lean_ctor_set(v_reuseFailAlloc_5579_, 2, v_v_5456_);
lean_ctor_set(v_reuseFailAlloc_5579_, 3, v___x_5576_);
lean_ctor_set(v_reuseFailAlloc_5579_, 4, v_r_5458_);
v___x_5578_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
return v___x_5578_;
}
}
}
else
{
lean_object* v_k_5581_; lean_object* v_v_5582_; lean_object* v___x_5584_; 
v_k_5581_ = lean_ctor_get(v___x_5464_, 0);
lean_inc(v_k_5581_);
v_v_5582_ = lean_ctor_get(v___x_5464_, 1);
lean_inc(v_v_5582_);
lean_dec_ref(v___x_5464_);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 3, v_r_5458_);
v___x_5584_ = v___x_5538_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_size_5454_);
lean_ctor_set(v_reuseFailAlloc_5589_, 1, v_k_5455_);
lean_ctor_set(v_reuseFailAlloc_5589_, 2, v_v_5456_);
lean_ctor_set(v_reuseFailAlloc_5589_, 3, v_r_5458_);
lean_ctor_set(v_reuseFailAlloc_5589_, 4, v_r_5458_);
v___x_5584_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
lean_object* v___x_5585_; lean_object* v___x_5587_; 
v___x_5585_ = lean_unsigned_to_nat(2u);
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 4, v___x_5584_);
lean_ctor_set(v___x_5462_, 3, v_r_5458_);
lean_ctor_set(v___x_5462_, 2, v_v_5582_);
lean_ctor_set(v___x_5462_, 1, v_k_5581_);
lean_ctor_set(v___x_5462_, 0, v___x_5585_);
v___x_5587_ = v___x_5462_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5585_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v_k_5581_);
lean_ctor_set(v_reuseFailAlloc_5588_, 2, v_v_5582_);
lean_ctor_set(v_reuseFailAlloc_5588_, 3, v_r_5458_);
lean_ctor_set(v_reuseFailAlloc_5588_, 4, v___x_5584_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
return v___x_5587_;
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
lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5754_; 
lean_inc(v_r_5458_);
lean_inc(v_v_5456_);
lean_inc(v_k_5455_);
v_isSharedCheck_5754_ = !lean_is_exclusive(v_r_5270_);
if (v_isSharedCheck_5754_ == 0)
{
lean_object* v_unused_5755_; lean_object* v_unused_5756_; lean_object* v_unused_5757_; lean_object* v_unused_5758_; lean_object* v_unused_5759_; 
v_unused_5755_ = lean_ctor_get(v_r_5270_, 4);
lean_dec(v_unused_5755_);
v_unused_5756_ = lean_ctor_get(v_r_5270_, 3);
lean_dec(v_unused_5756_);
v_unused_5757_ = lean_ctor_get(v_r_5270_, 2);
lean_dec(v_unused_5757_);
v_unused_5758_ = lean_ctor_get(v_r_5270_, 1);
lean_dec(v_unused_5758_);
v_unused_5759_ = lean_ctor_get(v_r_5270_, 0);
lean_dec(v_unused_5759_);
v___x_5603_ = v_r_5270_;
v_isShared_5604_ = v_isSharedCheck_5754_;
goto v_resetjp_5602_;
}
else
{
lean_dec(v_r_5270_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5754_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5605_; lean_object* v_tree_5606_; 
v___x_5605_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5455_, v_v_5456_, v_l_5457_, v_r_5458_);
v_tree_5606_ = lean_ctor_get(v___x_5605_, 2);
lean_inc(v_tree_5606_);
if (lean_obj_tag(v_tree_5606_) == 0)
{
lean_object* v_k_5607_; lean_object* v_v_5608_; lean_object* v_size_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; uint8_t v___x_5612_; 
v_k_5607_ = lean_ctor_get(v___x_5605_, 0);
lean_inc(v_k_5607_);
v_v_5608_ = lean_ctor_get(v___x_5605_, 1);
lean_inc(v_v_5608_);
lean_dec_ref(v___x_5605_);
v_size_5609_ = lean_ctor_get(v_tree_5606_, 0);
v___x_5610_ = lean_unsigned_to_nat(3u);
v___x_5611_ = lean_nat_mul(v___x_5610_, v_size_5609_);
v___x_5612_ = lean_nat_dec_lt(v___x_5611_, v_size_5449_);
lean_dec(v___x_5611_);
if (v___x_5612_ == 0)
{
lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5616_; 
lean_dec(v_r_5453_);
v___x_5613_ = lean_nat_add(v___x_5459_, v_size_5449_);
v___x_5614_ = lean_nat_add(v___x_5613_, v_size_5609_);
lean_dec(v___x_5613_);
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 4, v_tree_5606_);
lean_ctor_set(v___x_5603_, 3, v_l_5269_);
lean_ctor_set(v___x_5603_, 2, v_v_5608_);
lean_ctor_set(v___x_5603_, 1, v_k_5607_);
lean_ctor_set(v___x_5603_, 0, v___x_5614_);
v___x_5616_ = v___x_5603_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v___x_5614_);
lean_ctor_set(v_reuseFailAlloc_5617_, 1, v_k_5607_);
lean_ctor_set(v_reuseFailAlloc_5617_, 2, v_v_5608_);
lean_ctor_set(v_reuseFailAlloc_5617_, 3, v_l_5269_);
lean_ctor_set(v_reuseFailAlloc_5617_, 4, v_tree_5606_);
v___x_5616_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
return v___x_5616_;
}
}
else
{
lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5683_; 
lean_inc(v_l_5452_);
lean_inc(v_v_5451_);
lean_inc(v_k_5450_);
lean_inc(v_size_5449_);
v_isSharedCheck_5683_ = !lean_is_exclusive(v_l_5269_);
if (v_isSharedCheck_5683_ == 0)
{
lean_object* v_unused_5684_; lean_object* v_unused_5685_; lean_object* v_unused_5686_; lean_object* v_unused_5687_; lean_object* v_unused_5688_; 
v_unused_5684_ = lean_ctor_get(v_l_5269_, 4);
lean_dec(v_unused_5684_);
v_unused_5685_ = lean_ctor_get(v_l_5269_, 3);
lean_dec(v_unused_5685_);
v_unused_5686_ = lean_ctor_get(v_l_5269_, 2);
lean_dec(v_unused_5686_);
v_unused_5687_ = lean_ctor_get(v_l_5269_, 1);
lean_dec(v_unused_5687_);
v_unused_5688_ = lean_ctor_get(v_l_5269_, 0);
lean_dec(v_unused_5688_);
v___x_5619_ = v_l_5269_;
v_isShared_5620_ = v_isSharedCheck_5683_;
goto v_resetjp_5618_;
}
else
{
lean_dec(v_l_5269_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5683_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v_size_5621_; lean_object* v_size_5622_; lean_object* v_k_5623_; lean_object* v_v_5624_; lean_object* v_l_5625_; lean_object* v_r_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; uint8_t v___x_5629_; 
v_size_5621_ = lean_ctor_get(v_l_5452_, 0);
v_size_5622_ = lean_ctor_get(v_r_5453_, 0);
v_k_5623_ = lean_ctor_get(v_r_5453_, 1);
v_v_5624_ = lean_ctor_get(v_r_5453_, 2);
v_l_5625_ = lean_ctor_get(v_r_5453_, 3);
v_r_5626_ = lean_ctor_get(v_r_5453_, 4);
v___x_5627_ = lean_unsigned_to_nat(2u);
v___x_5628_ = lean_nat_mul(v___x_5627_, v_size_5621_);
v___x_5629_ = lean_nat_dec_lt(v_size_5622_, v___x_5628_);
lean_dec(v___x_5628_);
if (v___x_5629_ == 0)
{
lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5667_; 
lean_inc(v_r_5626_);
lean_inc(v_l_5625_);
lean_inc(v_v_5624_);
lean_inc(v_k_5623_);
lean_del_object(v___x_5619_);
v_isSharedCheck_5667_ = !lean_is_exclusive(v_r_5453_);
if (v_isSharedCheck_5667_ == 0)
{
lean_object* v_unused_5668_; lean_object* v_unused_5669_; lean_object* v_unused_5670_; lean_object* v_unused_5671_; lean_object* v_unused_5672_; 
v_unused_5668_ = lean_ctor_get(v_r_5453_, 4);
lean_dec(v_unused_5668_);
v_unused_5669_ = lean_ctor_get(v_r_5453_, 3);
lean_dec(v_unused_5669_);
v_unused_5670_ = lean_ctor_get(v_r_5453_, 2);
lean_dec(v_unused_5670_);
v_unused_5671_ = lean_ctor_get(v_r_5453_, 1);
lean_dec(v_unused_5671_);
v_unused_5672_ = lean_ctor_get(v_r_5453_, 0);
lean_dec(v_unused_5672_);
v___x_5631_ = v_r_5453_;
v_isShared_5632_ = v_isSharedCheck_5667_;
goto v_resetjp_5630_;
}
else
{
lean_dec(v_r_5453_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5667_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___y_5636_; lean_object* v___y_5637_; lean_object* v___y_5638_; lean_object* v___x_5655_; lean_object* v___y_5657_; 
v___x_5633_ = lean_nat_add(v___x_5459_, v_size_5449_);
lean_dec(v_size_5449_);
v___x_5634_ = lean_nat_add(v___x_5633_, v_size_5609_);
lean_dec(v___x_5633_);
v___x_5655_ = lean_nat_add(v___x_5459_, v_size_5621_);
if (lean_obj_tag(v_l_5625_) == 0)
{
lean_object* v_size_5665_; 
v_size_5665_ = lean_ctor_get(v_l_5625_, 0);
lean_inc(v_size_5665_);
v___y_5657_ = v_size_5665_;
goto v___jp_5656_;
}
else
{
lean_object* v___x_5666_; 
v___x_5666_ = lean_unsigned_to_nat(0u);
v___y_5657_ = v___x_5666_;
goto v___jp_5656_;
}
v___jp_5635_:
{
lean_object* v___x_5639_; lean_object* v___x_5641_; 
v___x_5639_ = lean_nat_add(v___y_5636_, v___y_5638_);
lean_dec(v___y_5638_);
lean_dec(v___y_5636_);
lean_inc_ref(v_tree_5606_);
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 4, v_tree_5606_);
lean_ctor_set(v___x_5631_, 3, v_r_5626_);
lean_ctor_set(v___x_5631_, 2, v_v_5608_);
lean_ctor_set(v___x_5631_, 1, v_k_5607_);
lean_ctor_set(v___x_5631_, 0, v___x_5639_);
v___x_5641_ = v___x_5631_;
goto v_reusejp_5640_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v___x_5639_);
lean_ctor_set(v_reuseFailAlloc_5654_, 1, v_k_5607_);
lean_ctor_set(v_reuseFailAlloc_5654_, 2, v_v_5608_);
lean_ctor_set(v_reuseFailAlloc_5654_, 3, v_r_5626_);
lean_ctor_set(v_reuseFailAlloc_5654_, 4, v_tree_5606_);
v___x_5641_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5640_;
}
v_reusejp_5640_:
{
lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5648_; 
v_isSharedCheck_5648_ = !lean_is_exclusive(v_tree_5606_);
if (v_isSharedCheck_5648_ == 0)
{
lean_object* v_unused_5649_; lean_object* v_unused_5650_; lean_object* v_unused_5651_; lean_object* v_unused_5652_; lean_object* v_unused_5653_; 
v_unused_5649_ = lean_ctor_get(v_tree_5606_, 4);
lean_dec(v_unused_5649_);
v_unused_5650_ = lean_ctor_get(v_tree_5606_, 3);
lean_dec(v_unused_5650_);
v_unused_5651_ = lean_ctor_get(v_tree_5606_, 2);
lean_dec(v_unused_5651_);
v_unused_5652_ = lean_ctor_get(v_tree_5606_, 1);
lean_dec(v_unused_5652_);
v_unused_5653_ = lean_ctor_get(v_tree_5606_, 0);
lean_dec(v_unused_5653_);
v___x_5643_ = v_tree_5606_;
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
else
{
lean_dec(v_tree_5606_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v___x_5646_; 
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 4, v___x_5641_);
lean_ctor_set(v___x_5643_, 3, v___y_5637_);
lean_ctor_set(v___x_5643_, 2, v_v_5624_);
lean_ctor_set(v___x_5643_, 1, v_k_5623_);
lean_ctor_set(v___x_5643_, 0, v___x_5634_);
v___x_5646_ = v___x_5643_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v___x_5634_);
lean_ctor_set(v_reuseFailAlloc_5647_, 1, v_k_5623_);
lean_ctor_set(v_reuseFailAlloc_5647_, 2, v_v_5624_);
lean_ctor_set(v_reuseFailAlloc_5647_, 3, v___y_5637_);
lean_ctor_set(v_reuseFailAlloc_5647_, 4, v___x_5641_);
v___x_5646_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
return v___x_5646_;
}
}
}
}
v___jp_5656_:
{
lean_object* v___x_5658_; lean_object* v___x_5660_; 
v___x_5658_ = lean_nat_add(v___x_5655_, v___y_5657_);
lean_dec(v___y_5657_);
lean_dec(v___x_5655_);
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 4, v_l_5625_);
lean_ctor_set(v___x_5603_, 3, v_l_5452_);
lean_ctor_set(v___x_5603_, 2, v_v_5451_);
lean_ctor_set(v___x_5603_, 1, v_k_5450_);
lean_ctor_set(v___x_5603_, 0, v___x_5658_);
v___x_5660_ = v___x_5603_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v___x_5658_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v_k_5450_);
lean_ctor_set(v_reuseFailAlloc_5664_, 2, v_v_5451_);
lean_ctor_set(v_reuseFailAlloc_5664_, 3, v_l_5452_);
lean_ctor_set(v_reuseFailAlloc_5664_, 4, v_l_5625_);
v___x_5660_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
lean_object* v___x_5661_; 
v___x_5661_ = lean_nat_add(v___x_5459_, v_size_5609_);
if (lean_obj_tag(v_r_5626_) == 0)
{
lean_object* v_size_5662_; 
v_size_5662_ = lean_ctor_get(v_r_5626_, 0);
lean_inc(v_size_5662_);
v___y_5636_ = v___x_5661_;
v___y_5637_ = v___x_5660_;
v___y_5638_ = v_size_5662_;
goto v___jp_5635_;
}
else
{
lean_object* v___x_5663_; 
v___x_5663_ = lean_unsigned_to_nat(0u);
v___y_5636_ = v___x_5661_;
v___y_5637_ = v___x_5660_;
v___y_5638_ = v___x_5663_;
goto v___jp_5635_;
}
}
}
}
}
else
{
lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5678_; 
v___x_5673_ = lean_nat_add(v___x_5459_, v_size_5449_);
lean_dec(v_size_5449_);
v___x_5674_ = lean_nat_add(v___x_5673_, v_size_5609_);
lean_dec(v___x_5673_);
v___x_5675_ = lean_nat_add(v___x_5459_, v_size_5609_);
v___x_5676_ = lean_nat_add(v___x_5675_, v_size_5622_);
lean_dec(v___x_5675_);
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 4, v_tree_5606_);
lean_ctor_set(v___x_5603_, 3, v_r_5453_);
lean_ctor_set(v___x_5603_, 2, v_v_5608_);
lean_ctor_set(v___x_5603_, 1, v_k_5607_);
lean_ctor_set(v___x_5603_, 0, v___x_5676_);
v___x_5678_ = v___x_5603_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v___x_5676_);
lean_ctor_set(v_reuseFailAlloc_5682_, 1, v_k_5607_);
lean_ctor_set(v_reuseFailAlloc_5682_, 2, v_v_5608_);
lean_ctor_set(v_reuseFailAlloc_5682_, 3, v_r_5453_);
lean_ctor_set(v_reuseFailAlloc_5682_, 4, v_tree_5606_);
v___x_5678_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
lean_object* v___x_5680_; 
if (v_isShared_5620_ == 0)
{
lean_ctor_set(v___x_5619_, 4, v___x_5678_);
lean_ctor_set(v___x_5619_, 0, v___x_5674_);
v___x_5680_ = v___x_5619_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v___x_5674_);
lean_ctor_set(v_reuseFailAlloc_5681_, 1, v_k_5450_);
lean_ctor_set(v_reuseFailAlloc_5681_, 2, v_v_5451_);
lean_ctor_set(v_reuseFailAlloc_5681_, 3, v_l_5452_);
lean_ctor_set(v_reuseFailAlloc_5681_, 4, v___x_5678_);
v___x_5680_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
return v___x_5680_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_5452_) == 0)
{
lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5712_; 
lean_inc_ref(v_l_5452_);
lean_inc(v_v_5451_);
lean_inc(v_k_5450_);
lean_inc(v_size_5449_);
v_isSharedCheck_5712_ = !lean_is_exclusive(v_l_5269_);
if (v_isSharedCheck_5712_ == 0)
{
lean_object* v_unused_5713_; lean_object* v_unused_5714_; lean_object* v_unused_5715_; lean_object* v_unused_5716_; lean_object* v_unused_5717_; 
v_unused_5713_ = lean_ctor_get(v_l_5269_, 4);
lean_dec(v_unused_5713_);
v_unused_5714_ = lean_ctor_get(v_l_5269_, 3);
lean_dec(v_unused_5714_);
v_unused_5715_ = lean_ctor_get(v_l_5269_, 2);
lean_dec(v_unused_5715_);
v_unused_5716_ = lean_ctor_get(v_l_5269_, 1);
lean_dec(v_unused_5716_);
v_unused_5717_ = lean_ctor_get(v_l_5269_, 0);
lean_dec(v_unused_5717_);
v___x_5690_ = v_l_5269_;
v_isShared_5691_ = v_isSharedCheck_5712_;
goto v_resetjp_5689_;
}
else
{
lean_dec(v_l_5269_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5712_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
if (lean_obj_tag(v_r_5453_) == 0)
{
lean_object* v_k_5692_; lean_object* v_v_5693_; lean_object* v_size_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5698_; 
v_k_5692_ = lean_ctor_get(v___x_5605_, 0);
lean_inc(v_k_5692_);
v_v_5693_ = lean_ctor_get(v___x_5605_, 1);
lean_inc(v_v_5693_);
lean_dec_ref(v___x_5605_);
v_size_5694_ = lean_ctor_get(v_r_5453_, 0);
v___x_5695_ = lean_nat_add(v___x_5459_, v_size_5449_);
lean_dec(v_size_5449_);
v___x_5696_ = lean_nat_add(v___x_5459_, v_size_5694_);
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 4, v_tree_5606_);
lean_ctor_set(v___x_5603_, 3, v_r_5453_);
lean_ctor_set(v___x_5603_, 2, v_v_5693_);
lean_ctor_set(v___x_5603_, 1, v_k_5692_);
lean_ctor_set(v___x_5603_, 0, v___x_5696_);
v___x_5698_ = v___x_5603_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5696_);
lean_ctor_set(v_reuseFailAlloc_5702_, 1, v_k_5692_);
lean_ctor_set(v_reuseFailAlloc_5702_, 2, v_v_5693_);
lean_ctor_set(v_reuseFailAlloc_5702_, 3, v_r_5453_);
lean_ctor_set(v_reuseFailAlloc_5702_, 4, v_tree_5606_);
v___x_5698_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
lean_object* v___x_5700_; 
if (v_isShared_5691_ == 0)
{
lean_ctor_set(v___x_5690_, 4, v___x_5698_);
lean_ctor_set(v___x_5690_, 0, v___x_5695_);
v___x_5700_ = v___x_5690_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v___x_5695_);
lean_ctor_set(v_reuseFailAlloc_5701_, 1, v_k_5450_);
lean_ctor_set(v_reuseFailAlloc_5701_, 2, v_v_5451_);
lean_ctor_set(v_reuseFailAlloc_5701_, 3, v_l_5452_);
lean_ctor_set(v_reuseFailAlloc_5701_, 4, v___x_5698_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
else
{
lean_object* v_k_5703_; lean_object* v_v_5704_; lean_object* v___x_5705_; lean_object* v___x_5707_; 
lean_dec(v_size_5449_);
v_k_5703_ = lean_ctor_get(v___x_5605_, 0);
lean_inc(v_k_5703_);
v_v_5704_ = lean_ctor_get(v___x_5605_, 1);
lean_inc(v_v_5704_);
lean_dec_ref(v___x_5605_);
v___x_5705_ = lean_unsigned_to_nat(3u);
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 4, v_r_5453_);
lean_ctor_set(v___x_5603_, 3, v_r_5453_);
lean_ctor_set(v___x_5603_, 2, v_v_5704_);
lean_ctor_set(v___x_5603_, 1, v_k_5703_);
lean_ctor_set(v___x_5603_, 0, v___x_5459_);
v___x_5707_ = v___x_5603_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5711_; 
v_reuseFailAlloc_5711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5711_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5711_, 1, v_k_5703_);
lean_ctor_set(v_reuseFailAlloc_5711_, 2, v_v_5704_);
lean_ctor_set(v_reuseFailAlloc_5711_, 3, v_r_5453_);
lean_ctor_set(v_reuseFailAlloc_5711_, 4, v_r_5453_);
v___x_5707_ = v_reuseFailAlloc_5711_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
lean_object* v___x_5709_; 
if (v_isShared_5691_ == 0)
{
lean_ctor_set(v___x_5690_, 4, v___x_5707_);
lean_ctor_set(v___x_5690_, 0, v___x_5705_);
v___x_5709_ = v___x_5690_;
goto v_reusejp_5708_;
}
else
{
lean_object* v_reuseFailAlloc_5710_; 
v_reuseFailAlloc_5710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5710_, 0, v___x_5705_);
lean_ctor_set(v_reuseFailAlloc_5710_, 1, v_k_5450_);
lean_ctor_set(v_reuseFailAlloc_5710_, 2, v_v_5451_);
lean_ctor_set(v_reuseFailAlloc_5710_, 3, v_l_5452_);
lean_ctor_set(v_reuseFailAlloc_5710_, 4, v___x_5707_);
v___x_5709_ = v_reuseFailAlloc_5710_;
goto v_reusejp_5708_;
}
v_reusejp_5708_:
{
return v___x_5709_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5453_) == 0)
{
lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5742_; 
lean_inc(v_l_5452_);
lean_inc(v_v_5451_);
lean_inc(v_k_5450_);
v_isSharedCheck_5742_ = !lean_is_exclusive(v_l_5269_);
if (v_isSharedCheck_5742_ == 0)
{
lean_object* v_unused_5743_; lean_object* v_unused_5744_; lean_object* v_unused_5745_; lean_object* v_unused_5746_; lean_object* v_unused_5747_; 
v_unused_5743_ = lean_ctor_get(v_l_5269_, 4);
lean_dec(v_unused_5743_);
v_unused_5744_ = lean_ctor_get(v_l_5269_, 3);
lean_dec(v_unused_5744_);
v_unused_5745_ = lean_ctor_get(v_l_5269_, 2);
lean_dec(v_unused_5745_);
v_unused_5746_ = lean_ctor_get(v_l_5269_, 1);
lean_dec(v_unused_5746_);
v_unused_5747_ = lean_ctor_get(v_l_5269_, 0);
lean_dec(v_unused_5747_);
v___x_5719_ = v_l_5269_;
v_isShared_5720_ = v_isSharedCheck_5742_;
goto v_resetjp_5718_;
}
else
{
lean_dec(v_l_5269_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5742_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v_k_5721_; lean_object* v_v_5722_; lean_object* v_k_5723_; lean_object* v_v_5724_; lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5738_; 
v_k_5721_ = lean_ctor_get(v___x_5605_, 0);
lean_inc(v_k_5721_);
v_v_5722_ = lean_ctor_get(v___x_5605_, 1);
lean_inc(v_v_5722_);
lean_dec_ref(v___x_5605_);
v_k_5723_ = lean_ctor_get(v_r_5453_, 1);
v_v_5724_ = lean_ctor_get(v_r_5453_, 2);
v_isSharedCheck_5738_ = !lean_is_exclusive(v_r_5453_);
if (v_isSharedCheck_5738_ == 0)
{
lean_object* v_unused_5739_; lean_object* v_unused_5740_; lean_object* v_unused_5741_; 
v_unused_5739_ = lean_ctor_get(v_r_5453_, 4);
lean_dec(v_unused_5739_);
v_unused_5740_ = lean_ctor_get(v_r_5453_, 3);
lean_dec(v_unused_5740_);
v_unused_5741_ = lean_ctor_get(v_r_5453_, 0);
lean_dec(v_unused_5741_);
v___x_5726_ = v_r_5453_;
v_isShared_5727_ = v_isSharedCheck_5738_;
goto v_resetjp_5725_;
}
else
{
lean_inc(v_v_5724_);
lean_inc(v_k_5723_);
lean_dec(v_r_5453_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5738_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v___x_5728_; lean_object* v___x_5730_; 
v___x_5728_ = lean_unsigned_to_nat(3u);
if (v_isShared_5727_ == 0)
{
lean_ctor_set(v___x_5726_, 4, v_l_5452_);
lean_ctor_set(v___x_5726_, 3, v_l_5452_);
lean_ctor_set(v___x_5726_, 2, v_v_5451_);
lean_ctor_set(v___x_5726_, 1, v_k_5450_);
lean_ctor_set(v___x_5726_, 0, v___x_5459_);
v___x_5730_ = v___x_5726_;
goto v_reusejp_5729_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5737_, 1, v_k_5450_);
lean_ctor_set(v_reuseFailAlloc_5737_, 2, v_v_5451_);
lean_ctor_set(v_reuseFailAlloc_5737_, 3, v_l_5452_);
lean_ctor_set(v_reuseFailAlloc_5737_, 4, v_l_5452_);
v___x_5730_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5729_;
}
v_reusejp_5729_:
{
lean_object* v___x_5732_; 
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 4, v_l_5452_);
lean_ctor_set(v___x_5603_, 3, v_l_5452_);
lean_ctor_set(v___x_5603_, 2, v_v_5722_);
lean_ctor_set(v___x_5603_, 1, v_k_5721_);
lean_ctor_set(v___x_5603_, 0, v___x_5459_);
v___x_5732_ = v___x_5603_;
goto v_reusejp_5731_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5736_, 1, v_k_5721_);
lean_ctor_set(v_reuseFailAlloc_5736_, 2, v_v_5722_);
lean_ctor_set(v_reuseFailAlloc_5736_, 3, v_l_5452_);
lean_ctor_set(v_reuseFailAlloc_5736_, 4, v_l_5452_);
v___x_5732_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5731_;
}
v_reusejp_5731_:
{
lean_object* v___x_5734_; 
if (v_isShared_5720_ == 0)
{
lean_ctor_set(v___x_5719_, 4, v___x_5732_);
lean_ctor_set(v___x_5719_, 3, v___x_5730_);
lean_ctor_set(v___x_5719_, 2, v_v_5724_);
lean_ctor_set(v___x_5719_, 1, v_k_5723_);
lean_ctor_set(v___x_5719_, 0, v___x_5728_);
v___x_5734_ = v___x_5719_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v___x_5728_);
lean_ctor_set(v_reuseFailAlloc_5735_, 1, v_k_5723_);
lean_ctor_set(v_reuseFailAlloc_5735_, 2, v_v_5724_);
lean_ctor_set(v_reuseFailAlloc_5735_, 3, v___x_5730_);
lean_ctor_set(v_reuseFailAlloc_5735_, 4, v___x_5732_);
v___x_5734_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
return v___x_5734_;
}
}
}
}
}
}
else
{
lean_object* v_k_5748_; lean_object* v_v_5749_; lean_object* v___x_5750_; lean_object* v___x_5752_; 
v_k_5748_ = lean_ctor_get(v___x_5605_, 0);
lean_inc(v_k_5748_);
v_v_5749_ = lean_ctor_get(v___x_5605_, 1);
lean_inc(v_v_5749_);
lean_dec_ref(v___x_5605_);
v___x_5750_ = lean_unsigned_to_nat(2u);
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 4, v_r_5453_);
lean_ctor_set(v___x_5603_, 3, v_l_5269_);
lean_ctor_set(v___x_5603_, 2, v_v_5749_);
lean_ctor_set(v___x_5603_, 1, v_k_5748_);
lean_ctor_set(v___x_5603_, 0, v___x_5750_);
v___x_5752_ = v___x_5603_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v___x_5750_);
lean_ctor_set(v_reuseFailAlloc_5753_, 1, v_k_5748_);
lean_ctor_set(v_reuseFailAlloc_5753_, 2, v_v_5749_);
lean_ctor_set(v_reuseFailAlloc_5753_, 3, v_l_5269_);
lean_ctor_set(v_reuseFailAlloc_5753_, 4, v_r_5453_);
v___x_5752_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
return v___x_5752_;
}
}
}
}
}
}
}
else
{
return v_l_5269_;
}
}
else
{
return v_r_5270_;
}
}
default: 
{
lean_object* v_impl_5760_; lean_object* v___x_5761_; 
v_impl_5760_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5265_, v_r_5270_);
v___x_5761_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5760_) == 0)
{
if (lean_obj_tag(v_l_5269_) == 0)
{
lean_object* v_size_5762_; lean_object* v_size_5763_; lean_object* v_k_5764_; lean_object* v_v_5765_; lean_object* v_l_5766_; lean_object* v_r_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; uint8_t v___x_5770_; 
v_size_5762_ = lean_ctor_get(v_impl_5760_, 0);
lean_inc(v_size_5762_);
v_size_5763_ = lean_ctor_get(v_l_5269_, 0);
v_k_5764_ = lean_ctor_get(v_l_5269_, 1);
v_v_5765_ = lean_ctor_get(v_l_5269_, 2);
v_l_5766_ = lean_ctor_get(v_l_5269_, 3);
v_r_5767_ = lean_ctor_get(v_l_5269_, 4);
lean_inc(v_r_5767_);
v___x_5768_ = lean_unsigned_to_nat(3u);
v___x_5769_ = lean_nat_mul(v___x_5768_, v_size_5762_);
v___x_5770_ = lean_nat_dec_lt(v___x_5769_, v_size_5763_);
lean_dec(v___x_5769_);
if (v___x_5770_ == 0)
{
lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5774_; 
lean_dec(v_r_5767_);
v___x_5771_ = lean_nat_add(v___x_5761_, v_size_5763_);
v___x_5772_ = lean_nat_add(v___x_5771_, v_size_5762_);
lean_dec(v_size_5762_);
lean_dec(v___x_5771_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v_impl_5760_);
lean_ctor_set(v___x_5272_, 0, v___x_5772_);
v___x_5774_ = v___x_5272_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5772_);
lean_ctor_set(v_reuseFailAlloc_5775_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5775_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5775_, 3, v_l_5269_);
lean_ctor_set(v_reuseFailAlloc_5775_, 4, v_impl_5760_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
else
{
lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5841_; 
lean_inc(v_l_5766_);
lean_inc(v_v_5765_);
lean_inc(v_k_5764_);
lean_inc(v_size_5763_);
v_isSharedCheck_5841_ = !lean_is_exclusive(v_l_5269_);
if (v_isSharedCheck_5841_ == 0)
{
lean_object* v_unused_5842_; lean_object* v_unused_5843_; lean_object* v_unused_5844_; lean_object* v_unused_5845_; lean_object* v_unused_5846_; 
v_unused_5842_ = lean_ctor_get(v_l_5269_, 4);
lean_dec(v_unused_5842_);
v_unused_5843_ = lean_ctor_get(v_l_5269_, 3);
lean_dec(v_unused_5843_);
v_unused_5844_ = lean_ctor_get(v_l_5269_, 2);
lean_dec(v_unused_5844_);
v_unused_5845_ = lean_ctor_get(v_l_5269_, 1);
lean_dec(v_unused_5845_);
v_unused_5846_ = lean_ctor_get(v_l_5269_, 0);
lean_dec(v_unused_5846_);
v___x_5777_ = v_l_5269_;
v_isShared_5778_ = v_isSharedCheck_5841_;
goto v_resetjp_5776_;
}
else
{
lean_dec(v_l_5269_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5841_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v_size_5779_; lean_object* v_size_5780_; lean_object* v_k_5781_; lean_object* v_v_5782_; lean_object* v_l_5783_; lean_object* v_r_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; uint8_t v___x_5787_; 
v_size_5779_ = lean_ctor_get(v_l_5766_, 0);
v_size_5780_ = lean_ctor_get(v_r_5767_, 0);
v_k_5781_ = lean_ctor_get(v_r_5767_, 1);
v_v_5782_ = lean_ctor_get(v_r_5767_, 2);
v_l_5783_ = lean_ctor_get(v_r_5767_, 3);
v_r_5784_ = lean_ctor_get(v_r_5767_, 4);
v___x_5785_ = lean_unsigned_to_nat(2u);
v___x_5786_ = lean_nat_mul(v___x_5785_, v_size_5779_);
v___x_5787_ = lean_nat_dec_lt(v_size_5780_, v___x_5786_);
lean_dec(v___x_5786_);
if (v___x_5787_ == 0)
{
lean_object* v___x_5789_; uint8_t v_isShared_5790_; uint8_t v_isSharedCheck_5816_; 
lean_inc(v_r_5784_);
lean_inc(v_l_5783_);
lean_inc(v_v_5782_);
lean_inc(v_k_5781_);
v_isSharedCheck_5816_ = !lean_is_exclusive(v_r_5767_);
if (v_isSharedCheck_5816_ == 0)
{
lean_object* v_unused_5817_; lean_object* v_unused_5818_; lean_object* v_unused_5819_; lean_object* v_unused_5820_; lean_object* v_unused_5821_; 
v_unused_5817_ = lean_ctor_get(v_r_5767_, 4);
lean_dec(v_unused_5817_);
v_unused_5818_ = lean_ctor_get(v_r_5767_, 3);
lean_dec(v_unused_5818_);
v_unused_5819_ = lean_ctor_get(v_r_5767_, 2);
lean_dec(v_unused_5819_);
v_unused_5820_ = lean_ctor_get(v_r_5767_, 1);
lean_dec(v_unused_5820_);
v_unused_5821_ = lean_ctor_get(v_r_5767_, 0);
lean_dec(v_unused_5821_);
v___x_5789_ = v_r_5767_;
v_isShared_5790_ = v_isSharedCheck_5816_;
goto v_resetjp_5788_;
}
else
{
lean_dec(v_r_5767_);
v___x_5789_ = lean_box(0);
v_isShared_5790_ = v_isSharedCheck_5816_;
goto v_resetjp_5788_;
}
v_resetjp_5788_:
{
lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___y_5794_; lean_object* v___y_5795_; lean_object* v___y_5796_; lean_object* v___x_5804_; lean_object* v___y_5806_; 
v___x_5791_ = lean_nat_add(v___x_5761_, v_size_5763_);
lean_dec(v_size_5763_);
v___x_5792_ = lean_nat_add(v___x_5791_, v_size_5762_);
lean_dec(v___x_5791_);
v___x_5804_ = lean_nat_add(v___x_5761_, v_size_5779_);
if (lean_obj_tag(v_l_5783_) == 0)
{
lean_object* v_size_5814_; 
v_size_5814_ = lean_ctor_get(v_l_5783_, 0);
lean_inc(v_size_5814_);
v___y_5806_ = v_size_5814_;
goto v___jp_5805_;
}
else
{
lean_object* v___x_5815_; 
v___x_5815_ = lean_unsigned_to_nat(0u);
v___y_5806_ = v___x_5815_;
goto v___jp_5805_;
}
v___jp_5793_:
{
lean_object* v___x_5797_; lean_object* v___x_5799_; 
v___x_5797_ = lean_nat_add(v___y_5794_, v___y_5796_);
lean_dec(v___y_5796_);
lean_dec(v___y_5794_);
if (v_isShared_5790_ == 0)
{
lean_ctor_set(v___x_5789_, 4, v_impl_5760_);
lean_ctor_set(v___x_5789_, 3, v_r_5784_);
lean_ctor_set(v___x_5789_, 2, v_v_5268_);
lean_ctor_set(v___x_5789_, 1, v_k_5267_);
lean_ctor_set(v___x_5789_, 0, v___x_5797_);
v___x_5799_ = v___x_5789_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5797_);
lean_ctor_set(v_reuseFailAlloc_5803_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5803_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5803_, 3, v_r_5784_);
lean_ctor_set(v_reuseFailAlloc_5803_, 4, v_impl_5760_);
v___x_5799_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
lean_object* v___x_5801_; 
if (v_isShared_5778_ == 0)
{
lean_ctor_set(v___x_5777_, 4, v___x_5799_);
lean_ctor_set(v___x_5777_, 3, v___y_5795_);
lean_ctor_set(v___x_5777_, 2, v_v_5782_);
lean_ctor_set(v___x_5777_, 1, v_k_5781_);
lean_ctor_set(v___x_5777_, 0, v___x_5792_);
v___x_5801_ = v___x_5777_;
goto v_reusejp_5800_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v___x_5792_);
lean_ctor_set(v_reuseFailAlloc_5802_, 1, v_k_5781_);
lean_ctor_set(v_reuseFailAlloc_5802_, 2, v_v_5782_);
lean_ctor_set(v_reuseFailAlloc_5802_, 3, v___y_5795_);
lean_ctor_set(v_reuseFailAlloc_5802_, 4, v___x_5799_);
v___x_5801_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5800_;
}
v_reusejp_5800_:
{
return v___x_5801_;
}
}
}
v___jp_5805_:
{
lean_object* v___x_5807_; lean_object* v___x_5809_; 
v___x_5807_ = lean_nat_add(v___x_5804_, v___y_5806_);
lean_dec(v___y_5806_);
lean_dec(v___x_5804_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v_l_5783_);
lean_ctor_set(v___x_5272_, 3, v_l_5766_);
lean_ctor_set(v___x_5272_, 2, v_v_5765_);
lean_ctor_set(v___x_5272_, 1, v_k_5764_);
lean_ctor_set(v___x_5272_, 0, v___x_5807_);
v___x_5809_ = v___x_5272_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5807_);
lean_ctor_set(v_reuseFailAlloc_5813_, 1, v_k_5764_);
lean_ctor_set(v_reuseFailAlloc_5813_, 2, v_v_5765_);
lean_ctor_set(v_reuseFailAlloc_5813_, 3, v_l_5766_);
lean_ctor_set(v_reuseFailAlloc_5813_, 4, v_l_5783_);
v___x_5809_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
lean_object* v___x_5810_; 
v___x_5810_ = lean_nat_add(v___x_5761_, v_size_5762_);
lean_dec(v_size_5762_);
if (lean_obj_tag(v_r_5784_) == 0)
{
lean_object* v_size_5811_; 
v_size_5811_ = lean_ctor_get(v_r_5784_, 0);
lean_inc(v_size_5811_);
v___y_5794_ = v___x_5810_;
v___y_5795_ = v___x_5809_;
v___y_5796_ = v_size_5811_;
goto v___jp_5793_;
}
else
{
lean_object* v___x_5812_; 
v___x_5812_ = lean_unsigned_to_nat(0u);
v___y_5794_ = v___x_5810_;
v___y_5795_ = v___x_5809_;
v___y_5796_ = v___x_5812_;
goto v___jp_5793_;
}
}
}
}
}
else
{
lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5827_; 
lean_del_object(v___x_5272_);
v___x_5822_ = lean_nat_add(v___x_5761_, v_size_5763_);
lean_dec(v_size_5763_);
v___x_5823_ = lean_nat_add(v___x_5822_, v_size_5762_);
lean_dec(v___x_5822_);
v___x_5824_ = lean_nat_add(v___x_5761_, v_size_5762_);
lean_dec(v_size_5762_);
v___x_5825_ = lean_nat_add(v___x_5824_, v_size_5780_);
lean_dec(v___x_5824_);
lean_inc_ref(v_impl_5760_);
if (v_isShared_5778_ == 0)
{
lean_ctor_set(v___x_5777_, 4, v_impl_5760_);
lean_ctor_set(v___x_5777_, 3, v_r_5767_);
lean_ctor_set(v___x_5777_, 2, v_v_5268_);
lean_ctor_set(v___x_5777_, 1, v_k_5267_);
lean_ctor_set(v___x_5777_, 0, v___x_5825_);
v___x_5827_ = v___x_5777_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5840_; 
v_reuseFailAlloc_5840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5840_, 0, v___x_5825_);
lean_ctor_set(v_reuseFailAlloc_5840_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5840_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5840_, 3, v_r_5767_);
lean_ctor_set(v_reuseFailAlloc_5840_, 4, v_impl_5760_);
v___x_5827_ = v_reuseFailAlloc_5840_;
goto v_reusejp_5826_;
}
v_reusejp_5826_:
{
lean_object* v___x_5829_; uint8_t v_isShared_5830_; uint8_t v_isSharedCheck_5834_; 
v_isSharedCheck_5834_ = !lean_is_exclusive(v_impl_5760_);
if (v_isSharedCheck_5834_ == 0)
{
lean_object* v_unused_5835_; lean_object* v_unused_5836_; lean_object* v_unused_5837_; lean_object* v_unused_5838_; lean_object* v_unused_5839_; 
v_unused_5835_ = lean_ctor_get(v_impl_5760_, 4);
lean_dec(v_unused_5835_);
v_unused_5836_ = lean_ctor_get(v_impl_5760_, 3);
lean_dec(v_unused_5836_);
v_unused_5837_ = lean_ctor_get(v_impl_5760_, 2);
lean_dec(v_unused_5837_);
v_unused_5838_ = lean_ctor_get(v_impl_5760_, 1);
lean_dec(v_unused_5838_);
v_unused_5839_ = lean_ctor_get(v_impl_5760_, 0);
lean_dec(v_unused_5839_);
v___x_5829_ = v_impl_5760_;
v_isShared_5830_ = v_isSharedCheck_5834_;
goto v_resetjp_5828_;
}
else
{
lean_dec(v_impl_5760_);
v___x_5829_ = lean_box(0);
v_isShared_5830_ = v_isSharedCheck_5834_;
goto v_resetjp_5828_;
}
v_resetjp_5828_:
{
lean_object* v___x_5832_; 
if (v_isShared_5830_ == 0)
{
lean_ctor_set(v___x_5829_, 4, v___x_5827_);
lean_ctor_set(v___x_5829_, 3, v_l_5766_);
lean_ctor_set(v___x_5829_, 2, v_v_5765_);
lean_ctor_set(v___x_5829_, 1, v_k_5764_);
lean_ctor_set(v___x_5829_, 0, v___x_5823_);
v___x_5832_ = v___x_5829_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5833_; 
v_reuseFailAlloc_5833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5833_, 0, v___x_5823_);
lean_ctor_set(v_reuseFailAlloc_5833_, 1, v_k_5764_);
lean_ctor_set(v_reuseFailAlloc_5833_, 2, v_v_5765_);
lean_ctor_set(v_reuseFailAlloc_5833_, 3, v_l_5766_);
lean_ctor_set(v_reuseFailAlloc_5833_, 4, v___x_5827_);
v___x_5832_ = v_reuseFailAlloc_5833_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
return v___x_5832_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5847_; lean_object* v___x_5848_; lean_object* v___x_5850_; 
v_size_5847_ = lean_ctor_get(v_impl_5760_, 0);
lean_inc(v_size_5847_);
v___x_5848_ = lean_nat_add(v___x_5761_, v_size_5847_);
lean_dec(v_size_5847_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v_impl_5760_);
lean_ctor_set(v___x_5272_, 0, v___x_5848_);
v___x_5850_ = v___x_5272_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5851_; 
v_reuseFailAlloc_5851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5851_, 0, v___x_5848_);
lean_ctor_set(v_reuseFailAlloc_5851_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5851_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5851_, 3, v_l_5269_);
lean_ctor_set(v_reuseFailAlloc_5851_, 4, v_impl_5760_);
v___x_5850_ = v_reuseFailAlloc_5851_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
return v___x_5850_;
}
}
}
else
{
if (lean_obj_tag(v_l_5269_) == 0)
{
lean_object* v_l_5852_; 
v_l_5852_ = lean_ctor_get(v_l_5269_, 3);
if (lean_obj_tag(v_l_5852_) == 0)
{
lean_object* v_r_5853_; 
lean_inc_ref(v_l_5852_);
v_r_5853_ = lean_ctor_get(v_l_5269_, 4);
lean_inc(v_r_5853_);
if (lean_obj_tag(v_r_5853_) == 0)
{
lean_object* v_size_5854_; lean_object* v_k_5855_; lean_object* v_v_5856_; lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5869_; 
v_size_5854_ = lean_ctor_get(v_l_5269_, 0);
v_k_5855_ = lean_ctor_get(v_l_5269_, 1);
v_v_5856_ = lean_ctor_get(v_l_5269_, 2);
v_isSharedCheck_5869_ = !lean_is_exclusive(v_l_5269_);
if (v_isSharedCheck_5869_ == 0)
{
lean_object* v_unused_5870_; lean_object* v_unused_5871_; 
v_unused_5870_ = lean_ctor_get(v_l_5269_, 4);
lean_dec(v_unused_5870_);
v_unused_5871_ = lean_ctor_get(v_l_5269_, 3);
lean_dec(v_unused_5871_);
v___x_5858_ = v_l_5269_;
v_isShared_5859_ = v_isSharedCheck_5869_;
goto v_resetjp_5857_;
}
else
{
lean_inc(v_v_5856_);
lean_inc(v_k_5855_);
lean_inc(v_size_5854_);
lean_dec(v_l_5269_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5869_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
lean_object* v_size_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5864_; 
v_size_5860_ = lean_ctor_get(v_r_5853_, 0);
v___x_5861_ = lean_nat_add(v___x_5761_, v_size_5854_);
lean_dec(v_size_5854_);
v___x_5862_ = lean_nat_add(v___x_5761_, v_size_5860_);
if (v_isShared_5859_ == 0)
{
lean_ctor_set(v___x_5858_, 4, v_impl_5760_);
lean_ctor_set(v___x_5858_, 3, v_r_5853_);
lean_ctor_set(v___x_5858_, 2, v_v_5268_);
lean_ctor_set(v___x_5858_, 1, v_k_5267_);
lean_ctor_set(v___x_5858_, 0, v___x_5862_);
v___x_5864_ = v___x_5858_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v___x_5862_);
lean_ctor_set(v_reuseFailAlloc_5868_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5868_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5868_, 3, v_r_5853_);
lean_ctor_set(v_reuseFailAlloc_5868_, 4, v_impl_5760_);
v___x_5864_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
lean_object* v___x_5866_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v___x_5864_);
lean_ctor_set(v___x_5272_, 3, v_l_5852_);
lean_ctor_set(v___x_5272_, 2, v_v_5856_);
lean_ctor_set(v___x_5272_, 1, v_k_5855_);
lean_ctor_set(v___x_5272_, 0, v___x_5861_);
v___x_5866_ = v___x_5272_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v___x_5861_);
lean_ctor_set(v_reuseFailAlloc_5867_, 1, v_k_5855_);
lean_ctor_set(v_reuseFailAlloc_5867_, 2, v_v_5856_);
lean_ctor_set(v_reuseFailAlloc_5867_, 3, v_l_5852_);
lean_ctor_set(v_reuseFailAlloc_5867_, 4, v___x_5864_);
v___x_5866_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
return v___x_5866_;
}
}
}
}
else
{
lean_object* v_k_5872_; lean_object* v_v_5873_; lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_5884_; 
v_k_5872_ = lean_ctor_get(v_l_5269_, 1);
v_v_5873_ = lean_ctor_get(v_l_5269_, 2);
v_isSharedCheck_5884_ = !lean_is_exclusive(v_l_5269_);
if (v_isSharedCheck_5884_ == 0)
{
lean_object* v_unused_5885_; lean_object* v_unused_5886_; lean_object* v_unused_5887_; 
v_unused_5885_ = lean_ctor_get(v_l_5269_, 4);
lean_dec(v_unused_5885_);
v_unused_5886_ = lean_ctor_get(v_l_5269_, 3);
lean_dec(v_unused_5886_);
v_unused_5887_ = lean_ctor_get(v_l_5269_, 0);
lean_dec(v_unused_5887_);
v___x_5875_ = v_l_5269_;
v_isShared_5876_ = v_isSharedCheck_5884_;
goto v_resetjp_5874_;
}
else
{
lean_inc(v_v_5873_);
lean_inc(v_k_5872_);
lean_dec(v_l_5269_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_5884_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
lean_object* v___x_5877_; lean_object* v___x_5879_; 
v___x_5877_ = lean_unsigned_to_nat(3u);
if (v_isShared_5876_ == 0)
{
lean_ctor_set(v___x_5875_, 3, v_r_5853_);
lean_ctor_set(v___x_5875_, 2, v_v_5268_);
lean_ctor_set(v___x_5875_, 1, v_k_5267_);
lean_ctor_set(v___x_5875_, 0, v___x_5761_);
v___x_5879_ = v___x_5875_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5883_; 
v_reuseFailAlloc_5883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5883_, 0, v___x_5761_);
lean_ctor_set(v_reuseFailAlloc_5883_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5883_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5883_, 3, v_r_5853_);
lean_ctor_set(v_reuseFailAlloc_5883_, 4, v_r_5853_);
v___x_5879_ = v_reuseFailAlloc_5883_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
lean_object* v___x_5881_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v___x_5879_);
lean_ctor_set(v___x_5272_, 3, v_l_5852_);
lean_ctor_set(v___x_5272_, 2, v_v_5873_);
lean_ctor_set(v___x_5272_, 1, v_k_5872_);
lean_ctor_set(v___x_5272_, 0, v___x_5877_);
v___x_5881_ = v___x_5272_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5882_; 
v_reuseFailAlloc_5882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5882_, 0, v___x_5877_);
lean_ctor_set(v_reuseFailAlloc_5882_, 1, v_k_5872_);
lean_ctor_set(v_reuseFailAlloc_5882_, 2, v_v_5873_);
lean_ctor_set(v_reuseFailAlloc_5882_, 3, v_l_5852_);
lean_ctor_set(v_reuseFailAlloc_5882_, 4, v___x_5879_);
v___x_5881_ = v_reuseFailAlloc_5882_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
return v___x_5881_;
}
}
}
}
}
else
{
lean_object* v_r_5888_; 
v_r_5888_ = lean_ctor_get(v_l_5269_, 4);
lean_inc(v_r_5888_);
if (lean_obj_tag(v_r_5888_) == 0)
{
lean_object* v_k_5889_; lean_object* v_v_5890_; lean_object* v___x_5892_; uint8_t v_isShared_5893_; uint8_t v_isSharedCheck_5913_; 
lean_inc(v_l_5852_);
v_k_5889_ = lean_ctor_get(v_l_5269_, 1);
v_v_5890_ = lean_ctor_get(v_l_5269_, 2);
v_isSharedCheck_5913_ = !lean_is_exclusive(v_l_5269_);
if (v_isSharedCheck_5913_ == 0)
{
lean_object* v_unused_5914_; lean_object* v_unused_5915_; lean_object* v_unused_5916_; 
v_unused_5914_ = lean_ctor_get(v_l_5269_, 4);
lean_dec(v_unused_5914_);
v_unused_5915_ = lean_ctor_get(v_l_5269_, 3);
lean_dec(v_unused_5915_);
v_unused_5916_ = lean_ctor_get(v_l_5269_, 0);
lean_dec(v_unused_5916_);
v___x_5892_ = v_l_5269_;
v_isShared_5893_ = v_isSharedCheck_5913_;
goto v_resetjp_5891_;
}
else
{
lean_inc(v_v_5890_);
lean_inc(v_k_5889_);
lean_dec(v_l_5269_);
v___x_5892_ = lean_box(0);
v_isShared_5893_ = v_isSharedCheck_5913_;
goto v_resetjp_5891_;
}
v_resetjp_5891_:
{
lean_object* v_k_5894_; lean_object* v_v_5895_; lean_object* v___x_5897_; uint8_t v_isShared_5898_; uint8_t v_isSharedCheck_5909_; 
v_k_5894_ = lean_ctor_get(v_r_5888_, 1);
v_v_5895_ = lean_ctor_get(v_r_5888_, 2);
v_isSharedCheck_5909_ = !lean_is_exclusive(v_r_5888_);
if (v_isSharedCheck_5909_ == 0)
{
lean_object* v_unused_5910_; lean_object* v_unused_5911_; lean_object* v_unused_5912_; 
v_unused_5910_ = lean_ctor_get(v_r_5888_, 4);
lean_dec(v_unused_5910_);
v_unused_5911_ = lean_ctor_get(v_r_5888_, 3);
lean_dec(v_unused_5911_);
v_unused_5912_ = lean_ctor_get(v_r_5888_, 0);
lean_dec(v_unused_5912_);
v___x_5897_ = v_r_5888_;
v_isShared_5898_ = v_isSharedCheck_5909_;
goto v_resetjp_5896_;
}
else
{
lean_inc(v_v_5895_);
lean_inc(v_k_5894_);
lean_dec(v_r_5888_);
v___x_5897_ = lean_box(0);
v_isShared_5898_ = v_isSharedCheck_5909_;
goto v_resetjp_5896_;
}
v_resetjp_5896_:
{
lean_object* v___x_5899_; lean_object* v___x_5901_; 
v___x_5899_ = lean_unsigned_to_nat(3u);
if (v_isShared_5898_ == 0)
{
lean_ctor_set(v___x_5897_, 4, v_l_5852_);
lean_ctor_set(v___x_5897_, 3, v_l_5852_);
lean_ctor_set(v___x_5897_, 2, v_v_5890_);
lean_ctor_set(v___x_5897_, 1, v_k_5889_);
lean_ctor_set(v___x_5897_, 0, v___x_5761_);
v___x_5901_ = v___x_5897_;
goto v_reusejp_5900_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v___x_5761_);
lean_ctor_set(v_reuseFailAlloc_5908_, 1, v_k_5889_);
lean_ctor_set(v_reuseFailAlloc_5908_, 2, v_v_5890_);
lean_ctor_set(v_reuseFailAlloc_5908_, 3, v_l_5852_);
lean_ctor_set(v_reuseFailAlloc_5908_, 4, v_l_5852_);
v___x_5901_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5900_;
}
v_reusejp_5900_:
{
lean_object* v___x_5903_; 
if (v_isShared_5893_ == 0)
{
lean_ctor_set(v___x_5892_, 4, v_l_5852_);
lean_ctor_set(v___x_5892_, 2, v_v_5268_);
lean_ctor_set(v___x_5892_, 1, v_k_5267_);
lean_ctor_set(v___x_5892_, 0, v___x_5761_);
v___x_5903_ = v___x_5892_;
goto v_reusejp_5902_;
}
else
{
lean_object* v_reuseFailAlloc_5907_; 
v_reuseFailAlloc_5907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5907_, 0, v___x_5761_);
lean_ctor_set(v_reuseFailAlloc_5907_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5907_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5907_, 3, v_l_5852_);
lean_ctor_set(v_reuseFailAlloc_5907_, 4, v_l_5852_);
v___x_5903_ = v_reuseFailAlloc_5907_;
goto v_reusejp_5902_;
}
v_reusejp_5902_:
{
lean_object* v___x_5905_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v___x_5903_);
lean_ctor_set(v___x_5272_, 3, v___x_5901_);
lean_ctor_set(v___x_5272_, 2, v_v_5895_);
lean_ctor_set(v___x_5272_, 1, v_k_5894_);
lean_ctor_set(v___x_5272_, 0, v___x_5899_);
v___x_5905_ = v___x_5272_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5906_; 
v_reuseFailAlloc_5906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5906_, 0, v___x_5899_);
lean_ctor_set(v_reuseFailAlloc_5906_, 1, v_k_5894_);
lean_ctor_set(v_reuseFailAlloc_5906_, 2, v_v_5895_);
lean_ctor_set(v_reuseFailAlloc_5906_, 3, v___x_5901_);
lean_ctor_set(v_reuseFailAlloc_5906_, 4, v___x_5903_);
v___x_5905_ = v_reuseFailAlloc_5906_;
goto v_reusejp_5904_;
}
v_reusejp_5904_:
{
return v___x_5905_;
}
}
}
}
}
}
else
{
lean_object* v___x_5917_; lean_object* v___x_5919_; 
v___x_5917_ = lean_unsigned_to_nat(2u);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v_r_5888_);
lean_ctor_set(v___x_5272_, 0, v___x_5917_);
v___x_5919_ = v___x_5272_;
goto v_reusejp_5918_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v___x_5917_);
lean_ctor_set(v_reuseFailAlloc_5920_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5920_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5920_, 3, v_l_5269_);
lean_ctor_set(v_reuseFailAlloc_5920_, 4, v_r_5888_);
v___x_5919_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5918_;
}
v_reusejp_5918_:
{
return v___x_5919_;
}
}
}
}
else
{
lean_object* v___x_5922_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 4, v_l_5269_);
lean_ctor_set(v___x_5272_, 0, v___x_5761_);
v___x_5922_ = v___x_5272_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v___x_5761_);
lean_ctor_set(v_reuseFailAlloc_5923_, 1, v_k_5267_);
lean_ctor_set(v_reuseFailAlloc_5923_, 2, v_v_5268_);
lean_ctor_set(v_reuseFailAlloc_5923_, 3, v_l_5269_);
lean_ctor_set(v_reuseFailAlloc_5923_, 4, v_l_5269_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
return v___x_5922_;
}
}
}
}
}
}
}
else
{
return v_t_5266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_5926_, lean_object* v_t_5927_){
_start:
{
lean_object* v_res_5928_; 
v_res_5928_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5926_, v_t_5927_);
lean_dec(v_k_5926_);
return v_res_5928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_5929_, lean_object* v_x_5930_){
_start:
{
if (lean_obj_tag(v_x_5930_) == 0)
{
lean_object* v_k_5931_; lean_object* v_l_5932_; lean_object* v_r_5933_; lean_object* v___x_5934_; lean_object* v_ileans_5935_; lean_object* v_workers_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_5945_; 
v_k_5931_ = lean_ctor_get(v_x_5930_, 1);
v_l_5932_ = lean_ctor_get(v_x_5930_, 3);
v_r_5933_ = lean_ctor_get(v_x_5930_, 4);
v___x_5934_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_5929_, v_l_5932_);
v_ileans_5935_ = lean_ctor_get(v___x_5934_, 0);
v_workers_5936_ = lean_ctor_get(v___x_5934_, 1);
v_isSharedCheck_5945_ = !lean_is_exclusive(v___x_5934_);
if (v_isSharedCheck_5945_ == 0)
{
v___x_5938_ = v___x_5934_;
v_isShared_5939_ = v_isSharedCheck_5945_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_workers_5936_);
lean_inc(v_ileans_5935_);
lean_dec(v___x_5934_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_5945_;
goto v_resetjp_5937_;
}
v_resetjp_5937_:
{
lean_object* v___x_5940_; lean_object* v___x_5942_; 
v___x_5940_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5931_, v_ileans_5935_);
if (v_isShared_5939_ == 0)
{
lean_ctor_set(v___x_5938_, 0, v___x_5940_);
v___x_5942_ = v___x_5938_;
goto v_reusejp_5941_;
}
else
{
lean_object* v_reuseFailAlloc_5944_; 
v_reuseFailAlloc_5944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5944_, 0, v___x_5940_);
lean_ctor_set(v_reuseFailAlloc_5944_, 1, v_workers_5936_);
v___x_5942_ = v_reuseFailAlloc_5944_;
goto v_reusejp_5941_;
}
v_reusejp_5941_:
{
v_init_5929_ = v___x_5942_;
v_x_5930_ = v_r_5933_;
goto _start;
}
}
}
else
{
return v_init_5929_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_5946_, lean_object* v_x_5947_){
_start:
{
lean_object* v_res_5948_; 
v_res_5948_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_5946_, v_x_5947_);
lean_dec(v_x_5947_);
return v_res_5948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_5949_, lean_object* v_path_5950_){
_start:
{
lean_object* v_ileans_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; 
v_ileans_5951_ = lean_ctor_get(v_self_5949_, 0);
lean_inc(v_ileans_5951_);
v___x_5952_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5950_, v_ileans_5951_);
v___x_5953_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_5949_, v___x_5952_);
lean_dec(v___x_5952_);
return v___x_5953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_5954_, lean_object* v_path_5955_){
_start:
{
lean_object* v_res_5956_; 
v_res_5956_ = l_Lean_Server_References_removeIlean(v_self_5954_, v_path_5955_);
lean_dec_ref(v_path_5955_);
return v_res_5956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_5957_, lean_object* v_k_5958_, lean_object* v_t_5959_, lean_object* v_h_5960_){
_start:
{
lean_object* v___x_5961_; 
v___x_5961_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5958_, v_t_5959_);
return v___x_5961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_5962_, lean_object* v_k_5963_, lean_object* v_t_5964_, lean_object* v_h_5965_){
_start:
{
lean_object* v_res_5966_; 
v_res_5966_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_5962_, v_k_5963_, v_t_5964_, v_h_5965_);
lean_dec(v_k_5963_);
return v_res_5966_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_5967_, lean_object* v_t_5968_, lean_object* v_hl_5969_){
_start:
{
lean_object* v___x_5970_; 
v___x_5970_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5967_, v_t_5968_);
return v___x_5970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_5971_, lean_object* v_t_5972_, lean_object* v_hl_5973_){
_start:
{
lean_object* v_res_5974_; 
v_res_5974_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_5971_, v_t_5972_, v_hl_5973_);
lean_dec_ref(v_path_5971_);
return v_res_5974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_5975_, lean_object* v_t_5976_){
_start:
{
lean_object* v___x_5977_; 
v___x_5977_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_5975_, v_t_5976_);
return v___x_5977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_5978_, lean_object* v_t_5979_){
_start:
{
lean_object* v_res_5980_; 
v_res_5980_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_5978_, v_t_5979_);
lean_dec(v_t_5979_);
return v_res_5980_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_5981_, lean_object* v_k_5982_){
_start:
{
if (lean_obj_tag(v_t_5981_) == 0)
{
lean_object* v_k_5983_; lean_object* v_v_5984_; lean_object* v_l_5985_; lean_object* v_r_5986_; uint8_t v___x_5987_; 
v_k_5983_ = lean_ctor_get(v_t_5981_, 1);
v_v_5984_ = lean_ctor_get(v_t_5981_, 2);
v_l_5985_ = lean_ctor_get(v_t_5981_, 3);
v_r_5986_ = lean_ctor_get(v_t_5981_, 4);
v___x_5987_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5982_, v_k_5983_);
switch(v___x_5987_)
{
case 0:
{
v_t_5981_ = v_l_5985_;
goto _start;
}
case 1:
{
lean_object* v___x_5989_; 
lean_inc(v_v_5984_);
v___x_5989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5989_, 0, v_v_5984_);
return v___x_5989_;
}
default: 
{
v_t_5981_ = v_r_5986_;
goto _start;
}
}
}
else
{
lean_object* v___x_5991_; 
v___x_5991_ = lean_box(0);
return v___x_5991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_5992_, lean_object* v_k_5993_){
_start:
{
lean_object* v_res_5994_; 
v_res_5994_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_5992_, v_k_5993_);
lean_dec(v_k_5993_);
lean_dec(v_t_5992_);
return v_res_5994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_5995_, lean_object* v_name_5996_, lean_object* v_moduleUri_5997_, lean_object* v_version_5998_, lean_object* v_directImports_5999_, uint8_t v_isSetupFailure_6000_){
_start:
{
lean_object* v___x_6002_; 
v___x_6002_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5999_);
if (lean_obj_tag(v___x_6002_) == 0)
{
lean_object* v_a_6003_; lean_object* v___x_6005_; uint8_t v_isShared_6006_; uint8_t v_isSharedCheck_6069_; 
v_a_6003_ = lean_ctor_get(v___x_6002_, 0);
v_isSharedCheck_6069_ = !lean_is_exclusive(v___x_6002_);
if (v_isSharedCheck_6069_ == 0)
{
v___x_6005_ = v___x_6002_;
v_isShared_6006_ = v_isSharedCheck_6069_;
goto v_resetjp_6004_;
}
else
{
lean_inc(v_a_6003_);
lean_dec(v___x_6002_);
v___x_6005_ = lean_box(0);
v_isShared_6006_ = v_isSharedCheck_6069_;
goto v_resetjp_6004_;
}
v_resetjp_6004_:
{
lean_object* v_ileans_6007_; lean_object* v_workers_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; 
v_ileans_6007_ = lean_ctor_get(v_self_5995_, 0);
v_workers_6008_ = lean_ctor_get(v_self_5995_, 1);
v___x_6009_ = lean_box(1);
v___x_6010_ = lean_box(v_isSetupFailure_6000_);
v___x_6011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6010_);
v___x_6012_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6008_, v_name_5996_);
if (lean_obj_tag(v___x_6012_) == 1)
{
lean_object* v_val_6013_; lean_object* v_version_6014_; lean_object* v_refs_6015_; lean_object* v_decls_6016_; lean_object* v___x_6018_; uint8_t v_isShared_6019_; uint8_t v_isSharedCheck_6051_; 
v_val_6013_ = lean_ctor_get(v___x_6012_, 0);
lean_inc(v_val_6013_);
lean_dec_ref(v___x_6012_);
v_version_6014_ = lean_ctor_get(v_val_6013_, 1);
v_refs_6015_ = lean_ctor_get(v_val_6013_, 4);
v_decls_6016_ = lean_ctor_get(v_val_6013_, 5);
v_isSharedCheck_6051_ = !lean_is_exclusive(v_val_6013_);
if (v_isSharedCheck_6051_ == 0)
{
lean_object* v_unused_6052_; lean_object* v_unused_6053_; lean_object* v_unused_6054_; 
v_unused_6052_ = lean_ctor_get(v_val_6013_, 3);
lean_dec(v_unused_6052_);
v_unused_6053_ = lean_ctor_get(v_val_6013_, 2);
lean_dec(v_unused_6053_);
v_unused_6054_ = lean_ctor_get(v_val_6013_, 0);
lean_dec(v_unused_6054_);
v___x_6018_ = v_val_6013_;
v_isShared_6019_ = v_isSharedCheck_6051_;
goto v_resetjp_6017_;
}
else
{
lean_inc(v_decls_6016_);
lean_inc(v_refs_6015_);
lean_inc(v_version_6014_);
lean_dec(v_val_6013_);
v___x_6018_ = lean_box(0);
v_isShared_6019_ = v_isSharedCheck_6051_;
goto v_resetjp_6017_;
}
v_resetjp_6017_:
{
uint8_t v___x_6020_; 
v___x_6020_ = lean_nat_dec_lt(v_version_5998_, v_version_6014_);
if (v___x_6020_ == 0)
{
lean_object* v___x_6022_; uint8_t v_isShared_6023_; uint8_t v_isSharedCheck_6045_; 
lean_inc(v_workers_6008_);
lean_inc(v_ileans_6007_);
v_isSharedCheck_6045_ = !lean_is_exclusive(v_self_5995_);
if (v_isSharedCheck_6045_ == 0)
{
lean_object* v_unused_6046_; lean_object* v_unused_6047_; 
v_unused_6046_ = lean_ctor_get(v_self_5995_, 1);
lean_dec(v_unused_6046_);
v_unused_6047_ = lean_ctor_get(v_self_5995_, 0);
lean_dec(v_unused_6047_);
v___x_6022_ = v_self_5995_;
v_isShared_6023_ = v_isSharedCheck_6045_;
goto v_resetjp_6021_;
}
else
{
lean_dec(v_self_5995_);
v___x_6022_ = lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6045_;
goto v_resetjp_6021_;
}
v_resetjp_6021_:
{
uint8_t v___x_6024_; 
v___x_6024_ = lean_nat_dec_eq(v_version_5998_, v_version_6014_);
lean_dec(v_version_6014_);
if (v___x_6024_ == 0)
{
lean_object* v___x_6026_; 
lean_dec(v_decls_6016_);
lean_dec(v_refs_6015_);
if (v_isShared_6019_ == 0)
{
lean_ctor_set(v___x_6018_, 5, v___x_6009_);
lean_ctor_set(v___x_6018_, 4, v___x_6009_);
lean_ctor_set(v___x_6018_, 3, v___x_6011_);
lean_ctor_set(v___x_6018_, 2, v_a_6003_);
lean_ctor_set(v___x_6018_, 1, v_version_5998_);
lean_ctor_set(v___x_6018_, 0, v_moduleUri_5997_);
v___x_6026_ = v___x_6018_;
goto v_reusejp_6025_;
}
else
{
lean_object* v_reuseFailAlloc_6034_; 
v_reuseFailAlloc_6034_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_moduleUri_5997_);
lean_ctor_set(v_reuseFailAlloc_6034_, 1, v_version_5998_);
lean_ctor_set(v_reuseFailAlloc_6034_, 2, v_a_6003_);
lean_ctor_set(v_reuseFailAlloc_6034_, 3, v___x_6011_);
lean_ctor_set(v_reuseFailAlloc_6034_, 4, v___x_6009_);
lean_ctor_set(v_reuseFailAlloc_6034_, 5, v___x_6009_);
v___x_6026_ = v_reuseFailAlloc_6034_;
goto v_reusejp_6025_;
}
v_reusejp_6025_:
{
lean_object* v___x_6027_; lean_object* v___x_6029_; 
v___x_6027_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_5996_, v___x_6026_, v_workers_6008_);
if (v_isShared_6023_ == 0)
{
lean_ctor_set(v___x_6022_, 1, v___x_6027_);
v___x_6029_ = v___x_6022_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v_ileans_6007_);
lean_ctor_set(v_reuseFailAlloc_6033_, 1, v___x_6027_);
v___x_6029_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
lean_object* v___x_6031_; 
if (v_isShared_6006_ == 0)
{
lean_ctor_set(v___x_6005_, 0, v___x_6029_);
v___x_6031_ = v___x_6005_;
goto v_reusejp_6030_;
}
else
{
lean_object* v_reuseFailAlloc_6032_; 
v_reuseFailAlloc_6032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6032_, 0, v___x_6029_);
v___x_6031_ = v_reuseFailAlloc_6032_;
goto v_reusejp_6030_;
}
v_reusejp_6030_:
{
return v___x_6031_;
}
}
}
}
else
{
lean_object* v___x_6036_; 
if (v_isShared_6019_ == 0)
{
lean_ctor_set(v___x_6018_, 3, v___x_6011_);
lean_ctor_set(v___x_6018_, 2, v_a_6003_);
lean_ctor_set(v___x_6018_, 1, v_version_5998_);
lean_ctor_set(v___x_6018_, 0, v_moduleUri_5997_);
v___x_6036_ = v___x_6018_;
goto v_reusejp_6035_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v_moduleUri_5997_);
lean_ctor_set(v_reuseFailAlloc_6044_, 1, v_version_5998_);
lean_ctor_set(v_reuseFailAlloc_6044_, 2, v_a_6003_);
lean_ctor_set(v_reuseFailAlloc_6044_, 3, v___x_6011_);
lean_ctor_set(v_reuseFailAlloc_6044_, 4, v_refs_6015_);
lean_ctor_set(v_reuseFailAlloc_6044_, 5, v_decls_6016_);
v___x_6036_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6035_;
}
v_reusejp_6035_:
{
lean_object* v___x_6037_; lean_object* v___x_6039_; 
v___x_6037_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_5996_, v___x_6036_, v_workers_6008_);
if (v_isShared_6023_ == 0)
{
lean_ctor_set(v___x_6022_, 1, v___x_6037_);
v___x_6039_ = v___x_6022_;
goto v_reusejp_6038_;
}
else
{
lean_object* v_reuseFailAlloc_6043_; 
v_reuseFailAlloc_6043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_ileans_6007_);
lean_ctor_set(v_reuseFailAlloc_6043_, 1, v___x_6037_);
v___x_6039_ = v_reuseFailAlloc_6043_;
goto v_reusejp_6038_;
}
v_reusejp_6038_:
{
lean_object* v___x_6041_; 
if (v_isShared_6006_ == 0)
{
lean_ctor_set(v___x_6005_, 0, v___x_6039_);
v___x_6041_ = v___x_6005_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6042_; 
v_reuseFailAlloc_6042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6042_, 0, v___x_6039_);
v___x_6041_ = v_reuseFailAlloc_6042_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
return v___x_6041_;
}
}
}
}
}
}
else
{
lean_object* v___x_6049_; 
lean_del_object(v___x_6018_);
lean_dec(v_decls_6016_);
lean_dec(v_refs_6015_);
lean_dec(v_version_6014_);
lean_dec_ref(v___x_6011_);
lean_dec(v_a_6003_);
lean_dec(v_version_5998_);
lean_dec_ref(v_moduleUri_5997_);
lean_dec(v_name_5996_);
if (v_isShared_6006_ == 0)
{
lean_ctor_set(v___x_6005_, 0, v_self_5995_);
v___x_6049_ = v___x_6005_;
goto v_reusejp_6048_;
}
else
{
lean_object* v_reuseFailAlloc_6050_; 
v_reuseFailAlloc_6050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6050_, 0, v_self_5995_);
v___x_6049_ = v_reuseFailAlloc_6050_;
goto v_reusejp_6048_;
}
v_reusejp_6048_:
{
return v___x_6049_;
}
}
}
}
else
{
lean_object* v___x_6056_; uint8_t v_isShared_6057_; uint8_t v_isSharedCheck_6066_; 
lean_inc(v_workers_6008_);
lean_inc(v_ileans_6007_);
lean_dec(v___x_6012_);
v_isSharedCheck_6066_ = !lean_is_exclusive(v_self_5995_);
if (v_isSharedCheck_6066_ == 0)
{
lean_object* v_unused_6067_; lean_object* v_unused_6068_; 
v_unused_6067_ = lean_ctor_get(v_self_5995_, 1);
lean_dec(v_unused_6067_);
v_unused_6068_ = lean_ctor_get(v_self_5995_, 0);
lean_dec(v_unused_6068_);
v___x_6056_ = v_self_5995_;
v_isShared_6057_ = v_isSharedCheck_6066_;
goto v_resetjp_6055_;
}
else
{
lean_dec(v_self_5995_);
v___x_6056_ = lean_box(0);
v_isShared_6057_ = v_isSharedCheck_6066_;
goto v_resetjp_6055_;
}
v_resetjp_6055_:
{
lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6061_; 
v___x_6058_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6058_, 0, v_moduleUri_5997_);
lean_ctor_set(v___x_6058_, 1, v_version_5998_);
lean_ctor_set(v___x_6058_, 2, v_a_6003_);
lean_ctor_set(v___x_6058_, 3, v___x_6011_);
lean_ctor_set(v___x_6058_, 4, v___x_6009_);
lean_ctor_set(v___x_6058_, 5, v___x_6009_);
v___x_6059_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_5996_, v___x_6058_, v_workers_6008_);
if (v_isShared_6057_ == 0)
{
lean_ctor_set(v___x_6056_, 1, v___x_6059_);
v___x_6061_ = v___x_6056_;
goto v_reusejp_6060_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_ileans_6007_);
lean_ctor_set(v_reuseFailAlloc_6065_, 1, v___x_6059_);
v___x_6061_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6060_;
}
v_reusejp_6060_:
{
lean_object* v___x_6063_; 
if (v_isShared_6006_ == 0)
{
lean_ctor_set(v___x_6005_, 0, v___x_6061_);
v___x_6063_ = v___x_6005_;
goto v_reusejp_6062_;
}
else
{
lean_object* v_reuseFailAlloc_6064_; 
v_reuseFailAlloc_6064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6064_, 0, v___x_6061_);
v___x_6063_ = v_reuseFailAlloc_6064_;
goto v_reusejp_6062_;
}
v_reusejp_6062_:
{
return v___x_6063_;
}
}
}
}
}
}
else
{
lean_object* v_a_6070_; lean_object* v___x_6072_; uint8_t v_isShared_6073_; uint8_t v_isSharedCheck_6077_; 
lean_dec(v_version_5998_);
lean_dec_ref(v_moduleUri_5997_);
lean_dec(v_name_5996_);
lean_dec_ref(v_self_5995_);
v_a_6070_ = lean_ctor_get(v___x_6002_, 0);
v_isSharedCheck_6077_ = !lean_is_exclusive(v___x_6002_);
if (v_isSharedCheck_6077_ == 0)
{
v___x_6072_ = v___x_6002_;
v_isShared_6073_ = v_isSharedCheck_6077_;
goto v_resetjp_6071_;
}
else
{
lean_inc(v_a_6070_);
lean_dec(v___x_6002_);
v___x_6072_ = lean_box(0);
v_isShared_6073_ = v_isSharedCheck_6077_;
goto v_resetjp_6071_;
}
v_resetjp_6071_:
{
lean_object* v___x_6075_; 
if (v_isShared_6073_ == 0)
{
v___x_6075_ = v___x_6072_;
goto v_reusejp_6074_;
}
else
{
lean_object* v_reuseFailAlloc_6076_; 
v_reuseFailAlloc_6076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6076_, 0, v_a_6070_);
v___x_6075_ = v_reuseFailAlloc_6076_;
goto v_reusejp_6074_;
}
v_reusejp_6074_:
{
return v___x_6075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6078_, lean_object* v_name_6079_, lean_object* v_moduleUri_6080_, lean_object* v_version_6081_, lean_object* v_directImports_6082_, lean_object* v_isSetupFailure_6083_, lean_object* v_a_6084_){
_start:
{
uint8_t v_isSetupFailure_boxed_6085_; lean_object* v_res_6086_; 
v_isSetupFailure_boxed_6085_ = lean_unbox(v_isSetupFailure_6083_);
v_res_6086_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6078_, v_name_6079_, v_moduleUri_6080_, v_version_6081_, v_directImports_6082_, v_isSetupFailure_boxed_6085_);
lean_dec_ref(v_directImports_6082_);
return v_res_6086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6087_, lean_object* v_t_6088_, lean_object* v_k_6089_){
_start:
{
lean_object* v___x_6090_; 
v___x_6090_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6088_, v_k_6089_);
return v___x_6090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6091_, lean_object* v_t_6092_, lean_object* v_k_6093_){
_start:
{
lean_object* v_res_6094_; 
v_res_6094_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6091_, v_t_6092_, v_k_6093_);
lean_dec(v_k_6093_);
lean_dec(v_t_6092_);
return v_res_6094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6095_, lean_object* v_____s_6096_){
_start:
{
lean_object* v_fst_6097_; lean_object* v_snd_6098_; lean_object* v_r_6099_; lean_object* v___x_6100_; 
v_fst_6097_ = lean_ctor_get(v_x_6095_, 0);
lean_inc(v_fst_6097_);
v_snd_6098_ = lean_ctor_get(v_x_6095_, 1);
lean_inc(v_snd_6098_);
lean_dec_ref(v_x_6095_);
v_r_6099_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6097_, v_snd_6098_, v_____s_6096_);
v___x_6100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6100_, 0, v_r_6099_);
return v___x_6100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6101_, lean_object* v_k_6102_, lean_object* v_fallback_6103_){
_start:
{
if (lean_obj_tag(v_t_6101_) == 0)
{
lean_object* v_k_6104_; lean_object* v_v_6105_; lean_object* v_l_6106_; lean_object* v_r_6107_; uint8_t v___x_6108_; 
v_k_6104_ = lean_ctor_get(v_t_6101_, 1);
v_v_6105_ = lean_ctor_get(v_t_6101_, 2);
v_l_6106_ = lean_ctor_get(v_t_6101_, 3);
v_r_6107_ = lean_ctor_get(v_t_6101_, 4);
v___x_6108_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6102_, v_k_6104_);
switch(v___x_6108_)
{
case 0:
{
v_t_6101_ = v_l_6106_;
goto _start;
}
case 1:
{
lean_inc(v_v_6105_);
return v_v_6105_;
}
default: 
{
v_t_6101_ = v_r_6107_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6103_);
return v_fallback_6103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6111_, lean_object* v_k_6112_, lean_object* v_fallback_6113_){
_start:
{
lean_object* v_res_6114_; 
v_res_6114_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6111_, v_k_6112_, v_fallback_6113_);
lean_dec(v_fallback_6113_);
lean_dec_ref(v_k_6112_);
lean_dec(v_t_6111_);
return v_res_6114_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6115_, lean_object* v_x_6116_){
_start:
{
if (lean_obj_tag(v_x_6116_) == 0)
{
lean_object* v_k_6117_; lean_object* v_v_6118_; lean_object* v_l_6119_; lean_object* v_r_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; 
v_k_6117_ = lean_ctor_get(v_x_6116_, 1);
lean_inc(v_k_6117_);
v_v_6118_ = lean_ctor_get(v_x_6116_, 2);
lean_inc(v_v_6118_);
v_l_6119_ = lean_ctor_get(v_x_6116_, 3);
lean_inc(v_l_6119_);
v_r_6120_ = lean_ctor_get(v_x_6116_, 4);
lean_inc(v_r_6120_);
lean_dec_ref(v_x_6116_);
v___x_6121_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6115_, v_l_6119_);
v___x_6122_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6123_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6121_, v_k_6117_, v___x_6122_);
v___x_6124_ = l_Lean_Lsp_RefInfo_merge(v___x_6123_, v_v_6118_);
v___x_6125_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6117_, v___x_6124_, v___x_6121_);
v_init_6115_ = v___x_6125_;
v_x_6116_ = v_r_6120_;
goto _start;
}
else
{
return v_init_6115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6128_, lean_object* v_name_6129_, lean_object* v_moduleUri_6130_, lean_object* v_version_6131_, lean_object* v_refs_6132_, lean_object* v_decls_6133_){
_start:
{
lean_object* v_ileans_6135_; lean_object* v_workers_6136_; lean_object* v___x_6137_; 
v_ileans_6135_ = lean_ctor_get(v_self_6128_, 0);
v_workers_6136_ = lean_ctor_get(v_self_6128_, 1);
v___x_6137_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6136_, v_name_6129_);
if (lean_obj_tag(v___x_6137_) == 1)
{
lean_object* v_val_6138_; lean_object* v___x_6140_; uint8_t v_isShared_6141_; uint8_t v_isSharedCheck_6186_; 
v_val_6138_ = lean_ctor_get(v___x_6137_, 0);
v_isSharedCheck_6186_ = !lean_is_exclusive(v___x_6137_);
if (v_isSharedCheck_6186_ == 0)
{
v___x_6140_ = v___x_6137_;
v_isShared_6141_ = v_isSharedCheck_6186_;
goto v_resetjp_6139_;
}
else
{
lean_inc(v_val_6138_);
lean_dec(v___x_6137_);
v___x_6140_ = lean_box(0);
v_isShared_6141_ = v_isSharedCheck_6186_;
goto v_resetjp_6139_;
}
v_resetjp_6139_:
{
lean_object* v_version_6142_; lean_object* v_directImports_6143_; lean_object* v_isSetupFailure_x3f_6144_; lean_object* v_refs_6145_; lean_object* v_decls_6146_; lean_object* v___x_6148_; uint8_t v_isShared_6149_; uint8_t v_isSharedCheck_6184_; 
v_version_6142_ = lean_ctor_get(v_val_6138_, 1);
v_directImports_6143_ = lean_ctor_get(v_val_6138_, 2);
v_isSetupFailure_x3f_6144_ = lean_ctor_get(v_val_6138_, 3);
v_refs_6145_ = lean_ctor_get(v_val_6138_, 4);
v_decls_6146_ = lean_ctor_get(v_val_6138_, 5);
v_isSharedCheck_6184_ = !lean_is_exclusive(v_val_6138_);
if (v_isSharedCheck_6184_ == 0)
{
lean_object* v_unused_6185_; 
v_unused_6185_ = lean_ctor_get(v_val_6138_, 0);
lean_dec(v_unused_6185_);
v___x_6148_ = v_val_6138_;
v_isShared_6149_ = v_isSharedCheck_6184_;
goto v_resetjp_6147_;
}
else
{
lean_inc(v_decls_6146_);
lean_inc(v_refs_6145_);
lean_inc(v_isSetupFailure_x3f_6144_);
lean_inc(v_directImports_6143_);
lean_inc(v_version_6142_);
lean_dec(v_val_6138_);
v___x_6148_ = lean_box(0);
v_isShared_6149_ = v_isSharedCheck_6184_;
goto v_resetjp_6147_;
}
v_resetjp_6147_:
{
uint8_t v___x_6150_; 
v___x_6150_ = lean_nat_dec_lt(v_version_6131_, v_version_6142_);
if (v___x_6150_ == 0)
{
lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6178_; 
lean_inc(v_workers_6136_);
lean_inc(v_ileans_6135_);
v_isSharedCheck_6178_ = !lean_is_exclusive(v_self_6128_);
if (v_isSharedCheck_6178_ == 0)
{
lean_object* v_unused_6179_; lean_object* v_unused_6180_; 
v_unused_6179_ = lean_ctor_get(v_self_6128_, 1);
lean_dec(v_unused_6179_);
v_unused_6180_ = lean_ctor_get(v_self_6128_, 0);
lean_dec(v_unused_6180_);
v___x_6152_ = v_self_6128_;
v_isShared_6153_ = v_isSharedCheck_6178_;
goto v_resetjp_6151_;
}
else
{
lean_dec(v_self_6128_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6178_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
uint8_t v___x_6154_; 
v___x_6154_ = lean_nat_dec_eq(v_version_6131_, v_version_6142_);
lean_dec(v_version_6142_);
if (v___x_6154_ == 0)
{
lean_object* v___x_6156_; 
lean_dec(v_decls_6146_);
lean_dec(v_refs_6145_);
if (v_isShared_6149_ == 0)
{
lean_ctor_set(v___x_6148_, 5, v_decls_6133_);
lean_ctor_set(v___x_6148_, 4, v_refs_6132_);
lean_ctor_set(v___x_6148_, 1, v_version_6131_);
lean_ctor_set(v___x_6148_, 0, v_moduleUri_6130_);
v___x_6156_ = v___x_6148_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6164_; 
v_reuseFailAlloc_6164_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6164_, 0, v_moduleUri_6130_);
lean_ctor_set(v_reuseFailAlloc_6164_, 1, v_version_6131_);
lean_ctor_set(v_reuseFailAlloc_6164_, 2, v_directImports_6143_);
lean_ctor_set(v_reuseFailAlloc_6164_, 3, v_isSetupFailure_x3f_6144_);
lean_ctor_set(v_reuseFailAlloc_6164_, 4, v_refs_6132_);
lean_ctor_set(v_reuseFailAlloc_6164_, 5, v_decls_6133_);
v___x_6156_ = v_reuseFailAlloc_6164_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
lean_object* v___x_6157_; lean_object* v___x_6159_; 
v___x_6157_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6129_, v___x_6156_, v_workers_6136_);
if (v_isShared_6153_ == 0)
{
lean_ctor_set(v___x_6152_, 1, v___x_6157_);
v___x_6159_ = v___x_6152_;
goto v_reusejp_6158_;
}
else
{
lean_object* v_reuseFailAlloc_6163_; 
v_reuseFailAlloc_6163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6163_, 0, v_ileans_6135_);
lean_ctor_set(v_reuseFailAlloc_6163_, 1, v___x_6157_);
v___x_6159_ = v_reuseFailAlloc_6163_;
goto v_reusejp_6158_;
}
v_reusejp_6158_:
{
lean_object* v___x_6161_; 
if (v_isShared_6141_ == 0)
{
lean_ctor_set_tag(v___x_6140_, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6159_);
v___x_6161_ = v___x_6140_;
goto v_reusejp_6160_;
}
else
{
lean_object* v_reuseFailAlloc_6162_; 
v_reuseFailAlloc_6162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6162_, 0, v___x_6159_);
v___x_6161_ = v_reuseFailAlloc_6162_;
goto v_reusejp_6160_;
}
v_reusejp_6160_:
{
return v___x_6161_;
}
}
}
}
else
{
lean_object* v___f_6165_; lean_object* v_mergedRefs_6166_; lean_object* v_mergedDecls_6167_; lean_object* v___x_6169_; 
v___f_6165_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6166_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6145_, v_refs_6132_);
v_mergedDecls_6167_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6133_, v_decls_6146_, v___f_6165_);
lean_dec(v_decls_6133_);
if (v_isShared_6149_ == 0)
{
lean_ctor_set(v___x_6148_, 5, v_mergedDecls_6167_);
lean_ctor_set(v___x_6148_, 4, v_mergedRefs_6166_);
lean_ctor_set(v___x_6148_, 1, v_version_6131_);
lean_ctor_set(v___x_6148_, 0, v_moduleUri_6130_);
v___x_6169_ = v___x_6148_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6177_; 
v_reuseFailAlloc_6177_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6177_, 0, v_moduleUri_6130_);
lean_ctor_set(v_reuseFailAlloc_6177_, 1, v_version_6131_);
lean_ctor_set(v_reuseFailAlloc_6177_, 2, v_directImports_6143_);
lean_ctor_set(v_reuseFailAlloc_6177_, 3, v_isSetupFailure_x3f_6144_);
lean_ctor_set(v_reuseFailAlloc_6177_, 4, v_mergedRefs_6166_);
lean_ctor_set(v_reuseFailAlloc_6177_, 5, v_mergedDecls_6167_);
v___x_6169_ = v_reuseFailAlloc_6177_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
lean_object* v___x_6170_; lean_object* v___x_6172_; 
v___x_6170_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6129_, v___x_6169_, v_workers_6136_);
if (v_isShared_6153_ == 0)
{
lean_ctor_set(v___x_6152_, 1, v___x_6170_);
v___x_6172_ = v___x_6152_;
goto v_reusejp_6171_;
}
else
{
lean_object* v_reuseFailAlloc_6176_; 
v_reuseFailAlloc_6176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6176_, 0, v_ileans_6135_);
lean_ctor_set(v_reuseFailAlloc_6176_, 1, v___x_6170_);
v___x_6172_ = v_reuseFailAlloc_6176_;
goto v_reusejp_6171_;
}
v_reusejp_6171_:
{
lean_object* v___x_6174_; 
if (v_isShared_6141_ == 0)
{
lean_ctor_set_tag(v___x_6140_, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6172_);
v___x_6174_ = v___x_6140_;
goto v_reusejp_6173_;
}
else
{
lean_object* v_reuseFailAlloc_6175_; 
v_reuseFailAlloc_6175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6175_, 0, v___x_6172_);
v___x_6174_ = v_reuseFailAlloc_6175_;
goto v_reusejp_6173_;
}
v_reusejp_6173_:
{
return v___x_6174_;
}
}
}
}
}
}
else
{
lean_object* v___x_6182_; 
lean_del_object(v___x_6148_);
lean_dec(v_decls_6146_);
lean_dec(v_refs_6145_);
lean_dec(v_isSetupFailure_x3f_6144_);
lean_dec_ref(v_directImports_6143_);
lean_dec(v_version_6142_);
lean_dec(v_decls_6133_);
lean_dec(v_refs_6132_);
lean_dec(v_version_6131_);
lean_dec_ref(v_moduleUri_6130_);
lean_dec(v_name_6129_);
if (v_isShared_6141_ == 0)
{
lean_ctor_set_tag(v___x_6140_, 0);
lean_ctor_set(v___x_6140_, 0, v_self_6128_);
v___x_6182_ = v___x_6140_;
goto v_reusejp_6181_;
}
else
{
lean_object* v_reuseFailAlloc_6183_; 
v_reuseFailAlloc_6183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6183_, 0, v_self_6128_);
v___x_6182_ = v_reuseFailAlloc_6183_;
goto v_reusejp_6181_;
}
v_reusejp_6181_:
{
return v___x_6182_;
}
}
}
}
}
else
{
lean_object* v___x_6188_; uint8_t v_isShared_6189_; uint8_t v_isSharedCheck_6198_; 
lean_inc(v_workers_6136_);
lean_inc(v_ileans_6135_);
lean_dec(v___x_6137_);
v_isSharedCheck_6198_ = !lean_is_exclusive(v_self_6128_);
if (v_isSharedCheck_6198_ == 0)
{
lean_object* v_unused_6199_; lean_object* v_unused_6200_; 
v_unused_6199_ = lean_ctor_get(v_self_6128_, 1);
lean_dec(v_unused_6199_);
v_unused_6200_ = lean_ctor_get(v_self_6128_, 0);
lean_dec(v_unused_6200_);
v___x_6188_ = v_self_6128_;
v_isShared_6189_ = v_isSharedCheck_6198_;
goto v_resetjp_6187_;
}
else
{
lean_dec(v_self_6128_);
v___x_6188_ = lean_box(0);
v_isShared_6189_ = v_isSharedCheck_6198_;
goto v_resetjp_6187_;
}
v_resetjp_6187_:
{
lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6195_; 
v___x_6190_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6191_ = lean_box(0);
v___x_6192_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6192_, 0, v_moduleUri_6130_);
lean_ctor_set(v___x_6192_, 1, v_version_6131_);
lean_ctor_set(v___x_6192_, 2, v___x_6190_);
lean_ctor_set(v___x_6192_, 3, v___x_6191_);
lean_ctor_set(v___x_6192_, 4, v_refs_6132_);
lean_ctor_set(v___x_6192_, 5, v_decls_6133_);
v___x_6193_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6129_, v___x_6192_, v_workers_6136_);
if (v_isShared_6189_ == 0)
{
lean_ctor_set(v___x_6188_, 1, v___x_6193_);
v___x_6195_ = v___x_6188_;
goto v_reusejp_6194_;
}
else
{
lean_object* v_reuseFailAlloc_6197_; 
v_reuseFailAlloc_6197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6197_, 0, v_ileans_6135_);
lean_ctor_set(v_reuseFailAlloc_6197_, 1, v___x_6193_);
v___x_6195_ = v_reuseFailAlloc_6197_;
goto v_reusejp_6194_;
}
v_reusejp_6194_:
{
lean_object* v___x_6196_; 
v___x_6196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6196_, 0, v___x_6195_);
return v___x_6196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6201_, lean_object* v_name_6202_, lean_object* v_moduleUri_6203_, lean_object* v_version_6204_, lean_object* v_refs_6205_, lean_object* v_decls_6206_, lean_object* v_a_6207_){
_start:
{
lean_object* v_res_6208_; 
v_res_6208_ = l_Lean_Server_References_updateWorkerRefs(v_self_6201_, v_name_6202_, v_moduleUri_6203_, v_version_6204_, v_refs_6205_, v_decls_6206_);
return v_res_6208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6209_, lean_object* v_t_6210_, lean_object* v_k_6211_, lean_object* v_fallback_6212_){
_start:
{
lean_object* v___x_6213_; 
v___x_6213_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6210_, v_k_6211_, v_fallback_6212_);
return v___x_6213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6214_, lean_object* v_t_6215_, lean_object* v_k_6216_, lean_object* v_fallback_6217_){
_start:
{
lean_object* v_res_6218_; 
v_res_6218_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6214_, v_t_6215_, v_k_6216_, v_fallback_6217_);
lean_dec(v_fallback_6217_);
lean_dec_ref(v_k_6216_);
lean_dec(v_t_6215_);
return v_res_6218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6219_, lean_object* v_t_6220_){
_start:
{
lean_object* v___x_6221_; 
v___x_6221_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6219_, v_t_6220_);
return v___x_6221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6222_, lean_object* v_name_6223_, lean_object* v_moduleUri_6224_, lean_object* v_version_6225_, lean_object* v_refs_6226_, lean_object* v_decls_6227_){
_start:
{
lean_object* v_ileans_6229_; lean_object* v_workers_6230_; lean_object* v___x_6231_; 
v_ileans_6229_ = lean_ctor_get(v_self_6222_, 0);
v_workers_6230_ = lean_ctor_get(v_self_6222_, 1);
v___x_6231_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6230_, v_name_6223_);
if (lean_obj_tag(v___x_6231_) == 1)
{
lean_object* v_val_6232_; lean_object* v___x_6234_; uint8_t v_isShared_6235_; uint8_t v_isSharedCheck_6266_; 
v_val_6232_ = lean_ctor_get(v___x_6231_, 0);
v_isSharedCheck_6266_ = !lean_is_exclusive(v___x_6231_);
if (v_isSharedCheck_6266_ == 0)
{
v___x_6234_ = v___x_6231_;
v_isShared_6235_ = v_isSharedCheck_6266_;
goto v_resetjp_6233_;
}
else
{
lean_inc(v_val_6232_);
lean_dec(v___x_6231_);
v___x_6234_ = lean_box(0);
v_isShared_6235_ = v_isSharedCheck_6266_;
goto v_resetjp_6233_;
}
v_resetjp_6233_:
{
lean_object* v_version_6236_; lean_object* v_directImports_6237_; lean_object* v_isSetupFailure_x3f_6238_; lean_object* v___x_6240_; uint8_t v_isShared_6241_; uint8_t v_isSharedCheck_6262_; 
v_version_6236_ = lean_ctor_get(v_val_6232_, 1);
v_directImports_6237_ = lean_ctor_get(v_val_6232_, 2);
v_isSetupFailure_x3f_6238_ = lean_ctor_get(v_val_6232_, 3);
v_isSharedCheck_6262_ = !lean_is_exclusive(v_val_6232_);
if (v_isSharedCheck_6262_ == 0)
{
lean_object* v_unused_6263_; lean_object* v_unused_6264_; lean_object* v_unused_6265_; 
v_unused_6263_ = lean_ctor_get(v_val_6232_, 5);
lean_dec(v_unused_6263_);
v_unused_6264_ = lean_ctor_get(v_val_6232_, 4);
lean_dec(v_unused_6264_);
v_unused_6265_ = lean_ctor_get(v_val_6232_, 0);
lean_dec(v_unused_6265_);
v___x_6240_ = v_val_6232_;
v_isShared_6241_ = v_isSharedCheck_6262_;
goto v_resetjp_6239_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6238_);
lean_inc(v_directImports_6237_);
lean_inc(v_version_6236_);
lean_dec(v_val_6232_);
v___x_6240_ = lean_box(0);
v_isShared_6241_ = v_isSharedCheck_6262_;
goto v_resetjp_6239_;
}
v_resetjp_6239_:
{
uint8_t v___x_6242_; 
v___x_6242_ = lean_nat_dec_lt(v_version_6225_, v_version_6236_);
lean_dec(v_version_6236_);
if (v___x_6242_ == 0)
{
lean_object* v___x_6244_; uint8_t v_isShared_6245_; uint8_t v_isSharedCheck_6256_; 
lean_inc(v_workers_6230_);
lean_inc(v_ileans_6229_);
v_isSharedCheck_6256_ = !lean_is_exclusive(v_self_6222_);
if (v_isSharedCheck_6256_ == 0)
{
lean_object* v_unused_6257_; lean_object* v_unused_6258_; 
v_unused_6257_ = lean_ctor_get(v_self_6222_, 1);
lean_dec(v_unused_6257_);
v_unused_6258_ = lean_ctor_get(v_self_6222_, 0);
lean_dec(v_unused_6258_);
v___x_6244_ = v_self_6222_;
v_isShared_6245_ = v_isSharedCheck_6256_;
goto v_resetjp_6243_;
}
else
{
lean_dec(v_self_6222_);
v___x_6244_ = lean_box(0);
v_isShared_6245_ = v_isSharedCheck_6256_;
goto v_resetjp_6243_;
}
v_resetjp_6243_:
{
lean_object* v___x_6247_; 
if (v_isShared_6241_ == 0)
{
lean_ctor_set(v___x_6240_, 5, v_decls_6227_);
lean_ctor_set(v___x_6240_, 4, v_refs_6226_);
lean_ctor_set(v___x_6240_, 1, v_version_6225_);
lean_ctor_set(v___x_6240_, 0, v_moduleUri_6224_);
v___x_6247_ = v___x_6240_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_moduleUri_6224_);
lean_ctor_set(v_reuseFailAlloc_6255_, 1, v_version_6225_);
lean_ctor_set(v_reuseFailAlloc_6255_, 2, v_directImports_6237_);
lean_ctor_set(v_reuseFailAlloc_6255_, 3, v_isSetupFailure_x3f_6238_);
lean_ctor_set(v_reuseFailAlloc_6255_, 4, v_refs_6226_);
lean_ctor_set(v_reuseFailAlloc_6255_, 5, v_decls_6227_);
v___x_6247_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
lean_object* v___x_6248_; lean_object* v___x_6250_; 
v___x_6248_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6223_, v___x_6247_, v_workers_6230_);
if (v_isShared_6245_ == 0)
{
lean_ctor_set(v___x_6244_, 1, v___x_6248_);
v___x_6250_ = v___x_6244_;
goto v_reusejp_6249_;
}
else
{
lean_object* v_reuseFailAlloc_6254_; 
v_reuseFailAlloc_6254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6254_, 0, v_ileans_6229_);
lean_ctor_set(v_reuseFailAlloc_6254_, 1, v___x_6248_);
v___x_6250_ = v_reuseFailAlloc_6254_;
goto v_reusejp_6249_;
}
v_reusejp_6249_:
{
lean_object* v___x_6252_; 
if (v_isShared_6235_ == 0)
{
lean_ctor_set_tag(v___x_6234_, 0);
lean_ctor_set(v___x_6234_, 0, v___x_6250_);
v___x_6252_ = v___x_6234_;
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
else
{
lean_object* v___x_6260_; 
lean_del_object(v___x_6240_);
lean_dec(v_isSetupFailure_x3f_6238_);
lean_dec_ref(v_directImports_6237_);
lean_dec(v_decls_6227_);
lean_dec(v_refs_6226_);
lean_dec(v_version_6225_);
lean_dec_ref(v_moduleUri_6224_);
lean_dec(v_name_6223_);
if (v_isShared_6235_ == 0)
{
lean_ctor_set_tag(v___x_6234_, 0);
lean_ctor_set(v___x_6234_, 0, v_self_6222_);
v___x_6260_ = v___x_6234_;
goto v_reusejp_6259_;
}
else
{
lean_object* v_reuseFailAlloc_6261_; 
v_reuseFailAlloc_6261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_self_6222_);
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
lean_object* v___x_6268_; uint8_t v_isShared_6269_; uint8_t v_isSharedCheck_6278_; 
lean_inc(v_workers_6230_);
lean_inc(v_ileans_6229_);
lean_dec(v___x_6231_);
v_isSharedCheck_6278_ = !lean_is_exclusive(v_self_6222_);
if (v_isSharedCheck_6278_ == 0)
{
lean_object* v_unused_6279_; lean_object* v_unused_6280_; 
v_unused_6279_ = lean_ctor_get(v_self_6222_, 1);
lean_dec(v_unused_6279_);
v_unused_6280_ = lean_ctor_get(v_self_6222_, 0);
lean_dec(v_unused_6280_);
v___x_6268_ = v_self_6222_;
v_isShared_6269_ = v_isSharedCheck_6278_;
goto v_resetjp_6267_;
}
else
{
lean_dec(v_self_6222_);
v___x_6268_ = lean_box(0);
v_isShared_6269_ = v_isSharedCheck_6278_;
goto v_resetjp_6267_;
}
v_resetjp_6267_:
{
lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6275_; 
v___x_6270_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6271_ = lean_box(0);
v___x_6272_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6272_, 0, v_moduleUri_6224_);
lean_ctor_set(v___x_6272_, 1, v_version_6225_);
lean_ctor_set(v___x_6272_, 2, v___x_6270_);
lean_ctor_set(v___x_6272_, 3, v___x_6271_);
lean_ctor_set(v___x_6272_, 4, v_refs_6226_);
lean_ctor_set(v___x_6272_, 5, v_decls_6227_);
v___x_6273_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6223_, v___x_6272_, v_workers_6230_);
if (v_isShared_6269_ == 0)
{
lean_ctor_set(v___x_6268_, 1, v___x_6273_);
v___x_6275_ = v___x_6268_;
goto v_reusejp_6274_;
}
else
{
lean_object* v_reuseFailAlloc_6277_; 
v_reuseFailAlloc_6277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6277_, 0, v_ileans_6229_);
lean_ctor_set(v_reuseFailAlloc_6277_, 1, v___x_6273_);
v___x_6275_ = v_reuseFailAlloc_6277_;
goto v_reusejp_6274_;
}
v_reusejp_6274_:
{
lean_object* v___x_6276_; 
v___x_6276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6276_, 0, v___x_6275_);
return v___x_6276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6281_, lean_object* v_name_6282_, lean_object* v_moduleUri_6283_, lean_object* v_version_6284_, lean_object* v_refs_6285_, lean_object* v_decls_6286_, lean_object* v_a_6287_){
_start:
{
lean_object* v_res_6288_; 
v_res_6288_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6281_, v_name_6282_, v_moduleUri_6283_, v_version_6284_, v_refs_6285_, v_decls_6286_);
return v_res_6288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6289_, lean_object* v_name_6290_){
_start:
{
lean_object* v_ileans_6291_; lean_object* v_workers_6292_; lean_object* v___x_6294_; uint8_t v_isShared_6295_; uint8_t v_isSharedCheck_6300_; 
v_ileans_6291_ = lean_ctor_get(v_self_6289_, 0);
v_workers_6292_ = lean_ctor_get(v_self_6289_, 1);
v_isSharedCheck_6300_ = !lean_is_exclusive(v_self_6289_);
if (v_isSharedCheck_6300_ == 0)
{
v___x_6294_ = v_self_6289_;
v_isShared_6295_ = v_isSharedCheck_6300_;
goto v_resetjp_6293_;
}
else
{
lean_inc(v_workers_6292_);
lean_inc(v_ileans_6291_);
lean_dec(v_self_6289_);
v___x_6294_ = lean_box(0);
v_isShared_6295_ = v_isSharedCheck_6300_;
goto v_resetjp_6293_;
}
v_resetjp_6293_:
{
lean_object* v___x_6296_; lean_object* v___x_6298_; 
v___x_6296_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6290_, v_workers_6292_);
if (v_isShared_6295_ == 0)
{
lean_ctor_set(v___x_6294_, 1, v___x_6296_);
v___x_6298_ = v___x_6294_;
goto v_reusejp_6297_;
}
else
{
lean_object* v_reuseFailAlloc_6299_; 
v_reuseFailAlloc_6299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6299_, 0, v_ileans_6291_);
lean_ctor_set(v_reuseFailAlloc_6299_, 1, v___x_6296_);
v___x_6298_ = v_reuseFailAlloc_6299_;
goto v_reusejp_6297_;
}
v_reusejp_6297_:
{
return v___x_6298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6301_, lean_object* v_name_6302_){
_start:
{
lean_object* v_res_6303_; 
v_res_6303_ = l_Lean_Server_References_removeWorkerRefs(v_self_6301_, v_name_6302_);
lean_dec(v_name_6302_);
return v_res_6303_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6304_, lean_object* v_x_6305_){
_start:
{
if (lean_obj_tag(v_x_6305_) == 0)
{
lean_object* v_v_6306_; lean_object* v_k_6307_; lean_object* v_l_6308_; lean_object* v_r_6309_; lean_object* v_moduleUri_6310_; lean_object* v_refs_6311_; lean_object* v_decls_6312_; lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; 
v_v_6306_ = lean_ctor_get(v_x_6305_, 2);
lean_inc(v_v_6306_);
v_k_6307_ = lean_ctor_get(v_x_6305_, 1);
lean_inc(v_k_6307_);
v_l_6308_ = lean_ctor_get(v_x_6305_, 3);
lean_inc(v_l_6308_);
v_r_6309_ = lean_ctor_get(v_x_6305_, 4);
lean_inc(v_r_6309_);
lean_dec_ref(v_x_6305_);
v_moduleUri_6310_ = lean_ctor_get(v_v_6306_, 0);
lean_inc_ref(v_moduleUri_6310_);
v_refs_6311_ = lean_ctor_get(v_v_6306_, 3);
lean_inc(v_refs_6311_);
v_decls_6312_ = lean_ctor_get(v_v_6306_, 4);
lean_inc(v_decls_6312_);
lean_dec(v_v_6306_);
v___x_6313_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6304_, v_l_6308_);
v___x_6314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6314_, 0, v_refs_6311_);
lean_ctor_set(v___x_6314_, 1, v_decls_6312_);
v___x_6315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6315_, 0, v_moduleUri_6310_);
lean_ctor_set(v___x_6315_, 1, v___x_6314_);
v___x_6316_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6307_, v___x_6315_, v___x_6313_);
v_init_6304_ = v___x_6316_;
v_x_6305_ = v_r_6309_;
goto _start;
}
else
{
return v_init_6304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6318_, lean_object* v_x_6319_){
_start:
{
if (lean_obj_tag(v_x_6319_) == 0)
{
lean_object* v_v_6320_; lean_object* v_k_6321_; lean_object* v_l_6322_; lean_object* v_r_6323_; lean_object* v_moduleUri_6324_; lean_object* v_refs_6325_; lean_object* v_decls_6326_; lean_object* v___x_6327_; uint8_t v___x_6328_; 
v_v_6320_ = lean_ctor_get(v_x_6319_, 2);
lean_inc(v_v_6320_);
v_k_6321_ = lean_ctor_get(v_x_6319_, 1);
lean_inc(v_k_6321_);
v_l_6322_ = lean_ctor_get(v_x_6319_, 3);
lean_inc(v_l_6322_);
v_r_6323_ = lean_ctor_get(v_x_6319_, 4);
lean_inc(v_r_6323_);
lean_dec_ref(v_x_6319_);
v_moduleUri_6324_ = lean_ctor_get(v_v_6320_, 0);
lean_inc_ref(v_moduleUri_6324_);
v_refs_6325_ = lean_ctor_get(v_v_6320_, 4);
lean_inc(v_refs_6325_);
v_decls_6326_ = lean_ctor_get(v_v_6320_, 5);
lean_inc(v_decls_6326_);
v___x_6327_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6318_, v_l_6322_);
v___x_6328_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6320_);
lean_dec(v_v_6320_);
if (v___x_6328_ == 0)
{
lean_dec(v_decls_6326_);
lean_dec(v_refs_6325_);
lean_dec_ref(v_moduleUri_6324_);
lean_dec(v_k_6321_);
v_init_6318_ = v___x_6327_;
v_x_6319_ = v_r_6323_;
goto _start;
}
else
{
lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; 
v___x_6330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6330_, 0, v_refs_6325_);
lean_ctor_set(v___x_6330_, 1, v_decls_6326_);
v___x_6331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6331_, 0, v_moduleUri_6324_);
lean_ctor_set(v___x_6331_, 1, v___x_6330_);
v___x_6332_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6321_, v___x_6331_, v___x_6327_);
v_init_6318_ = v___x_6332_;
v_x_6319_ = v_r_6323_;
goto _start;
}
}
else
{
return v_init_6318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6334_){
_start:
{
lean_object* v_ileans_6335_; lean_object* v_workers_6336_; lean_object* v___x_6337_; lean_object* v_ileanRefs_6338_; lean_object* v___x_6339_; 
v_ileans_6335_ = lean_ctor_get(v_self_6334_, 0);
lean_inc(v_ileans_6335_);
v_workers_6336_ = lean_ctor_get(v_self_6334_, 1);
lean_inc(v_workers_6336_);
lean_dec_ref(v_self_6334_);
v___x_6337_ = lean_box(1);
v_ileanRefs_6338_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6337_, v_ileans_6335_);
v___x_6339_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6338_, v_workers_6336_);
return v___x_6339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6340_, lean_object* v_t_6341_){
_start:
{
lean_object* v___x_6342_; 
v___x_6342_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6340_, v_t_6341_);
return v___x_6342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6343_, lean_object* v_t_6344_){
_start:
{
lean_object* v___x_6345_; 
v___x_6345_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6343_, v_t_6344_);
return v___x_6345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6346_, lean_object* v_x_6347_){
_start:
{
if (lean_obj_tag(v_x_6347_) == 0)
{
lean_object* v_k_6348_; lean_object* v_v_6349_; lean_object* v_l_6350_; lean_object* v_r_6351_; lean_object* v___x_6352_; lean_object* v_a_6353_; uint8_t v___x_6354_; 
v_k_6348_ = lean_ctor_get(v_x_6347_, 1);
lean_inc(v_k_6348_);
v_v_6349_ = lean_ctor_get(v_x_6347_, 2);
lean_inc(v_v_6349_);
v_l_6350_ = lean_ctor_get(v_x_6347_, 3);
lean_inc(v_l_6350_);
v_r_6351_ = lean_ctor_get(v_x_6347_, 4);
lean_inc(v_r_6351_);
lean_dec_ref(v_x_6347_);
v___x_6352_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6346_, v_l_6350_);
v_a_6353_ = lean_ctor_get(v___x_6352_, 0);
lean_inc(v_a_6353_);
v___x_6354_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6349_);
if (v___x_6354_ == 0)
{
lean_object* v_a_6355_; 
lean_dec(v_a_6353_);
lean_dec(v_v_6349_);
lean_dec(v_k_6348_);
v_a_6355_ = lean_ctor_get(v___x_6352_, 0);
lean_inc(v_a_6355_);
lean_dec_ref(v___x_6352_);
v_init_6346_ = v_a_6355_;
v_x_6347_ = v_r_6351_;
goto _start;
}
else
{
lean_object* v_moduleUri_6357_; lean_object* v_directImports_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; 
lean_dec_ref(v___x_6352_);
v_moduleUri_6357_ = lean_ctor_get(v_v_6349_, 0);
lean_inc_ref(v_moduleUri_6357_);
v_directImports_6358_ = lean_ctor_get(v_v_6349_, 2);
lean_inc_ref(v_directImports_6358_);
lean_dec(v_v_6349_);
v___x_6359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6359_, 0, v_moduleUri_6357_);
lean_ctor_set(v___x_6359_, 1, v_directImports_6358_);
v___x_6360_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6348_, v___x_6359_, v_a_6353_);
v_init_6346_ = v___x_6360_;
v_x_6347_ = v_r_6351_;
goto _start;
}
}
else
{
lean_object* v___x_6362_; 
v___x_6362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6362_, 0, v_init_6346_);
return v___x_6362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6363_, lean_object* v_x_6364_){
_start:
{
if (lean_obj_tag(v_x_6364_) == 0)
{
lean_object* v_k_6365_; lean_object* v_v_6366_; lean_object* v_l_6367_; lean_object* v_r_6368_; lean_object* v___x_6369_; lean_object* v_a_6370_; lean_object* v_moduleUri_6371_; lean_object* v_directImports_6372_; lean_object* v___x_6373_; lean_object* v___x_6374_; 
v_k_6365_ = lean_ctor_get(v_x_6364_, 1);
lean_inc(v_k_6365_);
v_v_6366_ = lean_ctor_get(v_x_6364_, 2);
lean_inc(v_v_6366_);
v_l_6367_ = lean_ctor_get(v_x_6364_, 3);
lean_inc(v_l_6367_);
v_r_6368_ = lean_ctor_get(v_x_6364_, 4);
lean_inc(v_r_6368_);
lean_dec_ref(v_x_6364_);
v___x_6369_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6363_, v_l_6367_);
v_a_6370_ = lean_ctor_get(v___x_6369_, 0);
lean_inc(v_a_6370_);
lean_dec_ref(v___x_6369_);
v_moduleUri_6371_ = lean_ctor_get(v_v_6366_, 0);
lean_inc_ref(v_moduleUri_6371_);
v_directImports_6372_ = lean_ctor_get(v_v_6366_, 2);
lean_inc_ref(v_directImports_6372_);
lean_dec(v_v_6366_);
v___x_6373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6373_, 0, v_moduleUri_6371_);
lean_ctor_set(v___x_6373_, 1, v_directImports_6372_);
v___x_6374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6365_, v___x_6373_, v_a_6370_);
v_init_6363_ = v___x_6374_;
v_x_6364_ = v_r_6368_;
goto _start;
}
else
{
lean_object* v___x_6376_; 
v___x_6376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6376_, 0, v_init_6363_);
return v___x_6376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6377_){
_start:
{
lean_object* v_ileans_6378_; lean_object* v_workers_6379_; lean_object* v___y_6381_; lean_object* v_allDirectImports_6384_; lean_object* v___x_6385_; lean_object* v_a_6386_; 
v_ileans_6378_ = lean_ctor_get(v_self_6377_, 0);
lean_inc(v_ileans_6378_);
v_workers_6379_ = lean_ctor_get(v_self_6377_, 1);
lean_inc(v_workers_6379_);
lean_dec_ref(v_self_6377_);
v_allDirectImports_6384_ = lean_box(1);
v___x_6385_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6384_, v_ileans_6378_);
v_a_6386_ = lean_ctor_get(v___x_6385_, 0);
lean_inc(v_a_6386_);
lean_dec_ref(v___x_6385_);
v___y_6381_ = v_a_6386_;
goto v___jp_6380_;
v___jp_6380_:
{
lean_object* v___x_6382_; lean_object* v_a_6383_; 
v___x_6382_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6381_, v_workers_6379_);
v_a_6383_ = lean_ctor_get(v___x_6382_, 0);
lean_inc(v_a_6383_);
lean_dec_ref(v___x_6382_);
return v_a_6383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6387_, lean_object* v_mod_6388_){
_start:
{
lean_object* v_ileans_6389_; lean_object* v_workers_6390_; lean_object* v___x_6392_; uint8_t v_isShared_6393_; uint8_t v_isSharedCheck_6427_; 
v_ileans_6389_ = lean_ctor_get(v_self_6387_, 0);
v_workers_6390_ = lean_ctor_get(v_self_6387_, 1);
v_isSharedCheck_6427_ = !lean_is_exclusive(v_self_6387_);
if (v_isSharedCheck_6427_ == 0)
{
v___x_6392_ = v_self_6387_;
v_isShared_6393_ = v_isSharedCheck_6427_;
goto v_resetjp_6391_;
}
else
{
lean_inc(v_workers_6390_);
lean_inc(v_ileans_6389_);
lean_dec(v_self_6387_);
v___x_6392_ = lean_box(0);
v_isShared_6393_ = v_isSharedCheck_6427_;
goto v_resetjp_6391_;
}
v_resetjp_6391_:
{
lean_object* v___x_6412_; 
v___x_6412_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6390_, v_mod_6388_);
lean_dec(v_workers_6390_);
if (lean_obj_tag(v___x_6412_) == 1)
{
lean_object* v_val_6413_; lean_object* v___x_6415_; uint8_t v_isShared_6416_; uint8_t v_isSharedCheck_6426_; 
v_val_6413_ = lean_ctor_get(v___x_6412_, 0);
v_isSharedCheck_6426_ = !lean_is_exclusive(v___x_6412_);
if (v_isSharedCheck_6426_ == 0)
{
v___x_6415_ = v___x_6412_;
v_isShared_6416_ = v_isSharedCheck_6426_;
goto v_resetjp_6414_;
}
else
{
lean_inc(v_val_6413_);
lean_dec(v___x_6412_);
v___x_6415_ = lean_box(0);
v_isShared_6416_ = v_isSharedCheck_6426_;
goto v_resetjp_6414_;
}
v_resetjp_6414_:
{
uint8_t v___x_6417_; 
v___x_6417_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6413_);
if (v___x_6417_ == 0)
{
lean_del_object(v___x_6415_);
lean_dec(v_val_6413_);
goto v___jp_6394_;
}
else
{
lean_object* v_moduleUri_6418_; lean_object* v_refs_6419_; lean_object* v_decls_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6424_; 
lean_del_object(v___x_6392_);
lean_dec(v_ileans_6389_);
v_moduleUri_6418_ = lean_ctor_get(v_val_6413_, 0);
lean_inc_ref(v_moduleUri_6418_);
v_refs_6419_ = lean_ctor_get(v_val_6413_, 4);
lean_inc(v_refs_6419_);
v_decls_6420_ = lean_ctor_get(v_val_6413_, 5);
lean_inc(v_decls_6420_);
lean_dec(v_val_6413_);
v___x_6421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6421_, 0, v_refs_6419_);
lean_ctor_set(v___x_6421_, 1, v_decls_6420_);
v___x_6422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6422_, 0, v_moduleUri_6418_);
lean_ctor_set(v___x_6422_, 1, v___x_6421_);
if (v_isShared_6416_ == 0)
{
lean_ctor_set(v___x_6415_, 0, v___x_6422_);
v___x_6424_ = v___x_6415_;
goto v_reusejp_6423_;
}
else
{
lean_object* v_reuseFailAlloc_6425_; 
v_reuseFailAlloc_6425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6425_, 0, v___x_6422_);
v___x_6424_ = v_reuseFailAlloc_6425_;
goto v_reusejp_6423_;
}
v_reusejp_6423_:
{
return v___x_6424_;
}
}
}
}
else
{
lean_dec(v___x_6412_);
goto v___jp_6394_;
}
v___jp_6394_:
{
lean_object* v___x_6395_; 
v___x_6395_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6389_, v_mod_6388_);
lean_dec(v_ileans_6389_);
if (lean_obj_tag(v___x_6395_) == 1)
{
lean_object* v_val_6396_; lean_object* v___x_6398_; uint8_t v_isShared_6399_; uint8_t v_isSharedCheck_6410_; 
v_val_6396_ = lean_ctor_get(v___x_6395_, 0);
v_isSharedCheck_6410_ = !lean_is_exclusive(v___x_6395_);
if (v_isSharedCheck_6410_ == 0)
{
v___x_6398_ = v___x_6395_;
v_isShared_6399_ = v_isSharedCheck_6410_;
goto v_resetjp_6397_;
}
else
{
lean_inc(v_val_6396_);
lean_dec(v___x_6395_);
v___x_6398_ = lean_box(0);
v_isShared_6399_ = v_isSharedCheck_6410_;
goto v_resetjp_6397_;
}
v_resetjp_6397_:
{
lean_object* v_moduleUri_6400_; lean_object* v_refs_6401_; lean_object* v_decls_6402_; lean_object* v___x_6404_; 
v_moduleUri_6400_ = lean_ctor_get(v_val_6396_, 0);
lean_inc_ref(v_moduleUri_6400_);
v_refs_6401_ = lean_ctor_get(v_val_6396_, 3);
lean_inc(v_refs_6401_);
v_decls_6402_ = lean_ctor_get(v_val_6396_, 4);
lean_inc(v_decls_6402_);
lean_dec(v_val_6396_);
if (v_isShared_6393_ == 0)
{
lean_ctor_set(v___x_6392_, 1, v_decls_6402_);
lean_ctor_set(v___x_6392_, 0, v_refs_6401_);
v___x_6404_ = v___x_6392_;
goto v_reusejp_6403_;
}
else
{
lean_object* v_reuseFailAlloc_6409_; 
v_reuseFailAlloc_6409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6409_, 0, v_refs_6401_);
lean_ctor_set(v_reuseFailAlloc_6409_, 1, v_decls_6402_);
v___x_6404_ = v_reuseFailAlloc_6409_;
goto v_reusejp_6403_;
}
v_reusejp_6403_:
{
lean_object* v___x_6405_; lean_object* v___x_6407_; 
v___x_6405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6405_, 0, v_moduleUri_6400_);
lean_ctor_set(v___x_6405_, 1, v___x_6404_);
if (v_isShared_6399_ == 0)
{
lean_ctor_set(v___x_6398_, 0, v___x_6405_);
v___x_6407_ = v___x_6398_;
goto v_reusejp_6406_;
}
else
{
lean_object* v_reuseFailAlloc_6408_; 
v_reuseFailAlloc_6408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6408_, 0, v___x_6405_);
v___x_6407_ = v_reuseFailAlloc_6408_;
goto v_reusejp_6406_;
}
v_reusejp_6406_:
{
return v___x_6407_;
}
}
}
}
else
{
lean_object* v___x_6411_; 
lean_dec(v___x_6395_);
lean_del_object(v___x_6392_);
v___x_6411_ = lean_box(0);
return v___x_6411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6428_, lean_object* v_mod_6429_){
_start:
{
lean_object* v_res_6430_; 
v_res_6430_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6428_, v_mod_6429_);
lean_dec(v_mod_6429_);
return v_res_6430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6431_, lean_object* v_mod_6432_){
_start:
{
lean_object* v_ileans_6433_; lean_object* v_workers_6434_; lean_object* v___x_6447_; 
v_ileans_6433_ = lean_ctor_get(v_self_6431_, 0);
v_workers_6434_ = lean_ctor_get(v_self_6431_, 1);
v___x_6447_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6434_, v_mod_6432_);
if (lean_obj_tag(v___x_6447_) == 1)
{
lean_object* v_val_6448_; lean_object* v___x_6450_; uint8_t v_isShared_6451_; uint8_t v_isSharedCheck_6457_; 
v_val_6448_ = lean_ctor_get(v___x_6447_, 0);
v_isSharedCheck_6457_ = !lean_is_exclusive(v___x_6447_);
if (v_isSharedCheck_6457_ == 0)
{
v___x_6450_ = v___x_6447_;
v_isShared_6451_ = v_isSharedCheck_6457_;
goto v_resetjp_6449_;
}
else
{
lean_inc(v_val_6448_);
lean_dec(v___x_6447_);
v___x_6450_ = lean_box(0);
v_isShared_6451_ = v_isSharedCheck_6457_;
goto v_resetjp_6449_;
}
v_resetjp_6449_:
{
uint8_t v___x_6452_; 
v___x_6452_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6448_);
if (v___x_6452_ == 0)
{
lean_del_object(v___x_6450_);
lean_dec(v_val_6448_);
goto v___jp_6435_;
}
else
{
lean_object* v_directImports_6453_; lean_object* v___x_6455_; 
v_directImports_6453_ = lean_ctor_get(v_val_6448_, 2);
lean_inc_ref(v_directImports_6453_);
lean_dec(v_val_6448_);
if (v_isShared_6451_ == 0)
{
lean_ctor_set(v___x_6450_, 0, v_directImports_6453_);
v___x_6455_ = v___x_6450_;
goto v_reusejp_6454_;
}
else
{
lean_object* v_reuseFailAlloc_6456_; 
v_reuseFailAlloc_6456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_directImports_6453_);
v___x_6455_ = v_reuseFailAlloc_6456_;
goto v_reusejp_6454_;
}
v_reusejp_6454_:
{
return v___x_6455_;
}
}
}
}
else
{
lean_dec(v___x_6447_);
goto v___jp_6435_;
}
v___jp_6435_:
{
lean_object* v___x_6436_; 
v___x_6436_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6433_, v_mod_6432_);
if (lean_obj_tag(v___x_6436_) == 1)
{
lean_object* v_val_6437_; lean_object* v___x_6439_; uint8_t v_isShared_6440_; uint8_t v_isSharedCheck_6445_; 
v_val_6437_ = lean_ctor_get(v___x_6436_, 0);
v_isSharedCheck_6445_ = !lean_is_exclusive(v___x_6436_);
if (v_isSharedCheck_6445_ == 0)
{
v___x_6439_ = v___x_6436_;
v_isShared_6440_ = v_isSharedCheck_6445_;
goto v_resetjp_6438_;
}
else
{
lean_inc(v_val_6437_);
lean_dec(v___x_6436_);
v___x_6439_ = lean_box(0);
v_isShared_6440_ = v_isSharedCheck_6445_;
goto v_resetjp_6438_;
}
v_resetjp_6438_:
{
lean_object* v_directImports_6441_; lean_object* v___x_6443_; 
v_directImports_6441_ = lean_ctor_get(v_val_6437_, 2);
lean_inc_ref(v_directImports_6441_);
lean_dec(v_val_6437_);
if (v_isShared_6440_ == 0)
{
lean_ctor_set(v___x_6439_, 0, v_directImports_6441_);
v___x_6443_ = v___x_6439_;
goto v_reusejp_6442_;
}
else
{
lean_object* v_reuseFailAlloc_6444_; 
v_reuseFailAlloc_6444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_directImports_6441_);
v___x_6443_ = v_reuseFailAlloc_6444_;
goto v_reusejp_6442_;
}
v_reusejp_6442_:
{
return v___x_6443_;
}
}
}
else
{
lean_object* v___x_6446_; 
lean_dec(v___x_6436_);
v___x_6446_ = lean_box(0);
return v___x_6446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6458_, lean_object* v_mod_6459_){
_start:
{
lean_object* v_res_6460_; 
v_res_6460_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6458_, v_mod_6459_);
lean_dec(v_mod_6459_);
lean_dec_ref(v_self_6458_);
return v_res_6460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6461_, lean_object* v_mod_6462_){
_start:
{
lean_object* v_ileans_6463_; lean_object* v_workers_6464_; lean_object* v___x_6477_; 
v_ileans_6463_ = lean_ctor_get(v_self_6461_, 0);
v_workers_6464_ = lean_ctor_get(v_self_6461_, 1);
v___x_6477_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6464_, v_mod_6462_);
if (lean_obj_tag(v___x_6477_) == 1)
{
lean_object* v_val_6478_; lean_object* v___x_6480_; uint8_t v_isShared_6481_; uint8_t v_isSharedCheck_6487_; 
v_val_6478_ = lean_ctor_get(v___x_6477_, 0);
v_isSharedCheck_6487_ = !lean_is_exclusive(v___x_6477_);
if (v_isSharedCheck_6487_ == 0)
{
v___x_6480_ = v___x_6477_;
v_isShared_6481_ = v_isSharedCheck_6487_;
goto v_resetjp_6479_;
}
else
{
lean_inc(v_val_6478_);
lean_dec(v___x_6477_);
v___x_6480_ = lean_box(0);
v_isShared_6481_ = v_isSharedCheck_6487_;
goto v_resetjp_6479_;
}
v_resetjp_6479_:
{
uint8_t v___x_6482_; 
v___x_6482_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6478_);
if (v___x_6482_ == 0)
{
lean_del_object(v___x_6480_);
lean_dec(v_val_6478_);
goto v___jp_6465_;
}
else
{
lean_object* v_decls_6483_; lean_object* v___x_6485_; 
v_decls_6483_ = lean_ctor_get(v_val_6478_, 5);
lean_inc(v_decls_6483_);
lean_dec(v_val_6478_);
if (v_isShared_6481_ == 0)
{
lean_ctor_set(v___x_6480_, 0, v_decls_6483_);
v___x_6485_ = v___x_6480_;
goto v_reusejp_6484_;
}
else
{
lean_object* v_reuseFailAlloc_6486_; 
v_reuseFailAlloc_6486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6486_, 0, v_decls_6483_);
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
lean_dec(v___x_6477_);
goto v___jp_6465_;
}
v___jp_6465_:
{
lean_object* v___x_6466_; 
v___x_6466_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6463_, v_mod_6462_);
if (lean_obj_tag(v___x_6466_) == 1)
{
lean_object* v_val_6467_; lean_object* v___x_6469_; uint8_t v_isShared_6470_; uint8_t v_isSharedCheck_6475_; 
v_val_6467_ = lean_ctor_get(v___x_6466_, 0);
v_isSharedCheck_6475_ = !lean_is_exclusive(v___x_6466_);
if (v_isSharedCheck_6475_ == 0)
{
v___x_6469_ = v___x_6466_;
v_isShared_6470_ = v_isSharedCheck_6475_;
goto v_resetjp_6468_;
}
else
{
lean_inc(v_val_6467_);
lean_dec(v___x_6466_);
v___x_6469_ = lean_box(0);
v_isShared_6470_ = v_isSharedCheck_6475_;
goto v_resetjp_6468_;
}
v_resetjp_6468_:
{
lean_object* v_decls_6471_; lean_object* v___x_6473_; 
v_decls_6471_ = lean_ctor_get(v_val_6467_, 4);
lean_inc(v_decls_6471_);
lean_dec(v_val_6467_);
if (v_isShared_6470_ == 0)
{
lean_ctor_set(v___x_6469_, 0, v_decls_6471_);
v___x_6473_ = v___x_6469_;
goto v_reusejp_6472_;
}
else
{
lean_object* v_reuseFailAlloc_6474_; 
v_reuseFailAlloc_6474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6474_, 0, v_decls_6471_);
v___x_6473_ = v_reuseFailAlloc_6474_;
goto v_reusejp_6472_;
}
v_reusejp_6472_:
{
return v___x_6473_;
}
}
}
else
{
lean_object* v___x_6476_; 
lean_dec(v___x_6466_);
v___x_6476_ = lean_box(0);
return v___x_6476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6488_, lean_object* v_mod_6489_){
_start:
{
lean_object* v_res_6490_; 
v_res_6490_ = l_Lean_Server_References_getDecls_x3f(v_self_6488_, v_mod_6489_);
lean_dec(v_mod_6489_);
lean_dec_ref(v_self_6488_);
return v_res_6490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6491_, lean_object* v_x_6492_){
_start:
{
if (lean_obj_tag(v_x_6492_) == 0)
{
lean_object* v_k_6493_; lean_object* v_v_6494_; lean_object* v_l_6495_; lean_object* v_r_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; 
v_k_6493_ = lean_ctor_get(v_x_6492_, 1);
v_v_6494_ = lean_ctor_get(v_x_6492_, 2);
v_l_6495_ = lean_ctor_get(v_x_6492_, 3);
v_r_6496_ = lean_ctor_get(v_x_6492_, 4);
v___x_6497_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6491_, v_l_6495_);
lean_inc(v_v_6494_);
lean_inc(v_k_6493_);
v___x_6498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6498_, 0, v_k_6493_);
lean_ctor_set(v___x_6498_, 1, v_v_6494_);
v___x_6499_ = lean_array_push(v___x_6497_, v___x_6498_);
v_init_6491_ = v___x_6499_;
v_x_6492_ = v_r_6496_;
goto _start;
}
else
{
return v_init_6491_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6501_, lean_object* v_x_6502_){
_start:
{
lean_object* v_res_6503_; 
v_res_6503_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6501_, v_x_6502_);
lean_dec(v_x_6502_);
return v_res_6503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6504_, lean_object* v_k_6505_){
_start:
{
if (lean_obj_tag(v_t_6504_) == 0)
{
lean_object* v_k_6506_; lean_object* v_v_6507_; lean_object* v_l_6508_; lean_object* v_r_6509_; uint8_t v___x_6510_; 
v_k_6506_ = lean_ctor_get(v_t_6504_, 1);
v_v_6507_ = lean_ctor_get(v_t_6504_, 2);
v_l_6508_ = lean_ctor_get(v_t_6504_, 3);
v_r_6509_ = lean_ctor_get(v_t_6504_, 4);
v___x_6510_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6505_, v_k_6506_);
switch(v___x_6510_)
{
case 0:
{
v_t_6504_ = v_l_6508_;
goto _start;
}
case 1:
{
lean_object* v___x_6512_; 
lean_inc(v_v_6507_);
v___x_6512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6512_, 0, v_v_6507_);
return v___x_6512_;
}
default: 
{
v_t_6504_ = v_r_6509_;
goto _start;
}
}
}
else
{
lean_object* v___x_6514_; 
v___x_6514_ = lean_box(0);
return v___x_6514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6515_, lean_object* v_k_6516_){
_start:
{
lean_object* v_res_6517_; 
v_res_6517_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6515_, v_k_6516_);
lean_dec_ref(v_k_6516_);
lean_dec(v_t_6515_);
return v_res_6517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6518_, lean_object* v_as_6519_, size_t v_sz_6520_, size_t v_i_6521_, lean_object* v_b_6522_){
_start:
{
lean_object* v_a_6524_; uint8_t v___x_6528_; 
v___x_6528_ = lean_usize_dec_lt(v_i_6521_, v_sz_6520_);
if (v___x_6528_ == 0)
{
return v_b_6522_;
}
else
{
lean_object* v_a_6529_; lean_object* v_snd_6530_; lean_object* v_snd_6531_; lean_object* v_fst_6532_; lean_object* v___x_6534_; uint8_t v_isShared_6535_; uint8_t v_isSharedCheck_6560_; 
v_a_6529_ = lean_array_uget(v_as_6519_, v_i_6521_);
v_snd_6530_ = lean_ctor_get(v_a_6529_, 1);
lean_inc(v_snd_6530_);
v_snd_6531_ = lean_ctor_get(v_snd_6530_, 1);
lean_inc(v_snd_6531_);
v_fst_6532_ = lean_ctor_get(v_a_6529_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v_a_6529_);
if (v_isSharedCheck_6560_ == 0)
{
lean_object* v_unused_6561_; 
v_unused_6561_ = lean_ctor_get(v_a_6529_, 1);
lean_dec(v_unused_6561_);
v___x_6534_ = v_a_6529_;
v_isShared_6535_ = v_isSharedCheck_6560_;
goto v_resetjp_6533_;
}
else
{
lean_inc(v_fst_6532_);
lean_dec(v_a_6529_);
v___x_6534_ = lean_box(0);
v_isShared_6535_ = v_isSharedCheck_6560_;
goto v_resetjp_6533_;
}
v_resetjp_6533_:
{
lean_object* v_fst_6536_; lean_object* v___x_6538_; uint8_t v_isShared_6539_; uint8_t v_isSharedCheck_6558_; 
v_fst_6536_ = lean_ctor_get(v_snd_6530_, 0);
v_isSharedCheck_6558_ = !lean_is_exclusive(v_snd_6530_);
if (v_isSharedCheck_6558_ == 0)
{
lean_object* v_unused_6559_; 
v_unused_6559_ = lean_ctor_get(v_snd_6530_, 1);
lean_dec(v_unused_6559_);
v___x_6538_ = v_snd_6530_;
v_isShared_6539_ = v_isSharedCheck_6558_;
goto v_resetjp_6537_;
}
else
{
lean_inc(v_fst_6536_);
lean_dec(v_snd_6530_);
v___x_6538_ = lean_box(0);
v_isShared_6539_ = v_isSharedCheck_6558_;
goto v_resetjp_6537_;
}
v_resetjp_6537_:
{
lean_object* v_fst_6540_; lean_object* v_snd_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6557_; 
v_fst_6540_ = lean_ctor_get(v_snd_6531_, 0);
v_snd_6541_ = lean_ctor_get(v_snd_6531_, 1);
v_isSharedCheck_6557_ = !lean_is_exclusive(v_snd_6531_);
if (v_isSharedCheck_6557_ == 0)
{
v___x_6543_ = v_snd_6531_;
v_isShared_6544_ = v_isSharedCheck_6557_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_snd_6541_);
lean_inc(v_fst_6540_);
lean_dec(v_snd_6531_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6557_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
lean_object* v___x_6545_; 
v___x_6545_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6540_, v_ident_6518_);
lean_dec(v_fst_6540_);
if (lean_obj_tag(v___x_6545_) == 1)
{
lean_object* v_val_6546_; lean_object* v___x_6548_; 
v_val_6546_ = lean_ctor_get(v___x_6545_, 0);
lean_inc(v_val_6546_);
lean_dec_ref(v___x_6545_);
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 0, v_val_6546_);
v___x_6548_ = v___x_6543_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6556_; 
v_reuseFailAlloc_6556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6556_, 0, v_val_6546_);
lean_ctor_set(v_reuseFailAlloc_6556_, 1, v_snd_6541_);
v___x_6548_ = v_reuseFailAlloc_6556_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
lean_object* v___x_6550_; 
if (v_isShared_6539_ == 0)
{
lean_ctor_set(v___x_6538_, 1, v___x_6548_);
lean_ctor_set(v___x_6538_, 0, v_fst_6532_);
v___x_6550_ = v___x_6538_;
goto v_reusejp_6549_;
}
else
{
lean_object* v_reuseFailAlloc_6555_; 
v_reuseFailAlloc_6555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6555_, 0, v_fst_6532_);
lean_ctor_set(v_reuseFailAlloc_6555_, 1, v___x_6548_);
v___x_6550_ = v_reuseFailAlloc_6555_;
goto v_reusejp_6549_;
}
v_reusejp_6549_:
{
lean_object* v___x_6552_; 
if (v_isShared_6535_ == 0)
{
lean_ctor_set(v___x_6534_, 1, v___x_6550_);
lean_ctor_set(v___x_6534_, 0, v_fst_6536_);
v___x_6552_ = v___x_6534_;
goto v_reusejp_6551_;
}
else
{
lean_object* v_reuseFailAlloc_6554_; 
v_reuseFailAlloc_6554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6554_, 0, v_fst_6536_);
lean_ctor_set(v_reuseFailAlloc_6554_, 1, v___x_6550_);
v___x_6552_ = v_reuseFailAlloc_6554_;
goto v_reusejp_6551_;
}
v_reusejp_6551_:
{
lean_object* v___x_6553_; 
v___x_6553_ = lean_array_push(v_b_6522_, v___x_6552_);
v_a_6524_ = v___x_6553_;
goto v___jp_6523_;
}
}
}
}
else
{
lean_dec(v___x_6545_);
lean_del_object(v___x_6543_);
lean_dec(v_snd_6541_);
lean_del_object(v___x_6538_);
lean_dec(v_fst_6536_);
lean_del_object(v___x_6534_);
lean_dec(v_fst_6532_);
v_a_6524_ = v_b_6522_;
goto v___jp_6523_;
}
}
}
}
}
v___jp_6523_:
{
size_t v___x_6525_; size_t v___x_6526_; 
v___x_6525_ = ((size_t)1ULL);
v___x_6526_ = lean_usize_add(v_i_6521_, v___x_6525_);
v_i_6521_ = v___x_6526_;
v_b_6522_ = v_a_6524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6562_, lean_object* v_as_6563_, lean_object* v_sz_6564_, lean_object* v_i_6565_, lean_object* v_b_6566_){
_start:
{
size_t v_sz_boxed_6567_; size_t v_i_boxed_6568_; lean_object* v_res_6569_; 
v_sz_boxed_6567_ = lean_unbox_usize(v_sz_6564_);
lean_dec(v_sz_6564_);
v_i_boxed_6568_ = lean_unbox_usize(v_i_6565_);
lean_dec(v_i_6565_);
v_res_6569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6562_, v_as_6563_, v_sz_boxed_6567_, v_i_boxed_6568_, v_b_6566_);
lean_dec_ref(v_as_6563_);
lean_dec_ref(v_ident_6562_);
return v_res_6569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6576_, lean_object* v_ident_6577_){
_start:
{
lean_object* v___y_6579_; 
if (lean_obj_tag(v_ident_6577_) == 0)
{
lean_object* v___x_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; 
v___x_6584_ = l_Lean_Server_References_allRefs(v_self_6576_);
v___x_6585_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6586_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6585_, v___x_6584_);
lean_dec(v___x_6584_);
v___y_6579_ = v___x_6586_;
goto v___jp_6578_;
}
else
{
lean_object* v_moduleName_6587_; lean_object* v_identModuleName_6588_; lean_object* v___x_6589_; 
v_moduleName_6587_ = lean_ctor_get(v_ident_6577_, 0);
lean_inc_ref(v_moduleName_6587_);
v_identModuleName_6588_ = l_String_toName(v_moduleName_6587_);
v___x_6589_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6576_, v_identModuleName_6588_);
if (lean_obj_tag(v___x_6589_) == 0)
{
lean_object* v___x_6590_; 
lean_dec(v_identModuleName_6588_);
v___x_6590_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6579_ = v___x_6590_;
goto v___jp_6578_;
}
else
{
lean_object* v_val_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; 
v_val_6591_ = lean_ctor_get(v___x_6589_, 0);
lean_inc(v_val_6591_);
lean_dec_ref(v___x_6589_);
v___x_6592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6592_, 0, v_identModuleName_6588_);
lean_ctor_set(v___x_6592_, 1, v_val_6591_);
v___x_6593_ = lean_unsigned_to_nat(1u);
v___x_6594_ = lean_mk_empty_array_with_capacity(v___x_6593_);
v___x_6595_ = lean_array_push(v___x_6594_, v___x_6592_);
v___y_6579_ = v___x_6595_;
goto v___jp_6578_;
}
}
v___jp_6578_:
{
lean_object* v_result_6580_; size_t v_sz_6581_; size_t v___x_6582_; lean_object* v___x_6583_; 
v_result_6580_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6581_ = lean_array_size(v___y_6579_);
v___x_6582_ = ((size_t)0ULL);
v___x_6583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6577_, v___y_6579_, v_sz_6581_, v___x_6582_, v_result_6580_);
lean_dec_ref(v___y_6579_);
lean_dec_ref(v_ident_6577_);
return v___x_6583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6596_, lean_object* v_t_6597_, lean_object* v_k_6598_){
_start:
{
lean_object* v___x_6599_; 
v___x_6599_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6597_, v_k_6598_);
return v___x_6599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6600_, lean_object* v_t_6601_, lean_object* v_k_6602_){
_start:
{
lean_object* v_res_6603_; 
v_res_6603_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6600_, v_t_6601_, v_k_6602_);
lean_dec_ref(v_k_6602_);
lean_dec(v_t_6601_);
return v_res_6603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6604_, lean_object* v_t_6605_){
_start:
{
lean_object* v___x_6606_; 
v___x_6606_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6604_, v_t_6605_);
return v___x_6606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6607_, lean_object* v_t_6608_){
_start:
{
lean_object* v_res_6609_; 
v_res_6609_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6607_, v_t_6608_);
lean_dec(v_t_6608_);
return v_res_6609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6610_, lean_object* v_module_6611_, lean_object* v_pos_6612_, uint8_t v_includeStop_6613_){
_start:
{
lean_object* v___x_6614_; 
v___x_6614_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6610_, v_module_6611_);
if (lean_obj_tag(v___x_6614_) == 1)
{
lean_object* v_val_6615_; lean_object* v_snd_6616_; lean_object* v_fst_6617_; lean_object* v___x_6618_; 
v_val_6615_ = lean_ctor_get(v___x_6614_, 0);
lean_inc(v_val_6615_);
lean_dec_ref(v___x_6614_);
v_snd_6616_ = lean_ctor_get(v_val_6615_, 1);
lean_inc(v_snd_6616_);
lean_dec(v_val_6615_);
v_fst_6617_ = lean_ctor_get(v_snd_6616_, 0);
lean_inc(v_fst_6617_);
lean_dec(v_snd_6616_);
v___x_6618_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6617_, v_pos_6612_, v_includeStop_6613_);
return v___x_6618_;
}
else
{
lean_object* v___x_6619_; 
lean_dec(v___x_6614_);
v___x_6619_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6620_, lean_object* v_module_6621_, lean_object* v_pos_6622_, lean_object* v_includeStop_6623_){
_start:
{
uint8_t v_includeStop_boxed_6624_; lean_object* v_res_6625_; 
v_includeStop_boxed_6624_ = lean_unbox(v_includeStop_6623_);
v_res_6625_ = l_Lean_Server_References_findAt(v_self_6620_, v_module_6621_, v_pos_6622_, v_includeStop_boxed_6624_);
lean_dec_ref(v_pos_6622_);
lean_dec(v_module_6621_);
return v_res_6625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6626_, lean_object* v_module_6627_, lean_object* v_pos_6628_, uint8_t v_includeStop_6629_){
_start:
{
lean_object* v___x_6630_; 
v___x_6630_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6626_, v_module_6627_);
if (lean_obj_tag(v___x_6630_) == 0)
{
lean_object* v___x_6631_; 
v___x_6631_ = lean_box(0);
return v___x_6631_;
}
else
{
lean_object* v_val_6632_; lean_object* v_snd_6633_; lean_object* v_fst_6634_; lean_object* v___x_6635_; 
v_val_6632_ = lean_ctor_get(v___x_6630_, 0);
lean_inc(v_val_6632_);
lean_dec_ref(v___x_6630_);
v_snd_6633_ = lean_ctor_get(v_val_6632_, 1);
lean_inc(v_snd_6633_);
lean_dec(v_val_6632_);
v_fst_6634_ = lean_ctor_get(v_snd_6633_, 0);
lean_inc(v_fst_6634_);
lean_dec(v_snd_6633_);
v___x_6635_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6634_, v_pos_6628_, v_includeStop_6629_);
lean_dec(v_fst_6634_);
return v___x_6635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6636_, lean_object* v_module_6637_, lean_object* v_pos_6638_, lean_object* v_includeStop_6639_){
_start:
{
uint8_t v_includeStop_boxed_6640_; lean_object* v_res_6641_; 
v_includeStop_boxed_6640_ = lean_unbox(v_includeStop_6639_);
v_res_6641_ = l_Lean_Server_References_findRange_x3f(v_self_6636_, v_module_6637_, v_pos_6638_, v_includeStop_boxed_6640_);
lean_dec_ref(v_pos_6638_);
lean_dec(v_module_6637_);
return v_res_6641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6642_, lean_object* v_k_6643_){
_start:
{
if (lean_obj_tag(v_t_6642_) == 0)
{
lean_object* v_k_6644_; lean_object* v_v_6645_; lean_object* v_l_6646_; lean_object* v_r_6647_; uint8_t v___x_6648_; 
v_k_6644_ = lean_ctor_get(v_t_6642_, 1);
v_v_6645_ = lean_ctor_get(v_t_6642_, 2);
v_l_6646_ = lean_ctor_get(v_t_6642_, 3);
v_r_6647_ = lean_ctor_get(v_t_6642_, 4);
v___x_6648_ = lean_string_dec_lt(v_k_6643_, v_k_6644_);
if (v___x_6648_ == 0)
{
uint8_t v___x_6649_; 
v___x_6649_ = lean_string_dec_eq(v_k_6643_, v_k_6644_);
if (v___x_6649_ == 0)
{
v_t_6642_ = v_r_6647_;
goto _start;
}
else
{
lean_object* v___x_6651_; 
lean_inc(v_v_6645_);
v___x_6651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6651_, 0, v_v_6645_);
return v___x_6651_;
}
}
else
{
v_t_6642_ = v_l_6646_;
goto _start;
}
}
else
{
lean_object* v___x_6653_; 
v___x_6653_ = lean_box(0);
return v___x_6653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6654_, lean_object* v_k_6655_){
_start:
{
lean_object* v_res_6656_; 
v_res_6656_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6654_, v_k_6655_);
lean_dec_ref(v_k_6655_);
lean_dec(v_t_6654_);
return v_res_6656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6657_, lean_object* v_name_6658_){
_start:
{
lean_object* v___x_6659_; 
v___x_6659_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6657_, v_name_6658_);
if (lean_obj_tag(v___x_6659_) == 0)
{
lean_object* v___x_6660_; 
lean_dec_ref(v_name_6658_);
v___x_6660_ = lean_box(0);
return v___x_6660_;
}
else
{
lean_object* v_val_6661_; lean_object* v___x_6663_; uint8_t v_isShared_6664_; uint8_t v_isSharedCheck_6671_; 
v_val_6661_ = lean_ctor_get(v___x_6659_, 0);
v_isSharedCheck_6671_ = !lean_is_exclusive(v___x_6659_);
if (v_isSharedCheck_6671_ == 0)
{
v___x_6663_ = v___x_6659_;
v_isShared_6664_ = v_isSharedCheck_6671_;
goto v_resetjp_6662_;
}
else
{
lean_inc(v_val_6661_);
lean_dec(v___x_6659_);
v___x_6663_ = lean_box(0);
v_isShared_6664_ = v_isSharedCheck_6671_;
goto v_resetjp_6662_;
}
v_resetjp_6662_:
{
lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; lean_object* v___x_6669_; 
v___x_6665_ = l_Lean_Lsp_DeclInfo_range(v_val_6661_);
v___x_6666_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6661_);
lean_dec(v_val_6661_);
v___x_6667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6667_, 0, v_name_6658_);
lean_ctor_set(v___x_6667_, 1, v___x_6665_);
lean_ctor_set(v___x_6667_, 2, v___x_6666_);
if (v_isShared_6664_ == 0)
{
lean_ctor_set(v___x_6663_, 0, v___x_6667_);
v___x_6669_ = v___x_6663_;
goto v_reusejp_6668_;
}
else
{
lean_object* v_reuseFailAlloc_6670_; 
v_reuseFailAlloc_6670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6670_, 0, v___x_6667_);
v___x_6669_ = v_reuseFailAlloc_6670_;
goto v_reusejp_6668_;
}
v_reusejp_6668_:
{
return v___x_6669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6672_, lean_object* v_name_6673_){
_start:
{
lean_object* v_res_6674_; 
v_res_6674_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6672_, v_name_6673_);
lean_dec(v_ds_6672_);
return v_res_6674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6675_, lean_object* v_t_6676_, lean_object* v_k_6677_){
_start:
{
lean_object* v___x_6678_; 
v___x_6678_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6676_, v_k_6677_);
return v___x_6678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6679_, lean_object* v_t_6680_, lean_object* v_k_6681_){
_start:
{
lean_object* v_res_6682_; 
v_res_6682_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6679_, v_t_6680_, v_k_6681_);
lean_dec_ref(v_k_6681_);
lean_dec(v_t_6680_);
return v_res_6682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6683_, lean_object* v_fst_6684_, lean_object* v_snd_6685_, lean_object* v_as_6686_, size_t v_sz_6687_, size_t v_i_6688_, lean_object* v_b_6689_){
_start:
{
uint8_t v___x_6690_; 
v___x_6690_ = lean_usize_dec_lt(v_i_6688_, v_sz_6687_);
if (v___x_6690_ == 0)
{
lean_dec(v_fst_6684_);
lean_dec_ref(v_fst_6683_);
return v_b_6689_;
}
else
{
lean_object* v_a_6691_; lean_object* v___y_6693_; lean_object* v___x_6701_; 
v_a_6691_ = lean_array_uget_borrowed(v_as_6686_, v_i_6688_);
v___x_6701_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6691_);
if (lean_obj_tag(v___x_6701_) == 0)
{
lean_object* v___x_6702_; 
v___x_6702_ = lean_box(0);
v___y_6693_ = v___x_6702_;
goto v___jp_6692_;
}
else
{
lean_object* v_val_6703_; lean_object* v___x_6704_; 
v_val_6703_ = lean_ctor_get(v___x_6701_, 0);
lean_inc(v_val_6703_);
lean_dec_ref(v___x_6701_);
v___x_6704_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6685_, v_val_6703_);
v___y_6693_ = v___x_6704_;
goto v___jp_6692_;
}
v___jp_6692_:
{
lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; lean_object* v___x_6697_; size_t v___x_6698_; size_t v___x_6699_; 
v___x_6694_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6691_);
lean_inc_ref(v_fst_6683_);
v___x_6695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6695_, 0, v_fst_6683_);
lean_ctor_set(v___x_6695_, 1, v___x_6694_);
lean_inc(v_fst_6684_);
v___x_6696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6696_, 0, v___x_6695_);
lean_ctor_set(v___x_6696_, 1, v_fst_6684_);
lean_ctor_set(v___x_6696_, 2, v___y_6693_);
v___x_6697_ = lean_array_push(v_b_6689_, v___x_6696_);
v___x_6698_ = ((size_t)1ULL);
v___x_6699_ = lean_usize_add(v_i_6688_, v___x_6698_);
v_i_6688_ = v___x_6699_;
v_b_6689_ = v___x_6697_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6705_, lean_object* v_fst_6706_, lean_object* v_snd_6707_, lean_object* v_as_6708_, lean_object* v_sz_6709_, lean_object* v_i_6710_, lean_object* v_b_6711_){
_start:
{
size_t v_sz_boxed_6712_; size_t v_i_boxed_6713_; lean_object* v_res_6714_; 
v_sz_boxed_6712_ = lean_unbox_usize(v_sz_6709_);
lean_dec(v_sz_6709_);
v_i_boxed_6713_ = lean_unbox_usize(v_i_6710_);
lean_dec(v_i_6710_);
v_res_6714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6705_, v_fst_6706_, v_snd_6707_, v_as_6708_, v_sz_boxed_6712_, v_i_boxed_6713_, v_b_6711_);
lean_dec_ref(v_as_6708_);
lean_dec(v_snd_6707_);
return v_res_6714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6715_, lean_object* v_as_6716_, size_t v_sz_6717_, size_t v_i_6718_, lean_object* v_b_6719_){
_start:
{
uint8_t v___x_6720_; 
v___x_6720_ = lean_usize_dec_lt(v_i_6718_, v_sz_6717_);
if (v___x_6720_ == 0)
{
return v_b_6719_;
}
else
{
lean_object* v_a_6721_; lean_object* v_snd_6722_; lean_object* v_snd_6723_; lean_object* v_fst_6724_; lean_object* v_fst_6725_; lean_object* v_fst_6726_; lean_object* v_snd_6727_; lean_object* v___x_6729_; uint8_t v_isShared_6730_; uint8_t v_isSharedCheck_6754_; 
v_a_6721_ = lean_array_uget_borrowed(v_as_6716_, v_i_6718_);
v_snd_6722_ = lean_ctor_get(v_a_6721_, 1);
v_snd_6723_ = lean_ctor_get(v_snd_6722_, 1);
lean_inc(v_snd_6723_);
v_fst_6724_ = lean_ctor_get(v_a_6721_, 0);
v_fst_6725_ = lean_ctor_get(v_snd_6722_, 0);
v_fst_6726_ = lean_ctor_get(v_snd_6723_, 0);
v_snd_6727_ = lean_ctor_get(v_snd_6723_, 1);
v_isSharedCheck_6754_ = !lean_is_exclusive(v_snd_6723_);
if (v_isSharedCheck_6754_ == 0)
{
v___x_6729_ = v_snd_6723_;
v_isShared_6730_ = v_isSharedCheck_6754_;
goto v_resetjp_6728_;
}
else
{
lean_inc(v_snd_6727_);
lean_inc(v_fst_6726_);
lean_dec(v_snd_6723_);
v___x_6729_ = lean_box(0);
v_isShared_6730_ = v_isSharedCheck_6754_;
goto v_resetjp_6728_;
}
v_resetjp_6728_:
{
lean_object* v_result_6732_; 
if (v_includeDefinition_6715_ == 0)
{
lean_del_object(v___x_6729_);
v_result_6732_ = v_b_6719_;
goto v___jp_6731_;
}
else
{
lean_object* v_definition_x3f_6740_; 
v_definition_x3f_6740_ = lean_ctor_get(v_fst_6726_, 0);
if (lean_obj_tag(v_definition_x3f_6740_) == 1)
{
lean_object* v_val_6741_; lean_object* v___y_6743_; lean_object* v___x_6750_; 
v_val_6741_ = lean_ctor_get(v_definition_x3f_6740_, 0);
v___x_6750_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6741_);
if (lean_obj_tag(v___x_6750_) == 0)
{
lean_object* v___x_6751_; 
v___x_6751_ = lean_box(0);
v___y_6743_ = v___x_6751_;
goto v___jp_6742_;
}
else
{
lean_object* v_val_6752_; lean_object* v___x_6753_; 
v_val_6752_ = lean_ctor_get(v___x_6750_, 0);
lean_inc(v_val_6752_);
lean_dec_ref(v___x_6750_);
v___x_6753_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6727_, v_val_6752_);
v___y_6743_ = v___x_6753_;
goto v___jp_6742_;
}
v___jp_6742_:
{
lean_object* v___x_6744_; lean_object* v___x_6746_; 
v___x_6744_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6741_);
lean_inc(v_fst_6724_);
if (v_isShared_6730_ == 0)
{
lean_ctor_set(v___x_6729_, 1, v___x_6744_);
lean_ctor_set(v___x_6729_, 0, v_fst_6724_);
v___x_6746_ = v___x_6729_;
goto v_reusejp_6745_;
}
else
{
lean_object* v_reuseFailAlloc_6749_; 
v_reuseFailAlloc_6749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6749_, 0, v_fst_6724_);
lean_ctor_set(v_reuseFailAlloc_6749_, 1, v___x_6744_);
v___x_6746_ = v_reuseFailAlloc_6749_;
goto v_reusejp_6745_;
}
v_reusejp_6745_:
{
lean_object* v___x_6747_; lean_object* v___x_6748_; 
lean_inc(v_fst_6725_);
v___x_6747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6747_, 0, v___x_6746_);
lean_ctor_set(v___x_6747_, 1, v_fst_6725_);
lean_ctor_set(v___x_6747_, 2, v___y_6743_);
v___x_6748_ = lean_array_push(v_b_6719_, v___x_6747_);
v_result_6732_ = v___x_6748_;
goto v___jp_6731_;
}
}
}
else
{
lean_del_object(v___x_6729_);
v_result_6732_ = v_b_6719_;
goto v___jp_6731_;
}
}
v___jp_6731_:
{
lean_object* v_usages_6733_; size_t v_sz_6734_; size_t v___x_6735_; lean_object* v___x_6736_; size_t v___x_6737_; size_t v___x_6738_; 
v_usages_6733_ = lean_ctor_get(v_fst_6726_, 1);
lean_inc_ref(v_usages_6733_);
lean_dec(v_fst_6726_);
v_sz_6734_ = lean_array_size(v_usages_6733_);
v___x_6735_ = ((size_t)0ULL);
lean_inc(v_fst_6725_);
lean_inc(v_fst_6724_);
v___x_6736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6724_, v_fst_6725_, v_snd_6727_, v_usages_6733_, v_sz_6734_, v___x_6735_, v_result_6732_);
lean_dec_ref(v_usages_6733_);
lean_dec(v_snd_6727_);
v___x_6737_ = ((size_t)1ULL);
v___x_6738_ = lean_usize_add(v_i_6718_, v___x_6737_);
v_i_6718_ = v___x_6738_;
v_b_6719_ = v___x_6736_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6755_, lean_object* v_as_6756_, lean_object* v_sz_6757_, lean_object* v_i_6758_, lean_object* v_b_6759_){
_start:
{
uint8_t v_includeDefinition_boxed_6760_; size_t v_sz_boxed_6761_; size_t v_i_boxed_6762_; lean_object* v_res_6763_; 
v_includeDefinition_boxed_6760_ = lean_unbox(v_includeDefinition_6755_);
v_sz_boxed_6761_ = lean_unbox_usize(v_sz_6757_);
lean_dec(v_sz_6757_);
v_i_boxed_6762_ = lean_unbox_usize(v_i_6758_);
lean_dec(v_i_6758_);
v_res_6763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6760_, v_as_6756_, v_sz_boxed_6761_, v_i_boxed_6762_, v_b_6759_);
lean_dec_ref(v_as_6756_);
return v_res_6763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6766_, lean_object* v_ident_6767_, uint8_t v_includeDefinition_6768_){
_start:
{
lean_object* v_result_6769_; lean_object* v___x_6770_; size_t v_sz_6771_; size_t v___x_6772_; lean_object* v___x_6773_; 
v_result_6769_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6770_ = l_Lean_Server_References_allRefsFor(v_self_6766_, v_ident_6767_);
v_sz_6771_ = lean_array_size(v___x_6770_);
v___x_6772_ = ((size_t)0ULL);
v___x_6773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6768_, v___x_6770_, v_sz_6771_, v___x_6772_, v_result_6769_);
lean_dec_ref(v___x_6770_);
return v___x_6773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6774_, lean_object* v_ident_6775_, lean_object* v_includeDefinition_6776_){
_start:
{
uint8_t v_includeDefinition_boxed_6777_; lean_object* v_res_6778_; 
v_includeDefinition_boxed_6777_ = lean_unbox(v_includeDefinition_6776_);
v_res_6778_ = l_Lean_Server_References_referringTo(v_self_6774_, v_ident_6775_, v_includeDefinition_boxed_6777_);
return v_res_6778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6782_, size_t v_sz_6783_, size_t v_i_6784_, lean_object* v_b_6785_){
_start:
{
uint8_t v___x_6786_; 
v___x_6786_ = lean_usize_dec_lt(v_i_6784_, v_sz_6783_);
if (v___x_6786_ == 0)
{
lean_inc_ref(v_b_6785_);
return v_b_6785_;
}
else
{
lean_object* v_a_6787_; lean_object* v_snd_6788_; lean_object* v_snd_6789_; lean_object* v_fst_6790_; lean_object* v_fst_6791_; lean_object* v_fst_6792_; lean_object* v_snd_6793_; lean_object* v___x_6795_; uint8_t v_isShared_6796_; uint8_t v_isSharedCheck_6831_; 
v_a_6787_ = lean_array_uget_borrowed(v_as_6782_, v_i_6784_);
v_snd_6788_ = lean_ctor_get(v_a_6787_, 1);
v_snd_6789_ = lean_ctor_get(v_snd_6788_, 1);
lean_inc(v_snd_6789_);
v_fst_6790_ = lean_ctor_get(v_snd_6789_, 0);
lean_inc(v_fst_6790_);
v_fst_6791_ = lean_ctor_get(v_a_6787_, 0);
v_fst_6792_ = lean_ctor_get(v_snd_6788_, 0);
v_snd_6793_ = lean_ctor_get(v_snd_6789_, 1);
v_isSharedCheck_6831_ = !lean_is_exclusive(v_snd_6789_);
if (v_isSharedCheck_6831_ == 0)
{
lean_object* v_unused_6832_; 
v_unused_6832_ = lean_ctor_get(v_snd_6789_, 0);
lean_dec(v_unused_6832_);
v___x_6795_ = v_snd_6789_;
v_isShared_6796_ = v_isSharedCheck_6831_;
goto v_resetjp_6794_;
}
else
{
lean_inc(v_snd_6793_);
lean_dec(v_snd_6789_);
v___x_6795_ = lean_box(0);
v_isShared_6796_ = v_isSharedCheck_6831_;
goto v_resetjp_6794_;
}
v_resetjp_6794_:
{
lean_object* v_definition_x3f_6797_; lean_object* v___x_6799_; uint8_t v_isShared_6800_; uint8_t v_isSharedCheck_6829_; 
v_definition_x3f_6797_ = lean_ctor_get(v_fst_6790_, 0);
v_isSharedCheck_6829_ = !lean_is_exclusive(v_fst_6790_);
if (v_isSharedCheck_6829_ == 0)
{
lean_object* v_unused_6830_; 
v_unused_6830_ = lean_ctor_get(v_fst_6790_, 1);
lean_dec(v_unused_6830_);
v___x_6799_ = v_fst_6790_;
v_isShared_6800_ = v_isSharedCheck_6829_;
goto v_resetjp_6798_;
}
else
{
lean_inc(v_definition_x3f_6797_);
lean_dec(v_fst_6790_);
v___x_6799_ = lean_box(0);
v_isShared_6800_ = v_isSharedCheck_6829_;
goto v_resetjp_6798_;
}
v_resetjp_6798_:
{
lean_object* v___x_6801_; 
v___x_6801_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6797_) == 1)
{
lean_object* v_val_6802_; lean_object* v___x_6804_; uint8_t v_isShared_6805_; uint8_t v_isSharedCheck_6824_; 
v_val_6802_ = lean_ctor_get(v_definition_x3f_6797_, 0);
v_isSharedCheck_6824_ = !lean_is_exclusive(v_definition_x3f_6797_);
if (v_isSharedCheck_6824_ == 0)
{
v___x_6804_ = v_definition_x3f_6797_;
v_isShared_6805_ = v_isSharedCheck_6824_;
goto v_resetjp_6803_;
}
else
{
lean_inc(v_val_6802_);
lean_dec(v_definition_x3f_6797_);
v___x_6804_ = lean_box(0);
v_isShared_6805_ = v_isSharedCheck_6824_;
goto v_resetjp_6803_;
}
v_resetjp_6803_:
{
lean_object* v___y_6807_; lean_object* v___x_6820_; 
v___x_6820_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6802_);
if (lean_obj_tag(v___x_6820_) == 0)
{
lean_object* v___x_6821_; 
lean_dec(v_snd_6793_);
v___x_6821_ = lean_box(0);
v___y_6807_ = v___x_6821_;
goto v___jp_6806_;
}
else
{
lean_object* v_val_6822_; lean_object* v___x_6823_; 
v_val_6822_ = lean_ctor_get(v___x_6820_, 0);
lean_inc(v_val_6822_);
lean_dec_ref(v___x_6820_);
v___x_6823_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6793_, v_val_6822_);
lean_dec(v_snd_6793_);
v___y_6807_ = v___x_6823_;
goto v___jp_6806_;
}
v___jp_6806_:
{
lean_object* v___x_6808_; lean_object* v___x_6810_; 
v___x_6808_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6802_);
lean_dec(v_val_6802_);
lean_inc(v_fst_6791_);
if (v_isShared_6800_ == 0)
{
lean_ctor_set(v___x_6799_, 1, v___x_6808_);
lean_ctor_set(v___x_6799_, 0, v_fst_6791_);
v___x_6810_ = v___x_6799_;
goto v_reusejp_6809_;
}
else
{
lean_object* v_reuseFailAlloc_6819_; 
v_reuseFailAlloc_6819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6819_, 0, v_fst_6791_);
lean_ctor_set(v_reuseFailAlloc_6819_, 1, v___x_6808_);
v___x_6810_ = v_reuseFailAlloc_6819_;
goto v_reusejp_6809_;
}
v_reusejp_6809_:
{
lean_object* v___x_6811_; lean_object* v___x_6813_; 
lean_inc(v_fst_6792_);
v___x_6811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6811_, 0, v___x_6810_);
lean_ctor_set(v___x_6811_, 1, v_fst_6792_);
lean_ctor_set(v___x_6811_, 2, v___y_6807_);
if (v_isShared_6805_ == 0)
{
lean_ctor_set(v___x_6804_, 0, v___x_6811_);
v___x_6813_ = v___x_6804_;
goto v_reusejp_6812_;
}
else
{
lean_object* v_reuseFailAlloc_6818_; 
v_reuseFailAlloc_6818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6818_, 0, v___x_6811_);
v___x_6813_ = v_reuseFailAlloc_6818_;
goto v_reusejp_6812_;
}
v_reusejp_6812_:
{
lean_object* v___x_6814_; lean_object* v___x_6816_; 
v___x_6814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6814_, 0, v___x_6813_);
if (v_isShared_6796_ == 0)
{
lean_ctor_set(v___x_6795_, 1, v___x_6801_);
lean_ctor_set(v___x_6795_, 0, v___x_6814_);
v___x_6816_ = v___x_6795_;
goto v_reusejp_6815_;
}
else
{
lean_object* v_reuseFailAlloc_6817_; 
v_reuseFailAlloc_6817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6817_, 0, v___x_6814_);
lean_ctor_set(v_reuseFailAlloc_6817_, 1, v___x_6801_);
v___x_6816_ = v_reuseFailAlloc_6817_;
goto v_reusejp_6815_;
}
v_reusejp_6815_:
{
return v___x_6816_;
}
}
}
}
}
}
else
{
lean_object* v___x_6825_; size_t v___x_6826_; size_t v___x_6827_; 
lean_del_object(v___x_6799_);
lean_dec(v_definition_x3f_6797_);
lean_del_object(v___x_6795_);
lean_dec(v_snd_6793_);
v___x_6825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6826_ = ((size_t)1ULL);
v___x_6827_ = lean_usize_add(v_i_6784_, v___x_6826_);
v_i_6784_ = v___x_6827_;
v_b_6785_ = v___x_6825_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6833_, lean_object* v_sz_6834_, lean_object* v_i_6835_, lean_object* v_b_6836_){
_start:
{
size_t v_sz_boxed_6837_; size_t v_i_boxed_6838_; lean_object* v_res_6839_; 
v_sz_boxed_6837_ = lean_unbox_usize(v_sz_6834_);
lean_dec(v_sz_6834_);
v_i_boxed_6838_ = lean_unbox_usize(v_i_6835_);
lean_dec(v_i_6835_);
v_res_6839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6833_, v_sz_boxed_6837_, v_i_boxed_6838_, v_b_6836_);
lean_dec_ref(v_b_6836_);
lean_dec_ref(v_as_6833_);
return v_res_6839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6840_, lean_object* v_ident_6841_){
_start:
{
lean_object* v___x_6842_; lean_object* v___x_6843_; lean_object* v___x_6844_; size_t v_sz_6845_; size_t v___x_6846_; lean_object* v___x_6847_; lean_object* v_fst_6848_; 
v___x_6842_ = l_Lean_Server_References_allRefsFor(v_self_6840_, v_ident_6841_);
v___x_6843_ = lean_box(0);
v___x_6844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6845_ = lean_array_size(v___x_6842_);
v___x_6846_ = ((size_t)0ULL);
v___x_6847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6842_, v_sz_6845_, v___x_6846_, v___x_6844_);
lean_dec_ref(v___x_6842_);
v_fst_6848_ = lean_ctor_get(v___x_6847_, 0);
lean_inc(v_fst_6848_);
lean_dec_ref(v___x_6847_);
if (lean_obj_tag(v_fst_6848_) == 0)
{
return v___x_6843_;
}
else
{
lean_object* v_val_6849_; 
v_val_6849_ = lean_ctor_get(v_fst_6848_, 0);
lean_inc(v_val_6849_);
lean_dec_ref(v_fst_6848_);
return v_val_6849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6850_, lean_object* v_a_6851_, lean_object* v_fst_6852_, lean_object* v_init_6853_, lean_object* v_x_6854_){
_start:
{
lean_object* v_d_6857_; 
if (lean_obj_tag(v_x_6854_) == 0)
{
lean_object* v_k_6859_; lean_object* v_v_6860_; lean_object* v_l_6861_; lean_object* v_r_6862_; lean_object* v___y_6864_; lean_object* v___x_6868_; 
v_k_6859_ = lean_ctor_get(v_x_6854_, 1);
lean_inc(v_k_6859_);
v_v_6860_ = lean_ctor_get(v_x_6854_, 2);
lean_inc(v_v_6860_);
v_l_6861_ = lean_ctor_get(v_x_6854_, 3);
lean_inc(v_l_6861_);
v_r_6862_ = lean_ctor_get(v_x_6854_, 4);
lean_inc(v_r_6862_);
lean_dec_ref(v_x_6854_);
lean_inc_ref(v_fst_6852_);
lean_inc(v_a_6851_);
lean_inc_ref(v_filterMapIdent_6850_);
v___x_6868_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6850_, v_a_6851_, v_fst_6852_, v_init_6853_, v_l_6861_);
if (lean_obj_tag(v___x_6868_) == 0)
{
lean_object* v_a_6869_; 
lean_dec(v_r_6862_);
lean_dec(v_v_6860_);
lean_dec(v_k_6859_);
lean_dec_ref(v_fst_6852_);
lean_dec(v_a_6851_);
lean_dec_ref(v_filterMapIdent_6850_);
v_a_6869_ = lean_ctor_get(v___x_6868_, 0);
lean_inc(v_a_6869_);
lean_dec_ref(v___x_6868_);
v_d_6857_ = v_a_6869_;
goto v___jp_6856_;
}
else
{
if (lean_obj_tag(v_k_6859_) == 0)
{
lean_object* v_definition_x3f_6870_; 
v_definition_x3f_6870_ = lean_ctor_get(v_v_6860_, 0);
lean_inc(v_definition_x3f_6870_);
lean_dec(v_v_6860_);
if (lean_obj_tag(v_definition_x3f_6870_) == 1)
{
lean_object* v_a_6871_; lean_object* v_identName_6872_; lean_object* v_val_6873_; lean_object* v___x_6874_; lean_object* v___x_6875_; 
v_a_6871_ = lean_ctor_get(v___x_6868_, 0);
lean_inc(v_a_6871_);
v_identName_6872_ = lean_ctor_get(v_k_6859_, 1);
lean_inc_ref(v_identName_6872_);
lean_dec_ref(v_k_6859_);
v_val_6873_ = lean_ctor_get(v_definition_x3f_6870_, 0);
lean_inc(v_val_6873_);
lean_dec_ref(v_definition_x3f_6870_);
v___x_6874_ = l_String_toName(v_identName_6872_);
lean_inc_ref(v_filterMapIdent_6850_);
v___x_6875_ = lean_apply_1(v_filterMapIdent_6850_, v___x_6874_);
if (lean_obj_tag(v___x_6875_) == 1)
{
lean_object* v_val_6876_; lean_object* v___x_6877_; lean_object* v___x_6878_; lean_object* v___x_6879_; 
lean_dec_ref(v___x_6868_);
v_val_6876_ = lean_ctor_get(v___x_6875_, 0);
lean_inc(v_val_6876_);
lean_dec_ref(v___x_6875_);
v___x_6877_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6873_);
lean_dec(v_val_6873_);
lean_inc_ref(v_fst_6852_);
lean_inc(v_a_6851_);
v___x_6878_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6878_, 0, v_a_6851_);
lean_ctor_set(v___x_6878_, 1, v_fst_6852_);
lean_ctor_set(v___x_6878_, 2, v_val_6876_);
lean_ctor_set(v___x_6878_, 3, v___x_6877_);
v___x_6879_ = lean_array_push(v_a_6871_, v___x_6878_);
v_init_6853_ = v___x_6879_;
v_x_6854_ = v_r_6862_;
goto _start;
}
else
{
lean_dec(v___x_6875_);
lean_dec(v_val_6873_);
lean_dec(v_a_6871_);
v___y_6864_ = v___x_6868_;
goto v___jp_6863_;
}
}
else
{
lean_dec(v_definition_x3f_6870_);
lean_dec_ref(v_k_6859_);
v___y_6864_ = v___x_6868_;
goto v___jp_6863_;
}
}
else
{
lean_dec(v_v_6860_);
lean_dec(v_k_6859_);
v___y_6864_ = v___x_6868_;
goto v___jp_6863_;
}
}
v___jp_6863_:
{
if (lean_obj_tag(v___y_6864_) == 0)
{
lean_object* v_a_6865_; 
lean_dec(v_r_6862_);
lean_dec_ref(v_fst_6852_);
lean_dec(v_a_6851_);
lean_dec_ref(v_filterMapIdent_6850_);
v_a_6865_ = lean_ctor_get(v___y_6864_, 0);
lean_inc(v_a_6865_);
lean_dec_ref(v___y_6864_);
v_d_6857_ = v_a_6865_;
goto v___jp_6856_;
}
else
{
lean_object* v_a_6866_; 
v_a_6866_ = lean_ctor_get(v___y_6864_, 0);
lean_inc(v_a_6866_);
lean_dec_ref(v___y_6864_);
v_init_6853_ = v_a_6866_;
v_x_6854_ = v_r_6862_;
goto _start;
}
}
}
else
{
lean_object* v___x_6881_; 
lean_dec_ref(v_fst_6852_);
lean_dec(v_a_6851_);
lean_dec_ref(v_filterMapIdent_6850_);
v___x_6881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6881_, 0, v_init_6853_);
return v___x_6881_;
}
v___jp_6856_:
{
lean_object* v___x_6858_; 
v___x_6858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6858_, 0, v_d_6857_);
return v___x_6858_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6882_, lean_object* v_a_6883_, lean_object* v_fst_6884_, lean_object* v_init_6885_, lean_object* v_x_6886_, lean_object* v___y_6887_){
_start:
{
lean_object* v_res_6888_; 
v_res_6888_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6882_, v_a_6883_, v_fst_6884_, v_init_6885_, v_x_6886_);
return v_res_6888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6889_, lean_object* v_cancelTk_x3f_6890_, lean_object* v_init_6891_, lean_object* v_x_6892_){
_start:
{
lean_object* v_d_6895_; 
if (lean_obj_tag(v_x_6892_) == 0)
{
lean_object* v_k_6897_; lean_object* v_v_6898_; lean_object* v_l_6899_; lean_object* v_r_6900_; lean_object* v___x_6901_; 
v_k_6897_ = lean_ctor_get(v_x_6892_, 1);
lean_inc(v_k_6897_);
v_v_6898_ = lean_ctor_get(v_x_6892_, 2);
lean_inc(v_v_6898_);
v_l_6899_ = lean_ctor_get(v_x_6892_, 3);
lean_inc(v_l_6899_);
v_r_6900_ = lean_ctor_get(v_x_6892_, 4);
lean_inc(v_r_6900_);
lean_dec_ref(v_x_6892_);
lean_inc(v_cancelTk_x3f_6890_);
lean_inc_ref(v_filterMapIdent_6889_);
v___x_6901_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6889_, v_cancelTk_x3f_6890_, v_init_6891_, v_l_6899_);
if (lean_obj_tag(v___x_6901_) == 0)
{
lean_object* v_a_6902_; 
lean_dec(v_r_6900_);
lean_dec(v_v_6898_);
lean_dec(v_k_6897_);
lean_dec(v_cancelTk_x3f_6890_);
lean_dec_ref(v_filterMapIdent_6889_);
v_a_6902_ = lean_ctor_get(v___x_6901_, 0);
lean_inc(v_a_6902_);
lean_dec_ref(v___x_6901_);
v_d_6895_ = v_a_6902_;
goto v___jp_6894_;
}
else
{
lean_object* v_snd_6903_; lean_object* v_a_6904_; lean_object* v_fst_6905_; lean_object* v_fst_6906_; lean_object* v___x_6908_; uint8_t v_isShared_6909_; uint8_t v_isSharedCheck_6939_; 
v_snd_6903_ = lean_ctor_get(v_v_6898_, 1);
lean_inc(v_snd_6903_);
v_a_6904_ = lean_ctor_get(v___x_6901_, 0);
lean_inc(v_a_6904_);
lean_dec_ref(v___x_6901_);
v_fst_6905_ = lean_ctor_get(v_v_6898_, 0);
lean_inc(v_fst_6905_);
lean_dec(v_v_6898_);
v_fst_6906_ = lean_ctor_get(v_snd_6903_, 0);
v_isSharedCheck_6939_ = !lean_is_exclusive(v_snd_6903_);
if (v_isSharedCheck_6939_ == 0)
{
lean_object* v_unused_6940_; 
v_unused_6940_ = lean_ctor_get(v_snd_6903_, 1);
lean_dec(v_unused_6940_);
v___x_6908_ = v_snd_6903_;
v_isShared_6909_ = v_isSharedCheck_6939_;
goto v_resetjp_6907_;
}
else
{
lean_inc(v_fst_6906_);
lean_dec(v_snd_6903_);
v___x_6908_ = lean_box(0);
v_isShared_6909_ = v_isSharedCheck_6939_;
goto v_resetjp_6907_;
}
v_resetjp_6907_:
{
lean_object* v_snd_6910_; lean_object* v___x_6912_; uint8_t v_isShared_6913_; uint8_t v_isSharedCheck_6937_; 
v_snd_6910_ = lean_ctor_get(v_a_6904_, 1);
v_isSharedCheck_6937_ = !lean_is_exclusive(v_a_6904_);
if (v_isSharedCheck_6937_ == 0)
{
lean_object* v_unused_6938_; 
v_unused_6938_ = lean_ctor_get(v_a_6904_, 0);
lean_dec(v_unused_6938_);
v___x_6912_ = v_a_6904_;
v_isShared_6913_ = v_isSharedCheck_6937_;
goto v_resetjp_6911_;
}
else
{
lean_inc(v_snd_6910_);
lean_dec(v_a_6904_);
v___x_6912_ = lean_box(0);
v_isShared_6913_ = v_isSharedCheck_6937_;
goto v_resetjp_6911_;
}
v_resetjp_6911_:
{
lean_object* v___x_6914_; lean_object* v_val_6916_; 
v___x_6914_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_6890_) == 1)
{
lean_object* v_val_6924_; uint8_t v___x_6925_; 
v_val_6924_ = lean_ctor_get(v_cancelTk_x3f_6890_, 0);
v___x_6925_ = l_IO_CancelToken_isSet(v_val_6924_);
if (v___x_6925_ == 0)
{
lean_del_object(v___x_6908_);
goto v___jp_6921_;
}
else
{
lean_object* v___x_6927_; uint8_t v_isShared_6928_; uint8_t v_isSharedCheck_6935_; 
lean_del_object(v___x_6912_);
lean_dec(v_fst_6906_);
lean_dec(v_fst_6905_);
lean_dec(v_r_6900_);
lean_dec(v_k_6897_);
lean_dec_ref(v_filterMapIdent_6889_);
v_isSharedCheck_6935_ = !lean_is_exclusive(v_cancelTk_x3f_6890_);
if (v_isSharedCheck_6935_ == 0)
{
lean_object* v_unused_6936_; 
v_unused_6936_ = lean_ctor_get(v_cancelTk_x3f_6890_, 0);
lean_dec(v_unused_6936_);
v___x_6927_ = v_cancelTk_x3f_6890_;
v_isShared_6928_ = v_isSharedCheck_6935_;
goto v_resetjp_6926_;
}
else
{
lean_dec(v_cancelTk_x3f_6890_);
v___x_6927_ = lean_box(0);
v_isShared_6928_ = v_isSharedCheck_6935_;
goto v_resetjp_6926_;
}
v_resetjp_6926_:
{
lean_object* v___x_6930_; 
lean_inc(v_snd_6910_);
if (v_isShared_6928_ == 0)
{
lean_ctor_set(v___x_6927_, 0, v_snd_6910_);
v___x_6930_ = v___x_6927_;
goto v_reusejp_6929_;
}
else
{
lean_object* v_reuseFailAlloc_6934_; 
v_reuseFailAlloc_6934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6934_, 0, v_snd_6910_);
v___x_6930_ = v_reuseFailAlloc_6934_;
goto v_reusejp_6929_;
}
v_reusejp_6929_:
{
lean_object* v___x_6932_; 
if (v_isShared_6909_ == 0)
{
lean_ctor_set(v___x_6908_, 1, v_snd_6910_);
lean_ctor_set(v___x_6908_, 0, v___x_6930_);
v___x_6932_ = v___x_6908_;
goto v_reusejp_6931_;
}
else
{
lean_object* v_reuseFailAlloc_6933_; 
v_reuseFailAlloc_6933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6933_, 0, v___x_6930_);
lean_ctor_set(v_reuseFailAlloc_6933_, 1, v_snd_6910_);
v___x_6932_ = v_reuseFailAlloc_6933_;
goto v_reusejp_6931_;
}
v_reusejp_6931_:
{
v_d_6895_ = v___x_6932_;
goto v___jp_6894_;
}
}
}
}
}
else
{
lean_del_object(v___x_6908_);
goto v___jp_6921_;
}
v___jp_6915_:
{
lean_object* v___x_6918_; 
if (v_isShared_6913_ == 0)
{
lean_ctor_set(v___x_6912_, 1, v_val_6916_);
lean_ctor_set(v___x_6912_, 0, v___x_6914_);
v___x_6918_ = v___x_6912_;
goto v_reusejp_6917_;
}
else
{
lean_object* v_reuseFailAlloc_6920_; 
v_reuseFailAlloc_6920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6920_, 0, v___x_6914_);
lean_ctor_set(v_reuseFailAlloc_6920_, 1, v_val_6916_);
v___x_6918_ = v_reuseFailAlloc_6920_;
goto v_reusejp_6917_;
}
v_reusejp_6917_:
{
v_init_6891_ = v___x_6918_;
v_x_6892_ = v_r_6900_;
goto _start;
}
}
v___jp_6921_:
{
lean_object* v___x_6922_; lean_object* v_a_6923_; 
lean_inc_ref(v_filterMapIdent_6889_);
v___x_6922_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6889_, v_k_6897_, v_fst_6905_, v_snd_6910_, v_fst_6906_);
v_a_6923_ = lean_ctor_get(v___x_6922_, 0);
lean_inc(v_a_6923_);
lean_dec_ref(v___x_6922_);
v_val_6916_ = v_a_6923_;
goto v___jp_6915_;
}
}
}
}
}
else
{
lean_object* v___x_6941_; 
lean_dec(v_cancelTk_x3f_6890_);
lean_dec_ref(v_filterMapIdent_6889_);
v___x_6941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6941_, 0, v_init_6891_);
return v___x_6941_;
}
v___jp_6894_:
{
lean_object* v___x_6896_; 
v___x_6896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6896_, 0, v_d_6895_);
return v___x_6896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_6942_, lean_object* v_cancelTk_x3f_6943_, lean_object* v_init_6944_, lean_object* v_x_6945_, lean_object* v___y_6946_){
_start:
{
lean_object* v_res_6947_; 
v_res_6947_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6942_, v_cancelTk_x3f_6943_, v_init_6944_, v_x_6945_);
return v_res_6947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_6953_, lean_object* v_filterMapIdent_6954_, lean_object* v_cancelTk_x3f_6955_){
_start:
{
lean_object* v___x_6957_; lean_object* v___x_6958_; lean_object* v___x_6959_; lean_object* v_val_6961_; lean_object* v_a_6965_; 
v___x_6957_ = l_Lean_Server_References_allRefs(v_self_6953_);
v___x_6958_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_6959_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6954_, v_cancelTk_x3f_6955_, v___x_6958_, v___x_6957_);
v_a_6965_ = lean_ctor_get(v___x_6959_, 0);
lean_inc(v_a_6965_);
lean_dec_ref(v___x_6959_);
v_val_6961_ = v_a_6965_;
goto v___jp_6960_;
v___jp_6960_:
{
lean_object* v_fst_6962_; 
v_fst_6962_ = lean_ctor_get(v_val_6961_, 0);
if (lean_obj_tag(v_fst_6962_) == 0)
{
lean_object* v_snd_6963_; 
v_snd_6963_ = lean_ctor_get(v_val_6961_, 1);
lean_inc(v_snd_6963_);
lean_dec_ref(v_val_6961_);
return v_snd_6963_;
}
else
{
lean_object* v_val_6964_; 
lean_inc_ref(v_fst_6962_);
lean_dec_ref(v_val_6961_);
v_val_6964_ = lean_ctor_get(v_fst_6962_, 0);
lean_inc(v_val_6964_);
lean_dec_ref(v_fst_6962_);
return v_val_6964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_6966_, lean_object* v_filterMapIdent_6967_, lean_object* v_cancelTk_x3f_6968_, lean_object* v_a_6969_){
_start:
{
lean_object* v_res_6970_; 
v_res_6970_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_6966_, v_filterMapIdent_6967_, v_cancelTk_x3f_6968_);
return v_res_6970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_6971_, lean_object* v_self_6972_, lean_object* v_filterMapIdent_6973_, lean_object* v_cancelTk_x3f_6974_){
_start:
{
lean_object* v___x_6976_; 
v___x_6976_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_6972_, v_filterMapIdent_6973_, v_cancelTk_x3f_6974_);
return v___x_6976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_6977_, lean_object* v_self_6978_, lean_object* v_filterMapIdent_6979_, lean_object* v_cancelTk_x3f_6980_, lean_object* v_a_6981_){
_start:
{
lean_object* v_res_6982_; 
v_res_6982_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_6977_, v_self_6978_, v_filterMapIdent_6979_, v_cancelTk_x3f_6980_);
return v_res_6982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_6983_, lean_object* v_filterMapIdent_6984_, lean_object* v_a_6985_, lean_object* v_fst_6986_, lean_object* v_init_6987_, lean_object* v_x_6988_){
_start:
{
lean_object* v___x_6990_; 
v___x_6990_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6984_, v_a_6985_, v_fst_6986_, v_init_6987_, v_x_6988_);
return v___x_6990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_6991_, lean_object* v_filterMapIdent_6992_, lean_object* v_a_6993_, lean_object* v_fst_6994_, lean_object* v_init_6995_, lean_object* v_x_6996_, lean_object* v___y_6997_){
_start:
{
lean_object* v_res_6998_; 
v_res_6998_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_6991_, v_filterMapIdent_6992_, v_a_6993_, v_fst_6994_, v_init_6995_, v_x_6996_);
return v_res_6998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_6999_, lean_object* v_filterMapIdent_7000_, lean_object* v_cancelTk_x3f_7001_, lean_object* v_init_7002_, lean_object* v_x_7003_){
_start:
{
lean_object* v___x_7005_; 
v___x_7005_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7000_, v_cancelTk_x3f_7001_, v_init_7002_, v_x_7003_);
return v___x_7005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7006_, lean_object* v_filterMapIdent_7007_, lean_object* v_cancelTk_x3f_7008_, lean_object* v_init_7009_, lean_object* v_x_7010_, lean_object* v___y_7011_){
_start:
{
lean_object* v_res_7012_; 
v_res_7012_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7006_, v_filterMapIdent_7007_, v_cancelTk_x3f_7008_, v_init_7009_, v_x_7010_);
return v_res_7012_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7013_){
_start:
{
lean_object* v___x_7014_; lean_object* v___x_7015_; 
v___x_7014_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7015_ = lean_panic_fn_borrowed(v___x_7014_, v_msg_7013_);
return v___x_7015_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7019_; lean_object* v___x_7020_; lean_object* v___x_7021_; lean_object* v___x_7022_; lean_object* v___x_7023_; lean_object* v___x_7024_; 
v___x_7019_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7020_ = lean_unsigned_to_nat(14u);
v___x_7021_ = lean_unsigned_to_nat(22u);
v___x_7022_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7023_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7024_ = l_mkPanicMessageWithDecl(v___x_7023_, v___x_7022_, v___x_7021_, v___x_7020_, v___x_7019_);
return v___x_7024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7025_, lean_object* v_init_7026_, lean_object* v_x_7027_){
_start:
{
if (lean_obj_tag(v_x_7027_) == 0)
{
lean_object* v_k_7028_; lean_object* v_v_7029_; lean_object* v_l_7030_; lean_object* v_r_7031_; lean_object* v___x_7032_; lean_object* v_a_7033_; lean_object* v_fst_7034_; lean_object* v_snd_7035_; lean_object* v___y_7037_; lean_object* v_index_7052_; lean_object* v___x_7053_; 
v_k_7028_ = lean_ctor_get(v_x_7027_, 1);
v_v_7029_ = lean_ctor_get(v_x_7027_, 2);
v_l_7030_ = lean_ctor_get(v_x_7027_, 3);
v_r_7031_ = lean_ctor_get(v_x_7027_, 4);
v___x_7032_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7025_, v_init_7026_, v_l_7030_);
v_a_7033_ = lean_ctor_get(v___x_7032_, 0);
lean_inc(v_a_7033_);
v_fst_7034_ = lean_ctor_get(v_v_7029_, 0);
v_snd_7035_ = lean_ctor_get(v_v_7029_, 1);
v_index_7052_ = lean_ctor_get(v_snd_7035_, 1);
v___x_7053_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7052_, v_requestedMod_7025_);
if (lean_obj_tag(v___x_7053_) == 1)
{
lean_object* v_val_7054_; lean_object* v___x_7055_; 
lean_dec_ref(v___x_7032_);
v_val_7054_ = lean_ctor_get(v___x_7053_, 0);
lean_inc(v_val_7054_);
lean_dec_ref(v___x_7053_);
v___x_7055_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7054_);
lean_dec(v_val_7054_);
if (lean_obj_tag(v___x_7055_) == 0)
{
lean_object* v___x_7056_; lean_object* v___x_7057_; 
v___x_7056_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7057_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7056_);
v___y_7037_ = v___x_7057_;
goto v___jp_7036_;
}
else
{
lean_object* v_val_7058_; 
v_val_7058_ = lean_ctor_get(v___x_7055_, 0);
lean_inc(v_val_7058_);
lean_dec_ref(v___x_7055_);
v___y_7037_ = v_val_7058_;
goto v___jp_7036_;
}
}
else
{
lean_object* v_a_7059_; 
lean_dec(v___x_7053_);
lean_dec(v_a_7033_);
v_a_7059_ = lean_ctor_get(v___x_7032_, 0);
lean_inc(v_a_7059_);
lean_dec_ref(v___x_7032_);
v_init_7026_ = v_a_7059_;
v_x_7027_ = v_r_7031_;
goto _start;
}
v___jp_7036_:
{
uint8_t v_isAll_7038_; uint8_t v_isPrivate_7039_; uint8_t v_metaKind_7040_; lean_object* v___x_7042_; uint8_t v_isShared_7043_; uint8_t v_isSharedCheck_7049_; 
v_isAll_7038_ = lean_ctor_get_uint8(v___y_7037_, sizeof(void*)*2);
v_isPrivate_7039_ = lean_ctor_get_uint8(v___y_7037_, sizeof(void*)*2 + 1);
v_metaKind_7040_ = lean_ctor_get_uint8(v___y_7037_, sizeof(void*)*2 + 2);
v_isSharedCheck_7049_ = !lean_is_exclusive(v___y_7037_);
if (v_isSharedCheck_7049_ == 0)
{
lean_object* v_unused_7050_; lean_object* v_unused_7051_; 
v_unused_7050_ = lean_ctor_get(v___y_7037_, 1);
lean_dec(v_unused_7050_);
v_unused_7051_ = lean_ctor_get(v___y_7037_, 0);
lean_dec(v_unused_7051_);
v___x_7042_ = v___y_7037_;
v_isShared_7043_ = v_isSharedCheck_7049_;
goto v_resetjp_7041_;
}
else
{
lean_dec(v___y_7037_);
v___x_7042_ = lean_box(0);
v_isShared_7043_ = v_isSharedCheck_7049_;
goto v_resetjp_7041_;
}
v_resetjp_7041_:
{
lean_object* v___x_7045_; 
lean_inc(v_fst_7034_);
lean_inc(v_k_7028_);
if (v_isShared_7043_ == 0)
{
lean_ctor_set(v___x_7042_, 1, v_fst_7034_);
lean_ctor_set(v___x_7042_, 0, v_k_7028_);
v___x_7045_ = v___x_7042_;
goto v_reusejp_7044_;
}
else
{
lean_object* v_reuseFailAlloc_7048_; 
v_reuseFailAlloc_7048_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7048_, 0, v_k_7028_);
lean_ctor_set(v_reuseFailAlloc_7048_, 1, v_fst_7034_);
lean_ctor_set_uint8(v_reuseFailAlloc_7048_, sizeof(void*)*2, v_isAll_7038_);
lean_ctor_set_uint8(v_reuseFailAlloc_7048_, sizeof(void*)*2 + 1, v_isPrivate_7039_);
lean_ctor_set_uint8(v_reuseFailAlloc_7048_, sizeof(void*)*2 + 2, v_metaKind_7040_);
v___x_7045_ = v_reuseFailAlloc_7048_;
goto v_reusejp_7044_;
}
v_reusejp_7044_:
{
lean_object* v___x_7046_; 
v___x_7046_ = lean_array_push(v_a_7033_, v___x_7045_);
v_init_7026_ = v___x_7046_;
v_x_7027_ = v_r_7031_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7061_; 
v___x_7061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7061_, 0, v_init_7026_);
return v___x_7061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object* v_requestedMod_7062_, lean_object* v_init_7063_, lean_object* v_x_7064_){
_start:
{
lean_object* v_res_7065_; 
v_res_7065_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7062_, v_init_7063_, v_x_7064_);
lean_dec(v_x_7064_);
lean_dec(v_requestedMod_7062_);
return v_res_7065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object* v_self_7066_, lean_object* v_requestedMod_7067_){
_start:
{
lean_object* v_result_7068_; lean_object* v___x_7069_; lean_object* v___x_7070_; lean_object* v_a_7071_; 
v_result_7068_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_7069_ = l_Lean_Server_References_allDirectImports(v_self_7066_);
v___x_7070_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7067_, v_result_7068_, v___x_7069_);
lean_dec(v___x_7069_);
v_a_7071_ = lean_ctor_get(v___x_7070_, 0);
lean_inc(v_a_7071_);
lean_dec_ref(v___x_7070_);
return v_a_7071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object* v_self_7072_, lean_object* v_requestedMod_7073_){
_start:
{
lean_object* v_res_7074_; 
v_res_7074_ = l_Lean_Server_References_importedBy(v_self_7072_, v_requestedMod_7073_);
lean_dec(v_requestedMod_7073_);
return v_res_7074_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Internal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Import(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_References(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

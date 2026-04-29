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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
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
lean_dec_ref(v___x_2076_);
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
lean_dec(v___x_2271_);
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
lean_dec(v___x_2277_);
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
lean_dec(v___x_2287_);
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
uint8_t v___x_3593__boxed_2473_; lean_object* v_res_2474_; 
v___x_3593__boxed_2473_ = lean_unbox(v___x_2468_);
v_res_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(v___x_3593__boxed_2473_, v_x_2469_, v_x_2470_, v_x_2471_, v___y_2472_);
lean_dec_ref(v_x_2471_);
lean_dec_ref(v_x_2470_);
lean_dec_ref(v_x_2469_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(lean_object* v_text_2475_, lean_object* v_ci_2476_, lean_object* v_info_2477_, lean_object* v_x_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2480_; 
lean_inc_ref(v_info_2477_);
v___x_2480_ = l_Lean_Server_identOf(v_ci_2476_, v_info_2477_);
if (lean_obj_tag(v___x_2480_) == 1)
{
lean_object* v_val_2481_; lean_object* v_fst_2482_; lean_object* v_snd_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2508_; 
v_val_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_val_2481_);
lean_dec_ref(v___x_2480_);
v_fst_2482_ = lean_ctor_get(v_val_2481_, 0);
v_snd_2483_ = lean_ctor_get(v_val_2481_, 1);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_val_2481_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2485_ = v_val_2481_;
v_isShared_2486_ = v_isSharedCheck_2508_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_snd_2483_);
lean_inc(v_fst_2482_);
lean_dec(v_val_2481_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2508_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_Elab_Info_range_x3f(v_info_2477_);
if (lean_obj_tag(v___x_2487_) == 1)
{
lean_object* v_val_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_val_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_val_2488_);
lean_dec_ref(v___x_2487_);
v___x_2489_ = l_Lean_Elab_Info_stx(v_info_2477_);
v___x_2490_ = l_Lean_Syntax_getHeadInfo(v___x_2489_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
lean_dec_ref(v___x_2490_);
v___x_2491_ = lean_box(0);
v___x_2492_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_2493_ = l_Lean_Syntax_Range_toLspRange(v_text_2475_, v_val_2488_);
v___x_2494_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2494_, 0, v_fst_2482_);
lean_ctor_set(v___x_2494_, 1, v___x_2492_);
lean_ctor_set(v___x_2494_, 2, v___x_2493_);
lean_ctor_set(v___x_2494_, 3, v___x_2489_);
lean_ctor_set(v___x_2494_, 4, v_ci_2476_);
lean_ctor_set(v___x_2494_, 5, v_info_2477_);
v___x_2495_ = lean_unbox(v_snd_2483_);
lean_dec(v_snd_2483_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*6, v___x_2495_);
v___x_2496_ = lean_array_push(v___y_2479_, v___x_2494_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___x_2496_);
lean_ctor_set(v___x_2485_, 0, v___x_2491_);
v___x_2498_ = v___x_2485_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2491_);
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
lean_object* v___x_2500_; lean_object* v___x_2502_; 
lean_dec(v___x_2490_);
lean_dec(v___x_2489_);
lean_dec(v_val_2488_);
lean_dec(v_snd_2483_);
lean_dec(v_fst_2482_);
lean_dec_ref(v_info_2477_);
lean_dec_ref(v_ci_2476_);
lean_dec_ref(v_text_2475_);
v___x_2500_ = lean_box(0);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___y_2479_);
lean_ctor_set(v___x_2485_, 0, v___x_2500_);
v___x_2502_ = v___x_2485_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___y_2479_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
lean_dec(v___x_2487_);
lean_dec(v_snd_2483_);
lean_dec(v_fst_2482_);
lean_dec_ref(v_info_2477_);
lean_dec_ref(v_ci_2476_);
lean_dec_ref(v_text_2475_);
v___x_2504_ = lean_box(0);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___y_2479_);
lean_ctor_set(v___x_2485_, 0, v___x_2504_);
v___x_2506_ = v___x_2485_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v___y_2479_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec(v___x_2480_);
lean_dec_ref(v_info_2477_);
lean_dec_ref(v_ci_2476_);
lean_dec_ref(v_text_2475_);
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___y_2479_);
return v___x_2510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed(lean_object* v_text_2511_, lean_object* v_ci_2512_, lean_object* v_info_2513_, lean_object* v_x_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(v_text_2511_, v_ci_2512_, v_info_2513_, v_x_2514_, v___y_2515_);
lean_dec_ref(v_x_2514_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object* v_postNode_2517_, lean_object* v_ci_2518_, lean_object* v_i_2519_, lean_object* v_cs_2520_, lean_object* v_x_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = lean_apply_4(v_postNode_2517_, v_ci_2518_, v_i_2519_, v_cs_2520_, v___y_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object* v_postNode_2524_, lean_object* v_ci_2525_, lean_object* v_i_2526_, lean_object* v_cs_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(v_postNode_2524_, v_ci_2525_, v_i_2526_, v_cs_2527_, v_x_2528_, v___y_2529_);
lean_dec(v_x_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___f_2540_; lean_object* v___f_2541_; lean_object* v___f_2542_; lean_object* v___f_2543_; lean_object* v___f_2544_; lean_object* v___f_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___f_2550_; lean_object* v___f_2551_; lean_object* v___f_2552_; lean_object* v___f_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_3187__overap_2562_; lean_object* v___x_2563_; 
v___f_2540_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_2541_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_2542_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_2543_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_2544_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_2545_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_2546_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___f_2540_);
lean_ctor_set(v___x_2547_, 1, v___f_2541_);
v___x_2548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v___f_2542_);
lean_ctor_set(v___x_2548_, 2, v___f_2543_);
lean_ctor_set(v___x_2548_, 3, v___f_2544_);
lean_ctor_set(v___x_2548_, 4, v___f_2545_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
lean_ctor_set(v___x_2549_, 1, v___f_2546_);
lean_inc_ref_n(v___x_2549_, 6);
v___f_2550_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2550_, 0, v___x_2549_);
v___f_2551_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2551_, 0, v___x_2549_);
v___f_2552_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2552_, 0, v___x_2549_);
v___f_2553_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2553_, 0, v___x_2549_);
v___x_2554_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2554_, 0, lean_box(0));
lean_closure_set(v___x_2554_, 1, lean_box(0));
lean_closure_set(v___x_2554_, 2, v___x_2549_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___f_2550_);
v___x_2556_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2556_, 0, lean_box(0));
lean_closure_set(v___x_2556_, 1, lean_box(0));
lean_closure_set(v___x_2556_, 2, v___x_2549_);
v___x_2557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
lean_ctor_set(v___x_2557_, 2, v___f_2551_);
lean_ctor_set(v___x_2557_, 3, v___f_2552_);
lean_ctor_set(v___x_2557_, 4, v___f_2553_);
v___x_2558_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2558_, 0, lean_box(0));
lean_closure_set(v___x_2558_, 1, lean_box(0));
lean_closure_set(v___x_2558_, 2, v___x_2549_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = lean_box(0);
v___x_2561_ = l_instInhabitedOfMonad___redArg(v___x_2559_, v___x_2560_);
v___x_3187__overap_2562_ = lean_panic_fn_borrowed(v___x_2561_, v_msg_2538_);
lean_dec(v___x_2561_);
v___x_2563_ = lean_apply_1(v___x_3187__overap_2562_, v___y_2539_);
return v___x_2563_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2567_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2));
v___x_2568_ = lean_unsigned_to_nat(21u);
v___x_2569_ = lean_unsigned_to_nat(65u);
v___x_2570_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1));
v___x_2571_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0));
v___x_2572_ = l_mkPanicMessageWithDecl(v___x_2571_, v___x_2570_, v___x_2569_, v___x_2568_, v___x_2567_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object* v_preNode_2573_, lean_object* v_postNode_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_, lean_object* v___y_2577_){
_start:
{
switch(lean_obj_tag(v_x_2576_))
{
case 0:
{
lean_object* v_i_2578_; lean_object* v_t_2579_; lean_object* v___x_2580_; 
v_i_2578_ = lean_ctor_get(v_x_2576_, 0);
lean_inc_ref(v_i_2578_);
v_t_2579_ = lean_ctor_get(v_x_2576_, 1);
lean_inc_ref(v_t_2579_);
lean_dec_ref(v_x_2576_);
v___x_2580_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2578_, v_x_2575_);
v_x_2575_ = v___x_2580_;
v_x_2576_ = v_t_2579_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_2575_) == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec_ref(v_x_2576_);
lean_dec_ref(v_postNode_2574_);
lean_dec_ref(v_preNode_2573_);
v___x_2582_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_2583_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v___x_2582_, v___y_2577_);
return v___x_2583_;
}
else
{
lean_object* v_i_2584_; lean_object* v_children_2585_; lean_object* v_val_2586_; lean_object* v___x_2587_; lean_object* v_fst_2588_; uint8_t v___x_2589_; 
v_i_2584_ = lean_ctor_get(v_x_2576_, 0);
lean_inc_ref_n(v_i_2584_, 2);
v_children_2585_ = lean_ctor_get(v_x_2576_, 1);
lean_inc_ref_n(v_children_2585_, 2);
lean_dec_ref(v_x_2576_);
v_val_2586_ = lean_ctor_get(v_x_2575_, 0);
lean_inc_n(v_val_2586_, 2);
lean_inc_ref(v_preNode_2573_);
v___x_2587_ = lean_apply_4(v_preNode_2573_, v_val_2586_, v_i_2584_, v_children_2585_, v___y_2577_);
v_fst_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_fst_2588_);
v___x_2589_ = lean_unbox(v_fst_2588_);
lean_dec(v_fst_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v_preNode_2573_);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_x_2575_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; 
v_unused_2609_ = lean_ctor_get(v_x_2575_, 0);
lean_dec(v_unused_2609_);
v___x_2591_ = v_x_2575_;
v_isShared_2592_ = v_isSharedCheck_2608_;
goto v_resetjp_2590_;
}
else
{
lean_dec(v_x_2575_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2608_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v_snd_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v_fst_2596_; lean_object* v_snd_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2607_; 
v_snd_2593_ = lean_ctor_get(v___x_2587_, 1);
lean_inc(v_snd_2593_);
lean_dec_ref(v___x_2587_);
v___x_2594_ = lean_box(0);
v___x_2595_ = lean_apply_5(v_postNode_2574_, v_val_2586_, v_i_2584_, v_children_2585_, v___x_2594_, v_snd_2593_);
v_fst_2596_ = lean_ctor_get(v___x_2595_, 0);
v_snd_2597_ = lean_ctor_get(v___x_2595_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2599_ = v___x_2595_;
v_isShared_2600_ = v_isSharedCheck_2607_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_snd_2597_);
lean_inc(v_fst_2596_);
lean_dec(v___x_2595_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2607_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v_fst_2596_);
v___x_2602_ = v___x_2591_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_fst_2596_);
v___x_2602_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2604_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2602_);
v___x_2604_ = v___x_2599_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_snd_2597_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
else
{
lean_object* v_snd_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v_fst_2615_; lean_object* v_snd_2616_; lean_object* v___x_2617_; lean_object* v_fst_2618_; lean_object* v_snd_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2627_; 
v_snd_2610_ = lean_ctor_get(v___x_2587_, 1);
lean_inc(v_snd_2610_);
lean_dec_ref(v___x_2587_);
v___x_2611_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2575_, v_i_2584_);
v___x_2612_ = l_Lean_PersistentArray_toList___redArg(v_children_2585_);
v___x_2613_ = lean_box(0);
lean_inc_ref(v_postNode_2574_);
v___x_2614_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2573_, v_postNode_2574_, v___x_2611_, v___x_2612_, v___x_2613_, v_snd_2610_);
v_fst_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_fst_2615_);
v_snd_2616_ = lean_ctor_get(v___x_2614_, 1);
lean_inc(v_snd_2616_);
lean_dec_ref(v___x_2614_);
v___x_2617_ = lean_apply_5(v_postNode_2574_, v_val_2586_, v_i_2584_, v_children_2585_, v_fst_2615_, v_snd_2616_);
v_fst_2618_ = lean_ctor_get(v___x_2617_, 0);
v_snd_2619_ = lean_ctor_get(v___x_2617_, 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2621_ = v___x_2617_;
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_snd_2619_);
lean_inc(v_fst_2618_);
lean_dec(v___x_2617_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2623_, 0, v_fst_2618_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2625_ = v___x_2621_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_snd_2619_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
default: 
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_dec_ref(v_x_2576_);
lean_dec(v_x_2575_);
lean_dec_ref(v_postNode_2574_);
lean_dec_ref(v_preNode_2573_);
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
lean_ctor_set(v___x_2629_, 1, v___y_2577_);
return v___x_2629_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_2630_, lean_object* v_postNode_2631_, lean_object* v___x_2632_, lean_object* v_x_2633_, lean_object* v_x_2634_, lean_object* v___y_2635_){
_start:
{
if (lean_obj_tag(v_x_2633_) == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_dec(v___x_2632_);
lean_dec_ref(v_postNode_2631_);
lean_dec_ref(v_preNode_2630_);
v___x_2636_ = l_List_reverse___redArg(v_x_2634_);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
lean_ctor_set(v___x_2637_, 1, v___y_2635_);
return v___x_2637_;
}
else
{
lean_object* v_head_2638_; lean_object* v_tail_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2650_; 
v_head_2638_ = lean_ctor_get(v_x_2633_, 0);
v_tail_2639_ = lean_ctor_get(v_x_2633_, 1);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_x_2633_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2641_ = v_x_2633_;
v_isShared_2642_ = v_isSharedCheck_2650_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_tail_2639_);
lean_inc(v_head_2638_);
lean_dec(v_x_2633_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2650_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v___x_2647_; 
lean_inc(v___x_2632_);
lean_inc_ref(v_postNode_2631_);
lean_inc_ref(v_preNode_2630_);
v___x_2643_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2630_, v_postNode_2631_, v___x_2632_, v_head_2638_, v___y_2635_);
v_fst_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_fst_2644_);
v_snd_2645_ = lean_ctor_get(v___x_2643_, 1);
lean_inc(v_snd_2645_);
lean_dec_ref(v___x_2643_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v_x_2634_);
lean_ctor_set(v___x_2641_, 0, v_fst_2644_);
v___x_2647_ = v___x_2641_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_fst_2644_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_x_2634_);
v___x_2647_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
v_x_2633_ = v_tail_2639_;
v_x_2634_ = v___x_2647_;
v___y_2635_ = v_snd_2645_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object* v_preNode_2651_, lean_object* v_postNode_2652_, lean_object* v_ctx_x3f_2653_, lean_object* v_t_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___f_2656_; lean_object* v___x_2657_; lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2666_; 
v___f_2656_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2656_, 0, v_postNode_2652_);
v___x_2657_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2651_, v___f_2656_, v_ctx_x3f_2653_, v_t_2654_, v___y_2655_);
v_snd_2658_ = lean_ctor_get(v___x_2657_, 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2657_, 0);
lean_dec(v_unused_2667_);
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2666_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2666_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2662_ = lean_box(0);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2662_);
v___x_2664_ = v___x_2660_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_snd_2658_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(lean_object* v_text_2668_, lean_object* v_as_2669_, size_t v_sz_2670_, size_t v_i_2671_, lean_object* v_b_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v___x_2674_; 
v___x_2674_ = lean_usize_dec_lt(v_i_2671_, v_sz_2670_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_dec_ref(v_text_2668_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_b_2672_);
lean_ctor_set(v___x_2675_, 1, v___y_2673_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; lean_object* v___f_2677_; lean_object* v___f_2678_; lean_object* v_a_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v_snd_2682_; lean_object* v___x_2683_; size_t v___x_2684_; size_t v___x_2685_; 
v___x_2676_ = lean_box(v___x_2674_);
v___f_2677_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2677_, 0, v___x_2676_);
lean_inc_ref(v_text_2668_);
v___f_2678_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2678_, 0, v_text_2668_);
v_a_2679_ = lean_array_uget_borrowed(v_as_2669_, v_i_2671_);
v___x_2680_ = lean_box(0);
lean_inc(v_a_2679_);
v___x_2681_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(v___f_2677_, v___f_2678_, v___x_2680_, v_a_2679_, v___y_2673_);
v_snd_2682_ = lean_ctor_get(v___x_2681_, 1);
lean_inc(v_snd_2682_);
lean_dec_ref(v___x_2681_);
v___x_2683_ = lean_box(0);
v___x_2684_ = ((size_t)1ULL);
v___x_2685_ = lean_usize_add(v_i_2671_, v___x_2684_);
v_i_2671_ = v___x_2685_;
v_b_2672_ = v___x_2683_;
v___y_2673_ = v_snd_2682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___boxed(lean_object* v_text_2687_, lean_object* v_as_2688_, lean_object* v_sz_2689_, lean_object* v_i_2690_, lean_object* v_b_2691_, lean_object* v___y_2692_){
_start:
{
size_t v_sz_boxed_2693_; size_t v_i_boxed_2694_; lean_object* v_res_2695_; 
v_sz_boxed_2693_ = lean_unbox_usize(v_sz_2689_);
lean_dec(v_sz_2689_);
v_i_boxed_2694_ = lean_unbox_usize(v_i_2690_);
lean_dec(v_i_2690_);
v_res_2695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2687_, v_as_2688_, v_sz_boxed_2693_, v_i_boxed_2694_, v_b_2691_, v___y_2692_);
lean_dec_ref(v_as_2688_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences(lean_object* v_text_2696_, lean_object* v_trees_2697_){
_start:
{
lean_object* v___x_2698_; size_t v_sz_2699_; size_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v_snd_2703_; 
v___x_2698_ = lean_box(0);
v_sz_2699_ = lean_array_size(v_trees_2697_);
v___x_2700_ = ((size_t)0ULL);
v___x_2701_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2696_, v_trees_2697_, v_sz_2699_, v___x_2700_, v___x_2698_, v___x_2701_);
v_snd_2703_ = lean_ctor_get(v___x_2702_, 1);
lean_inc(v_snd_2703_);
lean_dec_ref(v___x_2702_);
return v_snd_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences___boxed(lean_object* v_text_2704_, lean_object* v_trees_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_Server_findReferences(v_text_2704_, v_trees_2705_);
lean_dec_ref(v_trees_2705_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2707_, lean_object* v_msg_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v_msg_2708_, v___y_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object* v_00_u03b1_2711_, lean_object* v_preNode_2712_, lean_object* v_postNode_2713_, lean_object* v_x_2714_, lean_object* v_x_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2712_, v_postNode_2713_, v_x_2714_, v_x_2715_, v___y_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2718_, lean_object* v_preNode_2719_, lean_object* v_postNode_2720_, lean_object* v___x_2721_, lean_object* v_x_2722_, lean_object* v_x_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2719_, v_postNode_2720_, v___x_2721_, v_x_2722_, v_x_2723_, v___y_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(lean_object* v_a_2726_, lean_object* v_x_2727_){
_start:
{
lean_object* v_key_2728_; lean_object* v_value_2729_; lean_object* v_tail_2730_; uint8_t v___x_2731_; 
v_key_2728_ = lean_ctor_get(v_x_2727_, 0);
v_value_2729_ = lean_ctor_get(v_x_2727_, 1);
v_tail_2730_ = lean_ctor_get(v_x_2727_, 2);
v___x_2731_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2728_, v_a_2726_);
if (v___x_2731_ == 0)
{
v_x_2727_ = v_tail_2730_;
goto _start;
}
else
{
lean_inc(v_value_2729_);
return v_value_2729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg___boxed(lean_object* v_a_2733_, lean_object* v_x_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2733_, v_x_2734_);
lean_dec(v_x_2734_);
lean_dec_ref(v_a_2733_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(lean_object* v_m_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_buckets_2738_; lean_object* v___x_2739_; uint64_t v___x_2740_; uint64_t v___x_2741_; uint64_t v___x_2742_; uint64_t v_fold_2743_; uint64_t v___x_2744_; uint64_t v___x_2745_; uint64_t v___x_2746_; size_t v___x_2747_; size_t v___x_2748_; size_t v___x_2749_; size_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_buckets_2738_ = lean_ctor_get(v_m_2736_, 1);
v___x_2739_ = lean_array_get_size(v_buckets_2738_);
v___x_2740_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2737_);
v___x_2741_ = 32ULL;
v___x_2742_ = lean_uint64_shift_right(v___x_2740_, v___x_2741_);
v_fold_2743_ = lean_uint64_xor(v___x_2740_, v___x_2742_);
v___x_2744_ = 16ULL;
v___x_2745_ = lean_uint64_shift_right(v_fold_2743_, v___x_2744_);
v___x_2746_ = lean_uint64_xor(v_fold_2743_, v___x_2745_);
v___x_2747_ = lean_uint64_to_usize(v___x_2746_);
v___x_2748_ = lean_usize_of_nat(v___x_2739_);
v___x_2749_ = ((size_t)1ULL);
v___x_2750_ = lean_usize_sub(v___x_2748_, v___x_2749_);
v___x_2751_ = lean_usize_land(v___x_2747_, v___x_2750_);
v___x_2752_ = lean_array_uget_borrowed(v_buckets_2738_, v___x_2751_);
v___x_2753_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2737_, v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg___boxed(lean_object* v_m_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2754_, v_a_2755_);
lean_dec_ref(v_a_2755_);
lean_dec_ref(v_m_2754_);
return v_res_2756_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(lean_object* v_a_2757_, lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2758_) == 0)
{
uint8_t v___x_2759_; 
v___x_2759_ = 0;
return v___x_2759_;
}
else
{
lean_object* v_key_2760_; lean_object* v_tail_2761_; uint8_t v___x_2762_; 
v_key_2760_ = lean_ctor_get(v_x_2758_, 0);
v_tail_2761_ = lean_ctor_get(v_x_2758_, 2);
v___x_2762_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2760_, v_a_2757_);
if (v___x_2762_ == 0)
{
v_x_2758_ = v_tail_2761_;
goto _start;
}
else
{
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg___boxed(lean_object* v_a_2764_, lean_object* v_x_2765_){
_start:
{
uint8_t v_res_2766_; lean_object* v_r_2767_; 
v_res_2766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2764_, v_x_2765_);
lean_dec(v_x_2765_);
lean_dec_ref(v_a_2764_);
v_r_2767_ = lean_box(v_res_2766_);
return v_r_2767_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(lean_object* v_m_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_buckets_2770_; lean_object* v___x_2771_; uint64_t v___x_2772_; uint64_t v___x_2773_; uint64_t v___x_2774_; uint64_t v_fold_2775_; uint64_t v___x_2776_; uint64_t v___x_2777_; uint64_t v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; size_t v___x_2781_; size_t v___x_2782_; size_t v___x_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; 
v_buckets_2770_ = lean_ctor_get(v_m_2768_, 1);
v___x_2771_ = lean_array_get_size(v_buckets_2770_);
v___x_2772_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2769_);
v___x_2773_ = 32ULL;
v___x_2774_ = lean_uint64_shift_right(v___x_2772_, v___x_2773_);
v_fold_2775_ = lean_uint64_xor(v___x_2772_, v___x_2774_);
v___x_2776_ = 16ULL;
v___x_2777_ = lean_uint64_shift_right(v_fold_2775_, v___x_2776_);
v___x_2778_ = lean_uint64_xor(v_fold_2775_, v___x_2777_);
v___x_2779_ = lean_uint64_to_usize(v___x_2778_);
v___x_2780_ = lean_usize_of_nat(v___x_2771_);
v___x_2781_ = ((size_t)1ULL);
v___x_2782_ = lean_usize_sub(v___x_2780_, v___x_2781_);
v___x_2783_ = lean_usize_land(v___x_2779_, v___x_2782_);
v___x_2784_ = lean_array_uget_borrowed(v_buckets_2770_, v___x_2783_);
v___x_2785_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2769_, v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg___boxed(lean_object* v_m_2786_, lean_object* v_a_2787_){
_start:
{
uint8_t v_res_2788_; lean_object* v_r_2789_; 
v_res_2788_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2786_, v_a_2787_);
lean_dec_ref(v_a_2787_);
lean_dec_ref(v_m_2786_);
v_r_2789_ = lean_box(v_res_2788_);
return v_r_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object* v_idMap_2790_, lean_object* v_b_2791_){
_start:
{
uint8_t v___x_2792_; 
v___x_2792_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_idMap_2790_, v_b_2791_);
if (v___x_2792_ == 0)
{
return v_b_2791_;
}
else
{
lean_object* v_canonicalRepresentative_2793_; 
v_canonicalRepresentative_2793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_idMap_2790_, v_b_2791_);
lean_dec_ref(v_b_2791_);
v_b_2791_ = v_canonicalRepresentative_2793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object* v_idMap_2795_, lean_object* v_b_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2795_, v_b_2796_);
lean_dec_ref(v_idMap_2795_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object* v_idMap_2798_, lean_object* v_id_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2798_, v_id_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object* v_idMap_2801_, lean_object* v_id_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(v_idMap_2801_, v_id_2802_);
lean_dec_ref(v_idMap_2801_);
return v_res_2803_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object* v_00_u03b2_2804_, lean_object* v_m_2805_, lean_object* v_a_2806_){
_start:
{
uint8_t v___x_2807_; 
v___x_2807_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2805_, v_a_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object* v_00_u03b2_2808_, lean_object* v_m_2809_, lean_object* v_a_2810_){
_start:
{
uint8_t v_res_2811_; lean_object* v_r_2812_; 
v_res_2811_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(v_00_u03b2_2808_, v_m_2809_, v_a_2810_);
lean_dec_ref(v_a_2810_);
lean_dec_ref(v_m_2809_);
v_r_2812_ = lean_box(v_res_2811_);
return v_r_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object* v_00_u03b2_2813_, lean_object* v_m_2814_, lean_object* v_a_2815_, lean_object* v_hma_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2814_, v_a_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object* v_00_u03b2_2818_, lean_object* v_m_2819_, lean_object* v_a_2820_, lean_object* v_hma_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(v_00_u03b2_2818_, v_m_2819_, v_a_2820_, v_hma_2821_);
lean_dec_ref(v_a_2820_);
lean_dec_ref(v_m_2819_);
return v_res_2822_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(lean_object* v_00_u03b2_2823_, lean_object* v_a_2824_, lean_object* v_x_2825_){
_start:
{
uint8_t v___x_2826_; 
v___x_2826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2824_, v_x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2827_, lean_object* v_a_2828_, lean_object* v_x_2829_){
_start:
{
uint8_t v_res_2830_; lean_object* v_r_2831_; 
v_res_2830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(v_00_u03b2_2827_, v_a_2828_, v_x_2829_);
lean_dec(v_x_2829_);
lean_dec_ref(v_a_2828_);
v_r_2831_ = lean_box(v_res_2830_);
return v_r_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(lean_object* v_00_u03b2_2832_, lean_object* v_a_2833_, lean_object* v_x_2834_, lean_object* v_x_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2833_, v_x_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2837_, lean_object* v_a_2838_, lean_object* v_x_2839_, lean_object* v_x_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(v_00_u03b2_2837_, v_a_2838_, v_x_2839_, v_x_2840_);
lean_dec(v_x_2839_);
lean_dec_ref(v_a_2838_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
if (lean_obj_tag(v_a_2842_) == 0)
{
lean_object* v___x_2844_; 
v___x_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2844_, 0, v_a_2843_);
return v___x_2844_;
}
else
{
if (lean_obj_tag(v_a_2843_) == 0)
{
lean_object* v_tail_2845_; 
v_tail_2845_ = lean_ctor_get(v_a_2842_, 2);
lean_inc(v_tail_2845_);
lean_dec_ref(v_a_2842_);
v_a_2842_ = v_tail_2845_;
goto _start;
}
else
{
lean_object* v_key_2847_; 
v_key_2847_ = lean_ctor_get(v_a_2842_, 0);
if (lean_obj_tag(v_key_2847_) == 0)
{
lean_object* v_tail_2848_; 
lean_inc_ref(v_key_2847_);
lean_dec_ref(v_a_2843_);
v_tail_2848_ = lean_ctor_get(v_a_2842_, 2);
lean_inc(v_tail_2848_);
lean_dec_ref(v_a_2842_);
v_a_2842_ = v_tail_2848_;
v_a_2843_ = v_key_2847_;
goto _start;
}
else
{
lean_object* v_tail_2850_; 
v_tail_2850_ = lean_ctor_get(v_a_2842_, 2);
lean_inc(v_tail_2850_);
lean_dec_ref(v_a_2842_);
v_a_2842_ = v_tail_2850_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(lean_object* v_as_2852_, size_t v_sz_2853_, size_t v_i_2854_, lean_object* v_b_2855_){
_start:
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_usize_dec_lt(v_i_2854_, v_sz_2853_);
if (v___x_2856_ == 0)
{
return v_b_2855_;
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2858_; 
v_a_2857_ = lean_array_uget_borrowed(v_as_2852_, v_i_2854_);
lean_inc(v_a_2857_);
v___x_2858_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(v_a_2857_, v_b_2855_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v___x_2858_);
return v_a_2859_;
}
else
{
lean_object* v_a_2860_; size_t v___x_2861_; size_t v___x_2862_; 
v_a_2860_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2860_);
lean_dec_ref(v___x_2858_);
v___x_2861_ = ((size_t)1ULL);
v___x_2862_ = lean_usize_add(v_i_2854_, v___x_2861_);
v_i_2854_ = v___x_2862_;
v_b_2855_ = v_a_2860_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5___boxed(lean_object* v_as_2864_, lean_object* v_sz_2865_, lean_object* v_i_2866_, lean_object* v_b_2867_){
_start:
{
size_t v_sz_boxed_2868_; size_t v_i_boxed_2869_; lean_object* v_res_2870_; 
v_sz_boxed_2868_ = lean_unbox_usize(v_sz_2865_);
lean_dec(v_sz_2865_);
v_i_boxed_2869_ = lean_unbox_usize(v_i_2866_);
lean_dec(v_i_2866_);
v_res_2870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_as_2864_, v_sz_boxed_2868_, v_i_boxed_2869_, v_b_2867_);
lean_dec_ref(v_as_2864_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(lean_object* v_a_2871_, lean_object* v_b_2872_, lean_object* v_x_2873_){
_start:
{
if (lean_obj_tag(v_x_2873_) == 0)
{
lean_dec(v_b_2872_);
lean_dec_ref(v_a_2871_);
return v_x_2873_;
}
else
{
lean_object* v_key_2874_; lean_object* v_value_2875_; lean_object* v_tail_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2888_; 
v_key_2874_ = lean_ctor_get(v_x_2873_, 0);
v_value_2875_ = lean_ctor_get(v_x_2873_, 1);
v_tail_2876_ = lean_ctor_get(v_x_2873_, 2);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_x_2873_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2878_ = v_x_2873_;
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_tail_2876_);
lean_inc(v_value_2875_);
lean_inc(v_key_2874_);
lean_dec(v_x_2873_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint8_t v___x_2880_; 
v___x_2880_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2874_, v_a_2871_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2871_, v_b_2872_, v_tail_2876_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 2, v___x_2881_);
v___x_2883_ = v___x_2878_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_key_2874_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_value_2875_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
else
{
lean_object* v___x_2886_; 
lean_dec(v_value_2875_);
lean_dec(v_key_2874_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 1, v_b_2872_);
lean_ctor_set(v___x_2878_, 0, v_a_2871_);
v___x_2886_ = v___x_2878_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2871_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_b_2872_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_tail_2876_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(lean_object* v_x_2889_, lean_object* v_x_2890_){
_start:
{
if (lean_obj_tag(v_x_2890_) == 0)
{
return v_x_2889_;
}
else
{
lean_object* v_key_2891_; lean_object* v_value_2892_; lean_object* v_tail_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2916_; 
v_key_2891_ = lean_ctor_get(v_x_2890_, 0);
v_value_2892_ = lean_ctor_get(v_x_2890_, 1);
v_tail_2893_ = lean_ctor_get(v_x_2890_, 2);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_x_2890_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2895_ = v_x_2890_;
v_isShared_2896_ = v_isSharedCheck_2916_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_tail_2893_);
lean_inc(v_value_2892_);
lean_inc(v_key_2891_);
lean_dec(v_x_2890_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2916_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; uint64_t v___x_2898_; uint64_t v___x_2899_; uint64_t v___x_2900_; uint64_t v_fold_2901_; uint64_t v___x_2902_; uint64_t v___x_2903_; uint64_t v___x_2904_; size_t v___x_2905_; size_t v___x_2906_; size_t v___x_2907_; size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2897_ = lean_array_get_size(v_x_2889_);
v___x_2898_ = l_Lean_Lsp_instHashableRefIdent_hash(v_key_2891_);
v___x_2899_ = 32ULL;
v___x_2900_ = lean_uint64_shift_right(v___x_2898_, v___x_2899_);
v_fold_2901_ = lean_uint64_xor(v___x_2898_, v___x_2900_);
v___x_2902_ = 16ULL;
v___x_2903_ = lean_uint64_shift_right(v_fold_2901_, v___x_2902_);
v___x_2904_ = lean_uint64_xor(v_fold_2901_, v___x_2903_);
v___x_2905_ = lean_uint64_to_usize(v___x_2904_);
v___x_2906_ = lean_usize_of_nat(v___x_2897_);
v___x_2907_ = ((size_t)1ULL);
v___x_2908_ = lean_usize_sub(v___x_2906_, v___x_2907_);
v___x_2909_ = lean_usize_land(v___x_2905_, v___x_2908_);
v___x_2910_ = lean_array_uget_borrowed(v_x_2889_, v___x_2909_);
lean_inc(v___x_2910_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 2, v___x_2910_);
v___x_2912_ = v___x_2895_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_key_2891_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_value_2892_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_array_uset(v_x_2889_, v___x_2909_, v___x_2912_);
v_x_2889_ = v___x_2913_;
v_x_2890_ = v_tail_2893_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(lean_object* v_i_2917_, lean_object* v_source_2918_, lean_object* v_target_2919_){
_start:
{
lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2920_ = lean_array_get_size(v_source_2918_);
v___x_2921_ = lean_nat_dec_lt(v_i_2917_, v___x_2920_);
if (v___x_2921_ == 0)
{
lean_dec_ref(v_source_2918_);
lean_dec(v_i_2917_);
return v_target_2919_;
}
else
{
lean_object* v_es_2922_; lean_object* v___x_2923_; lean_object* v_source_2924_; lean_object* v_target_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v_es_2922_ = lean_array_fget(v_source_2918_, v_i_2917_);
v___x_2923_ = lean_box(0);
v_source_2924_ = lean_array_fset(v_source_2918_, v_i_2917_, v___x_2923_);
v_target_2925_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_target_2919_, v_es_2922_);
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = lean_nat_add(v_i_2917_, v___x_2926_);
lean_dec(v_i_2917_);
v_i_2917_ = v___x_2927_;
v_source_2918_ = v_source_2924_;
v_target_2919_ = v_target_2925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(lean_object* v_data_2929_){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v_nbuckets_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2930_ = lean_array_get_size(v_data_2929_);
v___x_2931_ = lean_unsigned_to_nat(2u);
v_nbuckets_2932_ = lean_nat_mul(v___x_2930_, v___x_2931_);
v___x_2933_ = lean_unsigned_to_nat(0u);
v___x_2934_ = lean_box(0);
v___x_2935_ = lean_mk_array(v_nbuckets_2932_, v___x_2934_);
v___x_2936_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2933_, v_data_2929_, v___x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object* v_m_2937_, lean_object* v_a_2938_, lean_object* v_b_2939_){
_start:
{
lean_object* v_size_2940_; lean_object* v_buckets_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2984_; 
v_size_2940_ = lean_ctor_get(v_m_2937_, 0);
v_buckets_2941_ = lean_ctor_get(v_m_2937_, 1);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_m_2937_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2943_ = v_m_2937_;
v_isShared_2944_ = v_isSharedCheck_2984_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_buckets_2941_);
lean_inc(v_size_2940_);
lean_dec(v_m_2937_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2984_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; uint64_t v___x_2946_; uint64_t v___x_2947_; uint64_t v___x_2948_; uint64_t v_fold_2949_; uint64_t v___x_2950_; uint64_t v___x_2951_; uint64_t v___x_2952_; size_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; lean_object* v_bkt_2958_; uint8_t v___x_2959_; 
v___x_2945_ = lean_array_get_size(v_buckets_2941_);
v___x_2946_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2938_);
v___x_2947_ = 32ULL;
v___x_2948_ = lean_uint64_shift_right(v___x_2946_, v___x_2947_);
v_fold_2949_ = lean_uint64_xor(v___x_2946_, v___x_2948_);
v___x_2950_ = 16ULL;
v___x_2951_ = lean_uint64_shift_right(v_fold_2949_, v___x_2950_);
v___x_2952_ = lean_uint64_xor(v_fold_2949_, v___x_2951_);
v___x_2953_ = lean_uint64_to_usize(v___x_2952_);
v___x_2954_ = lean_usize_of_nat(v___x_2945_);
v___x_2955_ = ((size_t)1ULL);
v___x_2956_ = lean_usize_sub(v___x_2954_, v___x_2955_);
v___x_2957_ = lean_usize_land(v___x_2953_, v___x_2956_);
v_bkt_2958_ = lean_array_uget_borrowed(v_buckets_2941_, v___x_2957_);
v___x_2959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2938_, v_bkt_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v_size_x27_2961_; lean_object* v___x_2962_; lean_object* v_buckets_x27_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2960_ = lean_unsigned_to_nat(1u);
v_size_x27_2961_ = lean_nat_add(v_size_2940_, v___x_2960_);
lean_dec(v_size_2940_);
lean_inc(v_bkt_2958_);
v___x_2962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2962_, 0, v_a_2938_);
lean_ctor_set(v___x_2962_, 1, v_b_2939_);
lean_ctor_set(v___x_2962_, 2, v_bkt_2958_);
v_buckets_x27_2963_ = lean_array_uset(v_buckets_2941_, v___x_2957_, v___x_2962_);
v___x_2964_ = lean_unsigned_to_nat(4u);
v___x_2965_ = lean_nat_mul(v_size_x27_2961_, v___x_2964_);
v___x_2966_ = lean_unsigned_to_nat(3u);
v___x_2967_ = lean_nat_div(v___x_2965_, v___x_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_array_get_size(v_buckets_x27_2963_);
v___x_2969_ = lean_nat_dec_le(v___x_2967_, v___x_2968_);
lean_dec(v___x_2967_);
if (v___x_2969_ == 0)
{
lean_object* v_val_2970_; lean_object* v___x_2972_; 
v_val_2970_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_2963_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v_val_2970_);
lean_ctor_set(v___x_2943_, 0, v_size_x27_2961_);
v___x_2972_ = v___x_2943_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_size_x27_2961_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_val_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
else
{
lean_object* v___x_2975_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v_buckets_x27_2963_);
lean_ctor_set(v___x_2943_, 0, v_size_x27_2961_);
v___x_2975_ = v___x_2943_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_size_x27_2961_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_buckets_x27_2963_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_object* v___x_2977_; lean_object* v_buckets_x27_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
lean_inc(v_bkt_2958_);
v___x_2977_ = lean_box(0);
v_buckets_x27_2978_ = lean_array_uset(v_buckets_2941_, v___x_2957_, v___x_2977_);
v___x_2979_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2938_, v_b_2939_, v_bkt_2958_);
v___x_2980_ = lean_array_uset(v_buckets_x27_2978_, v___x_2957_, v___x_2979_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v___x_2980_);
v___x_2982_ = v___x_2943_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_size_2940_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object* v___x_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
if (lean_obj_tag(v_a_2986_) == 0)
{
lean_object* v___x_2988_; 
lean_dec_ref(v___x_2985_);
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_a_2987_);
return v___x_2988_;
}
else
{
lean_object* v_key_2989_; lean_object* v_tail_2990_; uint8_t v___x_2991_; 
v_key_2989_ = lean_ctor_get(v_a_2986_, 0);
lean_inc(v_key_2989_);
v_tail_2990_ = lean_ctor_get(v_a_2986_, 2);
lean_inc(v_tail_2990_);
lean_dec_ref(v_a_2986_);
v___x_2991_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2989_, v___x_2985_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
lean_inc_ref(v___x_2985_);
v___x_2992_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_2987_, v_key_2989_, v___x_2985_);
v_a_2986_ = v_tail_2990_;
v_a_2987_ = v___x_2992_;
goto _start;
}
else
{
lean_dec(v_key_2989_);
v_a_2986_ = v_tail_2990_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object* v___x_2995_, lean_object* v_as_2996_, size_t v_sz_2997_, size_t v_i_2998_, lean_object* v_b_2999_){
_start:
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_usize_dec_lt(v_i_2998_, v_sz_2997_);
if (v___x_3000_ == 0)
{
lean_dec_ref(v___x_2995_);
return v_b_2999_;
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3002_; 
v_a_3001_ = lean_array_uget_borrowed(v_as_2996_, v_i_2998_);
lean_inc(v_a_3001_);
lean_inc_ref(v___x_2995_);
v___x_3002_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(v___x_2995_, v_a_3001_, v_b_2999_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; 
lean_dec_ref(v___x_2995_);
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref(v___x_3002_);
return v_a_3003_;
}
else
{
lean_object* v_a_3004_; size_t v___x_3005_; size_t v___x_3006_; 
v_a_3004_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3002_);
v___x_3005_ = ((size_t)1ULL);
v___x_3006_ = lean_usize_add(v_i_2998_, v___x_3005_);
v_i_2998_ = v___x_3006_;
v_b_2999_ = v_a_3004_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object* v___x_3008_, lean_object* v_as_3009_, lean_object* v_sz_3010_, lean_object* v_i_3011_, lean_object* v_b_3012_){
_start:
{
size_t v_sz_boxed_3013_; size_t v_i_boxed_3014_; lean_object* v_res_3015_; 
v_sz_boxed_3013_ = lean_unbox_usize(v_sz_3010_);
lean_dec(v_sz_3010_);
v_i_boxed_3014_ = lean_unbox_usize(v_i_3011_);
lean_dec(v_i_3011_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3008_, v_as_3009_, v_sz_boxed_3013_, v_i_boxed_3014_, v_b_3012_);
lean_dec_ref(v_as_3009_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
if (lean_obj_tag(v_a_3016_) == 0)
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_a_3017_);
return v___x_3018_;
}
else
{
lean_object* v_value_3019_; lean_object* v_key_3020_; lean_object* v_tail_3021_; lean_object* v_buckets_3022_; size_t v_sz_3023_; size_t v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_value_3019_ = lean_ctor_get(v_a_3016_, 1);
lean_inc(v_value_3019_);
v_key_3020_ = lean_ctor_get(v_a_3016_, 0);
lean_inc(v_key_3020_);
v_tail_3021_ = lean_ctor_get(v_a_3016_, 2);
lean_inc(v_tail_3021_);
lean_dec_ref(v_a_3016_);
v_buckets_3022_ = lean_ctor_get(v_value_3019_, 1);
lean_inc_ref(v_buckets_3022_);
lean_dec(v_value_3019_);
v_sz_3023_ = lean_array_size(v_buckets_3022_);
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_buckets_3022_, v_sz_3023_, v___x_3024_, v_key_3020_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3025_, v_buckets_3022_, v_sz_3023_, v___x_3024_, v_a_3017_);
lean_dec_ref(v_buckets_3022_);
v_a_3016_ = v_tail_3021_;
v_a_3017_ = v___x_3026_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object* v_as_3028_, size_t v_sz_3029_, size_t v_i_3030_, lean_object* v_b_3031_){
_start:
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_usize_dec_lt(v_i_3030_, v_sz_3029_);
if (v___x_3032_ == 0)
{
return v_b_3031_;
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3034_; 
v_a_3033_ = lean_array_uget_borrowed(v_as_3028_, v_i_3030_);
lean_inc(v_a_3033_);
v___x_3034_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(v_a_3033_, v_b_3031_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
return v_a_3035_;
}
else
{
lean_object* v_a_3036_; size_t v___x_3037_; size_t v___x_3038_; 
v_a_3036_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3036_);
lean_dec_ref(v___x_3034_);
v___x_3037_ = ((size_t)1ULL);
v___x_3038_ = lean_usize_add(v_i_3030_, v___x_3037_);
v_i_3030_ = v___x_3038_;
v_b_3031_ = v_a_3036_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object* v_as_3040_, lean_object* v_sz_3041_, lean_object* v_i_3042_, lean_object* v_b_3043_){
_start:
{
size_t v_sz_boxed_3044_; size_t v_i_boxed_3045_; lean_object* v_res_3046_; 
v_sz_boxed_3044_ = lean_unbox_usize(v_sz_3041_);
lean_dec(v_sz_3041_);
v_i_boxed_3045_ = lean_unbox_usize(v_i_3042_);
lean_dec(v_i_3042_);
v_res_3046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_as_3040_, v_sz_boxed_3044_, v_i_boxed_3045_, v_b_3043_);
lean_dec_ref(v_as_3040_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object* v_a_3047_, lean_object* v_x_3048_){
_start:
{
if (lean_obj_tag(v_x_3048_) == 0)
{
return v_x_3048_;
}
else
{
lean_object* v_key_3049_; lean_object* v_value_3050_; lean_object* v_tail_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3060_; 
v_key_3049_ = lean_ctor_get(v_x_3048_, 0);
v_value_3050_ = lean_ctor_get(v_x_3048_, 1);
v_tail_3051_ = lean_ctor_get(v_x_3048_, 2);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_x_3048_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3053_ = v_x_3048_;
v_isShared_3054_ = v_isSharedCheck_3060_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_tail_3051_);
lean_inc(v_value_3050_);
lean_inc(v_key_3049_);
lean_dec(v_x_3048_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3060_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
uint8_t v___x_3055_; 
v___x_3055_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3049_, v_a_3047_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3056_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3047_, v_tail_3051_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 2, v___x_3056_);
v___x_3058_ = v___x_3053_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_key_3049_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_value_3050_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
else
{
lean_del_object(v___x_3053_);
lean_dec(v_value_3050_);
lean_dec(v_key_3049_);
return v_tail_3051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object* v_a_3061_, lean_object* v_x_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3061_, v_x_3062_);
lean_dec_ref(v_a_3061_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object* v_m_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_size_3066_; lean_object* v_buckets_3067_; lean_object* v___x_3068_; uint64_t v___x_3069_; uint64_t v___x_3070_; uint64_t v___x_3071_; uint64_t v_fold_3072_; uint64_t v___x_3073_; uint64_t v___x_3074_; uint64_t v___x_3075_; size_t v___x_3076_; size_t v___x_3077_; size_t v___x_3078_; size_t v___x_3079_; size_t v___x_3080_; lean_object* v_bkt_3081_; uint8_t v___x_3082_; 
v_size_3066_ = lean_ctor_get(v_m_3064_, 0);
v_buckets_3067_ = lean_ctor_get(v_m_3064_, 1);
v___x_3068_ = lean_array_get_size(v_buckets_3067_);
v___x_3069_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3065_);
v___x_3070_ = 32ULL;
v___x_3071_ = lean_uint64_shift_right(v___x_3069_, v___x_3070_);
v_fold_3072_ = lean_uint64_xor(v___x_3069_, v___x_3071_);
v___x_3073_ = 16ULL;
v___x_3074_ = lean_uint64_shift_right(v_fold_3072_, v___x_3073_);
v___x_3075_ = lean_uint64_xor(v_fold_3072_, v___x_3074_);
v___x_3076_ = lean_uint64_to_usize(v___x_3075_);
v___x_3077_ = lean_usize_of_nat(v___x_3068_);
v___x_3078_ = ((size_t)1ULL);
v___x_3079_ = lean_usize_sub(v___x_3077_, v___x_3078_);
v___x_3080_ = lean_usize_land(v___x_3076_, v___x_3079_);
v_bkt_3081_ = lean_array_uget_borrowed(v_buckets_3067_, v___x_3080_);
v___x_3082_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3065_, v_bkt_3081_);
if (v___x_3082_ == 0)
{
return v_m_3064_;
}
else
{
lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3095_; 
lean_inc(v_bkt_3081_);
lean_inc_ref(v_buckets_3067_);
lean_inc(v_size_3066_);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_m_3064_);
if (v_isSharedCheck_3095_ == 0)
{
lean_object* v_unused_3096_; lean_object* v_unused_3097_; 
v_unused_3096_ = lean_ctor_get(v_m_3064_, 1);
lean_dec(v_unused_3096_);
v_unused_3097_ = lean_ctor_get(v_m_3064_, 0);
lean_dec(v_unused_3097_);
v___x_3084_ = v_m_3064_;
v_isShared_3085_ = v_isSharedCheck_3095_;
goto v_resetjp_3083_;
}
else
{
lean_dec(v_m_3064_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3095_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v_buckets_x27_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3086_ = lean_box(0);
v_buckets_x27_3087_ = lean_array_uset(v_buckets_3067_, v___x_3080_, v___x_3086_);
v___x_3088_ = lean_unsigned_to_nat(1u);
v___x_3089_ = lean_nat_sub(v_size_3066_, v___x_3088_);
lean_dec(v_size_3066_);
v___x_3090_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3065_, v_bkt_3081_);
v___x_3091_ = lean_array_uset(v_buckets_x27_3087_, v___x_3080_, v___x_3090_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 1, v___x_3091_);
lean_ctor_set(v___x_3084_, 0, v___x_3089_);
v___x_3093_ = v___x_3084_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3089_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object* v_m_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3098_, v_a_3099_);
lean_dec_ref(v_a_3099_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object* v_m_3101_, lean_object* v_a_3102_, lean_object* v_b_3103_){
_start:
{
lean_object* v_size_3104_; lean_object* v_buckets_3105_; lean_object* v___x_3106_; uint64_t v___x_3107_; uint64_t v___x_3108_; uint64_t v___x_3109_; uint64_t v_fold_3110_; uint64_t v___x_3111_; uint64_t v___x_3112_; uint64_t v___x_3113_; size_t v___x_3114_; size_t v___x_3115_; size_t v___x_3116_; size_t v___x_3117_; size_t v___x_3118_; lean_object* v_bkt_3119_; uint8_t v___x_3120_; 
v_size_3104_ = lean_ctor_get(v_m_3101_, 0);
v_buckets_3105_ = lean_ctor_get(v_m_3101_, 1);
v___x_3106_ = lean_array_get_size(v_buckets_3105_);
v___x_3107_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3102_);
v___x_3108_ = 32ULL;
v___x_3109_ = lean_uint64_shift_right(v___x_3107_, v___x_3108_);
v_fold_3110_ = lean_uint64_xor(v___x_3107_, v___x_3109_);
v___x_3111_ = 16ULL;
v___x_3112_ = lean_uint64_shift_right(v_fold_3110_, v___x_3111_);
v___x_3113_ = lean_uint64_xor(v_fold_3110_, v___x_3112_);
v___x_3114_ = lean_uint64_to_usize(v___x_3113_);
v___x_3115_ = lean_usize_of_nat(v___x_3106_);
v___x_3116_ = ((size_t)1ULL);
v___x_3117_ = lean_usize_sub(v___x_3115_, v___x_3116_);
v___x_3118_ = lean_usize_land(v___x_3114_, v___x_3117_);
v_bkt_3119_ = lean_array_uget_borrowed(v_buckets_3105_, v___x_3118_);
v___x_3120_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3102_, v_bkt_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3141_; 
lean_inc_ref(v_buckets_3105_);
lean_inc(v_size_3104_);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_m_3101_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; lean_object* v_unused_3143_; 
v_unused_3142_ = lean_ctor_get(v_m_3101_, 1);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v_m_3101_, 0);
lean_dec(v_unused_3143_);
v___x_3122_ = v_m_3101_;
v_isShared_3123_ = v_isSharedCheck_3141_;
goto v_resetjp_3121_;
}
else
{
lean_dec(v_m_3101_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3141_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v_size_x27_3125_; lean_object* v___x_3126_; lean_object* v_buckets_x27_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3124_ = lean_unsigned_to_nat(1u);
v_size_x27_3125_ = lean_nat_add(v_size_3104_, v___x_3124_);
lean_dec(v_size_3104_);
lean_inc(v_bkt_3119_);
v___x_3126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3126_, 0, v_a_3102_);
lean_ctor_set(v___x_3126_, 1, v_b_3103_);
lean_ctor_set(v___x_3126_, 2, v_bkt_3119_);
v_buckets_x27_3127_ = lean_array_uset(v_buckets_3105_, v___x_3118_, v___x_3126_);
v___x_3128_ = lean_unsigned_to_nat(4u);
v___x_3129_ = lean_nat_mul(v_size_x27_3125_, v___x_3128_);
v___x_3130_ = lean_unsigned_to_nat(3u);
v___x_3131_ = lean_nat_div(v___x_3129_, v___x_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_array_get_size(v_buckets_x27_3127_);
v___x_3133_ = lean_nat_dec_le(v___x_3131_, v___x_3132_);
lean_dec(v___x_3131_);
if (v___x_3133_ == 0)
{
lean_object* v_val_3134_; lean_object* v___x_3136_; 
v_val_3134_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3127_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 1, v_val_3134_);
lean_ctor_set(v___x_3122_, 0, v_size_x27_3125_);
v___x_3136_ = v___x_3122_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_size_x27_3125_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_val_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
else
{
lean_object* v___x_3139_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 1, v_buckets_x27_3127_);
lean_ctor_set(v___x_3122_, 0, v_size_x27_3125_);
v___x_3139_ = v___x_3122_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_size_x27_3125_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v_buckets_x27_3127_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_dec(v_b_3103_);
lean_dec_ref(v_a_3102_);
return v_m_3101_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object* v_a_3144_, lean_object* v_fallback_3145_, lean_object* v_x_3146_){
_start:
{
if (lean_obj_tag(v_x_3146_) == 0)
{
lean_inc(v_fallback_3145_);
return v_fallback_3145_;
}
else
{
lean_object* v_key_3147_; lean_object* v_value_3148_; lean_object* v_tail_3149_; uint8_t v___x_3150_; 
v_key_3147_ = lean_ctor_get(v_x_3146_, 0);
v_value_3148_ = lean_ctor_get(v_x_3146_, 1);
v_tail_3149_ = lean_ctor_get(v_x_3146_, 2);
v___x_3150_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3147_, v_a_3144_);
if (v___x_3150_ == 0)
{
v_x_3146_ = v_tail_3149_;
goto _start;
}
else
{
lean_inc(v_value_3148_);
return v_value_3148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object* v_a_3152_, lean_object* v_fallback_3153_, lean_object* v_x_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3152_, v_fallback_3153_, v_x_3154_);
lean_dec(v_x_3154_);
lean_dec(v_fallback_3153_);
lean_dec_ref(v_a_3152_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object* v_m_3156_, lean_object* v_a_3157_, lean_object* v_fallback_3158_){
_start:
{
lean_object* v_buckets_3159_; lean_object* v___x_3160_; uint64_t v___x_3161_; uint64_t v___x_3162_; uint64_t v___x_3163_; uint64_t v_fold_3164_; uint64_t v___x_3165_; uint64_t v___x_3166_; uint64_t v___x_3167_; size_t v___x_3168_; size_t v___x_3169_; size_t v___x_3170_; size_t v___x_3171_; size_t v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_buckets_3159_ = lean_ctor_get(v_m_3156_, 1);
v___x_3160_ = lean_array_get_size(v_buckets_3159_);
v___x_3161_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3157_);
v___x_3162_ = 32ULL;
v___x_3163_ = lean_uint64_shift_right(v___x_3161_, v___x_3162_);
v_fold_3164_ = lean_uint64_xor(v___x_3161_, v___x_3163_);
v___x_3165_ = 16ULL;
v___x_3166_ = lean_uint64_shift_right(v_fold_3164_, v___x_3165_);
v___x_3167_ = lean_uint64_xor(v_fold_3164_, v___x_3166_);
v___x_3168_ = lean_uint64_to_usize(v___x_3167_);
v___x_3169_ = lean_usize_of_nat(v___x_3160_);
v___x_3170_ = ((size_t)1ULL);
v___x_3171_ = lean_usize_sub(v___x_3169_, v___x_3170_);
v___x_3172_ = lean_usize_land(v___x_3168_, v___x_3171_);
v___x_3173_ = lean_array_uget_borrowed(v_buckets_3159_, v___x_3172_);
v___x_3174_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3157_, v_fallback_3158_, v___x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object* v_m_3175_, lean_object* v_a_3176_, lean_object* v_fallback_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3175_, v_a_3176_, v_fallback_3177_);
lean_dec(v_fallback_3177_);
lean_dec_ref(v_a_3176_);
lean_dec_ref(v_m_3175_);
return v_res_3178_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = lean_box(0);
v___x_3180_ = lean_unsigned_to_nat(16u);
v___x_3181_ = lean_mk_array(v___x_3180_, v___x_3179_);
return v___x_3181_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v___x_3182_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object* v_idMap_3185_, lean_object* v_classesById_3186_, lean_object* v_id_3187_){
_start:
{
lean_object* v_representative_3188_; lean_object* v___x_3189_; lean_object* v_class_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v_class_3193_; lean_object* v___x_3194_; 
lean_inc_ref(v_id_3187_);
v_representative_3188_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_3185_, v_id_3187_);
v___x_3189_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_class_3190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_classesById_3186_, v_representative_3188_, v___x_3189_);
v___x_3191_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_classesById_3186_, v_representative_3188_);
v___x_3192_ = lean_box(0);
v_class_3193_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_class_3190_, v_id_3187_, v___x_3192_);
v___x_3194_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v___x_3191_, v_representative_3188_, v_class_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object* v_idMap_3195_, lean_object* v_classesById_3196_, lean_object* v_id_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3195_, v_classesById_3196_, v_id_3197_);
lean_dec_ref(v_idMap_3195_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object* v_idMap_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
if (lean_obj_tag(v_a_3200_) == 0)
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3202_, 0, v_a_3201_);
return v___x_3202_;
}
else
{
lean_object* v_key_3203_; lean_object* v_value_3204_; lean_object* v_tail_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_key_3203_ = lean_ctor_get(v_a_3200_, 0);
lean_inc(v_key_3203_);
v_value_3204_ = lean_ctor_get(v_a_3200_, 1);
lean_inc(v_value_3204_);
v_tail_3205_ = lean_ctor_get(v_a_3200_, 2);
lean_inc(v_tail_3205_);
lean_dec_ref(v_a_3200_);
v___x_3206_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3199_, v_a_3201_, v_key_3203_);
v___x_3207_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3199_, v___x_3206_, v_value_3204_);
v_a_3200_ = v_tail_3205_;
v_a_3201_ = v___x_3207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object* v_idMap_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3209_, v_a_3210_, v_a_3211_);
lean_dec_ref(v_idMap_3209_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object* v_idMap_3213_, lean_object* v_as_3214_, size_t v_sz_3215_, size_t v_i_3216_, lean_object* v_b_3217_){
_start:
{
uint8_t v___x_3218_; 
v___x_3218_ = lean_usize_dec_lt(v_i_3216_, v_sz_3215_);
if (v___x_3218_ == 0)
{
return v_b_3217_;
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3220_; 
v_a_3219_ = lean_array_uget_borrowed(v_as_3214_, v_i_3216_);
lean_inc(v_a_3219_);
v___x_3220_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3213_, v_a_3219_, v_b_3217_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref(v___x_3220_);
return v_a_3221_;
}
else
{
lean_object* v_a_3222_; size_t v___x_3223_; size_t v___x_3224_; 
v_a_3222_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3222_);
lean_dec_ref(v___x_3220_);
v___x_3223_ = ((size_t)1ULL);
v___x_3224_ = lean_usize_add(v_i_3216_, v___x_3223_);
v_i_3216_ = v___x_3224_;
v_b_3217_ = v_a_3222_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object* v_idMap_3226_, lean_object* v_as_3227_, lean_object* v_sz_3228_, lean_object* v_i_3229_, lean_object* v_b_3230_){
_start:
{
size_t v_sz_boxed_3231_; size_t v_i_boxed_3232_; lean_object* v_res_3233_; 
v_sz_boxed_3231_ = lean_unbox_usize(v_sz_3228_);
lean_dec(v_sz_3228_);
v_i_boxed_3232_ = lean_unbox_usize(v_i_3229_);
lean_dec(v_i_3229_);
v_res_3233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3226_, v_as_3227_, v_sz_boxed_3231_, v_i_boxed_3232_, v_b_3230_);
lean_dec_ref(v_as_3227_);
lean_dec_ref(v_idMap_3226_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object* v_idMap_3234_){
_start:
{
lean_object* v_buckets_3235_; lean_object* v_classesById_3236_; size_t v_sz_3237_; size_t v___x_3238_; lean_object* v___x_3239_; lean_object* v_buckets_3240_; size_t v_sz_3241_; lean_object* v___x_3242_; 
v_buckets_3235_ = lean_ctor_get(v_idMap_3234_, 1);
v_classesById_3236_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_sz_3237_ = lean_array_size(v_buckets_3235_);
v___x_3238_ = ((size_t)0ULL);
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3234_, v_buckets_3235_, v_sz_3237_, v___x_3238_, v_classesById_3236_);
v_buckets_3240_ = lean_ctor_get(v___x_3239_, 1);
lean_inc_ref(v_buckets_3240_);
lean_dec_ref(v___x_3239_);
v_sz_3241_ = lean_array_size(v_buckets_3240_);
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_buckets_3240_, v_sz_3241_, v___x_3238_, v_classesById_3236_);
lean_dec_ref(v_buckets_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object* v_idMap_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v_idMap_3243_);
lean_dec_ref(v_idMap_3243_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object* v_00_u03b2_3245_, lean_object* v_m_3246_, lean_object* v_a_3247_, lean_object* v_fallback_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3246_, v_a_3247_, v_fallback_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object* v_00_u03b2_3250_, lean_object* v_m_3251_, lean_object* v_a_3252_, lean_object* v_fallback_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(v_00_u03b2_3250_, v_m_3251_, v_a_3252_, v_fallback_3253_);
lean_dec(v_fallback_3253_);
lean_dec_ref(v_a_3252_);
lean_dec_ref(v_m_3251_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object* v_00_u03b2_3255_, lean_object* v_m_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3256_, v_a_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object* v_00_u03b2_3259_, lean_object* v_m_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(v_00_u03b2_3259_, v_m_3260_, v_a_3261_);
lean_dec_ref(v_a_3261_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object* v_00_u03b2_3263_, lean_object* v_m_3264_, lean_object* v_a_3265_, lean_object* v_b_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_m_3264_, v_a_3265_, v_b_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object* v_00_u03b2_3268_, lean_object* v_m_3269_, lean_object* v_a_3270_, lean_object* v_b_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_m_3269_, v_a_3270_, v_b_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object* v_00_u03b2_3273_, lean_object* v_a_3274_, lean_object* v_fallback_3275_, lean_object* v_x_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3274_, v_fallback_3275_, v_x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3278_, lean_object* v_a_3279_, lean_object* v_fallback_3280_, lean_object* v_x_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(v_00_u03b2_3278_, v_a_3279_, v_fallback_3280_, v_x_3281_);
lean_dec(v_x_3281_);
lean_dec(v_fallback_3280_);
lean_dec_ref(v_a_3279_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object* v_00_u03b2_3283_, lean_object* v_a_3284_, lean_object* v_x_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3284_, v_x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3287_, lean_object* v_a_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(v_00_u03b2_3287_, v_a_3288_, v_x_3289_);
lean_dec_ref(v_a_3288_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object* v_00_u03b2_3291_, lean_object* v_data_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_data_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object* v_00_u03b2_3294_, lean_object* v_a_3295_, lean_object* v_b_3296_, lean_object* v_x_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_3295_, v_b_3296_, v_x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3299_, lean_object* v_i_3300_, lean_object* v_source_3301_, lean_object* v_target_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v_i_3300_, v_source_3301_, v_target_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object* v_00_u03b2_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_x_3305_, v_x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object* v_id_3308_, lean_object* v_baseId_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; 
v___x_3311_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_a_3310_, v_id_3308_);
v___x_3312_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_a_3310_, v_baseId_3309_);
v___x_3313_ = l_Lean_Lsp_instBEqRefIdent_beq(v___x_3312_, v___x_3311_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = lean_box(0);
v___x_3315_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3310_, v___x_3311_, v___x_3312_);
v___x_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
return v___x_3316_;
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec_ref(v___x_3312_);
lean_dec_ref(v___x_3311_);
v___x_3317_ = lean_box(0);
v___x_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
lean_ctor_set(v___x_3318_, 1, v_a_3310_);
return v___x_3318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object* v_ci_3319_, lean_object* v_info_3320_, lean_object* v_x_3321_, lean_object* v___y_3322_){
_start:
{
if (lean_obj_tag(v_info_3320_) == 11)
{
lean_object* v_toCommandContextInfo_3323_; lean_object* v_i_3324_; lean_object* v_env_3325_; lean_object* v___x_3326_; lean_object* v_mainModule_3327_; lean_object* v_id_3328_; lean_object* v_baseId_3329_; uint8_t v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_toCommandContextInfo_3323_ = lean_ctor_get(v_ci_3319_, 0);
v_i_3324_ = lean_ctor_get(v_info_3320_, 0);
lean_inc_ref(v_i_3324_);
lean_dec_ref(v_info_3320_);
v_env_3325_ = lean_ctor_get(v_toCommandContextInfo_3323_, 0);
v___x_3326_ = l_Lean_Environment_header(v_env_3325_);
v_mainModule_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_mainModule_3327_);
lean_dec_ref(v___x_3326_);
v_id_3328_ = lean_ctor_get(v_i_3324_, 1);
lean_inc(v_id_3328_);
v_baseId_3329_ = lean_ctor_get(v_i_3324_, 2);
lean_inc(v_baseId_3329_);
lean_dec_ref(v_i_3324_);
v___x_3330_ = 1;
v___x_3331_ = l_Lean_Name_toString(v_mainModule_3327_, v___x_3330_);
v___x_3332_ = l_Lean_Name_toString(v_id_3328_, v___x_3330_);
lean_inc_ref(v___x_3331_);
v___x_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = l_Lean_Name_toString(v_baseId_3329_, v___x_3330_);
v___x_3335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3331_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v___x_3333_, v___x_3335_, v___y_3322_);
return v___x_3336_;
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec_ref(v_info_3320_);
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
lean_ctor_set(v___x_3338_, 1, v___y_3322_);
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object* v_ci_3339_, lean_object* v_info_3340_, lean_object* v_x_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(v_ci_3339_, v_info_3340_, v_x_3341_, v___y_3342_);
lean_dec_ref(v_x_3341_);
lean_dec_ref(v_ci_3339_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object* v_x_3344_, lean_object* v_x_3345_, lean_object* v_x_3346_, lean_object* v___y_3347_){
_start:
{
uint8_t v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = 1;
v___x_3349_ = lean_box(v___x_3348_);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_ctor_set(v___x_3350_, 1, v___y_3347_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(v_x_3351_, v_x_3352_, v_x_3353_, v___y_3354_);
lean_dec_ref(v_x_3353_);
lean_dec_ref(v_x_3352_);
lean_dec_ref(v_x_3351_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3356_, lean_object* v_ci_3357_, lean_object* v_i_3358_, lean_object* v_cs_3359_, lean_object* v_x_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = lean_apply_4(v_postNode_3356_, v_ci_3357_, v_i_3358_, v_cs_3359_, v___y_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3363_, lean_object* v_ci_3364_, lean_object* v_i_3365_, lean_object* v_cs_3366_, lean_object* v_x_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3363_, v_ci_3364_, v_i_3365_, v_cs_3366_, v_x_3367_, v___y_3368_);
lean_dec(v_x_3367_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v___f_3372_; lean_object* v___f_3373_; lean_object* v___f_3374_; lean_object* v___f_3375_; lean_object* v___f_3376_; lean_object* v___f_3377_; lean_object* v___f_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___f_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3784__overap_3394_; lean_object* v___x_3395_; 
v___f_3372_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3373_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3374_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3375_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3376_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3377_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3378_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___f_3372_);
lean_ctor_set(v___x_3379_, 1, v___f_3373_);
v___x_3380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
lean_ctor_set(v___x_3380_, 1, v___f_3374_);
lean_ctor_set(v___x_3380_, 2, v___f_3375_);
lean_ctor_set(v___x_3380_, 3, v___f_3376_);
lean_ctor_set(v___x_3380_, 4, v___f_3377_);
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v___f_3378_);
lean_inc_ref_n(v___x_3381_, 6);
v___f_3382_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3382_, 0, v___x_3381_);
v___f_3383_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3383_, 0, v___x_3381_);
v___f_3384_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3384_, 0, v___x_3381_);
v___f_3385_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3385_, 0, v___x_3381_);
v___x_3386_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3386_, 0, lean_box(0));
lean_closure_set(v___x_3386_, 1, lean_box(0));
lean_closure_set(v___x_3386_, 2, v___x_3381_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v___f_3382_);
v___x_3388_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3388_, 0, lean_box(0));
lean_closure_set(v___x_3388_, 1, lean_box(0));
lean_closure_set(v___x_3388_, 2, v___x_3381_);
v___x_3389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
lean_ctor_set(v___x_3389_, 2, v___f_3383_);
lean_ctor_set(v___x_3389_, 3, v___f_3384_);
lean_ctor_set(v___x_3389_, 4, v___f_3385_);
v___x_3390_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3390_, 0, lean_box(0));
lean_closure_set(v___x_3390_, 1, lean_box(0));
lean_closure_set(v___x_3390_, 2, v___x_3381_);
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = lean_box(0);
v___x_3393_ = l_instInhabitedOfMonad___redArg(v___x_3391_, v___x_3392_);
v___x_3784__overap_3394_ = lean_panic_fn_borrowed(v___x_3393_, v_msg_3370_);
lean_dec(v___x_3393_);
v___x_3395_ = lean_apply_1(v___x_3784__overap_3394_, v___y_3371_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3396_, lean_object* v_postNode_3397_, lean_object* v_x_3398_, lean_object* v_x_3399_, lean_object* v___y_3400_){
_start:
{
switch(lean_obj_tag(v_x_3399_))
{
case 0:
{
lean_object* v_i_3401_; lean_object* v_t_3402_; lean_object* v___x_3403_; 
v_i_3401_ = lean_ctor_get(v_x_3399_, 0);
lean_inc_ref(v_i_3401_);
v_t_3402_ = lean_ctor_get(v_x_3399_, 1);
lean_inc_ref(v_t_3402_);
lean_dec_ref(v_x_3399_);
v___x_3403_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3401_, v_x_3398_);
v_x_3398_ = v___x_3403_;
v_x_3399_ = v_t_3402_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3398_) == 0)
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_dec_ref(v_x_3399_);
lean_dec_ref(v_postNode_3397_);
lean_dec_ref(v_preNode_3396_);
v___x_3405_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3406_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3405_, v___y_3400_);
return v___x_3406_;
}
else
{
lean_object* v_i_3407_; lean_object* v_children_3408_; lean_object* v_val_3409_; lean_object* v___x_3410_; lean_object* v_fst_3411_; uint8_t v___x_3412_; 
v_i_3407_ = lean_ctor_get(v_x_3399_, 0);
lean_inc_ref_n(v_i_3407_, 2);
v_children_3408_ = lean_ctor_get(v_x_3399_, 1);
lean_inc_ref_n(v_children_3408_, 2);
lean_dec_ref(v_x_3399_);
v_val_3409_ = lean_ctor_get(v_x_3398_, 0);
lean_inc_n(v_val_3409_, 2);
lean_inc_ref(v_preNode_3396_);
v___x_3410_ = lean_apply_4(v_preNode_3396_, v_val_3409_, v_i_3407_, v_children_3408_, v___y_3400_);
v_fst_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_fst_3411_);
v___x_3412_ = lean_unbox(v_fst_3411_);
lean_dec(v_fst_3411_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_preNode_3396_);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_x_3398_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v_x_3398_, 0);
lean_dec(v_unused_3432_);
v___x_3414_ = v_x_3398_;
v_isShared_3415_ = v_isSharedCheck_3431_;
goto v_resetjp_3413_;
}
else
{
lean_dec(v_x_3398_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3431_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v_snd_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v_fst_3419_; lean_object* v_snd_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3430_; 
v_snd_3416_ = lean_ctor_get(v___x_3410_, 1);
lean_inc(v_snd_3416_);
lean_dec_ref(v___x_3410_);
v___x_3417_ = lean_box(0);
v___x_3418_ = lean_apply_5(v_postNode_3397_, v_val_3409_, v_i_3407_, v_children_3408_, v___x_3417_, v_snd_3416_);
v_fst_3419_ = lean_ctor_get(v___x_3418_, 0);
v_snd_3420_ = lean_ctor_get(v___x_3418_, 1);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3422_ = v___x_3418_;
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_snd_3420_);
lean_inc(v_fst_3419_);
lean_dec(v___x_3418_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v_fst_3419_);
v___x_3425_ = v___x_3414_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_fst_3419_);
v___x_3425_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_snd_3420_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
else
{
lean_object* v_snd_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v_fst_3438_; lean_object* v_snd_3439_; lean_object* v___x_3440_; lean_object* v_fst_3441_; lean_object* v_snd_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3450_; 
v_snd_3433_ = lean_ctor_get(v___x_3410_, 1);
lean_inc(v_snd_3433_);
lean_dec_ref(v___x_3410_);
v___x_3434_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3398_, v_i_3407_);
v___x_3435_ = l_Lean_PersistentArray_toList___redArg(v_children_3408_);
v___x_3436_ = lean_box(0);
lean_inc_ref(v_postNode_3397_);
v___x_3437_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3396_, v_postNode_3397_, v___x_3434_, v___x_3435_, v___x_3436_, v_snd_3433_);
v_fst_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_fst_3438_);
v_snd_3439_ = lean_ctor_get(v___x_3437_, 1);
lean_inc(v_snd_3439_);
lean_dec_ref(v___x_3437_);
v___x_3440_ = lean_apply_5(v_postNode_3397_, v_val_3409_, v_i_3407_, v_children_3408_, v_fst_3438_, v_snd_3439_);
v_fst_3441_ = lean_ctor_get(v___x_3440_, 0);
v_snd_3442_ = lean_ctor_get(v___x_3440_, 1);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3444_ = v___x_3440_;
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_snd_3442_);
lean_inc(v_fst_3441_);
lean_dec(v___x_3440_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_fst_3441_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3446_);
v___x_3448_ = v___x_3444_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_snd_3442_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
default: 
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
lean_dec_ref(v_x_3399_);
lean_dec(v_x_3398_);
lean_dec_ref(v_postNode_3397_);
lean_dec_ref(v_preNode_3396_);
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v___y_3400_);
return v___x_3452_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3453_, lean_object* v_postNode_3454_, lean_object* v___x_3455_, lean_object* v_x_3456_, lean_object* v_x_3457_, lean_object* v___y_3458_){
_start:
{
if (lean_obj_tag(v_x_3456_) == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_dec(v___x_3455_);
lean_dec_ref(v_postNode_3454_);
lean_dec_ref(v_preNode_3453_);
v___x_3459_ = l_List_reverse___redArg(v_x_3457_);
v___x_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
lean_ctor_set(v___x_3460_, 1, v___y_3458_);
return v___x_3460_;
}
else
{
lean_object* v_head_3461_; lean_object* v_tail_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3473_; 
v_head_3461_ = lean_ctor_get(v_x_3456_, 0);
v_tail_3462_ = lean_ctor_get(v_x_3456_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_x_3456_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3464_ = v_x_3456_;
v_isShared_3465_ = v_isSharedCheck_3473_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_tail_3462_);
lean_inc(v_head_3461_);
lean_dec(v_x_3456_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3473_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v_fst_3467_; lean_object* v_snd_3468_; lean_object* v___x_3470_; 
lean_inc(v___x_3455_);
lean_inc_ref(v_postNode_3454_);
lean_inc_ref(v_preNode_3453_);
v___x_3466_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3453_, v_postNode_3454_, v___x_3455_, v_head_3461_, v___y_3458_);
v_fst_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_fst_3467_);
v_snd_3468_ = lean_ctor_get(v___x_3466_, 1);
lean_inc(v_snd_3468_);
lean_dec_ref(v___x_3466_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 1, v_x_3457_);
lean_ctor_set(v___x_3464_, 0, v_fst_3467_);
v___x_3470_ = v___x_3464_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_fst_3467_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_x_3457_);
v___x_3470_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
v_x_3456_ = v_tail_3462_;
v_x_3457_ = v___x_3470_;
v___y_3458_ = v_snd_3468_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3474_, lean_object* v_postNode_3475_, lean_object* v_ctx_x3f_3476_, lean_object* v_t_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v___f_3479_; lean_object* v___x_3480_; lean_object* v_snd_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3489_; 
v___f_3479_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3479_, 0, v_postNode_3475_);
v___x_3480_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3474_, v___f_3479_, v_ctx_x3f_3476_, v_t_3477_, v___y_3478_);
v_snd_3481_ = lean_ctor_get(v___x_3480_, 1);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3489_ == 0)
{
lean_object* v_unused_3490_; 
v_unused_3490_ = lean_ctor_get(v___x_3480_, 0);
lean_dec(v_unused_3490_);
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3489_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_snd_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3489_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3485_ = lean_box(0);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3485_);
v___x_3487_ = v___x_3483_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v_snd_3481_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object* v_hi_3884_, lean_object* v_pivot_3885_, lean_object* v_as_3886_, lean_object* v_i_3887_, lean_object* v_k_3888_){
_start:
{
uint8_t v___x_3893_; 
v___x_3893_ = lean_nat_dec_lt(v_k_3888_, v_hi_3884_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec(v_k_3888_);
v___x_3894_ = lean_array_fswap(v_as_3886_, v_i_3887_, v_hi_3884_);
v___x_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3895_, 0, v_i_3887_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
return v___x_3895_;
}
else
{
lean_object* v___x_3896_; lean_object* v_range_3897_; lean_object* v_range_3898_; uint8_t v___x_3899_; 
v___x_3896_ = lean_array_fget_borrowed(v_as_3886_, v_k_3888_);
v_range_3897_ = lean_ctor_get(v___x_3896_, 2);
v_range_3898_ = lean_ctor_get(v_pivot_3885_, 2);
v___x_3899_ = l_Lean_Lsp_instOrdRange_ord(v_range_3897_, v_range_3898_);
if (v___x_3899_ == 0)
{
if (v___x_3893_ == 0)
{
goto v___jp_3889_;
}
else
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3900_ = lean_array_fswap(v_as_3886_, v_i_3887_, v_k_3888_);
v___x_3901_ = lean_unsigned_to_nat(1u);
v___x_3902_ = lean_nat_add(v_i_3887_, v___x_3901_);
lean_dec(v_i_3887_);
v___x_3903_ = lean_nat_add(v_k_3888_, v___x_3901_);
lean_dec(v_k_3888_);
v_as_3886_ = v___x_3900_;
v_i_3887_ = v___x_3902_;
v_k_3888_ = v___x_3903_;
goto _start;
}
}
else
{
goto v___jp_3889_;
}
}
v___jp_3889_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_unsigned_to_nat(1u);
v___x_3891_ = lean_nat_add(v_k_3888_, v___x_3890_);
lean_dec(v_k_3888_);
v_k_3888_ = v___x_3891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object* v_hi_3905_, lean_object* v_pivot_3906_, lean_object* v_as_3907_, lean_object* v_i_3908_, lean_object* v_k_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3905_, v_pivot_3906_, v_as_3907_, v_i_3908_, v_k_3909_);
lean_dec_ref(v_pivot_3906_);
lean_dec(v_hi_3905_);
return v_res_3910_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3911_, lean_object* v_x1_3912_, lean_object* v_x2_3913_){
_start:
{
lean_object* v_range_3914_; lean_object* v_range_3915_; uint8_t v___x_3916_; 
v_range_3914_ = lean_ctor_get(v_x1_3912_, 2);
v_range_3915_ = lean_ctor_get(v_x2_3913_, 2);
v___x_3916_ = l_Lean_Lsp_instOrdRange_ord(v_range_3914_, v_range_3915_);
if (v___x_3916_ == 0)
{
return v___x_3911_;
}
else
{
uint8_t v___x_3917_; 
v___x_3917_ = 0;
return v___x_3917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3918_, lean_object* v_x1_3919_, lean_object* v_x2_3920_){
_start:
{
uint8_t v___x_2063__boxed_3921_; uint8_t v_res_3922_; lean_object* v_r_3923_; 
v___x_2063__boxed_3921_ = lean_unbox(v___x_3918_);
v_res_3922_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_2063__boxed_3921_, v_x1_3919_, v_x2_3920_);
lean_dec_ref(v_x2_3920_);
lean_dec_ref(v_x1_3919_);
v_r_3923_ = lean_box(v_res_3922_);
return v_r_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_n_3924_, lean_object* v_as_3925_, lean_object* v_lo_3926_, lean_object* v_hi_3927_){
_start:
{
lean_object* v___y_3929_; uint8_t v___x_3939_; 
v___x_3939_ = lean_nat_dec_lt(v_lo_3926_, v_hi_3927_);
if (v___x_3939_ == 0)
{
lean_dec(v_lo_3926_);
return v_as_3925_;
}
else
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v_mid_3942_; lean_object* v___y_3944_; lean_object* v___y_3950_; lean_object* v___x_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v___x_3940_ = lean_nat_add(v_lo_3926_, v_hi_3927_);
v___x_3941_ = lean_unsigned_to_nat(1u);
v_mid_3942_ = lean_nat_shiftr(v___x_3940_, v___x_3941_);
lean_dec(v___x_3940_);
v___x_3955_ = lean_array_fget_borrowed(v_as_3925_, v_mid_3942_);
v___x_3956_ = lean_array_fget_borrowed(v_as_3925_, v_lo_3926_);
v___x_3957_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3939_, v___x_3955_, v___x_3956_);
if (v___x_3957_ == 0)
{
v___y_3950_ = v_as_3925_;
goto v___jp_3949_;
}
else
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_array_fswap(v_as_3925_, v_lo_3926_, v_mid_3942_);
v___y_3950_ = v___x_3958_;
goto v___jp_3949_;
}
v___jp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; uint8_t v___x_3947_; 
v___x_3945_ = lean_array_fget_borrowed(v___y_3944_, v_mid_3942_);
v___x_3946_ = lean_array_fget_borrowed(v___y_3944_, v_hi_3927_);
v___x_3947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3939_, v___x_3945_, v___x_3946_);
if (v___x_3947_ == 0)
{
lean_dec(v_mid_3942_);
v___y_3929_ = v___y_3944_;
goto v___jp_3928_;
}
else
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_array_fswap(v___y_3944_, v_mid_3942_, v_hi_3927_);
lean_dec(v_mid_3942_);
v___y_3929_ = v___x_3948_;
goto v___jp_3928_;
}
}
v___jp_3949_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3951_ = lean_array_fget_borrowed(v___y_3950_, v_hi_3927_);
v___x_3952_ = lean_array_fget_borrowed(v___y_3950_, v_lo_3926_);
v___x_3953_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3939_, v___x_3951_, v___x_3952_);
if (v___x_3953_ == 0)
{
v___y_3944_ = v___y_3950_;
goto v___jp_3943_;
}
else
{
lean_object* v___x_3954_; 
v___x_3954_ = lean_array_fswap(v___y_3950_, v_lo_3926_, v_hi_3927_);
v___y_3944_ = v___x_3954_;
goto v___jp_3943_;
}
}
}
v___jp_3928_:
{
lean_object* v_pivot_3930_; lean_object* v___x_3931_; lean_object* v_fst_3932_; lean_object* v_snd_3933_; uint8_t v___x_3934_; 
v_pivot_3930_ = lean_array_fget(v___y_3929_, v_hi_3927_);
lean_inc_n(v_lo_3926_, 2);
v___x_3931_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3927_, v_pivot_3930_, v___y_3929_, v_lo_3926_, v_lo_3926_);
lean_dec(v_pivot_3930_);
v_fst_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_fst_3932_);
v_snd_3933_ = lean_ctor_get(v___x_3931_, 1);
lean_inc(v_snd_3933_);
lean_dec_ref(v___x_3931_);
v___x_3934_ = lean_nat_dec_le(v_hi_3927_, v_fst_3932_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3924_, v_snd_3933_, v_lo_3926_, v_fst_3932_);
v___x_3936_ = lean_unsigned_to_nat(1u);
v___x_3937_ = lean_nat_add(v_fst_3932_, v___x_3936_);
lean_dec(v_fst_3932_);
v_as_3925_ = v___x_3935_;
v_lo_3926_ = v___x_3937_;
goto _start;
}
else
{
lean_dec(v_fst_3932_);
lean_dec(v_lo_3926_);
return v_snd_3933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_n_3959_, lean_object* v_as_3960_, lean_object* v_lo_3961_, lean_object* v_hi_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3959_, v_as_3960_, v_lo_3961_, v_hi_3962_);
lean_dec(v_hi_3962_);
lean_dec(v_n_3959_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object* v_x_3964_, lean_object* v_x_3965_){
_start:
{
if (lean_obj_tag(v_x_3965_) == 0)
{
return v_x_3964_;
}
else
{
lean_object* v_key_3966_; lean_object* v_snd_3967_; lean_object* v_value_3968_; lean_object* v_tail_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_4009_; 
v_key_3966_ = lean_ctor_get(v_x_3965_, 0);
lean_inc(v_key_3966_);
v_snd_3967_ = lean_ctor_get(v_key_3966_, 1);
v_value_3968_ = lean_ctor_get(v_x_3965_, 1);
v_tail_3969_ = lean_ctor_get(v_x_3965_, 2);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_x_3965_);
if (v_isSharedCheck_4009_ == 0)
{
lean_object* v_unused_4010_; 
v_unused_4010_ = lean_ctor_get(v_x_3965_, 0);
lean_dec(v_unused_4010_);
v___x_3971_ = v_x_3965_;
v_isShared_3972_ = v_isSharedCheck_4009_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_tail_3969_);
lean_inc(v_value_3968_);
lean_dec(v_x_3965_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_4009_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v_fst_3973_; lean_object* v_fst_3974_; lean_object* v_snd_3975_; lean_object* v___x_3976_; uint64_t v___x_3977_; uint64_t v___y_3979_; uint64_t v___y_4001_; 
v_fst_3973_ = lean_ctor_get(v_key_3966_, 0);
v_fst_3974_ = lean_ctor_get(v_snd_3967_, 0);
v_snd_3975_ = lean_ctor_get(v_snd_3967_, 1);
v___x_3976_ = lean_array_get_size(v_x_3964_);
v___x_3977_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_3973_);
if (lean_obj_tag(v_fst_3974_) == 0)
{
uint64_t v___x_4004_; 
v___x_4004_ = 11ULL;
v___y_3979_ = v___x_4004_;
goto v___jp_3978_;
}
else
{
lean_object* v_val_4005_; uint8_t v___x_4006_; 
v_val_4005_ = lean_ctor_get(v_fst_3974_, 0);
v___x_4006_ = lean_unbox(v_val_4005_);
if (v___x_4006_ == 0)
{
uint64_t v___x_4007_; 
v___x_4007_ = 13ULL;
v___y_4001_ = v___x_4007_;
goto v___jp_4000_;
}
else
{
uint64_t v___x_4008_; 
v___x_4008_ = 11ULL;
v___y_4001_ = v___x_4008_;
goto v___jp_4000_;
}
}
v___jp_3978_:
{
uint64_t v___x_3980_; uint64_t v___x_3981_; uint64_t v___x_3982_; uint64_t v___x_3983_; uint64_t v___x_3984_; uint64_t v_fold_3985_; uint64_t v___x_3986_; uint64_t v___x_3987_; uint64_t v___x_3988_; size_t v___x_3989_; size_t v___x_3990_; size_t v___x_3991_; size_t v___x_3992_; size_t v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
v___x_3980_ = l_Lean_Lsp_instHashableRange_hash(v_snd_3975_);
v___x_3981_ = lean_uint64_mix_hash(v___y_3979_, v___x_3980_);
v___x_3982_ = lean_uint64_mix_hash(v___x_3977_, v___x_3981_);
v___x_3983_ = 32ULL;
v___x_3984_ = lean_uint64_shift_right(v___x_3982_, v___x_3983_);
v_fold_3985_ = lean_uint64_xor(v___x_3982_, v___x_3984_);
v___x_3986_ = 16ULL;
v___x_3987_ = lean_uint64_shift_right(v_fold_3985_, v___x_3986_);
v___x_3988_ = lean_uint64_xor(v_fold_3985_, v___x_3987_);
v___x_3989_ = lean_uint64_to_usize(v___x_3988_);
v___x_3990_ = lean_usize_of_nat(v___x_3976_);
v___x_3991_ = ((size_t)1ULL);
v___x_3992_ = lean_usize_sub(v___x_3990_, v___x_3991_);
v___x_3993_ = lean_usize_land(v___x_3989_, v___x_3992_);
v___x_3994_ = lean_array_uget_borrowed(v_x_3964_, v___x_3993_);
lean_inc(v___x_3994_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 2, v___x_3994_);
v___x_3996_ = v___x_3971_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_key_3966_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_value_3968_);
lean_ctor_set(v_reuseFailAlloc_3999_, 2, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_array_uset(v_x_3964_, v___x_3993_, v___x_3996_);
v_x_3964_ = v___x_3997_;
v_x_3965_ = v_tail_3969_;
goto _start;
}
}
v___jp_4000_:
{
uint64_t v___x_4002_; uint64_t v___x_4003_; 
v___x_4002_ = 13ULL;
v___x_4003_ = lean_uint64_mix_hash(v___y_4001_, v___x_4002_);
v___y_3979_ = v___x_4003_;
goto v___jp_3978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object* v_i_4011_, lean_object* v_source_4012_, lean_object* v_target_4013_){
_start:
{
lean_object* v___x_4014_; uint8_t v___x_4015_; 
v___x_4014_ = lean_array_get_size(v_source_4012_);
v___x_4015_ = lean_nat_dec_lt(v_i_4011_, v___x_4014_);
if (v___x_4015_ == 0)
{
lean_dec_ref(v_source_4012_);
lean_dec(v_i_4011_);
return v_target_4013_;
}
else
{
lean_object* v_es_4016_; lean_object* v___x_4017_; lean_object* v_source_4018_; lean_object* v_target_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v_es_4016_ = lean_array_fget(v_source_4012_, v_i_4011_);
v___x_4017_ = lean_box(0);
v_source_4018_ = lean_array_fset(v_source_4012_, v_i_4011_, v___x_4017_);
v_target_4019_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_target_4013_, v_es_4016_);
v___x_4020_ = lean_unsigned_to_nat(1u);
v___x_4021_ = lean_nat_add(v_i_4011_, v___x_4020_);
lean_dec(v_i_4011_);
v_i_4011_ = v___x_4021_;
v_source_4012_ = v_source_4018_;
v_target_4013_ = v_target_4019_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object* v_data_4023_){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v_nbuckets_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4024_ = lean_array_get_size(v_data_4023_);
v___x_4025_ = lean_unsigned_to_nat(2u);
v_nbuckets_4026_ = lean_nat_mul(v___x_4024_, v___x_4025_);
v___x_4027_ = lean_unsigned_to_nat(0u);
v___x_4028_ = lean_box(0);
v___x_4029_ = lean_mk_array(v_nbuckets_4026_, v___x_4028_);
v___x_4030_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v___x_4027_, v_data_4023_, v___x_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object* v_x_4031_, lean_object* v_x_4032_){
_start:
{
if (lean_obj_tag(v_x_4031_) == 0)
{
if (lean_obj_tag(v_x_4032_) == 0)
{
uint8_t v___x_4033_; 
v___x_4033_ = 1;
return v___x_4033_;
}
else
{
uint8_t v___x_4034_; 
v___x_4034_ = 0;
return v___x_4034_;
}
}
else
{
if (lean_obj_tag(v_x_4032_) == 0)
{
uint8_t v___x_4035_; 
v___x_4035_ = 0;
return v___x_4035_;
}
else
{
lean_object* v_val_4036_; uint8_t v___x_4037_; 
v_val_4036_ = lean_ctor_get(v_x_4031_, 0);
v___x_4037_ = lean_unbox(v_val_4036_);
if (v___x_4037_ == 0)
{
lean_object* v_val_4038_; uint8_t v___x_4039_; 
v_val_4038_ = lean_ctor_get(v_x_4032_, 0);
v___x_4039_ = lean_unbox(v_val_4038_);
if (v___x_4039_ == 0)
{
uint8_t v___x_4040_; 
v___x_4040_ = 1;
return v___x_4040_;
}
else
{
uint8_t v___x_4041_; 
v___x_4041_ = lean_unbox(v_val_4036_);
return v___x_4041_;
}
}
else
{
lean_object* v_val_4042_; uint8_t v___x_4043_; 
v_val_4042_ = lean_ctor_get(v_x_4032_, 0);
v___x_4043_ = lean_unbox(v_val_4042_);
return v___x_4043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object* v_x_4044_, lean_object* v_x_4045_){
_start:
{
uint8_t v_res_4046_; lean_object* v_r_4047_; 
v_res_4046_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_x_4044_, v_x_4045_);
lean_dec(v_x_4045_);
lean_dec(v_x_4044_);
v_r_4047_ = lean_box(v_res_4046_);
return v_r_4047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object* v_a_4048_, lean_object* v_x_4049_){
_start:
{
if (lean_obj_tag(v_x_4049_) == 0)
{
lean_object* v___x_4050_; 
v___x_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4050_, 0, v_a_4048_);
return v___x_4050_;
}
else
{
lean_object* v_val_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4079_; 
v_val_4051_ = lean_ctor_get(v_x_4049_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_x_4049_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4053_ = v_x_4049_;
v_isShared_4054_ = v_isSharedCheck_4079_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_val_4051_);
lean_dec(v_x_4049_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4079_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v_ident_4055_; lean_object* v_aliases_4056_; lean_object* v_range_4057_; lean_object* v_stx_4058_; lean_object* v_ci_4059_; lean_object* v_info_4060_; uint8_t v_isBinder_4061_; lean_object* v_aliases_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4073_; 
v_ident_4055_ = lean_ctor_get(v_val_4051_, 0);
lean_inc_ref(v_ident_4055_);
v_aliases_4056_ = lean_ctor_get(v_val_4051_, 1);
lean_inc_ref(v_aliases_4056_);
v_range_4057_ = lean_ctor_get(v_val_4051_, 2);
lean_inc_ref(v_range_4057_);
v_stx_4058_ = lean_ctor_get(v_val_4051_, 3);
lean_inc(v_stx_4058_);
v_ci_4059_ = lean_ctor_get(v_val_4051_, 4);
lean_inc_ref(v_ci_4059_);
v_info_4060_ = lean_ctor_get(v_val_4051_, 5);
lean_inc_ref(v_info_4060_);
v_isBinder_4061_ = lean_ctor_get_uint8(v_val_4051_, sizeof(void*)*6);
lean_dec(v_val_4051_);
v_aliases_4062_ = lean_ctor_get(v_a_4048_, 1);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_a_4048_);
if (v_isSharedCheck_4073_ == 0)
{
lean_object* v_unused_4074_; lean_object* v_unused_4075_; lean_object* v_unused_4076_; lean_object* v_unused_4077_; lean_object* v_unused_4078_; 
v_unused_4074_ = lean_ctor_get(v_a_4048_, 5);
lean_dec(v_unused_4074_);
v_unused_4075_ = lean_ctor_get(v_a_4048_, 4);
lean_dec(v_unused_4075_);
v_unused_4076_ = lean_ctor_get(v_a_4048_, 3);
lean_dec(v_unused_4076_);
v_unused_4077_ = lean_ctor_get(v_a_4048_, 2);
lean_dec(v_unused_4077_);
v_unused_4078_ = lean_ctor_get(v_a_4048_, 0);
lean_dec(v_unused_4078_);
v___x_4064_ = v_a_4048_;
v_isShared_4065_ = v_isSharedCheck_4073_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_aliases_4062_);
lean_dec(v_a_4048_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4073_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4066_; lean_object* v___x_4068_; 
v___x_4066_ = l_Array_append___redArg(v_aliases_4056_, v_aliases_4062_);
lean_dec_ref(v_aliases_4062_);
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 5, v_info_4060_);
lean_ctor_set(v___x_4064_, 4, v_ci_4059_);
lean_ctor_set(v___x_4064_, 3, v_stx_4058_);
lean_ctor_set(v___x_4064_, 2, v_range_4057_);
lean_ctor_set(v___x_4064_, 1, v___x_4066_);
lean_ctor_set(v___x_4064_, 0, v_ident_4055_);
v___x_4068_ = v___x_4064_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_ident_4055_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4072_, 2, v_range_4057_);
lean_ctor_set(v_reuseFailAlloc_4072_, 3, v_stx_4058_);
lean_ctor_set(v_reuseFailAlloc_4072_, 4, v_ci_4059_);
lean_ctor_set(v_reuseFailAlloc_4072_, 5, v_info_4060_);
v___x_4068_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4070_; 
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*6, v_isBinder_4061_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4068_);
v___x_4070_ = v___x_4053_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_x_4082_){
_start:
{
if (lean_obj_tag(v_x_4082_) == 0)
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v_val_4085_; lean_object* v___x_4086_; 
v___x_4083_ = lean_box(0);
v___x_4084_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4080_, v___x_4083_);
v_val_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_val_4085_);
lean_dec(v___x_4084_);
v___x_4086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4086_, 0, v_a_4081_);
lean_ctor_set(v___x_4086_, 1, v_val_4085_);
lean_ctor_set(v___x_4086_, 2, v_x_4082_);
return v___x_4086_;
}
else
{
lean_object* v_key_4087_; lean_object* v_value_4088_; lean_object* v_tail_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4116_; 
v_key_4087_ = lean_ctor_get(v_x_4082_, 0);
v_value_4088_ = lean_ctor_get(v_x_4082_, 1);
v_tail_4089_ = lean_ctor_get(v_x_4082_, 2);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_x_4082_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4091_ = v_x_4082_;
v_isShared_4092_ = v_isSharedCheck_4116_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_tail_4089_);
lean_inc(v_value_4088_);
lean_inc(v_key_4087_);
lean_dec(v_x_4082_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4116_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
uint8_t v___y_4094_; lean_object* v_fst_4105_; lean_object* v_snd_4106_; lean_object* v_fst_4107_; lean_object* v_snd_4108_; uint8_t v___x_4109_; 
v_fst_4105_ = lean_ctor_get(v_key_4087_, 0);
v_snd_4106_ = lean_ctor_get(v_key_4087_, 1);
v_fst_4107_ = lean_ctor_get(v_a_4081_, 0);
v_snd_4108_ = lean_ctor_get(v_a_4081_, 1);
v___x_4109_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4105_, v_fst_4107_);
if (v___x_4109_ == 0)
{
v___y_4094_ = v___x_4109_;
goto v___jp_4093_;
}
else
{
lean_object* v_fst_4110_; lean_object* v_snd_4111_; lean_object* v_fst_4112_; lean_object* v_snd_4113_; uint8_t v___x_4114_; 
v_fst_4110_ = lean_ctor_get(v_snd_4106_, 0);
v_snd_4111_ = lean_ctor_get(v_snd_4106_, 1);
v_fst_4112_ = lean_ctor_get(v_snd_4108_, 0);
v_snd_4113_ = lean_ctor_get(v_snd_4108_, 1);
v___x_4114_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4110_, v_fst_4112_);
if (v___x_4114_ == 0)
{
v___y_4094_ = v___x_4114_;
goto v___jp_4093_;
}
else
{
uint8_t v___x_4115_; 
v___x_4115_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4111_, v_snd_4113_);
v___y_4094_ = v___x_4115_;
goto v___jp_4093_;
}
}
v___jp_4093_:
{
if (v___y_4094_ == 0)
{
lean_object* v_tail_4095_; lean_object* v___x_4097_; 
v_tail_4095_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4080_, v_a_4081_, v_tail_4089_);
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 2, v_tail_4095_);
v___x_4097_ = v___x_4091_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_key_4087_);
lean_ctor_set(v_reuseFailAlloc_4098_, 1, v_value_4088_);
lean_ctor_set(v_reuseFailAlloc_4098_, 2, v_tail_4095_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
else
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v_val_4101_; lean_object* v___x_4103_; 
lean_dec(v_key_4087_);
v___x_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_value_4088_);
v___x_4100_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4080_, v___x_4099_);
v_val_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_val_4101_);
lean_dec(v___x_4100_);
if (v_isShared_4092_ == 0)
{
lean_ctor_set(v___x_4091_, 1, v_val_4101_);
lean_ctor_set(v___x_4091_, 0, v_a_4081_);
v___x_4103_ = v___x_4091_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4081_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v_val_4101_);
lean_ctor_set(v_reuseFailAlloc_4104_, 2, v_tail_4089_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_a_4117_, lean_object* v_x_4118_){
_start:
{
if (lean_obj_tag(v_x_4118_) == 0)
{
uint8_t v___x_4119_; 
v___x_4119_ = 0;
return v___x_4119_;
}
else
{
lean_object* v_key_4120_; lean_object* v_tail_4121_; uint8_t v___y_4123_; lean_object* v_fst_4125_; lean_object* v_snd_4126_; lean_object* v_fst_4127_; lean_object* v_snd_4128_; uint8_t v___x_4129_; 
v_key_4120_ = lean_ctor_get(v_x_4118_, 0);
v_tail_4121_ = lean_ctor_get(v_x_4118_, 2);
v_fst_4125_ = lean_ctor_get(v_key_4120_, 0);
v_snd_4126_ = lean_ctor_get(v_key_4120_, 1);
v_fst_4127_ = lean_ctor_get(v_a_4117_, 0);
v_snd_4128_ = lean_ctor_get(v_a_4117_, 1);
v___x_4129_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4125_, v_fst_4127_);
if (v___x_4129_ == 0)
{
v___y_4123_ = v___x_4129_;
goto v___jp_4122_;
}
else
{
lean_object* v_fst_4130_; lean_object* v_snd_4131_; lean_object* v_fst_4132_; lean_object* v_snd_4133_; uint8_t v___x_4134_; 
v_fst_4130_ = lean_ctor_get(v_snd_4126_, 0);
v_snd_4131_ = lean_ctor_get(v_snd_4126_, 1);
v_fst_4132_ = lean_ctor_get(v_snd_4128_, 0);
v_snd_4133_ = lean_ctor_get(v_snd_4128_, 1);
v___x_4134_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4130_, v_fst_4132_);
if (v___x_4134_ == 0)
{
v___y_4123_ = v___x_4134_;
goto v___jp_4122_;
}
else
{
uint8_t v___x_4135_; 
v___x_4135_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4131_, v_snd_4133_);
v___y_4123_ = v___x_4135_;
goto v___jp_4122_;
}
}
v___jp_4122_:
{
if (v___y_4123_ == 0)
{
v_x_4118_ = v_tail_4121_;
goto _start;
}
else
{
return v___y_4123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object* v_a_4136_, lean_object* v_x_4137_){
_start:
{
uint8_t v_res_4138_; lean_object* v_r_4139_; 
v_res_4138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4136_, v_x_4137_);
lean_dec(v_x_4137_);
lean_dec_ref(v_a_4136_);
v_r_4139_ = lean_box(v_res_4138_);
return v_r_4139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4140_, lean_object* v_m_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v___y_4144_; size_t v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v_snd_4150_; lean_object* v_size_4151_; lean_object* v_buckets_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4211_; 
v_snd_4150_ = lean_ctor_get(v_a_4142_, 1);
v_size_4151_ = lean_ctor_get(v_m_4141_, 0);
v_buckets_4152_ = lean_ctor_get(v_m_4141_, 1);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_m_4141_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4154_ = v_m_4141_;
v_isShared_4155_ = v_isSharedCheck_4211_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_buckets_4152_);
lean_inc(v_size_4151_);
lean_dec(v_m_4141_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4211_;
goto v_resetjp_4153_;
}
v___jp_4143_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_array_uset(v___y_4146_, v___y_4145_, v___y_4144_);
v___x_4149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___y_4147_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
return v___x_4149_;
}
v_resetjp_4153_:
{
lean_object* v_fst_4156_; lean_object* v_fst_4157_; lean_object* v_snd_4158_; lean_object* v___x_4159_; uint64_t v___x_4160_; uint64_t v___y_4162_; uint64_t v___y_4203_; 
v_fst_4156_ = lean_ctor_get(v_a_4142_, 0);
v_fst_4157_ = lean_ctor_get(v_snd_4150_, 0);
v_snd_4158_ = lean_ctor_get(v_snd_4150_, 1);
v___x_4159_ = lean_array_get_size(v_buckets_4152_);
v___x_4160_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4156_);
if (lean_obj_tag(v_fst_4157_) == 0)
{
uint64_t v___x_4206_; 
v___x_4206_ = 11ULL;
v___y_4162_ = v___x_4206_;
goto v___jp_4161_;
}
else
{
lean_object* v_val_4207_; uint8_t v___x_4208_; 
v_val_4207_ = lean_ctor_get(v_fst_4157_, 0);
v___x_4208_ = lean_unbox(v_val_4207_);
if (v___x_4208_ == 0)
{
uint64_t v___x_4209_; 
v___x_4209_ = 13ULL;
v___y_4203_ = v___x_4209_;
goto v___jp_4202_;
}
else
{
uint64_t v___x_4210_; 
v___x_4210_ = 11ULL;
v___y_4203_ = v___x_4210_;
goto v___jp_4202_;
}
}
v___jp_4161_:
{
uint64_t v___x_4163_; uint64_t v___x_4164_; uint64_t v___x_4165_; uint64_t v___x_4166_; uint64_t v___x_4167_; uint64_t v_fold_4168_; uint64_t v___x_4169_; uint64_t v___x_4170_; uint64_t v___x_4171_; size_t v___x_4172_; size_t v___x_4173_; size_t v___x_4174_; size_t v___x_4175_; size_t v___x_4176_; lean_object* v_bkt_4177_; uint8_t v___x_4178_; 
v___x_4163_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4158_);
v___x_4164_ = lean_uint64_mix_hash(v___y_4162_, v___x_4163_);
v___x_4165_ = lean_uint64_mix_hash(v___x_4160_, v___x_4164_);
v___x_4166_ = 32ULL;
v___x_4167_ = lean_uint64_shift_right(v___x_4165_, v___x_4166_);
v_fold_4168_ = lean_uint64_xor(v___x_4165_, v___x_4167_);
v___x_4169_ = 16ULL;
v___x_4170_ = lean_uint64_shift_right(v_fold_4168_, v___x_4169_);
v___x_4171_ = lean_uint64_xor(v_fold_4168_, v___x_4170_);
v___x_4172_ = lean_uint64_to_usize(v___x_4171_);
v___x_4173_ = lean_usize_of_nat(v___x_4159_);
v___x_4174_ = ((size_t)1ULL);
v___x_4175_ = lean_usize_sub(v___x_4173_, v___x_4174_);
v___x_4176_ = lean_usize_land(v___x_4172_, v___x_4175_);
v_bkt_4177_ = lean_array_uget_borrowed(v_buckets_4152_, v___x_4176_);
v___x_4178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4142_, v_bkt_4177_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; lean_object* v_size_x27_4180_; lean_object* v___x_4181_; lean_object* v_buckets_x27_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; 
v___x_4179_ = lean_unsigned_to_nat(1u);
v_size_x27_4180_ = lean_nat_add(v_size_4151_, v___x_4179_);
lean_dec(v_size_4151_);
lean_inc(v_bkt_4177_);
v___x_4181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4181_, 0, v_a_4142_);
lean_ctor_set(v___x_4181_, 1, v_a_4140_);
lean_ctor_set(v___x_4181_, 2, v_bkt_4177_);
v_buckets_x27_4182_ = lean_array_uset(v_buckets_4152_, v___x_4176_, v___x_4181_);
v___x_4183_ = lean_unsigned_to_nat(4u);
v___x_4184_ = lean_nat_mul(v_size_x27_4180_, v___x_4183_);
v___x_4185_ = lean_unsigned_to_nat(3u);
v___x_4186_ = lean_nat_div(v___x_4184_, v___x_4185_);
lean_dec(v___x_4184_);
v___x_4187_ = lean_array_get_size(v_buckets_x27_4182_);
v___x_4188_ = lean_nat_dec_le(v___x_4186_, v___x_4187_);
lean_dec(v___x_4186_);
if (v___x_4188_ == 0)
{
lean_object* v_val_4189_; lean_object* v___x_4191_; 
v_val_4189_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_buckets_x27_4182_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 1, v_val_4189_);
lean_ctor_set(v___x_4154_, 0, v_size_x27_4180_);
v___x_4191_ = v___x_4154_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_size_x27_4180_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_val_4189_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
else
{
lean_object* v___x_4194_; 
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 1, v_buckets_x27_4182_);
lean_ctor_set(v___x_4154_, 0, v_size_x27_4180_);
v___x_4194_ = v___x_4154_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_size_x27_4180_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v_buckets_x27_4182_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
else
{
lean_object* v___x_4196_; lean_object* v_buckets_x27_4197_; lean_object* v_bkt_x27_4198_; uint8_t v___x_4199_; 
lean_inc(v_bkt_4177_);
lean_del_object(v___x_4154_);
v___x_4196_ = lean_box(0);
v_buckets_x27_4197_ = lean_array_uset(v_buckets_4152_, v___x_4176_, v___x_4196_);
lean_inc_ref(v_a_4142_);
v_bkt_x27_4198_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4140_, v_a_4142_, v_bkt_4177_);
v___x_4199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4142_, v_bkt_x27_4198_);
lean_dec_ref(v_a_4142_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_unsigned_to_nat(1u);
v___x_4201_ = lean_nat_sub(v_size_4151_, v___x_4200_);
lean_dec(v_size_4151_);
v___y_4144_ = v_bkt_x27_4198_;
v___y_4145_ = v___x_4176_;
v___y_4146_ = v_buckets_x27_4197_;
v___y_4147_ = v___x_4201_;
goto v___jp_4143_;
}
else
{
v___y_4144_ = v_bkt_x27_4198_;
v___y_4145_ = v___x_4176_;
v___y_4146_ = v_buckets_x27_4197_;
v___y_4147_ = v_size_4151_;
goto v___jp_4143_;
}
}
}
v___jp_4202_:
{
uint64_t v___x_4204_; uint64_t v___x_4205_; 
v___x_4204_ = 13ULL;
v___x_4205_ = lean_uint64_mix_hash(v___y_4203_, v___x_4204_);
v___y_4162_ = v___x_4205_;
goto v___jp_4161_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4212_, lean_object* v_as_4213_, size_t v_sz_4214_, size_t v_i_4215_, lean_object* v_b_4216_){
_start:
{
uint8_t v___x_4217_; 
v___x_4217_ = lean_usize_dec_lt(v_i_4215_, v_sz_4214_);
if (v___x_4217_ == 0)
{
return v_b_4216_;
}
else
{
lean_object* v_a_4218_; lean_object* v___y_4220_; 
v_a_4218_ = lean_array_uget_borrowed(v_as_4213_, v_i_4215_);
if (v_allowSimultaneousBinderUse_4212_ == 0)
{
lean_object* v___x_4229_; 
v___x_4229_ = lean_box(0);
v___y_4220_ = v___x_4229_;
goto v___jp_4219_;
}
else
{
uint8_t v_isBinder_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v_isBinder_4230_ = lean_ctor_get_uint8(v_a_4218_, sizeof(void*)*6);
v___x_4231_ = lean_box(v_isBinder_4230_);
v___x_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
v___y_4220_ = v___x_4232_;
goto v___jp_4219_;
}
v___jp_4219_:
{
lean_object* v_ident_4221_; lean_object* v_range_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; size_t v___x_4226_; size_t v___x_4227_; 
v_ident_4221_ = lean_ctor_get(v_a_4218_, 0);
v_range_4222_ = lean_ctor_get(v_a_4218_, 2);
lean_inc_ref(v_range_4222_);
v___x_4223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4223_, 0, v___y_4220_);
lean_ctor_set(v___x_4223_, 1, v_range_4222_);
lean_inc_ref(v_ident_4221_);
v___x_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4224_, 0, v_ident_4221_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
lean_inc(v_a_4218_);
v___x_4225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4218_, v_b_4216_, v___x_4224_);
v___x_4226_ = ((size_t)1ULL);
v___x_4227_ = lean_usize_add(v_i_4215_, v___x_4226_);
v_i_4215_ = v___x_4227_;
v_b_4216_ = v___x_4225_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4233_, lean_object* v_as_4234_, lean_object* v_sz_4235_, lean_object* v_i_4236_, lean_object* v_b_4237_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4238_; size_t v_sz_boxed_4239_; size_t v_i_boxed_4240_; lean_object* v_res_4241_; 
v_allowSimultaneousBinderUse_boxed_4238_ = lean_unbox(v_allowSimultaneousBinderUse_4233_);
v_sz_boxed_4239_ = lean_unbox_usize(v_sz_4235_);
lean_dec(v_sz_4235_);
v_i_boxed_4240_ = lean_unbox_usize(v_i_4236_);
lean_dec(v_i_4236_);
v_res_4241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4238_, v_as_4234_, v_sz_boxed_4239_, v_i_boxed_4240_, v_b_4237_);
lean_dec_ref(v_as_4234_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4242_, lean_object* v_x_4243_){
_start:
{
if (lean_obj_tag(v_x_4243_) == 0)
{
return v_x_4242_;
}
else
{
lean_object* v_value_4244_; lean_object* v_tail_4245_; lean_object* v___x_4246_; 
v_value_4244_ = lean_ctor_get(v_x_4243_, 1);
lean_inc(v_value_4244_);
v_tail_4245_ = lean_ctor_get(v_x_4243_, 2);
lean_inc(v_tail_4245_);
lean_dec_ref(v_x_4243_);
v___x_4246_ = lean_array_push(v_x_4242_, v_value_4244_);
v_x_4242_ = v___x_4246_;
v_x_4243_ = v_tail_4245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4248_, size_t v_i_4249_, size_t v_stop_4250_, lean_object* v_b_4251_){
_start:
{
uint8_t v___x_4252_; 
v___x_4252_ = lean_usize_dec_eq(v_i_4249_, v_stop_4250_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4254_; size_t v___x_4255_; size_t v___x_4256_; 
v___x_4253_ = lean_array_uget_borrowed(v_as_4248_, v_i_4249_);
lean_inc(v___x_4253_);
v___x_4254_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4251_, v___x_4253_);
v___x_4255_ = ((size_t)1ULL);
v___x_4256_ = lean_usize_add(v_i_4249_, v___x_4255_);
v_i_4249_ = v___x_4256_;
v_b_4251_ = v___x_4254_;
goto _start;
}
else
{
return v_b_4251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4258_, lean_object* v_i_4259_, lean_object* v_stop_4260_, lean_object* v_b_4261_){
_start:
{
size_t v_i_boxed_4262_; size_t v_stop_boxed_4263_; lean_object* v_res_4264_; 
v_i_boxed_4262_ = lean_unbox_usize(v_i_4259_);
lean_dec(v_i_4259_);
v_stop_boxed_4263_ = lean_unbox_usize(v_stop_4260_);
lean_dec(v_stop_4260_);
v_res_4264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4258_, v_i_boxed_4262_, v_stop_boxed_4263_, v_b_4261_);
lean_dec_ref(v_as_4258_);
return v_res_4264_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4265_ = lean_box(0);
v___x_4266_ = lean_unsigned_to_nat(16u);
v___x_4267_ = lean_mk_array(v___x_4266_, v___x_4265_);
return v___x_4267_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v_refsByIdAndRange_4270_; 
v___x_4268_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4269_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4270_, 0, v___x_4269_);
lean_ctor_set(v_refsByIdAndRange_4270_, 1, v___x_4268_);
return v_refsByIdAndRange_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4271_, uint8_t v_allowSimultaneousBinderUse_4272_){
_start:
{
lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4282_; lean_object* v___x_4289_; lean_object* v_refsByIdAndRange_4290_; size_t v_sz_4291_; size_t v___x_4292_; lean_object* v___x_4293_; lean_object* v_buckets_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; uint8_t v___x_4297_; 
v___x_4289_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4290_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4291_ = lean_array_size(v_refs_4271_);
v___x_4292_ = ((size_t)0ULL);
v___x_4293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4272_, v_refs_4271_, v_sz_4291_, v___x_4292_, v_refsByIdAndRange_4290_);
v_buckets_4294_ = lean_ctor_get(v___x_4293_, 1);
lean_inc_ref(v_buckets_4294_);
lean_dec_ref(v___x_4293_);
v___x_4295_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4296_ = lean_array_get_size(v_buckets_4294_);
v___x_4297_ = lean_nat_dec_lt(v___x_4289_, v___x_4296_);
if (v___x_4297_ == 0)
{
lean_dec_ref(v_buckets_4294_);
v___y_4282_ = v___x_4295_;
goto v___jp_4281_;
}
else
{
uint8_t v___x_4298_; 
v___x_4298_ = lean_nat_dec_le(v___x_4296_, v___x_4296_);
if (v___x_4298_ == 0)
{
if (v___x_4297_ == 0)
{
lean_dec_ref(v_buckets_4294_);
v___y_4282_ = v___x_4295_;
goto v___jp_4281_;
}
else
{
size_t v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = lean_usize_of_nat(v___x_4296_);
v___x_4300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4294_, v___x_4292_, v___x_4299_, v___x_4295_);
lean_dec_ref(v_buckets_4294_);
v___y_4282_ = v___x_4300_;
goto v___jp_4281_;
}
}
else
{
size_t v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = lean_usize_of_nat(v___x_4296_);
v___x_4302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4294_, v___x_4292_, v___x_4301_, v___x_4295_);
lean_dec_ref(v_buckets_4294_);
v___y_4282_ = v___x_4302_;
goto v___jp_4281_;
}
}
v___jp_4273_:
{
uint8_t v___x_4278_; 
v___x_4278_ = lean_nat_dec_le(v___y_4277_, v___y_4276_);
if (v___x_4278_ == 0)
{
lean_object* v___x_4279_; 
lean_dec(v___y_4276_);
lean_inc(v___y_4277_);
v___x_4279_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4275_, v___y_4274_, v___y_4277_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec(v___y_4275_);
return v___x_4279_;
}
else
{
lean_object* v___x_4280_; 
v___x_4280_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4275_, v___y_4274_, v___y_4277_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec(v___y_4275_);
return v___x_4280_;
}
}
v___jp_4281_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; 
v___x_4283_ = lean_array_get_size(v___y_4282_);
v___x_4284_ = lean_unsigned_to_nat(0u);
v___x_4285_ = lean_nat_dec_eq(v___x_4283_, v___x_4284_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; 
v___x_4286_ = lean_unsigned_to_nat(1u);
v___x_4287_ = lean_nat_sub(v___x_4283_, v___x_4286_);
v___x_4288_ = lean_nat_dec_le(v___x_4284_, v___x_4287_);
if (v___x_4288_ == 0)
{
lean_inc(v___x_4287_);
v___y_4274_ = v___y_4282_;
v___y_4275_ = v___x_4283_;
v___y_4276_ = v___x_4287_;
v___y_4277_ = v___x_4287_;
goto v___jp_4273_;
}
else
{
v___y_4274_ = v___y_4282_;
v___y_4275_ = v___x_4283_;
v___y_4276_ = v___x_4287_;
v___y_4277_ = v___x_4284_;
goto v___jp_4273_;
}
}
else
{
return v___y_4282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object* v_refs_4303_, lean_object* v_allowSimultaneousBinderUse_4304_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4305_; lean_object* v_res_4306_; 
v_allowSimultaneousBinderUse_boxed_4305_ = lean_unbox(v_allowSimultaneousBinderUse_4304_);
v_res_4306_ = l_Lean_Server_dedupReferences(v_refs_4303_, v_allowSimultaneousBinderUse_boxed_4305_);
lean_dec_ref(v_refs_4303_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object* v_n_4307_, lean_object* v_as_4308_, lean_object* v_lo_4309_, lean_object* v_hi_4310_, lean_object* v_w_4311_, lean_object* v_hlo_4312_, lean_object* v_hhi_4313_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4307_, v_as_4308_, v_lo_4309_, v_hi_4310_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object* v_n_4315_, lean_object* v_as_4316_, lean_object* v_lo_4317_, lean_object* v_hi_4318_, lean_object* v_w_4319_, lean_object* v_hlo_4320_, lean_object* v_hhi_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(v_n_4315_, v_as_4316_, v_lo_4317_, v_hi_4318_, v_w_4319_, v_hlo_4320_, v_hhi_4321_);
lean_dec(v_hi_4318_);
lean_dec(v_n_4315_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(lean_object* v_n_4323_, lean_object* v_lo_4324_, lean_object* v_hi_4325_, lean_object* v_hhi_4326_, lean_object* v_pivot_4327_, lean_object* v_as_4328_, lean_object* v_i_4329_, lean_object* v_k_4330_, lean_object* v_ilo_4331_, lean_object* v_ik_4332_, lean_object* v_w_4333_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_4325_, v_pivot_4327_, v_as_4328_, v_i_4329_, v_k_4330_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___boxed(lean_object* v_n_4335_, lean_object* v_lo_4336_, lean_object* v_hi_4337_, lean_object* v_hhi_4338_, lean_object* v_pivot_4339_, lean_object* v_as_4340_, lean_object* v_i_4341_, lean_object* v_k_4342_, lean_object* v_ilo_4343_, lean_object* v_ik_4344_, lean_object* v_w_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(v_n_4335_, v_lo_4336_, v_hi_4337_, v_hhi_4338_, v_pivot_4339_, v_as_4340_, v_i_4341_, v_k_4342_, v_ilo_4343_, v_ik_4344_, v_w_4345_);
lean_dec_ref(v_pivot_4339_);
lean_dec(v_hi_4337_);
lean_dec(v_lo_4336_);
lean_dec(v_n_4335_);
return v_res_4346_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object* v_00_u03b2_4347_, lean_object* v_a_4348_, lean_object* v_x_4349_){
_start:
{
uint8_t v___x_4350_; 
v___x_4350_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4348_, v_x_4349_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4351_, lean_object* v_a_4352_, lean_object* v_x_4353_){
_start:
{
uint8_t v_res_4354_; lean_object* v_r_4355_; 
v_res_4354_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(v_00_u03b2_4351_, v_a_4352_, v_x_4353_);
lean_dec(v_x_4353_);
lean_dec_ref(v_a_4352_);
v_r_4355_ = lean_box(v_res_4354_);
return v_r_4355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object* v_00_u03b2_4356_, lean_object* v_data_4357_){
_start:
{
lean_object* v___x_4358_; 
v___x_4358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_data_4357_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4359_, lean_object* v_i_4360_, lean_object* v_source_4361_, lean_object* v_target_4362_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v_i_4360_, v_source_4361_, v_target_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4364_, lean_object* v_x_4365_, lean_object* v_x_4366_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_x_4365_, v_x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object* v_as_4368_, size_t v_i_4369_, size_t v_stop_4370_, lean_object* v_b_4371_){
_start:
{
uint8_t v___x_4372_; 
v___x_4372_ = lean_usize_dec_eq(v_i_4369_, v_stop_4370_);
if (v___x_4372_ == 0)
{
lean_object* v___x_4373_; lean_object* v___x_4374_; size_t v___x_4375_; size_t v___x_4376_; 
v___x_4373_ = lean_array_uget_borrowed(v_as_4368_, v_i_4369_);
lean_inc(v___x_4373_);
v___x_4374_ = l_Lean_Server_ModuleRefs_addRef(v_b_4371_, v___x_4373_);
v___x_4375_ = ((size_t)1ULL);
v___x_4376_ = lean_usize_add(v_i_4369_, v___x_4375_);
v_i_4369_ = v___x_4376_;
v_b_4371_ = v___x_4374_;
goto _start;
}
else
{
return v_b_4371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object* v_as_4378_, lean_object* v_i_4379_, lean_object* v_stop_4380_, lean_object* v_b_4381_){
_start:
{
size_t v_i_boxed_4382_; size_t v_stop_boxed_4383_; lean_object* v_res_4384_; 
v_i_boxed_4382_ = lean_unbox_usize(v_i_4379_);
lean_dec(v_i_4379_);
v_stop_boxed_4383_ = lean_unbox_usize(v_stop_4380_);
lean_dec(v_stop_4380_);
v_res_4384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_as_4378_, v_i_boxed_4382_, v_stop_boxed_4383_, v_b_4381_);
lean_dec_ref(v_as_4378_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object* v_as_4385_, size_t v_i_4386_, size_t v_stop_4387_, lean_object* v_b_4388_){
_start:
{
lean_object* v___y_4390_; uint8_t v___x_4394_; 
v___x_4394_ = lean_usize_dec_eq(v_i_4386_, v_stop_4387_);
if (v___x_4394_ == 0)
{
lean_object* v___x_4395_; lean_object* v_ident_4396_; 
v___x_4395_ = lean_array_uget_borrowed(v_as_4385_, v_i_4386_);
v_ident_4396_ = lean_ctor_get(v___x_4395_, 0);
if (lean_obj_tag(v_ident_4396_) == 1)
{
v___y_4390_ = v_b_4388_;
goto v___jp_4389_;
}
else
{
lean_object* v___x_4397_; 
lean_inc(v___x_4395_);
v___x_4397_ = lean_array_push(v_b_4388_, v___x_4395_);
v___y_4390_ = v___x_4397_;
goto v___jp_4389_;
}
}
else
{
return v_b_4388_;
}
v___jp_4389_:
{
size_t v___x_4391_; size_t v___x_4392_; 
v___x_4391_ = ((size_t)1ULL);
v___x_4392_ = lean_usize_add(v_i_4386_, v___x_4391_);
v_i_4386_ = v___x_4392_;
v_b_4388_ = v___y_4390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object* v_as_4398_, lean_object* v_i_4399_, lean_object* v_stop_4400_, lean_object* v_b_4401_){
_start:
{
size_t v_i_boxed_4402_; size_t v_stop_boxed_4403_; lean_object* v_res_4404_; 
v_i_boxed_4402_ = lean_unbox_usize(v_i_4399_);
lean_dec(v_i_4399_);
v_stop_boxed_4403_ = lean_unbox_usize(v_stop_4400_);
lean_dec(v_stop_4400_);
v_res_4404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_as_4398_, v_i_boxed_4402_, v_stop_boxed_4403_, v_b_4401_);
lean_dec_ref(v_as_4398_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object* v_text_4405_, lean_object* v_trees_4406_, uint8_t v_localVars_4407_, uint8_t v_allowSimultaneousBinderUse_4408_){
_start:
{
lean_object* v_refs_4410_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v_refs_4424_; 
v___x_4422_ = l_Lean_Server_findReferences(v_text_4405_, v_trees_4406_);
v___x_4423_ = l_Lean_Server_combineIdents(v_trees_4406_, v___x_4422_);
lean_dec_ref(v___x_4422_);
v_refs_4424_ = l_Lean_Server_dedupReferences(v___x_4423_, v_allowSimultaneousBinderUse_4408_);
lean_dec_ref(v___x_4423_);
if (v_localVars_4407_ == 0)
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; 
v___x_4425_ = lean_unsigned_to_nat(0u);
v___x_4426_ = lean_array_get_size(v_refs_4424_);
v___x_4427_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4428_ = lean_nat_dec_lt(v___x_4425_, v___x_4426_);
if (v___x_4428_ == 0)
{
lean_dec_ref(v_refs_4424_);
v_refs_4410_ = v___x_4427_;
goto v___jp_4409_;
}
else
{
uint8_t v___x_4429_; 
v___x_4429_ = lean_nat_dec_le(v___x_4426_, v___x_4426_);
if (v___x_4429_ == 0)
{
if (v___x_4428_ == 0)
{
lean_dec_ref(v_refs_4424_);
v_refs_4410_ = v___x_4427_;
goto v___jp_4409_;
}
else
{
size_t v___x_4430_; size_t v___x_4431_; lean_object* v___x_4432_; 
v___x_4430_ = ((size_t)0ULL);
v___x_4431_ = lean_usize_of_nat(v___x_4426_);
v___x_4432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4424_, v___x_4430_, v___x_4431_, v___x_4427_);
lean_dec_ref(v_refs_4424_);
v_refs_4410_ = v___x_4432_;
goto v___jp_4409_;
}
}
else
{
size_t v___x_4433_; size_t v___x_4434_; lean_object* v___x_4435_; 
v___x_4433_ = ((size_t)0ULL);
v___x_4434_ = lean_usize_of_nat(v___x_4426_);
v___x_4435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4424_, v___x_4433_, v___x_4434_, v___x_4427_);
lean_dec_ref(v_refs_4424_);
v_refs_4410_ = v___x_4435_;
goto v___jp_4409_;
}
}
}
else
{
v_refs_4410_ = v_refs_4424_;
goto v___jp_4409_;
}
v___jp_4409_:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; uint8_t v___x_4414_; 
v___x_4411_ = lean_box(1);
v___x_4412_ = lean_unsigned_to_nat(0u);
v___x_4413_ = lean_array_get_size(v_refs_4410_);
v___x_4414_ = lean_nat_dec_lt(v___x_4412_, v___x_4413_);
if (v___x_4414_ == 0)
{
lean_dec_ref(v_refs_4410_);
return v___x_4411_;
}
else
{
uint8_t v___x_4415_; 
v___x_4415_ = lean_nat_dec_le(v___x_4413_, v___x_4413_);
if (v___x_4415_ == 0)
{
if (v___x_4414_ == 0)
{
lean_dec_ref(v_refs_4410_);
return v___x_4411_;
}
else
{
size_t v___x_4416_; size_t v___x_4417_; lean_object* v___x_4418_; 
v___x_4416_ = ((size_t)0ULL);
v___x_4417_ = lean_usize_of_nat(v___x_4413_);
v___x_4418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4410_, v___x_4416_, v___x_4417_, v___x_4411_);
lean_dec_ref(v_refs_4410_);
return v___x_4418_;
}
}
else
{
size_t v___x_4419_; size_t v___x_4420_; lean_object* v___x_4421_; 
v___x_4419_ = ((size_t)0ULL);
v___x_4420_ = lean_usize_of_nat(v___x_4413_);
v___x_4421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4410_, v___x_4419_, v___x_4420_, v___x_4411_);
lean_dec_ref(v_refs_4410_);
return v___x_4421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object* v_text_4436_, lean_object* v_trees_4437_, lean_object* v_localVars_4438_, lean_object* v_allowSimultaneousBinderUse_4439_){
_start:
{
uint8_t v_localVars_boxed_4440_; uint8_t v_allowSimultaneousBinderUse_boxed_4441_; lean_object* v_res_4442_; 
v_localVars_boxed_4440_ = lean_unbox(v_localVars_4438_);
v_allowSimultaneousBinderUse_boxed_4441_ = lean_unbox(v_allowSimultaneousBinderUse_4439_);
v_res_4442_ = l_Lean_Server_findModuleRefs(v_text_4436_, v_trees_4437_, v_localVars_boxed_4440_, v_allowSimultaneousBinderUse_boxed_4441_);
lean_dec_ref(v_trees_4437_);
return v_res_4442_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t v_a_4450_, uint8_t v_a_4451_){
_start:
{
switch(v_a_4450_)
{
case 0:
{
if (v_a_4451_ == 1)
{
uint8_t v___x_4452_; 
v___x_4452_ = 2;
return v___x_4452_;
}
else
{
return v_a_4451_;
}
}
case 1:
{
if (v_a_4451_ == 0)
{
uint8_t v___x_4453_; 
v___x_4453_ = 2;
return v___x_4453_;
}
else
{
return v_a_4451_;
}
}
default: 
{
return v_a_4450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
uint8_t v_a_46__boxed_4456_; uint8_t v_a_47__boxed_4457_; uint8_t v_res_4458_; lean_object* v_r_4459_; 
v_a_46__boxed_4456_ = lean_unbox(v_a_4454_);
v_a_47__boxed_4457_ = lean_unbox(v_a_4455_);
v_res_4458_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_a_46__boxed_4456_, v_a_47__boxed_4457_);
v_r_4459_ = lean_box(v_res_4458_);
return v_r_4459_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object* v_upperBound_4460_, lean_object* v_identicalImports_4461_, lean_object* v_a_4462_, lean_object* v_b_4463_){
_start:
{
uint8_t v___x_4464_; 
v___x_4464_ = lean_nat_dec_lt(v_a_4462_, v_upperBound_4460_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; 
lean_dec(v_a_4462_);
v___x_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4465_, 0, v_b_4463_);
return v___x_4465_;
}
else
{
lean_object* v_module_4466_; lean_object* v_uri_4467_; uint8_t v_isAll_4468_; uint8_t v_isPrivate_4469_; uint8_t v_metaKind_4470_; lean_object* v___x_4471_; lean_object* v_module_4472_; lean_object* v_uri_4473_; uint8_t v_isAll_4474_; uint8_t v_isPrivate_4475_; uint8_t v_metaKind_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4496_; 
v_module_4466_ = lean_ctor_get(v_b_4463_, 0);
lean_inc(v_module_4466_);
v_uri_4467_ = lean_ctor_get(v_b_4463_, 1);
lean_inc_ref(v_uri_4467_);
v_isAll_4468_ = lean_ctor_get_uint8(v_b_4463_, sizeof(void*)*2);
v_isPrivate_4469_ = lean_ctor_get_uint8(v_b_4463_, sizeof(void*)*2 + 1);
v_metaKind_4470_ = lean_ctor_get_uint8(v_b_4463_, sizeof(void*)*2 + 2);
lean_dec_ref(v_b_4463_);
v___x_4471_ = lean_array_fget(v_identicalImports_4461_, v_a_4462_);
v_module_4472_ = lean_ctor_get(v___x_4471_, 0);
v_uri_4473_ = lean_ctor_get(v___x_4471_, 1);
v_isAll_4474_ = lean_ctor_get_uint8(v___x_4471_, sizeof(void*)*2);
v_isPrivate_4475_ = lean_ctor_get_uint8(v___x_4471_, sizeof(void*)*2 + 1);
v_metaKind_4476_ = lean_ctor_get_uint8(v___x_4471_, sizeof(void*)*2 + 2);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4478_ = v___x_4471_;
v_isShared_4479_ = v_isSharedCheck_4496_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_uri_4473_);
lean_inc(v_module_4472_);
lean_dec(v___x_4471_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4496_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
uint8_t v___y_4481_; uint8_t v___y_4482_; uint8_t v___y_4491_; uint8_t v___x_4492_; 
v___x_4492_ = lean_name_eq(v_module_4466_, v_module_4472_);
lean_dec(v_module_4472_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; 
lean_del_object(v___x_4478_);
lean_dec_ref(v_uri_4473_);
lean_dec_ref(v_uri_4467_);
lean_dec(v_module_4466_);
lean_dec(v_a_4462_);
v___x_4493_ = lean_box(0);
return v___x_4493_;
}
else
{
uint8_t v___x_4494_; 
v___x_4494_ = lean_string_dec_eq(v_uri_4467_, v_uri_4473_);
lean_dec_ref(v_uri_4473_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; 
lean_del_object(v___x_4478_);
lean_dec_ref(v_uri_4467_);
lean_dec(v_module_4466_);
lean_dec(v_a_4462_);
v___x_4495_ = lean_box(0);
return v___x_4495_;
}
else
{
if (v_isAll_4468_ == 0)
{
v___y_4491_ = v_isAll_4474_;
goto v___jp_4490_;
}
else
{
v___y_4491_ = v_isAll_4468_;
goto v___jp_4490_;
}
}
}
v___jp_4480_:
{
uint8_t v___x_4483_; lean_object* v___x_4485_; 
v___x_4483_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_metaKind_4470_, v_metaKind_4476_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 1, v_uri_4467_);
lean_ctor_set(v___x_4478_, 0, v_module_4466_);
v___x_4485_ = v___x_4478_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_module_4466_);
lean_ctor_set(v_reuseFailAlloc_4489_, 1, v_uri_4467_);
v___x_4485_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_ctor_set_uint8(v___x_4485_, sizeof(void*)*2, v___y_4481_);
lean_ctor_set_uint8(v___x_4485_, sizeof(void*)*2 + 1, v___y_4482_);
lean_ctor_set_uint8(v___x_4485_, sizeof(void*)*2 + 2, v___x_4483_);
v___x_4486_ = lean_unsigned_to_nat(1u);
v___x_4487_ = lean_nat_add(v_a_4462_, v___x_4486_);
lean_dec(v_a_4462_);
v_a_4462_ = v___x_4487_;
v_b_4463_ = v___x_4485_;
goto _start;
}
}
v___jp_4490_:
{
if (v_isPrivate_4469_ == 0)
{
v___y_4481_ = v___y_4491_;
v___y_4482_ = v_isPrivate_4469_;
goto v___jp_4480_;
}
else
{
v___y_4481_ = v___y_4491_;
v___y_4482_ = v_isPrivate_4475_;
goto v___jp_4480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_4497_, lean_object* v_identicalImports_4498_, lean_object* v_a_4499_, lean_object* v_b_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4497_, v_identicalImports_4498_, v_a_4499_, v_b_4500_);
lean_dec_ref(v_identicalImports_4498_);
lean_dec(v_upperBound_4497_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object* v_identicalImports_4502_){
_start:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4503_ = lean_unsigned_to_nat(0u);
v___x_4504_ = lean_array_get_size(v_identicalImports_4502_);
v___x_4505_ = lean_nat_dec_lt(v___x_4503_, v___x_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; 
v___x_4506_ = lean_box(0);
return v___x_4506_;
}
else
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4507_ = lean_unsigned_to_nat(1u);
v___x_4508_ = lean_array_fget_borrowed(v_identicalImports_4502_, v___x_4503_);
lean_inc(v___x_4508_);
v___x_4509_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v___x_4504_, v_identicalImports_4502_, v___x_4507_, v___x_4508_);
return v___x_4509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object* v_identicalImports_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_identicalImports_4510_);
lean_dec_ref(v_identicalImports_4510_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object* v_upperBound_4512_, lean_object* v_identicalImports_4513_, lean_object* v_inst_4514_, lean_object* v_R_4515_, lean_object* v_a_4516_, lean_object* v_b_4517_, lean_object* v_c_4518_){
_start:
{
lean_object* v___x_4519_; 
v___x_4519_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4512_, v_identicalImports_4513_, v_a_4516_, v_b_4517_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object* v_upperBound_4520_, lean_object* v_identicalImports_4521_, lean_object* v_inst_4522_, lean_object* v_R_4523_, lean_object* v_a_4524_, lean_object* v_b_4525_, lean_object* v_c_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(v_upperBound_4520_, v_identicalImports_4521_, v_inst_4522_, v_R_4523_, v_a_4524_, v_b_4525_, v_c_4526_);
lean_dec_ref(v_identicalImports_4521_);
lean_dec(v_upperBound_4520_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object* v_x_4534_){
_start:
{
lean_object* v_module_4535_; 
v_module_4535_ = lean_ctor_get(v_x_4534_, 0);
lean_inc(v_module_4535_);
return v_module_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object* v_x_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_Server_DirectImports_convertImportInfos___lam__0(v_x_4536_);
lean_dec_ref(v_x_4536_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object* v_x_4538_, lean_object* v_x_4539_){
_start:
{
if (lean_obj_tag(v_x_4539_) == 0)
{
return v_x_4538_;
}
else
{
lean_object* v_key_4540_; lean_object* v_value_4541_; lean_object* v_tail_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v_key_4540_ = lean_ctor_get(v_x_4539_, 0);
v_value_4541_ = lean_ctor_get(v_x_4539_, 1);
v_tail_4542_ = lean_ctor_get(v_x_4539_, 2);
lean_inc(v_value_4541_);
lean_inc(v_key_4540_);
v___x_4543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4543_, 0, v_key_4540_);
lean_ctor_set(v___x_4543_, 1, v_value_4541_);
v___x_4544_ = lean_array_push(v_x_4538_, v___x_4543_);
v_x_4538_ = v___x_4544_;
v_x_4539_ = v_tail_4542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object* v_x_4546_, lean_object* v_x_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_x_4546_, v_x_4547_);
lean_dec(v_x_4547_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object* v_as_4549_, size_t v_i_4550_, size_t v_stop_4551_, lean_object* v_b_4552_){
_start:
{
uint8_t v___x_4553_; 
v___x_4553_ = lean_usize_dec_eq(v_i_4550_, v_stop_4551_);
if (v___x_4553_ == 0)
{
lean_object* v___x_4554_; lean_object* v___x_4555_; size_t v___x_4556_; size_t v___x_4557_; 
v___x_4554_ = lean_array_uget_borrowed(v_as_4549_, v_i_4550_);
v___x_4555_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_b_4552_, v___x_4554_);
v___x_4556_ = ((size_t)1ULL);
v___x_4557_ = lean_usize_add(v_i_4550_, v___x_4556_);
v_i_4550_ = v___x_4557_;
v_b_4552_ = v___x_4555_;
goto _start;
}
else
{
return v_b_4552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object* v_as_4559_, lean_object* v_i_4560_, lean_object* v_stop_4561_, lean_object* v_b_4562_){
_start:
{
size_t v_i_boxed_4563_; size_t v_stop_boxed_4564_; lean_object* v_res_4565_; 
v_i_boxed_4563_ = lean_unbox_usize(v_i_4560_);
lean_dec(v_i_4560_);
v_stop_boxed_4564_ = lean_unbox_usize(v_stop_4561_);
lean_dec(v_stop_4561_);
v_res_4565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_as_4559_, v_i_boxed_4563_, v_stop_boxed_4564_, v_b_4562_);
lean_dec_ref(v_as_4559_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object* v_as_4566_, size_t v_i_4567_, size_t v_stop_4568_, lean_object* v_b_4569_){
_start:
{
uint8_t v___x_4571_; 
v___x_4571_ = lean_usize_dec_eq(v_i_4567_, v_stop_4568_);
if (v___x_4571_ == 0)
{
lean_object* v___x_4572_; lean_object* v_module_4573_; uint8_t v_isPrivate_4574_; uint8_t v_isAll_4575_; uint8_t v_isMeta_4576_; lean_object* v_module_4577_; lean_object* v___x_4578_; 
v___x_4572_ = lean_array_uget_borrowed(v_as_4566_, v_i_4567_);
v_module_4573_ = lean_ctor_get(v___x_4572_, 0);
v_isPrivate_4574_ = lean_ctor_get_uint8(v___x_4572_, sizeof(void*)*1);
v_isAll_4575_ = lean_ctor_get_uint8(v___x_4572_, sizeof(void*)*1 + 1);
v_isMeta_4576_ = lean_ctor_get_uint8(v___x_4572_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4573_);
v_module_4577_ = l_String_toName(v_module_4573_);
lean_inc(v_module_4577_);
v___x_4578_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4577_);
if (lean_obj_tag(v___x_4578_) == 0)
{
lean_object* v_a_4579_; lean_object* v_a_4581_; 
v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
lean_inc(v_a_4579_);
lean_dec_ref(v___x_4578_);
if (lean_obj_tag(v_a_4579_) == 1)
{
lean_object* v_val_4585_; uint8_t v___y_4587_; 
v_val_4585_ = lean_ctor_get(v_a_4579_, 0);
lean_inc(v_val_4585_);
lean_dec_ref(v_a_4579_);
if (v_isMeta_4576_ == 0)
{
uint8_t v___x_4590_; 
v___x_4590_ = 0;
v___y_4587_ = v___x_4590_;
goto v___jp_4586_;
}
else
{
uint8_t v___x_4591_; 
v___x_4591_ = 1;
v___y_4587_ = v___x_4591_;
goto v___jp_4586_;
}
v___jp_4586_:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4588_, 0, v_module_4577_);
lean_ctor_set(v___x_4588_, 1, v_val_4585_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*2, v_isAll_4575_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*2 + 1, v_isPrivate_4574_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*2 + 2, v___y_4587_);
v___x_4589_ = lean_array_push(v_b_4569_, v___x_4588_);
v_a_4581_ = v___x_4589_;
goto v___jp_4580_;
}
}
else
{
lean_dec(v_a_4579_);
lean_dec(v_module_4577_);
v_a_4581_ = v_b_4569_;
goto v___jp_4580_;
}
v___jp_4580_:
{
size_t v___x_4582_; size_t v___x_4583_; 
v___x_4582_ = ((size_t)1ULL);
v___x_4583_ = lean_usize_add(v_i_4567_, v___x_4582_);
v_i_4567_ = v___x_4583_;
v_b_4569_ = v_a_4581_;
goto _start;
}
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
lean_dec(v_module_4577_);
lean_dec_ref(v_b_4569_);
v_a_4592_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___x_4578_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4578_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
else
{
lean_object* v___x_4600_; 
v___x_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4600_, 0, v_b_4569_);
return v___x_4600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object* v_as_4601_, lean_object* v_i_4602_, lean_object* v_stop_4603_, lean_object* v_b_4604_, lean_object* v___y_4605_){
_start:
{
size_t v_i_boxed_4606_; size_t v_stop_boxed_4607_; lean_object* v_res_4608_; 
v_i_boxed_4606_ = lean_unbox_usize(v_i_4602_);
lean_dec(v_i_4602_);
v_stop_boxed_4607_ = lean_unbox_usize(v_stop_4603_);
lean_dec(v_stop_4603_);
v_res_4608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4601_, v_i_boxed_4606_, v_stop_boxed_4607_, v_b_4604_);
lean_dec_ref(v_as_4601_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object* v_as_4609_, lean_object* v_start_4610_, lean_object* v_stop_4611_){
_start:
{
lean_object* v___x_4613_; uint8_t v___x_4614_; 
v___x_4613_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_4614_ = lean_nat_dec_lt(v_start_4610_, v_stop_4611_);
if (v___x_4614_ == 0)
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4613_);
return v___x_4615_;
}
else
{
lean_object* v___x_4616_; uint8_t v___x_4617_; 
v___x_4616_ = lean_array_get_size(v_as_4609_);
v___x_4617_ = lean_nat_dec_le(v_stop_4611_, v___x_4616_);
if (v___x_4617_ == 0)
{
uint8_t v___x_4618_; 
v___x_4618_ = lean_nat_dec_lt(v_start_4610_, v___x_4616_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; 
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4613_);
return v___x_4619_;
}
else
{
size_t v___x_4620_; size_t v___x_4621_; lean_object* v___x_4622_; 
v___x_4620_ = lean_usize_of_nat(v_start_4610_);
v___x_4621_ = lean_usize_of_nat(v___x_4616_);
v___x_4622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4609_, v___x_4620_, v___x_4621_, v___x_4613_);
return v___x_4622_;
}
}
else
{
size_t v___x_4623_; size_t v___x_4624_; lean_object* v___x_4625_; 
v___x_4623_ = lean_usize_of_nat(v_start_4610_);
v___x_4624_ = lean_usize_of_nat(v_stop_4611_);
v___x_4625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4609_, v___x_4623_, v___x_4624_, v___x_4613_);
return v___x_4625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object* v_as_4626_, lean_object* v_start_4627_, lean_object* v_stop_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_as_4626_, v_start_4627_, v_stop_4628_);
lean_dec(v_stop_4628_);
lean_dec(v_start_4627_);
lean_dec_ref(v_as_4626_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object* v_k_4631_, lean_object* v_v_4632_, lean_object* v_t_4633_){
_start:
{
if (lean_obj_tag(v_t_4633_) == 0)
{
lean_object* v_size_4634_; lean_object* v_k_4635_; lean_object* v_v_4636_; lean_object* v_l_4637_; lean_object* v_r_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4918_; 
v_size_4634_ = lean_ctor_get(v_t_4633_, 0);
v_k_4635_ = lean_ctor_get(v_t_4633_, 1);
v_v_4636_ = lean_ctor_get(v_t_4633_, 2);
v_l_4637_ = lean_ctor_get(v_t_4633_, 3);
v_r_4638_ = lean_ctor_get(v_t_4633_, 4);
v_isSharedCheck_4918_ = !lean_is_exclusive(v_t_4633_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4640_ = v_t_4633_;
v_isShared_4641_ = v_isSharedCheck_4918_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_r_4638_);
lean_inc(v_l_4637_);
lean_inc(v_v_4636_);
lean_inc(v_k_4635_);
lean_inc(v_size_4634_);
lean_dec(v_t_4633_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4918_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
uint8_t v___x_4642_; 
v___x_4642_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4631_, v_k_4635_);
switch(v___x_4642_)
{
case 0:
{
lean_object* v_impl_4643_; lean_object* v___x_4644_; 
lean_dec(v_size_4634_);
v_impl_4643_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4631_, v_v_4632_, v_l_4637_);
v___x_4644_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4638_) == 0)
{
lean_object* v_size_4645_; lean_object* v_size_4646_; lean_object* v_k_4647_; lean_object* v_v_4648_; lean_object* v_l_4649_; lean_object* v_r_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; 
v_size_4645_ = lean_ctor_get(v_r_4638_, 0);
v_size_4646_ = lean_ctor_get(v_impl_4643_, 0);
lean_inc(v_size_4646_);
v_k_4647_ = lean_ctor_get(v_impl_4643_, 1);
lean_inc(v_k_4647_);
v_v_4648_ = lean_ctor_get(v_impl_4643_, 2);
lean_inc(v_v_4648_);
v_l_4649_ = lean_ctor_get(v_impl_4643_, 3);
lean_inc(v_l_4649_);
v_r_4650_ = lean_ctor_get(v_impl_4643_, 4);
lean_inc(v_r_4650_);
v___x_4651_ = lean_unsigned_to_nat(3u);
v___x_4652_ = lean_nat_mul(v___x_4651_, v_size_4645_);
v___x_4653_ = lean_nat_dec_lt(v___x_4652_, v_size_4646_);
lean_dec(v___x_4652_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4657_; 
lean_dec(v_r_4650_);
lean_dec(v_l_4649_);
lean_dec(v_v_4648_);
lean_dec(v_k_4647_);
v___x_4654_ = lean_nat_add(v___x_4644_, v_size_4646_);
lean_dec(v_size_4646_);
v___x_4655_ = lean_nat_add(v___x_4654_, v_size_4645_);
lean_dec(v___x_4654_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 3, v_impl_4643_);
lean_ctor_set(v___x_4640_, 0, v___x_4655_);
v___x_4657_ = v___x_4640_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4658_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4658_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4658_, 3, v_impl_4643_);
lean_ctor_set(v_reuseFailAlloc_4658_, 4, v_r_4638_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
else
{
lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4724_; 
v_isSharedCheck_4724_ = !lean_is_exclusive(v_impl_4643_);
if (v_isSharedCheck_4724_ == 0)
{
lean_object* v_unused_4725_; lean_object* v_unused_4726_; lean_object* v_unused_4727_; lean_object* v_unused_4728_; lean_object* v_unused_4729_; 
v_unused_4725_ = lean_ctor_get(v_impl_4643_, 4);
lean_dec(v_unused_4725_);
v_unused_4726_ = lean_ctor_get(v_impl_4643_, 3);
lean_dec(v_unused_4726_);
v_unused_4727_ = lean_ctor_get(v_impl_4643_, 2);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_impl_4643_, 1);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_impl_4643_, 0);
lean_dec(v_unused_4729_);
v___x_4660_ = v_impl_4643_;
v_isShared_4661_ = v_isSharedCheck_4724_;
goto v_resetjp_4659_;
}
else
{
lean_dec(v_impl_4643_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4724_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v_size_4662_; lean_object* v_size_4663_; lean_object* v_k_4664_; lean_object* v_v_4665_; lean_object* v_l_4666_; lean_object* v_r_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; uint8_t v___x_4670_; 
v_size_4662_ = lean_ctor_get(v_l_4649_, 0);
v_size_4663_ = lean_ctor_get(v_r_4650_, 0);
v_k_4664_ = lean_ctor_get(v_r_4650_, 1);
v_v_4665_ = lean_ctor_get(v_r_4650_, 2);
v_l_4666_ = lean_ctor_get(v_r_4650_, 3);
v_r_4667_ = lean_ctor_get(v_r_4650_, 4);
v___x_4668_ = lean_unsigned_to_nat(2u);
v___x_4669_ = lean_nat_mul(v___x_4668_, v_size_4662_);
v___x_4670_ = lean_nat_dec_lt(v_size_4663_, v___x_4669_);
lean_dec(v___x_4669_);
if (v___x_4670_ == 0)
{
lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4699_; 
lean_inc(v_r_4667_);
lean_inc(v_l_4666_);
lean_inc(v_v_4665_);
lean_inc(v_k_4664_);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_r_4650_);
if (v_isSharedCheck_4699_ == 0)
{
lean_object* v_unused_4700_; lean_object* v_unused_4701_; lean_object* v_unused_4702_; lean_object* v_unused_4703_; lean_object* v_unused_4704_; 
v_unused_4700_ = lean_ctor_get(v_r_4650_, 4);
lean_dec(v_unused_4700_);
v_unused_4701_ = lean_ctor_get(v_r_4650_, 3);
lean_dec(v_unused_4701_);
v_unused_4702_ = lean_ctor_get(v_r_4650_, 2);
lean_dec(v_unused_4702_);
v_unused_4703_ = lean_ctor_get(v_r_4650_, 1);
lean_dec(v_unused_4703_);
v_unused_4704_ = lean_ctor_get(v_r_4650_, 0);
lean_dec(v_unused_4704_);
v___x_4672_ = v_r_4650_;
v_isShared_4673_ = v_isSharedCheck_4699_;
goto v_resetjp_4671_;
}
else
{
lean_dec(v_r_4650_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4699_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4679_; lean_object* v___x_4687_; lean_object* v___y_4689_; 
v___x_4674_ = lean_nat_add(v___x_4644_, v_size_4646_);
lean_dec(v_size_4646_);
v___x_4675_ = lean_nat_add(v___x_4674_, v_size_4645_);
lean_dec(v___x_4674_);
v___x_4687_ = lean_nat_add(v___x_4644_, v_size_4662_);
if (lean_obj_tag(v_l_4666_) == 0)
{
lean_object* v_size_4697_; 
v_size_4697_ = lean_ctor_get(v_l_4666_, 0);
lean_inc(v_size_4697_);
v___y_4689_ = v_size_4697_;
goto v___jp_4688_;
}
else
{
lean_object* v___x_4698_; 
v___x_4698_ = lean_unsigned_to_nat(0u);
v___y_4689_ = v___x_4698_;
goto v___jp_4688_;
}
v___jp_4676_:
{
lean_object* v___x_4680_; lean_object* v___x_4682_; 
v___x_4680_ = lean_nat_add(v___y_4677_, v___y_4679_);
lean_dec(v___y_4679_);
lean_dec(v___y_4677_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 4, v_r_4638_);
lean_ctor_set(v___x_4672_, 3, v_r_4667_);
lean_ctor_set(v___x_4672_, 2, v_v_4636_);
lean_ctor_set(v___x_4672_, 1, v_k_4635_);
lean_ctor_set(v___x_4672_, 0, v___x_4680_);
v___x_4682_ = v___x_4672_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4680_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4686_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4686_, 3, v_r_4667_);
lean_ctor_set(v_reuseFailAlloc_4686_, 4, v_r_4638_);
v___x_4682_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4684_; 
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 4, v___x_4682_);
lean_ctor_set(v___x_4660_, 3, v___y_4678_);
lean_ctor_set(v___x_4660_, 2, v_v_4665_);
lean_ctor_set(v___x_4660_, 1, v_k_4664_);
lean_ctor_set(v___x_4660_, 0, v___x_4675_);
v___x_4684_ = v___x_4660_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4675_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_k_4664_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_v_4665_);
lean_ctor_set(v_reuseFailAlloc_4685_, 3, v___y_4678_);
lean_ctor_set(v_reuseFailAlloc_4685_, 4, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
v___jp_4688_:
{
lean_object* v___x_4690_; lean_object* v___x_4692_; 
v___x_4690_ = lean_nat_add(v___x_4687_, v___y_4689_);
lean_dec(v___y_4689_);
lean_dec(v___x_4687_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v_l_4666_);
lean_ctor_set(v___x_4640_, 3, v_l_4649_);
lean_ctor_set(v___x_4640_, 2, v_v_4648_);
lean_ctor_set(v___x_4640_, 1, v_k_4647_);
lean_ctor_set(v___x_4640_, 0, v___x_4690_);
v___x_4692_ = v___x_4640_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4690_);
lean_ctor_set(v_reuseFailAlloc_4696_, 1, v_k_4647_);
lean_ctor_set(v_reuseFailAlloc_4696_, 2, v_v_4648_);
lean_ctor_set(v_reuseFailAlloc_4696_, 3, v_l_4649_);
lean_ctor_set(v_reuseFailAlloc_4696_, 4, v_l_4666_);
v___x_4692_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
lean_object* v___x_4693_; 
v___x_4693_ = lean_nat_add(v___x_4644_, v_size_4645_);
if (lean_obj_tag(v_r_4667_) == 0)
{
lean_object* v_size_4694_; 
v_size_4694_ = lean_ctor_get(v_r_4667_, 0);
lean_inc(v_size_4694_);
v___y_4677_ = v___x_4693_;
v___y_4678_ = v___x_4692_;
v___y_4679_ = v_size_4694_;
goto v___jp_4676_;
}
else
{
lean_object* v___x_4695_; 
v___x_4695_ = lean_unsigned_to_nat(0u);
v___y_4677_ = v___x_4693_;
v___y_4678_ = v___x_4692_;
v___y_4679_ = v___x_4695_;
goto v___jp_4676_;
}
}
}
}
}
else
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4710_; 
lean_del_object(v___x_4640_);
v___x_4705_ = lean_nat_add(v___x_4644_, v_size_4646_);
lean_dec(v_size_4646_);
v___x_4706_ = lean_nat_add(v___x_4705_, v_size_4645_);
lean_dec(v___x_4705_);
v___x_4707_ = lean_nat_add(v___x_4644_, v_size_4645_);
v___x_4708_ = lean_nat_add(v___x_4707_, v_size_4663_);
lean_dec(v___x_4707_);
lean_inc_ref(v_r_4638_);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 4, v_r_4638_);
lean_ctor_set(v___x_4660_, 3, v_r_4650_);
lean_ctor_set(v___x_4660_, 2, v_v_4636_);
lean_ctor_set(v___x_4660_, 1, v_k_4635_);
lean_ctor_set(v___x_4660_, 0, v___x_4708_);
v___x_4710_ = v___x_4660_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4708_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4723_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4723_, 3, v_r_4650_);
lean_ctor_set(v_reuseFailAlloc_4723_, 4, v_r_4638_);
v___x_4710_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
v_isSharedCheck_4717_ = !lean_is_exclusive(v_r_4638_);
if (v_isSharedCheck_4717_ == 0)
{
lean_object* v_unused_4718_; lean_object* v_unused_4719_; lean_object* v_unused_4720_; lean_object* v_unused_4721_; lean_object* v_unused_4722_; 
v_unused_4718_ = lean_ctor_get(v_r_4638_, 4);
lean_dec(v_unused_4718_);
v_unused_4719_ = lean_ctor_get(v_r_4638_, 3);
lean_dec(v_unused_4719_);
v_unused_4720_ = lean_ctor_get(v_r_4638_, 2);
lean_dec(v_unused_4720_);
v_unused_4721_ = lean_ctor_get(v_r_4638_, 1);
lean_dec(v_unused_4721_);
v_unused_4722_ = lean_ctor_get(v_r_4638_, 0);
lean_dec(v_unused_4722_);
v___x_4712_ = v_r_4638_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_dec(v_r_4638_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 4, v___x_4710_);
lean_ctor_set(v___x_4712_, 3, v_l_4649_);
lean_ctor_set(v___x_4712_, 2, v_v_4648_);
lean_ctor_set(v___x_4712_, 1, v_k_4647_);
lean_ctor_set(v___x_4712_, 0, v___x_4706_);
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4706_);
lean_ctor_set(v_reuseFailAlloc_4716_, 1, v_k_4647_);
lean_ctor_set(v_reuseFailAlloc_4716_, 2, v_v_4648_);
lean_ctor_set(v_reuseFailAlloc_4716_, 3, v_l_4649_);
lean_ctor_set(v_reuseFailAlloc_4716_, 4, v___x_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4730_; 
v_l_4730_ = lean_ctor_get(v_impl_4643_, 3);
lean_inc(v_l_4730_);
if (lean_obj_tag(v_l_4730_) == 0)
{
lean_object* v_r_4731_; lean_object* v_k_4732_; lean_object* v_v_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4744_; 
v_r_4731_ = lean_ctor_get(v_impl_4643_, 4);
v_k_4732_ = lean_ctor_get(v_impl_4643_, 1);
v_v_4733_ = lean_ctor_get(v_impl_4643_, 2);
v_isSharedCheck_4744_ = !lean_is_exclusive(v_impl_4643_);
if (v_isSharedCheck_4744_ == 0)
{
lean_object* v_unused_4745_; lean_object* v_unused_4746_; 
v_unused_4745_ = lean_ctor_get(v_impl_4643_, 3);
lean_dec(v_unused_4745_);
v_unused_4746_ = lean_ctor_get(v_impl_4643_, 0);
lean_dec(v_unused_4746_);
v___x_4735_ = v_impl_4643_;
v_isShared_4736_ = v_isSharedCheck_4744_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_r_4731_);
lean_inc(v_v_4733_);
lean_inc(v_k_4732_);
lean_dec(v_impl_4643_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4744_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4737_; lean_object* v___x_4739_; 
v___x_4737_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4731_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 3, v_r_4731_);
lean_ctor_set(v___x_4735_, 2, v_v_4636_);
lean_ctor_set(v___x_4735_, 1, v_k_4635_);
lean_ctor_set(v___x_4735_, 0, v___x_4644_);
v___x_4739_ = v___x_4735_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4743_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4743_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4743_, 3, v_r_4731_);
lean_ctor_set(v_reuseFailAlloc_4743_, 4, v_r_4731_);
v___x_4739_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
lean_object* v___x_4741_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v___x_4739_);
lean_ctor_set(v___x_4640_, 3, v_l_4730_);
lean_ctor_set(v___x_4640_, 2, v_v_4733_);
lean_ctor_set(v___x_4640_, 1, v_k_4732_);
lean_ctor_set(v___x_4640_, 0, v___x_4737_);
v___x_4741_ = v___x_4640_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4737_);
lean_ctor_set(v_reuseFailAlloc_4742_, 1, v_k_4732_);
lean_ctor_set(v_reuseFailAlloc_4742_, 2, v_v_4733_);
lean_ctor_set(v_reuseFailAlloc_4742_, 3, v_l_4730_);
lean_ctor_set(v_reuseFailAlloc_4742_, 4, v___x_4739_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
else
{
lean_object* v_r_4747_; 
v_r_4747_ = lean_ctor_get(v_impl_4643_, 4);
lean_inc(v_r_4747_);
if (lean_obj_tag(v_r_4747_) == 0)
{
lean_object* v_k_4748_; lean_object* v_v_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4772_; 
v_k_4748_ = lean_ctor_get(v_impl_4643_, 1);
v_v_4749_ = lean_ctor_get(v_impl_4643_, 2);
v_isSharedCheck_4772_ = !lean_is_exclusive(v_impl_4643_);
if (v_isSharedCheck_4772_ == 0)
{
lean_object* v_unused_4773_; lean_object* v_unused_4774_; lean_object* v_unused_4775_; 
v_unused_4773_ = lean_ctor_get(v_impl_4643_, 4);
lean_dec(v_unused_4773_);
v_unused_4774_ = lean_ctor_get(v_impl_4643_, 3);
lean_dec(v_unused_4774_);
v_unused_4775_ = lean_ctor_get(v_impl_4643_, 0);
lean_dec(v_unused_4775_);
v___x_4751_ = v_impl_4643_;
v_isShared_4752_ = v_isSharedCheck_4772_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_v_4749_);
lean_inc(v_k_4748_);
lean_dec(v_impl_4643_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4772_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v_k_4753_; lean_object* v_v_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4768_; 
v_k_4753_ = lean_ctor_get(v_r_4747_, 1);
v_v_4754_ = lean_ctor_get(v_r_4747_, 2);
v_isSharedCheck_4768_ = !lean_is_exclusive(v_r_4747_);
if (v_isSharedCheck_4768_ == 0)
{
lean_object* v_unused_4769_; lean_object* v_unused_4770_; lean_object* v_unused_4771_; 
v_unused_4769_ = lean_ctor_get(v_r_4747_, 4);
lean_dec(v_unused_4769_);
v_unused_4770_ = lean_ctor_get(v_r_4747_, 3);
lean_dec(v_unused_4770_);
v_unused_4771_ = lean_ctor_get(v_r_4747_, 0);
lean_dec(v_unused_4771_);
v___x_4756_ = v_r_4747_;
v_isShared_4757_ = v_isSharedCheck_4768_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_v_4754_);
lean_inc(v_k_4753_);
lean_dec(v_r_4747_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4768_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4758_ = lean_unsigned_to_nat(3u);
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 4, v_l_4730_);
lean_ctor_set(v___x_4756_, 3, v_l_4730_);
lean_ctor_set(v___x_4756_, 2, v_v_4749_);
lean_ctor_set(v___x_4756_, 1, v_k_4748_);
lean_ctor_set(v___x_4756_, 0, v___x_4644_);
v___x_4760_ = v___x_4756_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4767_, 1, v_k_4748_);
lean_ctor_set(v_reuseFailAlloc_4767_, 2, v_v_4749_);
lean_ctor_set(v_reuseFailAlloc_4767_, 3, v_l_4730_);
lean_ctor_set(v_reuseFailAlloc_4767_, 4, v_l_4730_);
v___x_4760_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4762_; 
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 4, v_l_4730_);
lean_ctor_set(v___x_4751_, 2, v_v_4636_);
lean_ctor_set(v___x_4751_, 1, v_k_4635_);
lean_ctor_set(v___x_4751_, 0, v___x_4644_);
v___x_4762_ = v___x_4751_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4766_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4766_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4766_, 3, v_l_4730_);
lean_ctor_set(v_reuseFailAlloc_4766_, 4, v_l_4730_);
v___x_4762_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4764_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v___x_4762_);
lean_ctor_set(v___x_4640_, 3, v___x_4760_);
lean_ctor_set(v___x_4640_, 2, v_v_4754_);
lean_ctor_set(v___x_4640_, 1, v_k_4753_);
lean_ctor_set(v___x_4640_, 0, v___x_4758_);
v___x_4764_ = v___x_4640_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4758_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v_k_4753_);
lean_ctor_set(v_reuseFailAlloc_4765_, 2, v_v_4754_);
lean_ctor_set(v_reuseFailAlloc_4765_, 3, v___x_4760_);
lean_ctor_set(v_reuseFailAlloc_4765_, 4, v___x_4762_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
}
}
else
{
lean_object* v___x_4776_; lean_object* v___x_4778_; 
v___x_4776_ = lean_unsigned_to_nat(2u);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v_r_4747_);
lean_ctor_set(v___x_4640_, 3, v_impl_4643_);
lean_ctor_set(v___x_4640_, 0, v___x_4776_);
v___x_4778_ = v___x_4640_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4776_);
lean_ctor_set(v_reuseFailAlloc_4779_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4779_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4779_, 3, v_impl_4643_);
lean_ctor_set(v_reuseFailAlloc_4779_, 4, v_r_4747_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4781_; 
lean_dec(v_v_4636_);
lean_dec(v_k_4635_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 2, v_v_4632_);
lean_ctor_set(v___x_4640_, 1, v_k_4631_);
v___x_4781_ = v___x_4640_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_size_4634_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_k_4631_);
lean_ctor_set(v_reuseFailAlloc_4782_, 2, v_v_4632_);
lean_ctor_set(v_reuseFailAlloc_4782_, 3, v_l_4637_);
lean_ctor_set(v_reuseFailAlloc_4782_, 4, v_r_4638_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
return v___x_4781_;
}
}
default: 
{
lean_object* v_impl_4783_; lean_object* v___x_4784_; 
lean_dec(v_size_4634_);
v_impl_4783_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4631_, v_v_4632_, v_r_4638_);
v___x_4784_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4637_) == 0)
{
lean_object* v_size_4785_; lean_object* v_size_4786_; lean_object* v_k_4787_; lean_object* v_v_4788_; lean_object* v_l_4789_; lean_object* v_r_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v_size_4785_ = lean_ctor_get(v_l_4637_, 0);
v_size_4786_ = lean_ctor_get(v_impl_4783_, 0);
lean_inc(v_size_4786_);
v_k_4787_ = lean_ctor_get(v_impl_4783_, 1);
lean_inc(v_k_4787_);
v_v_4788_ = lean_ctor_get(v_impl_4783_, 2);
lean_inc(v_v_4788_);
v_l_4789_ = lean_ctor_get(v_impl_4783_, 3);
lean_inc(v_l_4789_);
v_r_4790_ = lean_ctor_get(v_impl_4783_, 4);
lean_inc(v_r_4790_);
v___x_4791_ = lean_unsigned_to_nat(3u);
v___x_4792_ = lean_nat_mul(v___x_4791_, v_size_4785_);
v___x_4793_ = lean_nat_dec_lt(v___x_4792_, v_size_4786_);
lean_dec(v___x_4792_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4797_; 
lean_dec(v_r_4790_);
lean_dec(v_l_4789_);
lean_dec(v_v_4788_);
lean_dec(v_k_4787_);
v___x_4794_ = lean_nat_add(v___x_4784_, v_size_4785_);
v___x_4795_ = lean_nat_add(v___x_4794_, v_size_4786_);
lean_dec(v_size_4786_);
lean_dec(v___x_4794_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v_impl_4783_);
lean_ctor_set(v___x_4640_, 0, v___x_4795_);
v___x_4797_ = v___x_4640_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4795_);
lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4798_, 3, v_l_4637_);
lean_ctor_set(v_reuseFailAlloc_4798_, 4, v_impl_4783_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
else
{
lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4862_; 
v_isSharedCheck_4862_ = !lean_is_exclusive(v_impl_4783_);
if (v_isSharedCheck_4862_ == 0)
{
lean_object* v_unused_4863_; lean_object* v_unused_4864_; lean_object* v_unused_4865_; lean_object* v_unused_4866_; lean_object* v_unused_4867_; 
v_unused_4863_ = lean_ctor_get(v_impl_4783_, 4);
lean_dec(v_unused_4863_);
v_unused_4864_ = lean_ctor_get(v_impl_4783_, 3);
lean_dec(v_unused_4864_);
v_unused_4865_ = lean_ctor_get(v_impl_4783_, 2);
lean_dec(v_unused_4865_);
v_unused_4866_ = lean_ctor_get(v_impl_4783_, 1);
lean_dec(v_unused_4866_);
v_unused_4867_ = lean_ctor_get(v_impl_4783_, 0);
lean_dec(v_unused_4867_);
v___x_4800_ = v_impl_4783_;
v_isShared_4801_ = v_isSharedCheck_4862_;
goto v_resetjp_4799_;
}
else
{
lean_dec(v_impl_4783_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4862_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v_size_4802_; lean_object* v_k_4803_; lean_object* v_v_4804_; lean_object* v_l_4805_; lean_object* v_r_4806_; lean_object* v_size_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v_size_4802_ = lean_ctor_get(v_l_4789_, 0);
v_k_4803_ = lean_ctor_get(v_l_4789_, 1);
v_v_4804_ = lean_ctor_get(v_l_4789_, 2);
v_l_4805_ = lean_ctor_get(v_l_4789_, 3);
v_r_4806_ = lean_ctor_get(v_l_4789_, 4);
v_size_4807_ = lean_ctor_get(v_r_4790_, 0);
v___x_4808_ = lean_unsigned_to_nat(2u);
v___x_4809_ = lean_nat_mul(v___x_4808_, v_size_4807_);
v___x_4810_ = lean_nat_dec_lt(v_size_4802_, v___x_4809_);
lean_dec(v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4838_; 
lean_inc(v_r_4806_);
lean_inc(v_l_4805_);
lean_inc(v_v_4804_);
lean_inc(v_k_4803_);
v_isSharedCheck_4838_ = !lean_is_exclusive(v_l_4789_);
if (v_isSharedCheck_4838_ == 0)
{
lean_object* v_unused_4839_; lean_object* v_unused_4840_; lean_object* v_unused_4841_; lean_object* v_unused_4842_; lean_object* v_unused_4843_; 
v_unused_4839_ = lean_ctor_get(v_l_4789_, 4);
lean_dec(v_unused_4839_);
v_unused_4840_ = lean_ctor_get(v_l_4789_, 3);
lean_dec(v_unused_4840_);
v_unused_4841_ = lean_ctor_get(v_l_4789_, 2);
lean_dec(v_unused_4841_);
v_unused_4842_ = lean_ctor_get(v_l_4789_, 1);
lean_dec(v_unused_4842_);
v_unused_4843_ = lean_ctor_get(v_l_4789_, 0);
lean_dec(v_unused_4843_);
v___x_4812_ = v_l_4789_;
v_isShared_4813_ = v_isSharedCheck_4838_;
goto v_resetjp_4811_;
}
else
{
lean_dec(v_l_4789_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4838_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___y_4817_; lean_object* v___y_4818_; lean_object* v___y_4819_; lean_object* v___y_4828_; 
v___x_4814_ = lean_nat_add(v___x_4784_, v_size_4785_);
v___x_4815_ = lean_nat_add(v___x_4814_, v_size_4786_);
lean_dec(v_size_4786_);
if (lean_obj_tag(v_l_4805_) == 0)
{
lean_object* v_size_4836_; 
v_size_4836_ = lean_ctor_get(v_l_4805_, 0);
lean_inc(v_size_4836_);
v___y_4828_ = v_size_4836_;
goto v___jp_4827_;
}
else
{
lean_object* v___x_4837_; 
v___x_4837_ = lean_unsigned_to_nat(0u);
v___y_4828_ = v___x_4837_;
goto v___jp_4827_;
}
v___jp_4816_:
{
lean_object* v___x_4820_; lean_object* v___x_4822_; 
v___x_4820_ = lean_nat_add(v___y_4818_, v___y_4819_);
lean_dec(v___y_4819_);
lean_dec(v___y_4818_);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 4, v_r_4790_);
lean_ctor_set(v___x_4812_, 3, v_r_4806_);
lean_ctor_set(v___x_4812_, 2, v_v_4788_);
lean_ctor_set(v___x_4812_, 1, v_k_4787_);
lean_ctor_set(v___x_4812_, 0, v___x_4820_);
v___x_4822_ = v___x_4812_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4826_, 1, v_k_4787_);
lean_ctor_set(v_reuseFailAlloc_4826_, 2, v_v_4788_);
lean_ctor_set(v_reuseFailAlloc_4826_, 3, v_r_4806_);
lean_ctor_set(v_reuseFailAlloc_4826_, 4, v_r_4790_);
v___x_4822_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
lean_object* v___x_4824_; 
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 4, v___x_4822_);
lean_ctor_set(v___x_4800_, 3, v___y_4817_);
lean_ctor_set(v___x_4800_, 2, v_v_4804_);
lean_ctor_set(v___x_4800_, 1, v_k_4803_);
lean_ctor_set(v___x_4800_, 0, v___x_4815_);
v___x_4824_ = v___x_4800_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4815_);
lean_ctor_set(v_reuseFailAlloc_4825_, 1, v_k_4803_);
lean_ctor_set(v_reuseFailAlloc_4825_, 2, v_v_4804_);
lean_ctor_set(v_reuseFailAlloc_4825_, 3, v___y_4817_);
lean_ctor_set(v_reuseFailAlloc_4825_, 4, v___x_4822_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
v___jp_4827_:
{
lean_object* v___x_4829_; lean_object* v___x_4831_; 
v___x_4829_ = lean_nat_add(v___x_4814_, v___y_4828_);
lean_dec(v___y_4828_);
lean_dec(v___x_4814_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v_l_4805_);
lean_ctor_set(v___x_4640_, 0, v___x_4829_);
v___x_4831_ = v___x_4640_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4829_);
lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4835_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4835_, 3, v_l_4637_);
lean_ctor_set(v_reuseFailAlloc_4835_, 4, v_l_4805_);
v___x_4831_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4832_; 
v___x_4832_ = lean_nat_add(v___x_4784_, v_size_4807_);
if (lean_obj_tag(v_r_4806_) == 0)
{
lean_object* v_size_4833_; 
v_size_4833_ = lean_ctor_get(v_r_4806_, 0);
lean_inc(v_size_4833_);
v___y_4817_ = v___x_4831_;
v___y_4818_ = v___x_4832_;
v___y_4819_ = v_size_4833_;
goto v___jp_4816_;
}
else
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_unsigned_to_nat(0u);
v___y_4817_ = v___x_4831_;
v___y_4818_ = v___x_4832_;
v___y_4819_ = v___x_4834_;
goto v___jp_4816_;
}
}
}
}
}
else
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4848_; 
lean_del_object(v___x_4640_);
v___x_4844_ = lean_nat_add(v___x_4784_, v_size_4785_);
v___x_4845_ = lean_nat_add(v___x_4844_, v_size_4786_);
lean_dec(v_size_4786_);
v___x_4846_ = lean_nat_add(v___x_4844_, v_size_4802_);
lean_dec(v___x_4844_);
lean_inc_ref(v_l_4637_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 4, v_l_4789_);
lean_ctor_set(v___x_4800_, 3, v_l_4637_);
lean_ctor_set(v___x_4800_, 2, v_v_4636_);
lean_ctor_set(v___x_4800_, 1, v_k_4635_);
lean_ctor_set(v___x_4800_, 0, v___x_4846_);
v___x_4848_ = v___x_4800_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4846_);
lean_ctor_set(v_reuseFailAlloc_4861_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4861_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4861_, 3, v_l_4637_);
lean_ctor_set(v_reuseFailAlloc_4861_, 4, v_l_4789_);
v___x_4848_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
v_isSharedCheck_4855_ = !lean_is_exclusive(v_l_4637_);
if (v_isSharedCheck_4855_ == 0)
{
lean_object* v_unused_4856_; lean_object* v_unused_4857_; lean_object* v_unused_4858_; lean_object* v_unused_4859_; lean_object* v_unused_4860_; 
v_unused_4856_ = lean_ctor_get(v_l_4637_, 4);
lean_dec(v_unused_4856_);
v_unused_4857_ = lean_ctor_get(v_l_4637_, 3);
lean_dec(v_unused_4857_);
v_unused_4858_ = lean_ctor_get(v_l_4637_, 2);
lean_dec(v_unused_4858_);
v_unused_4859_ = lean_ctor_get(v_l_4637_, 1);
lean_dec(v_unused_4859_);
v_unused_4860_ = lean_ctor_get(v_l_4637_, 0);
lean_dec(v_unused_4860_);
v___x_4850_ = v_l_4637_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_dec(v_l_4637_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 4, v_r_4790_);
lean_ctor_set(v___x_4850_, 3, v___x_4848_);
lean_ctor_set(v___x_4850_, 2, v_v_4788_);
lean_ctor_set(v___x_4850_, 1, v_k_4787_);
lean_ctor_set(v___x_4850_, 0, v___x_4845_);
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4845_);
lean_ctor_set(v_reuseFailAlloc_4854_, 1, v_k_4787_);
lean_ctor_set(v_reuseFailAlloc_4854_, 2, v_v_4788_);
lean_ctor_set(v_reuseFailAlloc_4854_, 3, v___x_4848_);
lean_ctor_set(v_reuseFailAlloc_4854_, 4, v_r_4790_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4868_; 
v_l_4868_ = lean_ctor_get(v_impl_4783_, 3);
lean_inc(v_l_4868_);
if (lean_obj_tag(v_l_4868_) == 0)
{
lean_object* v_r_4869_; lean_object* v_k_4870_; lean_object* v_v_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4894_; 
v_r_4869_ = lean_ctor_get(v_impl_4783_, 4);
v_k_4870_ = lean_ctor_get(v_impl_4783_, 1);
v_v_4871_ = lean_ctor_get(v_impl_4783_, 2);
v_isSharedCheck_4894_ = !lean_is_exclusive(v_impl_4783_);
if (v_isSharedCheck_4894_ == 0)
{
lean_object* v_unused_4895_; lean_object* v_unused_4896_; 
v_unused_4895_ = lean_ctor_get(v_impl_4783_, 3);
lean_dec(v_unused_4895_);
v_unused_4896_ = lean_ctor_get(v_impl_4783_, 0);
lean_dec(v_unused_4896_);
v___x_4873_ = v_impl_4783_;
v_isShared_4874_ = v_isSharedCheck_4894_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_r_4869_);
lean_inc(v_v_4871_);
lean_inc(v_k_4870_);
lean_dec(v_impl_4783_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4894_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v_k_4875_; lean_object* v_v_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4890_; 
v_k_4875_ = lean_ctor_get(v_l_4868_, 1);
v_v_4876_ = lean_ctor_get(v_l_4868_, 2);
v_isSharedCheck_4890_ = !lean_is_exclusive(v_l_4868_);
if (v_isSharedCheck_4890_ == 0)
{
lean_object* v_unused_4891_; lean_object* v_unused_4892_; lean_object* v_unused_4893_; 
v_unused_4891_ = lean_ctor_get(v_l_4868_, 4);
lean_dec(v_unused_4891_);
v_unused_4892_ = lean_ctor_get(v_l_4868_, 3);
lean_dec(v_unused_4892_);
v_unused_4893_ = lean_ctor_get(v_l_4868_, 0);
lean_dec(v_unused_4893_);
v___x_4878_ = v_l_4868_;
v_isShared_4879_ = v_isSharedCheck_4890_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_v_4876_);
lean_inc(v_k_4875_);
lean_dec(v_l_4868_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4890_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4880_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4869_, 2);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 4, v_r_4869_);
lean_ctor_set(v___x_4878_, 3, v_r_4869_);
lean_ctor_set(v___x_4878_, 2, v_v_4636_);
lean_ctor_set(v___x_4878_, 1, v_k_4635_);
lean_ctor_set(v___x_4878_, 0, v___x_4784_);
v___x_4882_ = v___x_4878_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4784_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4889_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4889_, 3, v_r_4869_);
lean_ctor_set(v_reuseFailAlloc_4889_, 4, v_r_4869_);
v___x_4882_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4884_; 
lean_inc(v_r_4869_);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 3, v_r_4869_);
lean_ctor_set(v___x_4873_, 0, v___x_4784_);
v___x_4884_ = v___x_4873_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4784_);
lean_ctor_set(v_reuseFailAlloc_4888_, 1, v_k_4870_);
lean_ctor_set(v_reuseFailAlloc_4888_, 2, v_v_4871_);
lean_ctor_set(v_reuseFailAlloc_4888_, 3, v_r_4869_);
lean_ctor_set(v_reuseFailAlloc_4888_, 4, v_r_4869_);
v___x_4884_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
lean_object* v___x_4886_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v___x_4884_);
lean_ctor_set(v___x_4640_, 3, v___x_4882_);
lean_ctor_set(v___x_4640_, 2, v_v_4876_);
lean_ctor_set(v___x_4640_, 1, v_k_4875_);
lean_ctor_set(v___x_4640_, 0, v___x_4880_);
v___x_4886_ = v___x_4640_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4880_);
lean_ctor_set(v_reuseFailAlloc_4887_, 1, v_k_4875_);
lean_ctor_set(v_reuseFailAlloc_4887_, 2, v_v_4876_);
lean_ctor_set(v_reuseFailAlloc_4887_, 3, v___x_4882_);
lean_ctor_set(v_reuseFailAlloc_4887_, 4, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
}
}
else
{
lean_object* v_r_4897_; 
v_r_4897_ = lean_ctor_get(v_impl_4783_, 4);
lean_inc(v_r_4897_);
if (lean_obj_tag(v_r_4897_) == 0)
{
lean_object* v_k_4898_; lean_object* v_v_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4910_; 
v_k_4898_ = lean_ctor_get(v_impl_4783_, 1);
v_v_4899_ = lean_ctor_get(v_impl_4783_, 2);
v_isSharedCheck_4910_ = !lean_is_exclusive(v_impl_4783_);
if (v_isSharedCheck_4910_ == 0)
{
lean_object* v_unused_4911_; lean_object* v_unused_4912_; lean_object* v_unused_4913_; 
v_unused_4911_ = lean_ctor_get(v_impl_4783_, 4);
lean_dec(v_unused_4911_);
v_unused_4912_ = lean_ctor_get(v_impl_4783_, 3);
lean_dec(v_unused_4912_);
v_unused_4913_ = lean_ctor_get(v_impl_4783_, 0);
lean_dec(v_unused_4913_);
v___x_4901_ = v_impl_4783_;
v_isShared_4902_ = v_isSharedCheck_4910_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_v_4899_);
lean_inc(v_k_4898_);
lean_dec(v_impl_4783_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4910_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; lean_object* v___x_4905_; 
v___x_4903_ = lean_unsigned_to_nat(3u);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 4, v_l_4868_);
lean_ctor_set(v___x_4901_, 2, v_v_4636_);
lean_ctor_set(v___x_4901_, 1, v_k_4635_);
lean_ctor_set(v___x_4901_, 0, v___x_4784_);
v___x_4905_ = v___x_4901_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4784_);
lean_ctor_set(v_reuseFailAlloc_4909_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4909_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4909_, 3, v_l_4868_);
lean_ctor_set(v_reuseFailAlloc_4909_, 4, v_l_4868_);
v___x_4905_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
lean_object* v___x_4907_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v_r_4897_);
lean_ctor_set(v___x_4640_, 3, v___x_4905_);
lean_ctor_set(v___x_4640_, 2, v_v_4899_);
lean_ctor_set(v___x_4640_, 1, v_k_4898_);
lean_ctor_set(v___x_4640_, 0, v___x_4903_);
v___x_4907_ = v___x_4640_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4903_);
lean_ctor_set(v_reuseFailAlloc_4908_, 1, v_k_4898_);
lean_ctor_set(v_reuseFailAlloc_4908_, 2, v_v_4899_);
lean_ctor_set(v_reuseFailAlloc_4908_, 3, v___x_4905_);
lean_ctor_set(v_reuseFailAlloc_4908_, 4, v_r_4897_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
else
{
lean_object* v___x_4914_; lean_object* v___x_4916_; 
v___x_4914_ = lean_unsigned_to_nat(2u);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v_impl_4783_);
lean_ctor_set(v___x_4640_, 3, v_r_4897_);
lean_ctor_set(v___x_4640_, 0, v___x_4914_);
v___x_4916_ = v___x_4640_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4914_);
lean_ctor_set(v_reuseFailAlloc_4917_, 1, v_k_4635_);
lean_ctor_set(v_reuseFailAlloc_4917_, 2, v_v_4636_);
lean_ctor_set(v_reuseFailAlloc_4917_, 3, v_r_4897_);
lean_ctor_set(v_reuseFailAlloc_4917_, 4, v_impl_4783_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
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
lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4919_ = lean_unsigned_to_nat(1u);
v___x_4920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4919_);
lean_ctor_set(v___x_4920_, 1, v_k_4631_);
lean_ctor_set(v___x_4920_, 2, v_v_4632_);
lean_ctor_set(v___x_4920_, 3, v_t_4633_);
lean_ctor_set(v___x_4920_, 4, v_t_4633_);
return v___x_4920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object* v_as_4921_, size_t v_sz_4922_, size_t v_i_4923_, lean_object* v_b_4924_){
_start:
{
uint8_t v___x_4925_; 
v___x_4925_ = lean_usize_dec_lt(v_i_4923_, v_sz_4922_);
if (v___x_4925_ == 0)
{
return v_b_4924_;
}
else
{
lean_object* v_a_4926_; lean_object* v_fst_4927_; lean_object* v_snd_4928_; lean_object* v_r_4929_; size_t v___x_4930_; size_t v___x_4931_; 
v_a_4926_ = lean_array_uget_borrowed(v_as_4921_, v_i_4923_);
v_fst_4927_ = lean_ctor_get(v_a_4926_, 0);
v_snd_4928_ = lean_ctor_get(v_a_4926_, 1);
lean_inc(v_snd_4928_);
lean_inc(v_fst_4927_);
v_r_4929_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_fst_4927_, v_snd_4928_, v_b_4924_);
v___x_4930_ = ((size_t)1ULL);
v___x_4931_ = lean_usize_add(v_i_4923_, v___x_4930_);
v_i_4923_ = v___x_4931_;
v_b_4924_ = v_r_4929_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object* v_as_4933_, lean_object* v_sz_4934_, lean_object* v_i_4935_, lean_object* v_b_4936_){
_start:
{
size_t v_sz_boxed_4937_; size_t v_i_boxed_4938_; lean_object* v_res_4939_; 
v_sz_boxed_4937_ = lean_unbox_usize(v_sz_4934_);
lean_dec(v_sz_4934_);
v_i_boxed_4938_ = lean_unbox_usize(v_i_4935_);
lean_dec(v_i_4935_);
v_res_4939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v_as_4933_, v_sz_boxed_4937_, v_i_boxed_4938_, v_b_4936_);
lean_dec_ref(v_as_4933_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object* v_a_4942_, lean_object* v_x_4943_){
_start:
{
lean_object* v___y_4945_; 
if (lean_obj_tag(v_x_4943_) == 0)
{
lean_object* v___x_4948_; 
v___x_4948_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___y_4945_ = v___x_4948_;
goto v___jp_4944_;
}
else
{
lean_object* v_val_4949_; 
v_val_4949_ = lean_ctor_get(v_x_4943_, 0);
lean_inc(v_val_4949_);
lean_dec_ref(v_x_4943_);
v___y_4945_ = v_val_4949_;
goto v___jp_4944_;
}
v___jp_4944_:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4946_ = lean_array_push(v___y_4945_, v_a_4942_);
v___x_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
return v___x_4947_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_x_4952_){
_start:
{
if (lean_obj_tag(v_x_4952_) == 0)
{
lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v_val_4955_; lean_object* v___x_4956_; 
v___x_4953_ = lean_box(0);
v___x_4954_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4950_, v___x_4953_);
v_val_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_val_4955_);
lean_dec(v___x_4954_);
v___x_4956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4956_, 0, v_a_4951_);
lean_ctor_set(v___x_4956_, 1, v_val_4955_);
lean_ctor_set(v___x_4956_, 2, v_x_4952_);
return v___x_4956_;
}
else
{
lean_object* v_key_4957_; lean_object* v_value_4958_; lean_object* v_tail_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4974_; 
v_key_4957_ = lean_ctor_get(v_x_4952_, 0);
v_value_4958_ = lean_ctor_get(v_x_4952_, 1);
v_tail_4959_ = lean_ctor_get(v_x_4952_, 2);
v_isSharedCheck_4974_ = !lean_is_exclusive(v_x_4952_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4961_ = v_x_4952_;
v_isShared_4962_ = v_isSharedCheck_4974_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_tail_4959_);
lean_inc(v_value_4958_);
lean_inc(v_key_4957_);
lean_dec(v_x_4952_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4974_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
uint8_t v___x_4963_; 
v___x_4963_ = lean_name_eq(v_key_4957_, v_a_4951_);
if (v___x_4963_ == 0)
{
lean_object* v_tail_4964_; lean_object* v___x_4966_; 
v_tail_4964_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4950_, v_a_4951_, v_tail_4959_);
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 2, v_tail_4964_);
v___x_4966_ = v___x_4961_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_key_4957_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v_value_4958_);
lean_ctor_set(v_reuseFailAlloc_4967_, 2, v_tail_4964_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
else
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v_val_4970_; lean_object* v___x_4972_; 
lean_dec(v_key_4957_);
v___x_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4968_, 0, v_value_4958_);
v___x_4969_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4950_, v___x_4968_);
v_val_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_val_4970_);
lean_dec(v___x_4969_);
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v_val_4970_);
lean_ctor_set(v___x_4961_, 0, v_a_4951_);
v___x_4972_ = v___x_4961_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4951_);
lean_ctor_set(v_reuseFailAlloc_4973_, 1, v_val_4970_);
lean_ctor_set(v_reuseFailAlloc_4973_, 2, v_tail_4959_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_4975_; uint64_t v___x_4976_; 
v___x_4975_ = lean_unsigned_to_nat(1723u);
v___x_4976_ = lean_uint64_of_nat(v___x_4975_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_4977_, lean_object* v_x_4978_){
_start:
{
if (lean_obj_tag(v_x_4978_) == 0)
{
return v_x_4977_;
}
else
{
lean_object* v_key_4979_; lean_object* v_value_4980_; lean_object* v_tail_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_5007_; 
v_key_4979_ = lean_ctor_get(v_x_4978_, 0);
v_value_4980_ = lean_ctor_get(v_x_4978_, 1);
v_tail_4981_ = lean_ctor_get(v_x_4978_, 2);
v_isSharedCheck_5007_ = !lean_is_exclusive(v_x_4978_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_4983_ = v_x_4978_;
v_isShared_4984_ = v_isSharedCheck_5007_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_tail_4981_);
lean_inc(v_value_4980_);
lean_inc(v_key_4979_);
lean_dec(v_x_4978_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_5007_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4985_; uint64_t v___y_4987_; 
v___x_4985_ = lean_array_get_size(v_x_4977_);
if (lean_obj_tag(v_key_4979_) == 0)
{
uint64_t v___x_5005_; 
v___x_5005_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0);
v___y_4987_ = v___x_5005_;
goto v___jp_4986_;
}
else
{
uint64_t v_hash_5006_; 
v_hash_5006_ = lean_ctor_get_uint64(v_key_4979_, sizeof(void*)*2);
v___y_4987_ = v_hash_5006_;
goto v___jp_4986_;
}
v___jp_4986_:
{
uint64_t v___x_4988_; uint64_t v___x_4989_; uint64_t v_fold_4990_; uint64_t v___x_4991_; uint64_t v___x_4992_; uint64_t v___x_4993_; size_t v___x_4994_; size_t v___x_4995_; size_t v___x_4996_; size_t v___x_4997_; size_t v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5001_; 
v___x_4988_ = 32ULL;
v___x_4989_ = lean_uint64_shift_right(v___y_4987_, v___x_4988_);
v_fold_4990_ = lean_uint64_xor(v___y_4987_, v___x_4989_);
v___x_4991_ = 16ULL;
v___x_4992_ = lean_uint64_shift_right(v_fold_4990_, v___x_4991_);
v___x_4993_ = lean_uint64_xor(v_fold_4990_, v___x_4992_);
v___x_4994_ = lean_uint64_to_usize(v___x_4993_);
v___x_4995_ = lean_usize_of_nat(v___x_4985_);
v___x_4996_ = ((size_t)1ULL);
v___x_4997_ = lean_usize_sub(v___x_4995_, v___x_4996_);
v___x_4998_ = lean_usize_land(v___x_4994_, v___x_4997_);
v___x_4999_ = lean_array_uget_borrowed(v_x_4977_, v___x_4998_);
lean_inc(v___x_4999_);
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 2, v___x_4999_);
v___x_5001_ = v___x_4983_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_key_4979_);
lean_ctor_set(v_reuseFailAlloc_5004_, 1, v_value_4980_);
lean_ctor_set(v_reuseFailAlloc_5004_, 2, v___x_4999_);
v___x_5001_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
lean_object* v___x_5002_; 
v___x_5002_ = lean_array_uset(v_x_4977_, v___x_4998_, v___x_5001_);
v_x_4977_ = v___x_5002_;
v_x_4978_ = v_tail_4981_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object* v_i_5008_, lean_object* v_source_5009_, lean_object* v_target_5010_){
_start:
{
lean_object* v___x_5011_; uint8_t v___x_5012_; 
v___x_5011_ = lean_array_get_size(v_source_5009_);
v___x_5012_ = lean_nat_dec_lt(v_i_5008_, v___x_5011_);
if (v___x_5012_ == 0)
{
lean_dec_ref(v_source_5009_);
lean_dec(v_i_5008_);
return v_target_5010_;
}
else
{
lean_object* v_es_5013_; lean_object* v___x_5014_; lean_object* v_source_5015_; lean_object* v_target_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v_es_5013_ = lean_array_fget(v_source_5009_, v_i_5008_);
v___x_5014_ = lean_box(0);
v_source_5015_ = lean_array_fset(v_source_5009_, v_i_5008_, v___x_5014_);
v_target_5016_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_target_5010_, v_es_5013_);
v___x_5017_ = lean_unsigned_to_nat(1u);
v___x_5018_ = lean_nat_add(v_i_5008_, v___x_5017_);
lean_dec(v_i_5008_);
v_i_5008_ = v___x_5018_;
v_source_5009_ = v_source_5015_;
v_target_5010_ = v_target_5016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object* v_data_5020_){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v_nbuckets_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5021_ = lean_array_get_size(v_data_5020_);
v___x_5022_ = lean_unsigned_to_nat(2u);
v_nbuckets_5023_ = lean_nat_mul(v___x_5021_, v___x_5022_);
v___x_5024_ = lean_unsigned_to_nat(0u);
v___x_5025_ = lean_box(0);
v___x_5026_ = lean_mk_array(v_nbuckets_5023_, v___x_5025_);
v___x_5027_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_5024_, v_data_5020_, v___x_5026_);
return v___x_5027_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_5028_, lean_object* v_x_5029_){
_start:
{
if (lean_obj_tag(v_x_5029_) == 0)
{
uint8_t v___x_5030_; 
v___x_5030_ = 0;
return v___x_5030_;
}
else
{
lean_object* v_key_5031_; lean_object* v_tail_5032_; uint8_t v___x_5033_; 
v_key_5031_ = lean_ctor_get(v_x_5029_, 0);
v_tail_5032_ = lean_ctor_get(v_x_5029_, 2);
v___x_5033_ = lean_name_eq(v_key_5031_, v_a_5028_);
if (v___x_5033_ == 0)
{
v_x_5029_ = v_tail_5032_;
goto _start;
}
else
{
return v___x_5033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_5035_, lean_object* v_x_5036_){
_start:
{
uint8_t v_res_5037_; lean_object* v_r_5038_; 
v_res_5037_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5035_, v_x_5036_);
lean_dec(v_x_5036_);
lean_dec(v_a_5035_);
v_r_5038_ = lean_box(v_res_5037_);
return v_r_5038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_5039_, lean_object* v_m_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v___y_5043_; lean_object* v___y_5044_; size_t v___y_5045_; lean_object* v___y_5046_; lean_object* v_size_5049_; lean_object* v_buckets_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5097_; 
v_size_5049_ = lean_ctor_get(v_m_5040_, 0);
v_buckets_5050_ = lean_ctor_get(v_m_5040_, 1);
v_isSharedCheck_5097_ = !lean_is_exclusive(v_m_5040_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5052_ = v_m_5040_;
v_isShared_5053_ = v_isSharedCheck_5097_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_buckets_5050_);
lean_inc(v_size_5049_);
lean_dec(v_m_5040_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5097_;
goto v_resetjp_5051_;
}
v___jp_5042_:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = lean_array_uset(v___y_5043_, v___y_5045_, v___y_5044_);
v___x_5048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5048_, 0, v___y_5046_);
lean_ctor_set(v___x_5048_, 1, v___x_5047_);
return v___x_5048_;
}
v_resetjp_5051_:
{
lean_object* v___x_5054_; uint64_t v___y_5056_; 
v___x_5054_ = lean_array_get_size(v_buckets_5050_);
if (lean_obj_tag(v_a_5041_) == 0)
{
uint64_t v___x_5095_; 
v___x_5095_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0);
v___y_5056_ = v___x_5095_;
goto v___jp_5055_;
}
else
{
uint64_t v_hash_5096_; 
v_hash_5096_ = lean_ctor_get_uint64(v_a_5041_, sizeof(void*)*2);
v___y_5056_ = v_hash_5096_;
goto v___jp_5055_;
}
v___jp_5055_:
{
uint64_t v___x_5057_; uint64_t v___x_5058_; uint64_t v_fold_5059_; uint64_t v___x_5060_; uint64_t v___x_5061_; uint64_t v___x_5062_; size_t v___x_5063_; size_t v___x_5064_; size_t v___x_5065_; size_t v___x_5066_; size_t v___x_5067_; lean_object* v_bkt_5068_; uint8_t v___x_5069_; 
v___x_5057_ = 32ULL;
v___x_5058_ = lean_uint64_shift_right(v___y_5056_, v___x_5057_);
v_fold_5059_ = lean_uint64_xor(v___y_5056_, v___x_5058_);
v___x_5060_ = 16ULL;
v___x_5061_ = lean_uint64_shift_right(v_fold_5059_, v___x_5060_);
v___x_5062_ = lean_uint64_xor(v_fold_5059_, v___x_5061_);
v___x_5063_ = lean_uint64_to_usize(v___x_5062_);
v___x_5064_ = lean_usize_of_nat(v___x_5054_);
v___x_5065_ = ((size_t)1ULL);
v___x_5066_ = lean_usize_sub(v___x_5064_, v___x_5065_);
v___x_5067_ = lean_usize_land(v___x_5063_, v___x_5066_);
v_bkt_5068_ = lean_array_uget_borrowed(v_buckets_5050_, v___x_5067_);
v___x_5069_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5041_, v_bkt_5068_);
if (v___x_5069_ == 0)
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v_size_x27_5073_; lean_object* v___x_5074_; lean_object* v_buckets_x27_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; uint8_t v___x_5081_; 
v___x_5070_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_5071_ = lean_array_push(v___x_5070_, v_a_5039_);
v___x_5072_ = lean_unsigned_to_nat(1u);
v_size_x27_5073_ = lean_nat_add(v_size_5049_, v___x_5072_);
lean_dec(v_size_5049_);
lean_inc(v_bkt_5068_);
v___x_5074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5074_, 0, v_a_5041_);
lean_ctor_set(v___x_5074_, 1, v___x_5071_);
lean_ctor_set(v___x_5074_, 2, v_bkt_5068_);
v_buckets_x27_5075_ = lean_array_uset(v_buckets_5050_, v___x_5067_, v___x_5074_);
v___x_5076_ = lean_unsigned_to_nat(4u);
v___x_5077_ = lean_nat_mul(v_size_x27_5073_, v___x_5076_);
v___x_5078_ = lean_unsigned_to_nat(3u);
v___x_5079_ = lean_nat_div(v___x_5077_, v___x_5078_);
lean_dec(v___x_5077_);
v___x_5080_ = lean_array_get_size(v_buckets_x27_5075_);
v___x_5081_ = lean_nat_dec_le(v___x_5079_, v___x_5080_);
lean_dec(v___x_5079_);
if (v___x_5081_ == 0)
{
lean_object* v_val_5082_; lean_object* v___x_5084_; 
v_val_5082_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5075_);
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 1, v_val_5082_);
lean_ctor_set(v___x_5052_, 0, v_size_x27_5073_);
v___x_5084_ = v___x_5052_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_size_x27_5073_);
lean_ctor_set(v_reuseFailAlloc_5085_, 1, v_val_5082_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
else
{
lean_object* v___x_5087_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 1, v_buckets_x27_5075_);
lean_ctor_set(v___x_5052_, 0, v_size_x27_5073_);
v___x_5087_ = v___x_5052_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_size_x27_5073_);
lean_ctor_set(v_reuseFailAlloc_5088_, 1, v_buckets_x27_5075_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
else
{
lean_object* v___x_5089_; lean_object* v_buckets_x27_5090_; lean_object* v_bkt_x27_5091_; uint8_t v___x_5092_; 
lean_inc(v_bkt_5068_);
lean_del_object(v___x_5052_);
v___x_5089_ = lean_box(0);
v_buckets_x27_5090_ = lean_array_uset(v_buckets_5050_, v___x_5067_, v___x_5089_);
lean_inc(v_a_5041_);
v_bkt_x27_5091_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5039_, v_a_5041_, v_bkt_5068_);
v___x_5092_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5041_, v_bkt_x27_5091_);
lean_dec(v_a_5041_);
if (v___x_5092_ == 0)
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = lean_unsigned_to_nat(1u);
v___x_5094_ = lean_nat_sub(v_size_5049_, v___x_5093_);
lean_dec(v_size_5049_);
v___y_5043_ = v_buckets_x27_5090_;
v___y_5044_ = v_bkt_x27_5091_;
v___y_5045_ = v___x_5067_;
v___y_5046_ = v___x_5094_;
goto v___jp_5042_;
}
else
{
v___y_5043_ = v_buckets_x27_5090_;
v___y_5044_ = v_bkt_x27_5091_;
v___y_5045_ = v___x_5067_;
v___y_5046_ = v_size_5049_;
goto v___jp_5042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5098_, lean_object* v_as_5099_, size_t v_sz_5100_, size_t v_i_5101_, lean_object* v_b_5102_){
_start:
{
uint8_t v___x_5103_; 
v___x_5103_ = lean_usize_dec_lt(v_i_5101_, v_sz_5100_);
if (v___x_5103_ == 0)
{
lean_dec_ref(v_key_5098_);
return v_b_5102_;
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; size_t v___x_5107_; size_t v___x_5108_; 
v_a_5104_ = lean_array_uget_borrowed(v_as_5099_, v_i_5101_);
lean_inc_ref(v_key_5098_);
lean_inc_n(v_a_5104_, 2);
v___x_5105_ = lean_apply_1(v_key_5098_, v_a_5104_);
v___x_5106_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5104_, v_b_5102_, v___x_5105_);
v___x_5107_ = ((size_t)1ULL);
v___x_5108_ = lean_usize_add(v_i_5101_, v___x_5107_);
v_i_5101_ = v___x_5108_;
v_b_5102_ = v___x_5106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5110_, lean_object* v_as_5111_, lean_object* v_sz_5112_, lean_object* v_i_5113_, lean_object* v_b_5114_){
_start:
{
size_t v_sz_boxed_5115_; size_t v_i_boxed_5116_; lean_object* v_res_5117_; 
v_sz_boxed_5115_ = lean_unbox_usize(v_sz_5112_);
lean_dec(v_sz_5112_);
v_i_boxed_5116_ = lean_unbox_usize(v_i_5113_);
lean_dec(v_i_5113_);
v_res_5117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5110_, v_as_5111_, v_sz_boxed_5115_, v_i_boxed_5116_, v_b_5114_);
lean_dec_ref(v_as_5111_);
return v_res_5117_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5118_ = lean_box(0);
v___x_5119_ = lean_unsigned_to_nat(16u);
v___x_5120_ = lean_mk_array(v___x_5119_, v___x_5118_);
return v___x_5120_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v_groups_5123_; 
v___x_5121_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5122_ = lean_unsigned_to_nat(0u);
v_groups_5123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5123_, 0, v___x_5122_);
lean_ctor_set(v_groups_5123_, 1, v___x_5121_);
return v_groups_5123_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5124_, lean_object* v_xs_5125_){
_start:
{
lean_object* v_groups_5126_; size_t v_sz_5127_; size_t v___x_5128_; lean_object* v___x_5129_; 
v_groups_5126_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5127_ = lean_array_size(v_xs_5125_);
v___x_5128_ = ((size_t)0ULL);
v___x_5129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5124_, v_xs_5125_, v_sz_5127_, v___x_5128_, v_groups_5126_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5130_, lean_object* v_xs_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5130_, v_xs_5131_);
lean_dec_ref(v_xs_5131_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5134_){
_start:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5136_ = lean_unsigned_to_nat(0u);
v___x_5137_ = lean_array_get_size(v_infos_5134_);
v___x_5138_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5134_, v___x_5136_, v___x_5137_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5167_; 
v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5141_ = v___x_5138_;
v_isShared_5142_ = v_isSharedCheck_5167_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_5138_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5167_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___y_5144_; lean_object* v___f_5153_; lean_object* v___x_5154_; lean_object* v_size_5155_; lean_object* v_buckets_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; 
v___f_5153_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5154_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5153_, v_a_5139_);
v_size_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_size_5155_);
v_buckets_5156_ = lean_ctor_get(v___x_5154_, 1);
lean_inc_ref(v_buckets_5156_);
lean_dec_ref(v___x_5154_);
v___x_5157_ = lean_mk_empty_array_with_capacity(v_size_5155_);
lean_dec(v_size_5155_);
v___x_5158_ = lean_array_get_size(v_buckets_5156_);
v___x_5159_ = lean_nat_dec_lt(v___x_5136_, v___x_5158_);
if (v___x_5159_ == 0)
{
lean_dec_ref(v_buckets_5156_);
v___y_5144_ = v___x_5157_;
goto v___jp_5143_;
}
else
{
uint8_t v___x_5160_; 
v___x_5160_ = lean_nat_dec_le(v___x_5158_, v___x_5158_);
if (v___x_5160_ == 0)
{
if (v___x_5159_ == 0)
{
lean_dec_ref(v_buckets_5156_);
v___y_5144_ = v___x_5157_;
goto v___jp_5143_;
}
else
{
size_t v___x_5161_; size_t v___x_5162_; lean_object* v___x_5163_; 
v___x_5161_ = ((size_t)0ULL);
v___x_5162_ = lean_usize_of_nat(v___x_5158_);
v___x_5163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5156_, v___x_5161_, v___x_5162_, v___x_5157_);
lean_dec_ref(v_buckets_5156_);
v___y_5144_ = v___x_5163_;
goto v___jp_5143_;
}
}
else
{
size_t v___x_5164_; size_t v___x_5165_; lean_object* v___x_5166_; 
v___x_5164_ = ((size_t)0ULL);
v___x_5165_ = lean_usize_of_nat(v___x_5158_);
v___x_5166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5156_, v___x_5164_, v___x_5165_, v___x_5157_);
lean_dec_ref(v_buckets_5156_);
v___y_5144_ = v___x_5166_;
goto v___jp_5143_;
}
}
v___jp_5143_:
{
lean_object* v_r_5145_; size_t v_sz_5146_; size_t v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5151_; 
v_r_5145_ = lean_box(1);
v_sz_5146_ = lean_array_size(v___y_5144_);
v___x_5147_ = ((size_t)0ULL);
v___x_5148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5144_, v_sz_5146_, v___x_5147_, v_r_5145_);
lean_dec_ref(v___y_5144_);
v___x_5149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5149_, 0, v_a_5139_);
lean_ctor_set(v___x_5149_, 1, v___x_5148_);
if (v_isShared_5142_ == 0)
{
lean_ctor_set(v___x_5141_, 0, v___x_5149_);
v___x_5151_ = v___x_5141_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5149_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5175_; 
v_a_5168_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5170_ = v___x_5138_;
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5138_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5173_; 
if (v_isShared_5171_ == 0)
{
v___x_5173_ = v___x_5170_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_a_5168_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5176_);
lean_dec_ref(v_infos_5176_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5179_, lean_object* v_k_5180_, lean_object* v_v_5181_, lean_object* v_t_5182_, lean_object* v_hl_5183_){
_start:
{
lean_object* v___x_5184_; 
v___x_5184_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5180_, v_v_5181_, v_t_5182_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5185_, lean_object* v_key_5186_, lean_object* v_xs_5187_){
_start:
{
lean_object* v___x_5188_; 
v___x_5188_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5186_, v_xs_5187_);
return v___x_5188_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5189_, lean_object* v_key_5190_, lean_object* v_xs_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5189_, v_key_5190_, v_xs_5191_);
lean_dec_ref(v_xs_5191_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5193_, lean_object* v_a_5194_, lean_object* v_m_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v___x_5197_; 
v___x_5197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5194_, v_m_5195_, v_a_5196_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5198_, lean_object* v_key_5199_, lean_object* v_as_5200_, size_t v_sz_5201_, size_t v_i_5202_, lean_object* v_b_5203_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5199_, v_as_5200_, v_sz_5201_, v_i_5202_, v_b_5203_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5205_, lean_object* v_key_5206_, lean_object* v_as_5207_, lean_object* v_sz_5208_, lean_object* v_i_5209_, lean_object* v_b_5210_){
_start:
{
size_t v_sz_boxed_5211_; size_t v_i_boxed_5212_; lean_object* v_res_5213_; 
v_sz_boxed_5211_ = lean_unbox_usize(v_sz_5208_);
lean_dec(v_sz_5208_);
v_i_boxed_5212_ = lean_unbox_usize(v_i_5209_);
lean_dec(v_i_5209_);
v_res_5213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5205_, v_key_5206_, v_as_5207_, v_sz_boxed_5211_, v_i_boxed_5212_, v_b_5210_);
lean_dec_ref(v_as_5207_);
return v_res_5213_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5214_, lean_object* v_a_5215_, lean_object* v_x_5216_){
_start:
{
uint8_t v___x_5217_; 
v___x_5217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5215_, v_x_5216_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5218_, lean_object* v_a_5219_, lean_object* v_x_5220_){
_start:
{
uint8_t v_res_5221_; lean_object* v_r_5222_; 
v_res_5221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5218_, v_a_5219_, v_x_5220_);
lean_dec(v_x_5220_);
lean_dec(v_a_5219_);
v_r_5222_ = lean_box(v_res_5221_);
return v_r_5222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5223_, lean_object* v_data_5224_){
_start:
{
lean_object* v___x_5225_; 
v___x_5225_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5224_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_x_5229_){
_start:
{
lean_object* v___x_5230_; 
v___x_5230_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5227_, v_a_5228_, v_x_5229_);
return v___x_5230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5231_, lean_object* v_i_5232_, lean_object* v_source_5233_, lean_object* v_target_5234_){
_start:
{
lean_object* v___x_5235_; 
v___x_5235_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5232_, v_source_5233_, v_target_5234_);
return v___x_5235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5236_, lean_object* v_x_5237_, lean_object* v_x_5238_){
_start:
{
lean_object* v___x_5239_; 
v___x_5239_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5237_, v_x_5238_);
return v___x_5239_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5240_){
_start:
{
lean_object* v_isSetupFailure_x3f_5241_; 
v_isSetupFailure_x3f_5241_ = lean_ctor_get(v_i_5240_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5241_) == 0)
{
uint8_t v___x_5242_; 
v___x_5242_ = 0;
return v___x_5242_;
}
else
{
lean_object* v_val_5243_; uint8_t v___x_5244_; 
v_val_5243_ = lean_ctor_get(v_isSetupFailure_x3f_5241_, 0);
v___x_5244_ = lean_unbox(v_val_5243_);
if (v___x_5244_ == 0)
{
uint8_t v___x_5245_; 
v___x_5245_ = 1;
return v___x_5245_;
}
else
{
uint8_t v___x_5246_; 
v___x_5246_ = 0;
return v___x_5246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5247_){
_start:
{
uint8_t v_res_5248_; lean_object* v_r_5249_; 
v_res_5248_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5247_);
lean_dec_ref(v_i_5247_);
v_r_5249_ = lean_box(v_res_5248_);
return v_r_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5255_, lean_object* v_path_5256_, lean_object* v_ilean_5257_){
_start:
{
lean_object* v_module_5259_; lean_object* v_directImports_5260_; lean_object* v_references_5261_; lean_object* v_decls_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5314_; 
v_module_5259_ = lean_ctor_get(v_ilean_5257_, 1);
v_directImports_5260_ = lean_ctor_get(v_ilean_5257_, 2);
v_references_5261_ = lean_ctor_get(v_ilean_5257_, 3);
v_decls_5262_ = lean_ctor_get(v_ilean_5257_, 4);
v_isSharedCheck_5314_ = !lean_is_exclusive(v_ilean_5257_);
if (v_isSharedCheck_5314_ == 0)
{
lean_object* v_unused_5315_; 
v_unused_5315_ = lean_ctor_get(v_ilean_5257_, 0);
lean_dec(v_unused_5315_);
v___x_5264_ = v_ilean_5257_;
v_isShared_5265_ = v_isSharedCheck_5314_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_decls_5262_);
lean_inc(v_references_5261_);
lean_inc(v_directImports_5260_);
lean_inc(v_module_5259_);
lean_dec(v_ilean_5257_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5314_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5266_; 
lean_inc(v_module_5259_);
v___x_5266_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5259_);
if (lean_obj_tag(v___x_5266_) == 0)
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5305_; 
v_a_5267_ = lean_ctor_get(v___x_5266_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5269_ = v___x_5266_;
v_isShared_5270_ = v_isSharedCheck_5305_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5266_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5305_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
if (lean_obj_tag(v_a_5267_) == 1)
{
lean_object* v_val_5271_; lean_object* v___x_5272_; 
lean_del_object(v___x_5269_);
v_val_5271_ = lean_ctor_get(v_a_5267_, 0);
lean_inc(v_val_5271_);
lean_dec_ref(v_a_5267_);
v___x_5272_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5260_);
lean_dec_ref(v_directImports_5260_);
if (lean_obj_tag(v___x_5272_) == 0)
{
lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5293_; 
v_a_5273_ = lean_ctor_get(v___x_5272_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5272_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5275_ = v___x_5272_;
v_isShared_5276_ = v_isSharedCheck_5293_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v___x_5272_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5293_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v_ileans_5277_; lean_object* v_workers_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5292_; 
v_ileans_5277_ = lean_ctor_get(v_self_5255_, 0);
v_workers_5278_ = lean_ctor_get(v_self_5255_, 1);
v_isSharedCheck_5292_ = !lean_is_exclusive(v_self_5255_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5280_ = v_self_5255_;
v_isShared_5281_ = v_isSharedCheck_5292_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_workers_5278_);
lean_inc(v_ileans_5277_);
lean_dec(v_self_5255_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5292_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v___x_5283_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 2, v_a_5273_);
lean_ctor_set(v___x_5264_, 1, v_path_5256_);
lean_ctor_set(v___x_5264_, 0, v_val_5271_);
v___x_5283_ = v___x_5264_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_val_5271_);
lean_ctor_set(v_reuseFailAlloc_5291_, 1, v_path_5256_);
lean_ctor_set(v_reuseFailAlloc_5291_, 2, v_a_5273_);
lean_ctor_set(v_reuseFailAlloc_5291_, 3, v_references_5261_);
lean_ctor_set(v_reuseFailAlloc_5291_, 4, v_decls_5262_);
v___x_5283_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
lean_object* v___x_5284_; lean_object* v___x_5286_; 
v___x_5284_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5259_, v___x_5283_, v_ileans_5277_);
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 0, v___x_5284_);
v___x_5286_ = v___x_5280_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v___x_5284_);
lean_ctor_set(v_reuseFailAlloc_5290_, 1, v_workers_5278_);
v___x_5286_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
lean_object* v___x_5288_; 
if (v_isShared_5276_ == 0)
{
lean_ctor_set(v___x_5275_, 0, v___x_5286_);
v___x_5288_ = v___x_5275_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v___x_5286_);
v___x_5288_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
return v___x_5288_;
}
}
}
}
}
}
else
{
lean_object* v_a_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5301_; 
lean_dec(v_val_5271_);
lean_del_object(v___x_5264_);
lean_dec(v_decls_5262_);
lean_dec(v_references_5261_);
lean_dec(v_module_5259_);
lean_dec_ref(v_path_5256_);
lean_dec_ref(v_self_5255_);
v_a_5294_ = lean_ctor_get(v___x_5272_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5272_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5296_ = v___x_5272_;
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_a_5294_);
lean_dec(v___x_5272_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v___x_5299_; 
if (v_isShared_5297_ == 0)
{
v___x_5299_ = v___x_5296_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5294_);
v___x_5299_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
return v___x_5299_;
}
}
}
}
else
{
lean_object* v___x_5303_; 
lean_dec(v_a_5267_);
lean_del_object(v___x_5264_);
lean_dec(v_decls_5262_);
lean_dec(v_references_5261_);
lean_dec_ref(v_directImports_5260_);
lean_dec(v_module_5259_);
lean_dec_ref(v_path_5256_);
if (v_isShared_5270_ == 0)
{
lean_ctor_set(v___x_5269_, 0, v_self_5255_);
v___x_5303_ = v___x_5269_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_self_5255_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
else
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5313_; 
lean_del_object(v___x_5264_);
lean_dec(v_decls_5262_);
lean_dec(v_references_5261_);
lean_dec_ref(v_directImports_5260_);
lean_dec(v_module_5259_);
lean_dec_ref(v_path_5256_);
lean_dec_ref(v_self_5255_);
v_a_5306_ = lean_ctor_get(v___x_5266_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5308_ = v___x_5266_;
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5266_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5311_; 
if (v_isShared_5309_ == 0)
{
v___x_5311_ = v___x_5308_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_a_5306_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5316_, lean_object* v_path_5317_, lean_object* v_ilean_5318_, lean_object* v_a_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l_Lean_Server_References_addIlean(v_self_5316_, v_path_5317_, v_ilean_5318_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5321_, lean_object* v_t_5322_){
_start:
{
if (lean_obj_tag(v_t_5322_) == 0)
{
lean_object* v_v_5323_; lean_object* v_k_5324_; lean_object* v_l_5325_; lean_object* v_r_5326_; lean_object* v_ileanPath_5327_; uint8_t v___x_5328_; 
v_v_5323_ = lean_ctor_get(v_t_5322_, 2);
lean_inc(v_v_5323_);
v_k_5324_ = lean_ctor_get(v_t_5322_, 1);
lean_inc(v_k_5324_);
v_l_5325_ = lean_ctor_get(v_t_5322_, 3);
lean_inc(v_l_5325_);
v_r_5326_ = lean_ctor_get(v_t_5322_, 4);
lean_inc(v_r_5326_);
lean_dec_ref(v_t_5322_);
v_ileanPath_5327_ = lean_ctor_get(v_v_5323_, 1);
v___x_5328_ = lean_string_dec_eq(v_ileanPath_5327_, v_path_5321_);
if (v___x_5328_ == 0)
{
lean_object* v_impl_5329_; lean_object* v_impl_5330_; lean_object* v___x_5331_; 
lean_dec(v_k_5324_);
lean_dec(v_v_5323_);
v_impl_5329_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5321_, v_l_5325_);
v_impl_5330_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5321_, v_r_5326_);
v___x_5331_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5329_, v_impl_5330_);
return v___x_5331_;
}
else
{
lean_object* v_impl_5332_; lean_object* v_impl_5333_; lean_object* v___x_5334_; 
v_impl_5332_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5321_, v_l_5325_);
v_impl_5333_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5321_, v_r_5326_);
v___x_5334_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5324_, v_v_5323_, v_impl_5332_, v_impl_5333_);
return v___x_5334_;
}
}
else
{
return v_t_5322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5335_, lean_object* v_t_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5335_, v_t_5336_);
lean_dec_ref(v_path_5335_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5338_, lean_object* v_t_5339_){
_start:
{
if (lean_obj_tag(v_t_5339_) == 0)
{
lean_object* v_k_5340_; lean_object* v_v_5341_; lean_object* v_l_5342_; lean_object* v_r_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5997_; 
v_k_5340_ = lean_ctor_get(v_t_5339_, 1);
v_v_5341_ = lean_ctor_get(v_t_5339_, 2);
v_l_5342_ = lean_ctor_get(v_t_5339_, 3);
v_r_5343_ = lean_ctor_get(v_t_5339_, 4);
v_isSharedCheck_5997_ = !lean_is_exclusive(v_t_5339_);
if (v_isSharedCheck_5997_ == 0)
{
lean_object* v_unused_5998_; 
v_unused_5998_ = lean_ctor_get(v_t_5339_, 0);
lean_dec(v_unused_5998_);
v___x_5345_ = v_t_5339_;
v_isShared_5346_ = v_isSharedCheck_5997_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_r_5343_);
lean_inc(v_l_5342_);
lean_inc(v_v_5341_);
lean_inc(v_k_5340_);
lean_dec(v_t_5339_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5997_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
uint8_t v___x_5347_; 
v___x_5347_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5338_, v_k_5340_);
switch(v___x_5347_)
{
case 0:
{
lean_object* v_impl_5348_; lean_object* v___x_5349_; 
v_impl_5348_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5338_, v_l_5342_);
v___x_5349_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5348_) == 0)
{
if (lean_obj_tag(v_r_5343_) == 0)
{
lean_object* v_size_5350_; lean_object* v_size_5351_; lean_object* v_k_5352_; lean_object* v_v_5353_; lean_object* v_l_5354_; lean_object* v_r_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; uint8_t v___x_5358_; 
v_size_5350_ = lean_ctor_get(v_impl_5348_, 0);
lean_inc(v_size_5350_);
v_size_5351_ = lean_ctor_get(v_r_5343_, 0);
v_k_5352_ = lean_ctor_get(v_r_5343_, 1);
v_v_5353_ = lean_ctor_get(v_r_5343_, 2);
v_l_5354_ = lean_ctor_get(v_r_5343_, 3);
lean_inc(v_l_5354_);
v_r_5355_ = lean_ctor_get(v_r_5343_, 4);
v___x_5356_ = lean_unsigned_to_nat(3u);
v___x_5357_ = lean_nat_mul(v___x_5356_, v_size_5350_);
v___x_5358_ = lean_nat_dec_lt(v___x_5357_, v_size_5351_);
lean_dec(v___x_5357_);
if (v___x_5358_ == 0)
{
lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5362_; 
lean_dec(v_l_5354_);
v___x_5359_ = lean_nat_add(v___x_5349_, v_size_5350_);
lean_dec(v_size_5350_);
v___x_5360_ = lean_nat_add(v___x_5359_, v_size_5351_);
lean_dec(v___x_5359_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 3, v_impl_5348_);
lean_ctor_set(v___x_5345_, 0, v___x_5360_);
v___x_5362_ = v___x_5345_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5360_);
lean_ctor_set(v_reuseFailAlloc_5363_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5363_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5363_, 3, v_impl_5348_);
lean_ctor_set(v_reuseFailAlloc_5363_, 4, v_r_5343_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
else
{
lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5427_; 
lean_inc(v_r_5355_);
lean_inc(v_v_5353_);
lean_inc(v_k_5352_);
lean_inc(v_size_5351_);
v_isSharedCheck_5427_ = !lean_is_exclusive(v_r_5343_);
if (v_isSharedCheck_5427_ == 0)
{
lean_object* v_unused_5428_; lean_object* v_unused_5429_; lean_object* v_unused_5430_; lean_object* v_unused_5431_; lean_object* v_unused_5432_; 
v_unused_5428_ = lean_ctor_get(v_r_5343_, 4);
lean_dec(v_unused_5428_);
v_unused_5429_ = lean_ctor_get(v_r_5343_, 3);
lean_dec(v_unused_5429_);
v_unused_5430_ = lean_ctor_get(v_r_5343_, 2);
lean_dec(v_unused_5430_);
v_unused_5431_ = lean_ctor_get(v_r_5343_, 1);
lean_dec(v_unused_5431_);
v_unused_5432_ = lean_ctor_get(v_r_5343_, 0);
lean_dec(v_unused_5432_);
v___x_5365_ = v_r_5343_;
v_isShared_5366_ = v_isSharedCheck_5427_;
goto v_resetjp_5364_;
}
else
{
lean_dec(v_r_5343_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5427_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v_size_5367_; lean_object* v_k_5368_; lean_object* v_v_5369_; lean_object* v_l_5370_; lean_object* v_r_5371_; lean_object* v_size_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; uint8_t v___x_5375_; 
v_size_5367_ = lean_ctor_get(v_l_5354_, 0);
v_k_5368_ = lean_ctor_get(v_l_5354_, 1);
v_v_5369_ = lean_ctor_get(v_l_5354_, 2);
v_l_5370_ = lean_ctor_get(v_l_5354_, 3);
v_r_5371_ = lean_ctor_get(v_l_5354_, 4);
v_size_5372_ = lean_ctor_get(v_r_5355_, 0);
v___x_5373_ = lean_unsigned_to_nat(2u);
v___x_5374_ = lean_nat_mul(v___x_5373_, v_size_5372_);
v___x_5375_ = lean_nat_dec_lt(v_size_5367_, v___x_5374_);
lean_dec(v___x_5374_);
if (v___x_5375_ == 0)
{
lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5403_; 
lean_inc(v_r_5371_);
lean_inc(v_l_5370_);
lean_inc(v_v_5369_);
lean_inc(v_k_5368_);
v_isSharedCheck_5403_ = !lean_is_exclusive(v_l_5354_);
if (v_isSharedCheck_5403_ == 0)
{
lean_object* v_unused_5404_; lean_object* v_unused_5405_; lean_object* v_unused_5406_; lean_object* v_unused_5407_; lean_object* v_unused_5408_; 
v_unused_5404_ = lean_ctor_get(v_l_5354_, 4);
lean_dec(v_unused_5404_);
v_unused_5405_ = lean_ctor_get(v_l_5354_, 3);
lean_dec(v_unused_5405_);
v_unused_5406_ = lean_ctor_get(v_l_5354_, 2);
lean_dec(v_unused_5406_);
v_unused_5407_ = lean_ctor_get(v_l_5354_, 1);
lean_dec(v_unused_5407_);
v_unused_5408_ = lean_ctor_get(v_l_5354_, 0);
lean_dec(v_unused_5408_);
v___x_5377_ = v_l_5354_;
v_isShared_5378_ = v_isSharedCheck_5403_;
goto v_resetjp_5376_;
}
else
{
lean_dec(v_l_5354_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5403_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___y_5382_; lean_object* v___y_5383_; lean_object* v___y_5384_; lean_object* v___y_5393_; 
v___x_5379_ = lean_nat_add(v___x_5349_, v_size_5350_);
lean_dec(v_size_5350_);
v___x_5380_ = lean_nat_add(v___x_5379_, v_size_5351_);
lean_dec(v_size_5351_);
if (lean_obj_tag(v_l_5370_) == 0)
{
lean_object* v_size_5401_; 
v_size_5401_ = lean_ctor_get(v_l_5370_, 0);
lean_inc(v_size_5401_);
v___y_5393_ = v_size_5401_;
goto v___jp_5392_;
}
else
{
lean_object* v___x_5402_; 
v___x_5402_ = lean_unsigned_to_nat(0u);
v___y_5393_ = v___x_5402_;
goto v___jp_5392_;
}
v___jp_5381_:
{
lean_object* v___x_5385_; lean_object* v___x_5387_; 
v___x_5385_ = lean_nat_add(v___y_5382_, v___y_5384_);
lean_dec(v___y_5384_);
lean_dec(v___y_5382_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 4, v_r_5355_);
lean_ctor_set(v___x_5377_, 3, v_r_5371_);
lean_ctor_set(v___x_5377_, 2, v_v_5353_);
lean_ctor_set(v___x_5377_, 1, v_k_5352_);
lean_ctor_set(v___x_5377_, 0, v___x_5385_);
v___x_5387_ = v___x_5377_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v___x_5385_);
lean_ctor_set(v_reuseFailAlloc_5391_, 1, v_k_5352_);
lean_ctor_set(v_reuseFailAlloc_5391_, 2, v_v_5353_);
lean_ctor_set(v_reuseFailAlloc_5391_, 3, v_r_5371_);
lean_ctor_set(v_reuseFailAlloc_5391_, 4, v_r_5355_);
v___x_5387_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
lean_object* v___x_5389_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v___x_5387_);
lean_ctor_set(v___x_5365_, 3, v___y_5383_);
lean_ctor_set(v___x_5365_, 2, v_v_5369_);
lean_ctor_set(v___x_5365_, 1, v_k_5368_);
lean_ctor_set(v___x_5365_, 0, v___x_5380_);
v___x_5389_ = v___x_5365_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v___x_5380_);
lean_ctor_set(v_reuseFailAlloc_5390_, 1, v_k_5368_);
lean_ctor_set(v_reuseFailAlloc_5390_, 2, v_v_5369_);
lean_ctor_set(v_reuseFailAlloc_5390_, 3, v___y_5383_);
lean_ctor_set(v_reuseFailAlloc_5390_, 4, v___x_5387_);
v___x_5389_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
return v___x_5389_;
}
}
}
v___jp_5392_:
{
lean_object* v___x_5394_; lean_object* v___x_5396_; 
v___x_5394_ = lean_nat_add(v___x_5379_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec(v___x_5379_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v_l_5370_);
lean_ctor_set(v___x_5345_, 3, v_impl_5348_);
lean_ctor_set(v___x_5345_, 0, v___x_5394_);
v___x_5396_ = v___x_5345_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5394_);
lean_ctor_set(v_reuseFailAlloc_5400_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5400_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5400_, 3, v_impl_5348_);
lean_ctor_set(v_reuseFailAlloc_5400_, 4, v_l_5370_);
v___x_5396_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
lean_object* v___x_5397_; 
v___x_5397_ = lean_nat_add(v___x_5349_, v_size_5372_);
if (lean_obj_tag(v_r_5371_) == 0)
{
lean_object* v_size_5398_; 
v_size_5398_ = lean_ctor_get(v_r_5371_, 0);
lean_inc(v_size_5398_);
v___y_5382_ = v___x_5397_;
v___y_5383_ = v___x_5396_;
v___y_5384_ = v_size_5398_;
goto v___jp_5381_;
}
else
{
lean_object* v___x_5399_; 
v___x_5399_ = lean_unsigned_to_nat(0u);
v___y_5382_ = v___x_5397_;
v___y_5383_ = v___x_5396_;
v___y_5384_ = v___x_5399_;
goto v___jp_5381_;
}
}
}
}
}
else
{
lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5413_; 
lean_del_object(v___x_5345_);
v___x_5409_ = lean_nat_add(v___x_5349_, v_size_5350_);
lean_dec(v_size_5350_);
v___x_5410_ = lean_nat_add(v___x_5409_, v_size_5351_);
lean_dec(v_size_5351_);
v___x_5411_ = lean_nat_add(v___x_5409_, v_size_5367_);
lean_dec(v___x_5409_);
lean_inc_ref(v_impl_5348_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v_l_5354_);
lean_ctor_set(v___x_5365_, 3, v_impl_5348_);
lean_ctor_set(v___x_5365_, 2, v_v_5341_);
lean_ctor_set(v___x_5365_, 1, v_k_5340_);
lean_ctor_set(v___x_5365_, 0, v___x_5411_);
v___x_5413_ = v___x_5365_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v___x_5411_);
lean_ctor_set(v_reuseFailAlloc_5426_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5426_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5426_, 3, v_impl_5348_);
lean_ctor_set(v_reuseFailAlloc_5426_, 4, v_l_5354_);
v___x_5413_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5420_; 
v_isSharedCheck_5420_ = !lean_is_exclusive(v_impl_5348_);
if (v_isSharedCheck_5420_ == 0)
{
lean_object* v_unused_5421_; lean_object* v_unused_5422_; lean_object* v_unused_5423_; lean_object* v_unused_5424_; lean_object* v_unused_5425_; 
v_unused_5421_ = lean_ctor_get(v_impl_5348_, 4);
lean_dec(v_unused_5421_);
v_unused_5422_ = lean_ctor_get(v_impl_5348_, 3);
lean_dec(v_unused_5422_);
v_unused_5423_ = lean_ctor_get(v_impl_5348_, 2);
lean_dec(v_unused_5423_);
v_unused_5424_ = lean_ctor_get(v_impl_5348_, 1);
lean_dec(v_unused_5424_);
v_unused_5425_ = lean_ctor_get(v_impl_5348_, 0);
lean_dec(v_unused_5425_);
v___x_5415_ = v_impl_5348_;
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
else
{
lean_dec(v_impl_5348_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v___x_5418_; 
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 4, v_r_5355_);
lean_ctor_set(v___x_5415_, 3, v___x_5413_);
lean_ctor_set(v___x_5415_, 2, v_v_5353_);
lean_ctor_set(v___x_5415_, 1, v_k_5352_);
lean_ctor_set(v___x_5415_, 0, v___x_5410_);
v___x_5418_ = v___x_5415_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5410_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v_k_5352_);
lean_ctor_set(v_reuseFailAlloc_5419_, 2, v_v_5353_);
lean_ctor_set(v_reuseFailAlloc_5419_, 3, v___x_5413_);
lean_ctor_set(v_reuseFailAlloc_5419_, 4, v_r_5355_);
v___x_5418_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
return v___x_5418_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5433_; lean_object* v___x_5434_; lean_object* v___x_5436_; 
v_size_5433_ = lean_ctor_get(v_impl_5348_, 0);
lean_inc(v_size_5433_);
v___x_5434_ = lean_nat_add(v___x_5349_, v_size_5433_);
lean_dec(v_size_5433_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 3, v_impl_5348_);
lean_ctor_set(v___x_5345_, 0, v___x_5434_);
v___x_5436_ = v___x_5345_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5434_);
lean_ctor_set(v_reuseFailAlloc_5437_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5437_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5437_, 3, v_impl_5348_);
lean_ctor_set(v_reuseFailAlloc_5437_, 4, v_r_5343_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
else
{
if (lean_obj_tag(v_r_5343_) == 0)
{
lean_object* v_l_5438_; 
v_l_5438_ = lean_ctor_get(v_r_5343_, 3);
lean_inc(v_l_5438_);
if (lean_obj_tag(v_l_5438_) == 0)
{
lean_object* v_r_5439_; 
v_r_5439_ = lean_ctor_get(v_r_5343_, 4);
lean_inc(v_r_5439_);
if (lean_obj_tag(v_r_5439_) == 0)
{
lean_object* v_size_5440_; lean_object* v_k_5441_; lean_object* v_v_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5455_; 
v_size_5440_ = lean_ctor_get(v_r_5343_, 0);
v_k_5441_ = lean_ctor_get(v_r_5343_, 1);
v_v_5442_ = lean_ctor_get(v_r_5343_, 2);
v_isSharedCheck_5455_ = !lean_is_exclusive(v_r_5343_);
if (v_isSharedCheck_5455_ == 0)
{
lean_object* v_unused_5456_; lean_object* v_unused_5457_; 
v_unused_5456_ = lean_ctor_get(v_r_5343_, 4);
lean_dec(v_unused_5456_);
v_unused_5457_ = lean_ctor_get(v_r_5343_, 3);
lean_dec(v_unused_5457_);
v___x_5444_ = v_r_5343_;
v_isShared_5445_ = v_isSharedCheck_5455_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_v_5442_);
lean_inc(v_k_5441_);
lean_inc(v_size_5440_);
lean_dec(v_r_5343_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5455_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v_size_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5450_; 
v_size_5446_ = lean_ctor_get(v_l_5438_, 0);
v___x_5447_ = lean_nat_add(v___x_5349_, v_size_5440_);
lean_dec(v_size_5440_);
v___x_5448_ = lean_nat_add(v___x_5349_, v_size_5446_);
if (v_isShared_5445_ == 0)
{
lean_ctor_set(v___x_5444_, 4, v_l_5438_);
lean_ctor_set(v___x_5444_, 3, v_impl_5348_);
lean_ctor_set(v___x_5444_, 2, v_v_5341_);
lean_ctor_set(v___x_5444_, 1, v_k_5340_);
lean_ctor_set(v___x_5444_, 0, v___x_5448_);
v___x_5450_ = v___x_5444_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5448_);
lean_ctor_set(v_reuseFailAlloc_5454_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5454_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5454_, 3, v_impl_5348_);
lean_ctor_set(v_reuseFailAlloc_5454_, 4, v_l_5438_);
v___x_5450_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
lean_object* v___x_5452_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v_r_5439_);
lean_ctor_set(v___x_5345_, 3, v___x_5450_);
lean_ctor_set(v___x_5345_, 2, v_v_5442_);
lean_ctor_set(v___x_5345_, 1, v_k_5441_);
lean_ctor_set(v___x_5345_, 0, v___x_5447_);
v___x_5452_ = v___x_5345_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v___x_5447_);
lean_ctor_set(v_reuseFailAlloc_5453_, 1, v_k_5441_);
lean_ctor_set(v_reuseFailAlloc_5453_, 2, v_v_5442_);
lean_ctor_set(v_reuseFailAlloc_5453_, 3, v___x_5450_);
lean_ctor_set(v_reuseFailAlloc_5453_, 4, v_r_5439_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
else
{
lean_object* v_k_5458_; lean_object* v_v_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5482_; 
v_k_5458_ = lean_ctor_get(v_r_5343_, 1);
v_v_5459_ = lean_ctor_get(v_r_5343_, 2);
v_isSharedCheck_5482_ = !lean_is_exclusive(v_r_5343_);
if (v_isSharedCheck_5482_ == 0)
{
lean_object* v_unused_5483_; lean_object* v_unused_5484_; lean_object* v_unused_5485_; 
v_unused_5483_ = lean_ctor_get(v_r_5343_, 4);
lean_dec(v_unused_5483_);
v_unused_5484_ = lean_ctor_get(v_r_5343_, 3);
lean_dec(v_unused_5484_);
v_unused_5485_ = lean_ctor_get(v_r_5343_, 0);
lean_dec(v_unused_5485_);
v___x_5461_ = v_r_5343_;
v_isShared_5462_ = v_isSharedCheck_5482_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_v_5459_);
lean_inc(v_k_5458_);
lean_dec(v_r_5343_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5482_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v_k_5463_; lean_object* v_v_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5478_; 
v_k_5463_ = lean_ctor_get(v_l_5438_, 1);
v_v_5464_ = lean_ctor_get(v_l_5438_, 2);
v_isSharedCheck_5478_ = !lean_is_exclusive(v_l_5438_);
if (v_isSharedCheck_5478_ == 0)
{
lean_object* v_unused_5479_; lean_object* v_unused_5480_; lean_object* v_unused_5481_; 
v_unused_5479_ = lean_ctor_get(v_l_5438_, 4);
lean_dec(v_unused_5479_);
v_unused_5480_ = lean_ctor_get(v_l_5438_, 3);
lean_dec(v_unused_5480_);
v_unused_5481_ = lean_ctor_get(v_l_5438_, 0);
lean_dec(v_unused_5481_);
v___x_5466_ = v_l_5438_;
v_isShared_5467_ = v_isSharedCheck_5478_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_v_5464_);
lean_inc(v_k_5463_);
lean_dec(v_l_5438_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5478_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5468_; lean_object* v___x_5470_; 
v___x_5468_ = lean_unsigned_to_nat(3u);
if (v_isShared_5467_ == 0)
{
lean_ctor_set(v___x_5466_, 4, v_r_5439_);
lean_ctor_set(v___x_5466_, 3, v_r_5439_);
lean_ctor_set(v___x_5466_, 2, v_v_5341_);
lean_ctor_set(v___x_5466_, 1, v_k_5340_);
lean_ctor_set(v___x_5466_, 0, v___x_5349_);
v___x_5470_ = v___x_5466_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5477_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5477_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5477_, 3, v_r_5439_);
lean_ctor_set(v_reuseFailAlloc_5477_, 4, v_r_5439_);
v___x_5470_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
lean_object* v___x_5472_; 
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 3, v_r_5439_);
lean_ctor_set(v___x_5461_, 0, v___x_5349_);
v___x_5472_ = v___x_5461_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5476_, 1, v_k_5458_);
lean_ctor_set(v_reuseFailAlloc_5476_, 2, v_v_5459_);
lean_ctor_set(v_reuseFailAlloc_5476_, 3, v_r_5439_);
lean_ctor_set(v_reuseFailAlloc_5476_, 4, v_r_5439_);
v___x_5472_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
lean_object* v___x_5474_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v___x_5472_);
lean_ctor_set(v___x_5345_, 3, v___x_5470_);
lean_ctor_set(v___x_5345_, 2, v_v_5464_);
lean_ctor_set(v___x_5345_, 1, v_k_5463_);
lean_ctor_set(v___x_5345_, 0, v___x_5468_);
v___x_5474_ = v___x_5345_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5468_);
lean_ctor_set(v_reuseFailAlloc_5475_, 1, v_k_5463_);
lean_ctor_set(v_reuseFailAlloc_5475_, 2, v_v_5464_);
lean_ctor_set(v_reuseFailAlloc_5475_, 3, v___x_5470_);
lean_ctor_set(v_reuseFailAlloc_5475_, 4, v___x_5472_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
return v___x_5474_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_5486_; 
v_r_5486_ = lean_ctor_get(v_r_5343_, 4);
lean_inc(v_r_5486_);
if (lean_obj_tag(v_r_5486_) == 0)
{
lean_object* v_k_5487_; lean_object* v_v_5488_; lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5499_; 
v_k_5487_ = lean_ctor_get(v_r_5343_, 1);
v_v_5488_ = lean_ctor_get(v_r_5343_, 2);
v_isSharedCheck_5499_ = !lean_is_exclusive(v_r_5343_);
if (v_isSharedCheck_5499_ == 0)
{
lean_object* v_unused_5500_; lean_object* v_unused_5501_; lean_object* v_unused_5502_; 
v_unused_5500_ = lean_ctor_get(v_r_5343_, 4);
lean_dec(v_unused_5500_);
v_unused_5501_ = lean_ctor_get(v_r_5343_, 3);
lean_dec(v_unused_5501_);
v_unused_5502_ = lean_ctor_get(v_r_5343_, 0);
lean_dec(v_unused_5502_);
v___x_5490_ = v_r_5343_;
v_isShared_5491_ = v_isSharedCheck_5499_;
goto v_resetjp_5489_;
}
else
{
lean_inc(v_v_5488_);
lean_inc(v_k_5487_);
lean_dec(v_r_5343_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5499_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v___x_5492_; lean_object* v___x_5494_; 
v___x_5492_ = lean_unsigned_to_nat(3u);
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 4, v_l_5438_);
lean_ctor_set(v___x_5490_, 2, v_v_5341_);
lean_ctor_set(v___x_5490_, 1, v_k_5340_);
lean_ctor_set(v___x_5490_, 0, v___x_5349_);
v___x_5494_ = v___x_5490_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5498_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5498_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5498_, 3, v_l_5438_);
lean_ctor_set(v_reuseFailAlloc_5498_, 4, v_l_5438_);
v___x_5494_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
lean_object* v___x_5496_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v_r_5486_);
lean_ctor_set(v___x_5345_, 3, v___x_5494_);
lean_ctor_set(v___x_5345_, 2, v_v_5488_);
lean_ctor_set(v___x_5345_, 1, v_k_5487_);
lean_ctor_set(v___x_5345_, 0, v___x_5492_);
v___x_5496_ = v___x_5345_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v___x_5492_);
lean_ctor_set(v_reuseFailAlloc_5497_, 1, v_k_5487_);
lean_ctor_set(v_reuseFailAlloc_5497_, 2, v_v_5488_);
lean_ctor_set(v_reuseFailAlloc_5497_, 3, v___x_5494_);
lean_ctor_set(v_reuseFailAlloc_5497_, 4, v_r_5486_);
v___x_5496_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
return v___x_5496_;
}
}
}
}
else
{
lean_object* v_size_5503_; lean_object* v_k_5504_; lean_object* v_v_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5516_; 
v_size_5503_ = lean_ctor_get(v_r_5343_, 0);
v_k_5504_ = lean_ctor_get(v_r_5343_, 1);
v_v_5505_ = lean_ctor_get(v_r_5343_, 2);
v_isSharedCheck_5516_ = !lean_is_exclusive(v_r_5343_);
if (v_isSharedCheck_5516_ == 0)
{
lean_object* v_unused_5517_; lean_object* v_unused_5518_; 
v_unused_5517_ = lean_ctor_get(v_r_5343_, 4);
lean_dec(v_unused_5517_);
v_unused_5518_ = lean_ctor_get(v_r_5343_, 3);
lean_dec(v_unused_5518_);
v___x_5507_ = v_r_5343_;
v_isShared_5508_ = v_isSharedCheck_5516_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_v_5505_);
lean_inc(v_k_5504_);
lean_inc(v_size_5503_);
lean_dec(v_r_5343_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5516_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5510_; 
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 3, v_r_5486_);
v___x_5510_ = v___x_5507_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_size_5503_);
lean_ctor_set(v_reuseFailAlloc_5515_, 1, v_k_5504_);
lean_ctor_set(v_reuseFailAlloc_5515_, 2, v_v_5505_);
lean_ctor_set(v_reuseFailAlloc_5515_, 3, v_r_5486_);
lean_ctor_set(v_reuseFailAlloc_5515_, 4, v_r_5486_);
v___x_5510_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5511_; lean_object* v___x_5513_; 
v___x_5511_ = lean_unsigned_to_nat(2u);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v___x_5510_);
lean_ctor_set(v___x_5345_, 3, v_r_5486_);
lean_ctor_set(v___x_5345_, 0, v___x_5511_);
v___x_5513_ = v___x_5345_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v___x_5511_);
lean_ctor_set(v_reuseFailAlloc_5514_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5514_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5514_, 3, v_r_5486_);
lean_ctor_set(v_reuseFailAlloc_5514_, 4, v___x_5510_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
}
}
}
else
{
lean_object* v___x_5520_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 3, v_r_5343_);
lean_ctor_set(v___x_5345_, 0, v___x_5349_);
v___x_5520_ = v___x_5345_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5521_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5521_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5521_, 3, v_r_5343_);
lean_ctor_set(v_reuseFailAlloc_5521_, 4, v_r_5343_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
return v___x_5520_;
}
}
}
}
case 1:
{
lean_del_object(v___x_5345_);
lean_dec(v_v_5341_);
lean_dec(v_k_5340_);
if (lean_obj_tag(v_l_5342_) == 0)
{
if (lean_obj_tag(v_r_5343_) == 0)
{
lean_object* v_size_5522_; lean_object* v_k_5523_; lean_object* v_v_5524_; lean_object* v_l_5525_; lean_object* v_r_5526_; lean_object* v_size_5527_; lean_object* v_k_5528_; lean_object* v_v_5529_; lean_object* v_l_5530_; lean_object* v_r_5531_; lean_object* v___x_5532_; uint8_t v___x_5533_; 
v_size_5522_ = lean_ctor_get(v_l_5342_, 0);
v_k_5523_ = lean_ctor_get(v_l_5342_, 1);
v_v_5524_ = lean_ctor_get(v_l_5342_, 2);
v_l_5525_ = lean_ctor_get(v_l_5342_, 3);
v_r_5526_ = lean_ctor_get(v_l_5342_, 4);
lean_inc(v_r_5526_);
v_size_5527_ = lean_ctor_get(v_r_5343_, 0);
v_k_5528_ = lean_ctor_get(v_r_5343_, 1);
v_v_5529_ = lean_ctor_get(v_r_5343_, 2);
v_l_5530_ = lean_ctor_get(v_r_5343_, 3);
lean_inc(v_l_5530_);
v_r_5531_ = lean_ctor_get(v_r_5343_, 4);
v___x_5532_ = lean_unsigned_to_nat(1u);
v___x_5533_ = lean_nat_dec_lt(v_size_5522_, v_size_5527_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5669_; 
lean_inc(v_l_5525_);
lean_inc(v_v_5524_);
lean_inc(v_k_5523_);
v_isSharedCheck_5669_ = !lean_is_exclusive(v_l_5342_);
if (v_isSharedCheck_5669_ == 0)
{
lean_object* v_unused_5670_; lean_object* v_unused_5671_; lean_object* v_unused_5672_; lean_object* v_unused_5673_; lean_object* v_unused_5674_; 
v_unused_5670_ = lean_ctor_get(v_l_5342_, 4);
lean_dec(v_unused_5670_);
v_unused_5671_ = lean_ctor_get(v_l_5342_, 3);
lean_dec(v_unused_5671_);
v_unused_5672_ = lean_ctor_get(v_l_5342_, 2);
lean_dec(v_unused_5672_);
v_unused_5673_ = lean_ctor_get(v_l_5342_, 1);
lean_dec(v_unused_5673_);
v_unused_5674_ = lean_ctor_get(v_l_5342_, 0);
lean_dec(v_unused_5674_);
v___x_5535_ = v_l_5342_;
v_isShared_5536_ = v_isSharedCheck_5669_;
goto v_resetjp_5534_;
}
else
{
lean_dec(v_l_5342_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5669_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5537_; lean_object* v_tree_5538_; 
v___x_5537_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5523_, v_v_5524_, v_l_5525_, v_r_5526_);
v_tree_5538_ = lean_ctor_get(v___x_5537_, 2);
lean_inc(v_tree_5538_);
if (lean_obj_tag(v_tree_5538_) == 0)
{
lean_object* v_k_5539_; lean_object* v_v_5540_; lean_object* v_size_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; uint8_t v___x_5544_; 
v_k_5539_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_k_5539_);
v_v_5540_ = lean_ctor_get(v___x_5537_, 1);
lean_inc(v_v_5540_);
lean_dec_ref(v___x_5537_);
v_size_5541_ = lean_ctor_get(v_tree_5538_, 0);
v___x_5542_ = lean_unsigned_to_nat(3u);
v___x_5543_ = lean_nat_mul(v___x_5542_, v_size_5541_);
v___x_5544_ = lean_nat_dec_lt(v___x_5543_, v_size_5527_);
lean_dec(v___x_5543_);
if (v___x_5544_ == 0)
{
lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5548_; 
lean_dec(v_l_5530_);
v___x_5545_ = lean_nat_add(v___x_5532_, v_size_5541_);
v___x_5546_ = lean_nat_add(v___x_5545_, v_size_5527_);
lean_dec(v___x_5545_);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 4, v_r_5343_);
lean_ctor_set(v___x_5535_, 3, v_tree_5538_);
lean_ctor_set(v___x_5535_, 2, v_v_5540_);
lean_ctor_set(v___x_5535_, 1, v_k_5539_);
lean_ctor_set(v___x_5535_, 0, v___x_5546_);
v___x_5548_ = v___x_5535_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5546_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v_k_5539_);
lean_ctor_set(v_reuseFailAlloc_5549_, 2, v_v_5540_);
lean_ctor_set(v_reuseFailAlloc_5549_, 3, v_tree_5538_);
lean_ctor_set(v_reuseFailAlloc_5549_, 4, v_r_5343_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
return v___x_5548_;
}
}
else
{
lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5604_; 
lean_inc(v_r_5531_);
lean_inc(v_v_5529_);
lean_inc(v_k_5528_);
lean_inc(v_size_5527_);
v_isSharedCheck_5604_ = !lean_is_exclusive(v_r_5343_);
if (v_isSharedCheck_5604_ == 0)
{
lean_object* v_unused_5605_; lean_object* v_unused_5606_; lean_object* v_unused_5607_; lean_object* v_unused_5608_; lean_object* v_unused_5609_; 
v_unused_5605_ = lean_ctor_get(v_r_5343_, 4);
lean_dec(v_unused_5605_);
v_unused_5606_ = lean_ctor_get(v_r_5343_, 3);
lean_dec(v_unused_5606_);
v_unused_5607_ = lean_ctor_get(v_r_5343_, 2);
lean_dec(v_unused_5607_);
v_unused_5608_ = lean_ctor_get(v_r_5343_, 1);
lean_dec(v_unused_5608_);
v_unused_5609_ = lean_ctor_get(v_r_5343_, 0);
lean_dec(v_unused_5609_);
v___x_5551_ = v_r_5343_;
v_isShared_5552_ = v_isSharedCheck_5604_;
goto v_resetjp_5550_;
}
else
{
lean_dec(v_r_5343_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5604_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v_size_5553_; lean_object* v_k_5554_; lean_object* v_v_5555_; lean_object* v_l_5556_; lean_object* v_r_5557_; lean_object* v_size_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; uint8_t v___x_5561_; 
v_size_5553_ = lean_ctor_get(v_l_5530_, 0);
v_k_5554_ = lean_ctor_get(v_l_5530_, 1);
v_v_5555_ = lean_ctor_get(v_l_5530_, 2);
v_l_5556_ = lean_ctor_get(v_l_5530_, 3);
v_r_5557_ = lean_ctor_get(v_l_5530_, 4);
v_size_5558_ = lean_ctor_get(v_r_5531_, 0);
v___x_5559_ = lean_unsigned_to_nat(2u);
v___x_5560_ = lean_nat_mul(v___x_5559_, v_size_5558_);
v___x_5561_ = lean_nat_dec_lt(v_size_5553_, v___x_5560_);
lean_dec(v___x_5560_);
if (v___x_5561_ == 0)
{
lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5589_; 
lean_inc(v_r_5557_);
lean_inc(v_l_5556_);
lean_inc(v_v_5555_);
lean_inc(v_k_5554_);
v_isSharedCheck_5589_ = !lean_is_exclusive(v_l_5530_);
if (v_isSharedCheck_5589_ == 0)
{
lean_object* v_unused_5590_; lean_object* v_unused_5591_; lean_object* v_unused_5592_; lean_object* v_unused_5593_; lean_object* v_unused_5594_; 
v_unused_5590_ = lean_ctor_get(v_l_5530_, 4);
lean_dec(v_unused_5590_);
v_unused_5591_ = lean_ctor_get(v_l_5530_, 3);
lean_dec(v_unused_5591_);
v_unused_5592_ = lean_ctor_get(v_l_5530_, 2);
lean_dec(v_unused_5592_);
v_unused_5593_ = lean_ctor_get(v_l_5530_, 1);
lean_dec(v_unused_5593_);
v_unused_5594_ = lean_ctor_get(v_l_5530_, 0);
lean_dec(v_unused_5594_);
v___x_5563_ = v_l_5530_;
v_isShared_5564_ = v_isSharedCheck_5589_;
goto v_resetjp_5562_;
}
else
{
lean_dec(v_l_5530_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5589_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___y_5568_; lean_object* v___y_5569_; lean_object* v___y_5570_; lean_object* v___y_5579_; 
v___x_5565_ = lean_nat_add(v___x_5532_, v_size_5541_);
v___x_5566_ = lean_nat_add(v___x_5565_, v_size_5527_);
lean_dec(v_size_5527_);
if (lean_obj_tag(v_l_5556_) == 0)
{
lean_object* v_size_5587_; 
v_size_5587_ = lean_ctor_get(v_l_5556_, 0);
lean_inc(v_size_5587_);
v___y_5579_ = v_size_5587_;
goto v___jp_5578_;
}
else
{
lean_object* v___x_5588_; 
v___x_5588_ = lean_unsigned_to_nat(0u);
v___y_5579_ = v___x_5588_;
goto v___jp_5578_;
}
v___jp_5567_:
{
lean_object* v___x_5571_; lean_object* v___x_5573_; 
v___x_5571_ = lean_nat_add(v___y_5568_, v___y_5570_);
lean_dec(v___y_5570_);
lean_dec(v___y_5568_);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 4, v_r_5531_);
lean_ctor_set(v___x_5563_, 3, v_r_5557_);
lean_ctor_set(v___x_5563_, 2, v_v_5529_);
lean_ctor_set(v___x_5563_, 1, v_k_5528_);
lean_ctor_set(v___x_5563_, 0, v___x_5571_);
v___x_5573_ = v___x_5563_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v___x_5571_);
lean_ctor_set(v_reuseFailAlloc_5577_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5577_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5577_, 3, v_r_5557_);
lean_ctor_set(v_reuseFailAlloc_5577_, 4, v_r_5531_);
v___x_5573_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
lean_object* v___x_5575_; 
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 4, v___x_5573_);
lean_ctor_set(v___x_5551_, 3, v___y_5569_);
lean_ctor_set(v___x_5551_, 2, v_v_5555_);
lean_ctor_set(v___x_5551_, 1, v_k_5554_);
lean_ctor_set(v___x_5551_, 0, v___x_5566_);
v___x_5575_ = v___x_5551_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v___x_5566_);
lean_ctor_set(v_reuseFailAlloc_5576_, 1, v_k_5554_);
lean_ctor_set(v_reuseFailAlloc_5576_, 2, v_v_5555_);
lean_ctor_set(v_reuseFailAlloc_5576_, 3, v___y_5569_);
lean_ctor_set(v_reuseFailAlloc_5576_, 4, v___x_5573_);
v___x_5575_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
return v___x_5575_;
}
}
}
v___jp_5578_:
{
lean_object* v___x_5580_; lean_object* v___x_5582_; 
v___x_5580_ = lean_nat_add(v___x_5565_, v___y_5579_);
lean_dec(v___y_5579_);
lean_dec(v___x_5565_);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 4, v_l_5556_);
lean_ctor_set(v___x_5535_, 3, v_tree_5538_);
lean_ctor_set(v___x_5535_, 2, v_v_5540_);
lean_ctor_set(v___x_5535_, 1, v_k_5539_);
lean_ctor_set(v___x_5535_, 0, v___x_5580_);
v___x_5582_ = v___x_5535_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5580_);
lean_ctor_set(v_reuseFailAlloc_5586_, 1, v_k_5539_);
lean_ctor_set(v_reuseFailAlloc_5586_, 2, v_v_5540_);
lean_ctor_set(v_reuseFailAlloc_5586_, 3, v_tree_5538_);
lean_ctor_set(v_reuseFailAlloc_5586_, 4, v_l_5556_);
v___x_5582_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
lean_object* v___x_5583_; 
v___x_5583_ = lean_nat_add(v___x_5532_, v_size_5558_);
if (lean_obj_tag(v_r_5557_) == 0)
{
lean_object* v_size_5584_; 
v_size_5584_ = lean_ctor_get(v_r_5557_, 0);
lean_inc(v_size_5584_);
v___y_5568_ = v___x_5583_;
v___y_5569_ = v___x_5582_;
v___y_5570_ = v_size_5584_;
goto v___jp_5567_;
}
else
{
lean_object* v___x_5585_; 
v___x_5585_ = lean_unsigned_to_nat(0u);
v___y_5568_ = v___x_5583_;
v___y_5569_ = v___x_5582_;
v___y_5570_ = v___x_5585_;
goto v___jp_5567_;
}
}
}
}
}
else
{
lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5599_; 
v___x_5595_ = lean_nat_add(v___x_5532_, v_size_5541_);
v___x_5596_ = lean_nat_add(v___x_5595_, v_size_5527_);
lean_dec(v_size_5527_);
v___x_5597_ = lean_nat_add(v___x_5595_, v_size_5553_);
lean_dec(v___x_5595_);
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 4, v_l_5530_);
lean_ctor_set(v___x_5551_, 3, v_tree_5538_);
lean_ctor_set(v___x_5551_, 2, v_v_5540_);
lean_ctor_set(v___x_5551_, 1, v_k_5539_);
lean_ctor_set(v___x_5551_, 0, v___x_5597_);
v___x_5599_ = v___x_5551_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5597_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v_k_5539_);
lean_ctor_set(v_reuseFailAlloc_5603_, 2, v_v_5540_);
lean_ctor_set(v_reuseFailAlloc_5603_, 3, v_tree_5538_);
lean_ctor_set(v_reuseFailAlloc_5603_, 4, v_l_5530_);
v___x_5599_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
lean_object* v___x_5601_; 
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 4, v_r_5531_);
lean_ctor_set(v___x_5535_, 3, v___x_5599_);
lean_ctor_set(v___x_5535_, 2, v_v_5529_);
lean_ctor_set(v___x_5535_, 1, v_k_5528_);
lean_ctor_set(v___x_5535_, 0, v___x_5596_);
v___x_5601_ = v___x_5535_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v___x_5596_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5602_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5602_, 3, v___x_5599_);
lean_ctor_set(v_reuseFailAlloc_5602_, 4, v_r_5531_);
v___x_5601_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
return v___x_5601_;
}
}
}
}
}
}
else
{
lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5663_; 
lean_inc(v_r_5531_);
lean_inc(v_v_5529_);
lean_inc(v_k_5528_);
lean_inc(v_size_5527_);
v_isSharedCheck_5663_ = !lean_is_exclusive(v_r_5343_);
if (v_isSharedCheck_5663_ == 0)
{
lean_object* v_unused_5664_; lean_object* v_unused_5665_; lean_object* v_unused_5666_; lean_object* v_unused_5667_; lean_object* v_unused_5668_; 
v_unused_5664_ = lean_ctor_get(v_r_5343_, 4);
lean_dec(v_unused_5664_);
v_unused_5665_ = lean_ctor_get(v_r_5343_, 3);
lean_dec(v_unused_5665_);
v_unused_5666_ = lean_ctor_get(v_r_5343_, 2);
lean_dec(v_unused_5666_);
v_unused_5667_ = lean_ctor_get(v_r_5343_, 1);
lean_dec(v_unused_5667_);
v_unused_5668_ = lean_ctor_get(v_r_5343_, 0);
lean_dec(v_unused_5668_);
v___x_5611_ = v_r_5343_;
v_isShared_5612_ = v_isSharedCheck_5663_;
goto v_resetjp_5610_;
}
else
{
lean_dec(v_r_5343_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5663_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
if (lean_obj_tag(v_l_5530_) == 0)
{
if (lean_obj_tag(v_r_5531_) == 0)
{
lean_object* v_k_5613_; lean_object* v_v_5614_; lean_object* v_size_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5619_; 
v_k_5613_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_k_5613_);
v_v_5614_ = lean_ctor_get(v___x_5537_, 1);
lean_inc(v_v_5614_);
lean_dec_ref(v___x_5537_);
v_size_5615_ = lean_ctor_get(v_l_5530_, 0);
v___x_5616_ = lean_nat_add(v___x_5532_, v_size_5527_);
lean_dec(v_size_5527_);
v___x_5617_ = lean_nat_add(v___x_5532_, v_size_5615_);
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 4, v_l_5530_);
lean_ctor_set(v___x_5611_, 3, v_tree_5538_);
lean_ctor_set(v___x_5611_, 2, v_v_5614_);
lean_ctor_set(v___x_5611_, 1, v_k_5613_);
lean_ctor_set(v___x_5611_, 0, v___x_5617_);
v___x_5619_ = v___x_5611_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5617_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v_k_5613_);
lean_ctor_set(v_reuseFailAlloc_5623_, 2, v_v_5614_);
lean_ctor_set(v_reuseFailAlloc_5623_, 3, v_tree_5538_);
lean_ctor_set(v_reuseFailAlloc_5623_, 4, v_l_5530_);
v___x_5619_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
lean_object* v___x_5621_; 
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 4, v_r_5531_);
lean_ctor_set(v___x_5535_, 3, v___x_5619_);
lean_ctor_set(v___x_5535_, 2, v_v_5529_);
lean_ctor_set(v___x_5535_, 1, v_k_5528_);
lean_ctor_set(v___x_5535_, 0, v___x_5616_);
v___x_5621_ = v___x_5535_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5616_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5622_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5622_, 3, v___x_5619_);
lean_ctor_set(v_reuseFailAlloc_5622_, 4, v_r_5531_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
else
{
lean_object* v_k_5624_; lean_object* v_v_5625_; lean_object* v_k_5626_; lean_object* v_v_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5641_; 
lean_dec(v_size_5527_);
v_k_5624_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_k_5624_);
v_v_5625_ = lean_ctor_get(v___x_5537_, 1);
lean_inc(v_v_5625_);
lean_dec_ref(v___x_5537_);
v_k_5626_ = lean_ctor_get(v_l_5530_, 1);
v_v_5627_ = lean_ctor_get(v_l_5530_, 2);
v_isSharedCheck_5641_ = !lean_is_exclusive(v_l_5530_);
if (v_isSharedCheck_5641_ == 0)
{
lean_object* v_unused_5642_; lean_object* v_unused_5643_; lean_object* v_unused_5644_; 
v_unused_5642_ = lean_ctor_get(v_l_5530_, 4);
lean_dec(v_unused_5642_);
v_unused_5643_ = lean_ctor_get(v_l_5530_, 3);
lean_dec(v_unused_5643_);
v_unused_5644_ = lean_ctor_get(v_l_5530_, 0);
lean_dec(v_unused_5644_);
v___x_5629_ = v_l_5530_;
v_isShared_5630_ = v_isSharedCheck_5641_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_v_5627_);
lean_inc(v_k_5626_);
lean_dec(v_l_5530_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5641_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v___x_5631_; lean_object* v___x_5633_; 
v___x_5631_ = lean_unsigned_to_nat(3u);
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 4, v_r_5531_);
lean_ctor_set(v___x_5629_, 3, v_r_5531_);
lean_ctor_set(v___x_5629_, 2, v_v_5625_);
lean_ctor_set(v___x_5629_, 1, v_k_5624_);
lean_ctor_set(v___x_5629_, 0, v___x_5532_);
v___x_5633_ = v___x_5629_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5640_, 1, v_k_5624_);
lean_ctor_set(v_reuseFailAlloc_5640_, 2, v_v_5625_);
lean_ctor_set(v_reuseFailAlloc_5640_, 3, v_r_5531_);
lean_ctor_set(v_reuseFailAlloc_5640_, 4, v_r_5531_);
v___x_5633_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
lean_object* v___x_5635_; 
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 3, v_r_5531_);
lean_ctor_set(v___x_5611_, 0, v___x_5532_);
v___x_5635_ = v___x_5611_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5639_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5639_, 3, v_r_5531_);
lean_ctor_set(v_reuseFailAlloc_5639_, 4, v_r_5531_);
v___x_5635_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
lean_object* v___x_5637_; 
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 4, v___x_5635_);
lean_ctor_set(v___x_5535_, 3, v___x_5633_);
lean_ctor_set(v___x_5535_, 2, v_v_5627_);
lean_ctor_set(v___x_5535_, 1, v_k_5626_);
lean_ctor_set(v___x_5535_, 0, v___x_5631_);
v___x_5637_ = v___x_5535_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v___x_5631_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v_k_5626_);
lean_ctor_set(v_reuseFailAlloc_5638_, 2, v_v_5627_);
lean_ctor_set(v_reuseFailAlloc_5638_, 3, v___x_5633_);
lean_ctor_set(v_reuseFailAlloc_5638_, 4, v___x_5635_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5531_) == 0)
{
lean_object* v_k_5645_; lean_object* v_v_5646_; lean_object* v___x_5647_; lean_object* v___x_5649_; 
lean_dec(v_size_5527_);
v_k_5645_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_k_5645_);
v_v_5646_ = lean_ctor_get(v___x_5537_, 1);
lean_inc(v_v_5646_);
lean_dec_ref(v___x_5537_);
v___x_5647_ = lean_unsigned_to_nat(3u);
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 4, v_l_5530_);
lean_ctor_set(v___x_5611_, 2, v_v_5646_);
lean_ctor_set(v___x_5611_, 1, v_k_5645_);
lean_ctor_set(v___x_5611_, 0, v___x_5532_);
v___x_5649_ = v___x_5611_;
goto v_reusejp_5648_;
}
else
{
lean_object* v_reuseFailAlloc_5653_; 
v_reuseFailAlloc_5653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5653_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5653_, 1, v_k_5645_);
lean_ctor_set(v_reuseFailAlloc_5653_, 2, v_v_5646_);
lean_ctor_set(v_reuseFailAlloc_5653_, 3, v_l_5530_);
lean_ctor_set(v_reuseFailAlloc_5653_, 4, v_l_5530_);
v___x_5649_ = v_reuseFailAlloc_5653_;
goto v_reusejp_5648_;
}
v_reusejp_5648_:
{
lean_object* v___x_5651_; 
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 4, v_r_5531_);
lean_ctor_set(v___x_5535_, 3, v___x_5649_);
lean_ctor_set(v___x_5535_, 2, v_v_5529_);
lean_ctor_set(v___x_5535_, 1, v_k_5528_);
lean_ctor_set(v___x_5535_, 0, v___x_5647_);
v___x_5651_ = v___x_5535_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v___x_5647_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5652_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5652_, 3, v___x_5649_);
lean_ctor_set(v_reuseFailAlloc_5652_, 4, v_r_5531_);
v___x_5651_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
return v___x_5651_;
}
}
}
else
{
lean_object* v_k_5654_; lean_object* v_v_5655_; lean_object* v___x_5657_; 
v_k_5654_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_k_5654_);
v_v_5655_ = lean_ctor_get(v___x_5537_, 1);
lean_inc(v_v_5655_);
lean_dec_ref(v___x_5537_);
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 3, v_r_5531_);
v___x_5657_ = v___x_5611_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_size_5527_);
lean_ctor_set(v_reuseFailAlloc_5662_, 1, v_k_5528_);
lean_ctor_set(v_reuseFailAlloc_5662_, 2, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5662_, 3, v_r_5531_);
lean_ctor_set(v_reuseFailAlloc_5662_, 4, v_r_5531_);
v___x_5657_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
lean_object* v___x_5658_; lean_object* v___x_5660_; 
v___x_5658_ = lean_unsigned_to_nat(2u);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 4, v___x_5657_);
lean_ctor_set(v___x_5535_, 3, v_r_5531_);
lean_ctor_set(v___x_5535_, 2, v_v_5655_);
lean_ctor_set(v___x_5535_, 1, v_k_5654_);
lean_ctor_set(v___x_5535_, 0, v___x_5658_);
v___x_5660_ = v___x_5535_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v___x_5658_);
lean_ctor_set(v_reuseFailAlloc_5661_, 1, v_k_5654_);
lean_ctor_set(v_reuseFailAlloc_5661_, 2, v_v_5655_);
lean_ctor_set(v_reuseFailAlloc_5661_, 3, v_r_5531_);
lean_ctor_set(v_reuseFailAlloc_5661_, 4, v___x_5657_);
v___x_5660_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
return v___x_5660_;
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
lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5827_; 
lean_inc(v_r_5531_);
lean_inc(v_v_5529_);
lean_inc(v_k_5528_);
v_isSharedCheck_5827_ = !lean_is_exclusive(v_r_5343_);
if (v_isSharedCheck_5827_ == 0)
{
lean_object* v_unused_5828_; lean_object* v_unused_5829_; lean_object* v_unused_5830_; lean_object* v_unused_5831_; lean_object* v_unused_5832_; 
v_unused_5828_ = lean_ctor_get(v_r_5343_, 4);
lean_dec(v_unused_5828_);
v_unused_5829_ = lean_ctor_get(v_r_5343_, 3);
lean_dec(v_unused_5829_);
v_unused_5830_ = lean_ctor_get(v_r_5343_, 2);
lean_dec(v_unused_5830_);
v_unused_5831_ = lean_ctor_get(v_r_5343_, 1);
lean_dec(v_unused_5831_);
v_unused_5832_ = lean_ctor_get(v_r_5343_, 0);
lean_dec(v_unused_5832_);
v___x_5676_ = v_r_5343_;
v_isShared_5677_ = v_isSharedCheck_5827_;
goto v_resetjp_5675_;
}
else
{
lean_dec(v_r_5343_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5827_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5678_; lean_object* v_tree_5679_; 
v___x_5678_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5528_, v_v_5529_, v_l_5530_, v_r_5531_);
v_tree_5679_ = lean_ctor_get(v___x_5678_, 2);
lean_inc(v_tree_5679_);
if (lean_obj_tag(v_tree_5679_) == 0)
{
lean_object* v_k_5680_; lean_object* v_v_5681_; lean_object* v_size_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; uint8_t v___x_5685_; 
v_k_5680_ = lean_ctor_get(v___x_5678_, 0);
lean_inc(v_k_5680_);
v_v_5681_ = lean_ctor_get(v___x_5678_, 1);
lean_inc(v_v_5681_);
lean_dec_ref(v___x_5678_);
v_size_5682_ = lean_ctor_get(v_tree_5679_, 0);
v___x_5683_ = lean_unsigned_to_nat(3u);
v___x_5684_ = lean_nat_mul(v___x_5683_, v_size_5682_);
v___x_5685_ = lean_nat_dec_lt(v___x_5684_, v_size_5522_);
lean_dec(v___x_5684_);
if (v___x_5685_ == 0)
{
lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5689_; 
lean_dec(v_r_5526_);
v___x_5686_ = lean_nat_add(v___x_5532_, v_size_5522_);
v___x_5687_ = lean_nat_add(v___x_5686_, v_size_5682_);
lean_dec(v___x_5686_);
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 4, v_tree_5679_);
lean_ctor_set(v___x_5676_, 3, v_l_5342_);
lean_ctor_set(v___x_5676_, 2, v_v_5681_);
lean_ctor_set(v___x_5676_, 1, v_k_5680_);
lean_ctor_set(v___x_5676_, 0, v___x_5687_);
v___x_5689_ = v___x_5676_;
goto v_reusejp_5688_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v___x_5687_);
lean_ctor_set(v_reuseFailAlloc_5690_, 1, v_k_5680_);
lean_ctor_set(v_reuseFailAlloc_5690_, 2, v_v_5681_);
lean_ctor_set(v_reuseFailAlloc_5690_, 3, v_l_5342_);
lean_ctor_set(v_reuseFailAlloc_5690_, 4, v_tree_5679_);
v___x_5689_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5688_;
}
v_reusejp_5688_:
{
return v___x_5689_;
}
}
else
{
lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5756_; 
lean_inc(v_l_5525_);
lean_inc(v_v_5524_);
lean_inc(v_k_5523_);
lean_inc(v_size_5522_);
v_isSharedCheck_5756_ = !lean_is_exclusive(v_l_5342_);
if (v_isSharedCheck_5756_ == 0)
{
lean_object* v_unused_5757_; lean_object* v_unused_5758_; lean_object* v_unused_5759_; lean_object* v_unused_5760_; lean_object* v_unused_5761_; 
v_unused_5757_ = lean_ctor_get(v_l_5342_, 4);
lean_dec(v_unused_5757_);
v_unused_5758_ = lean_ctor_get(v_l_5342_, 3);
lean_dec(v_unused_5758_);
v_unused_5759_ = lean_ctor_get(v_l_5342_, 2);
lean_dec(v_unused_5759_);
v_unused_5760_ = lean_ctor_get(v_l_5342_, 1);
lean_dec(v_unused_5760_);
v_unused_5761_ = lean_ctor_get(v_l_5342_, 0);
lean_dec(v_unused_5761_);
v___x_5692_ = v_l_5342_;
v_isShared_5693_ = v_isSharedCheck_5756_;
goto v_resetjp_5691_;
}
else
{
lean_dec(v_l_5342_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5756_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v_size_5694_; lean_object* v_size_5695_; lean_object* v_k_5696_; lean_object* v_v_5697_; lean_object* v_l_5698_; lean_object* v_r_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; uint8_t v___x_5702_; 
v_size_5694_ = lean_ctor_get(v_l_5525_, 0);
v_size_5695_ = lean_ctor_get(v_r_5526_, 0);
v_k_5696_ = lean_ctor_get(v_r_5526_, 1);
v_v_5697_ = lean_ctor_get(v_r_5526_, 2);
v_l_5698_ = lean_ctor_get(v_r_5526_, 3);
v_r_5699_ = lean_ctor_get(v_r_5526_, 4);
v___x_5700_ = lean_unsigned_to_nat(2u);
v___x_5701_ = lean_nat_mul(v___x_5700_, v_size_5694_);
v___x_5702_ = lean_nat_dec_lt(v_size_5695_, v___x_5701_);
lean_dec(v___x_5701_);
if (v___x_5702_ == 0)
{
lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5740_; 
lean_inc(v_r_5699_);
lean_inc(v_l_5698_);
lean_inc(v_v_5697_);
lean_inc(v_k_5696_);
lean_del_object(v___x_5692_);
v_isSharedCheck_5740_ = !lean_is_exclusive(v_r_5526_);
if (v_isSharedCheck_5740_ == 0)
{
lean_object* v_unused_5741_; lean_object* v_unused_5742_; lean_object* v_unused_5743_; lean_object* v_unused_5744_; lean_object* v_unused_5745_; 
v_unused_5741_ = lean_ctor_get(v_r_5526_, 4);
lean_dec(v_unused_5741_);
v_unused_5742_ = lean_ctor_get(v_r_5526_, 3);
lean_dec(v_unused_5742_);
v_unused_5743_ = lean_ctor_get(v_r_5526_, 2);
lean_dec(v_unused_5743_);
v_unused_5744_ = lean_ctor_get(v_r_5526_, 1);
lean_dec(v_unused_5744_);
v_unused_5745_ = lean_ctor_get(v_r_5526_, 0);
lean_dec(v_unused_5745_);
v___x_5704_ = v_r_5526_;
v_isShared_5705_ = v_isSharedCheck_5740_;
goto v_resetjp_5703_;
}
else
{
lean_dec(v_r_5526_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5740_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___y_5709_; lean_object* v___y_5710_; lean_object* v___y_5711_; lean_object* v___x_5728_; lean_object* v___y_5730_; 
v___x_5706_ = lean_nat_add(v___x_5532_, v_size_5522_);
lean_dec(v_size_5522_);
v___x_5707_ = lean_nat_add(v___x_5706_, v_size_5682_);
lean_dec(v___x_5706_);
v___x_5728_ = lean_nat_add(v___x_5532_, v_size_5694_);
if (lean_obj_tag(v_l_5698_) == 0)
{
lean_object* v_size_5738_; 
v_size_5738_ = lean_ctor_get(v_l_5698_, 0);
lean_inc(v_size_5738_);
v___y_5730_ = v_size_5738_;
goto v___jp_5729_;
}
else
{
lean_object* v___x_5739_; 
v___x_5739_ = lean_unsigned_to_nat(0u);
v___y_5730_ = v___x_5739_;
goto v___jp_5729_;
}
v___jp_5708_:
{
lean_object* v___x_5712_; lean_object* v___x_5714_; 
v___x_5712_ = lean_nat_add(v___y_5709_, v___y_5711_);
lean_dec(v___y_5711_);
lean_dec(v___y_5709_);
lean_inc_ref(v_tree_5679_);
if (v_isShared_5705_ == 0)
{
lean_ctor_set(v___x_5704_, 4, v_tree_5679_);
lean_ctor_set(v___x_5704_, 3, v_r_5699_);
lean_ctor_set(v___x_5704_, 2, v_v_5681_);
lean_ctor_set(v___x_5704_, 1, v_k_5680_);
lean_ctor_set(v___x_5704_, 0, v___x_5712_);
v___x_5714_ = v___x_5704_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v___x_5712_);
lean_ctor_set(v_reuseFailAlloc_5727_, 1, v_k_5680_);
lean_ctor_set(v_reuseFailAlloc_5727_, 2, v_v_5681_);
lean_ctor_set(v_reuseFailAlloc_5727_, 3, v_r_5699_);
lean_ctor_set(v_reuseFailAlloc_5727_, 4, v_tree_5679_);
v___x_5714_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
lean_object* v___x_5716_; uint8_t v_isShared_5717_; uint8_t v_isSharedCheck_5721_; 
v_isSharedCheck_5721_ = !lean_is_exclusive(v_tree_5679_);
if (v_isSharedCheck_5721_ == 0)
{
lean_object* v_unused_5722_; lean_object* v_unused_5723_; lean_object* v_unused_5724_; lean_object* v_unused_5725_; lean_object* v_unused_5726_; 
v_unused_5722_ = lean_ctor_get(v_tree_5679_, 4);
lean_dec(v_unused_5722_);
v_unused_5723_ = lean_ctor_get(v_tree_5679_, 3);
lean_dec(v_unused_5723_);
v_unused_5724_ = lean_ctor_get(v_tree_5679_, 2);
lean_dec(v_unused_5724_);
v_unused_5725_ = lean_ctor_get(v_tree_5679_, 1);
lean_dec(v_unused_5725_);
v_unused_5726_ = lean_ctor_get(v_tree_5679_, 0);
lean_dec(v_unused_5726_);
v___x_5716_ = v_tree_5679_;
v_isShared_5717_ = v_isSharedCheck_5721_;
goto v_resetjp_5715_;
}
else
{
lean_dec(v_tree_5679_);
v___x_5716_ = lean_box(0);
v_isShared_5717_ = v_isSharedCheck_5721_;
goto v_resetjp_5715_;
}
v_resetjp_5715_:
{
lean_object* v___x_5719_; 
if (v_isShared_5717_ == 0)
{
lean_ctor_set(v___x_5716_, 4, v___x_5714_);
lean_ctor_set(v___x_5716_, 3, v___y_5710_);
lean_ctor_set(v___x_5716_, 2, v_v_5697_);
lean_ctor_set(v___x_5716_, 1, v_k_5696_);
lean_ctor_set(v___x_5716_, 0, v___x_5707_);
v___x_5719_ = v___x_5716_;
goto v_reusejp_5718_;
}
else
{
lean_object* v_reuseFailAlloc_5720_; 
v_reuseFailAlloc_5720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5720_, 0, v___x_5707_);
lean_ctor_set(v_reuseFailAlloc_5720_, 1, v_k_5696_);
lean_ctor_set(v_reuseFailAlloc_5720_, 2, v_v_5697_);
lean_ctor_set(v_reuseFailAlloc_5720_, 3, v___y_5710_);
lean_ctor_set(v_reuseFailAlloc_5720_, 4, v___x_5714_);
v___x_5719_ = v_reuseFailAlloc_5720_;
goto v_reusejp_5718_;
}
v_reusejp_5718_:
{
return v___x_5719_;
}
}
}
}
v___jp_5729_:
{
lean_object* v___x_5731_; lean_object* v___x_5733_; 
v___x_5731_ = lean_nat_add(v___x_5728_, v___y_5730_);
lean_dec(v___y_5730_);
lean_dec(v___x_5728_);
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 4, v_l_5698_);
lean_ctor_set(v___x_5676_, 3, v_l_5525_);
lean_ctor_set(v___x_5676_, 2, v_v_5524_);
lean_ctor_set(v___x_5676_, 1, v_k_5523_);
lean_ctor_set(v___x_5676_, 0, v___x_5731_);
v___x_5733_ = v___x_5676_;
goto v_reusejp_5732_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v___x_5731_);
lean_ctor_set(v_reuseFailAlloc_5737_, 1, v_k_5523_);
lean_ctor_set(v_reuseFailAlloc_5737_, 2, v_v_5524_);
lean_ctor_set(v_reuseFailAlloc_5737_, 3, v_l_5525_);
lean_ctor_set(v_reuseFailAlloc_5737_, 4, v_l_5698_);
v___x_5733_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5732_;
}
v_reusejp_5732_:
{
lean_object* v___x_5734_; 
v___x_5734_ = lean_nat_add(v___x_5532_, v_size_5682_);
if (lean_obj_tag(v_r_5699_) == 0)
{
lean_object* v_size_5735_; 
v_size_5735_ = lean_ctor_get(v_r_5699_, 0);
lean_inc(v_size_5735_);
v___y_5709_ = v___x_5734_;
v___y_5710_ = v___x_5733_;
v___y_5711_ = v_size_5735_;
goto v___jp_5708_;
}
else
{
lean_object* v___x_5736_; 
v___x_5736_ = lean_unsigned_to_nat(0u);
v___y_5709_ = v___x_5734_;
v___y_5710_ = v___x_5733_;
v___y_5711_ = v___x_5736_;
goto v___jp_5708_;
}
}
}
}
}
else
{
lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5751_; 
v___x_5746_ = lean_nat_add(v___x_5532_, v_size_5522_);
lean_dec(v_size_5522_);
v___x_5747_ = lean_nat_add(v___x_5746_, v_size_5682_);
lean_dec(v___x_5746_);
v___x_5748_ = lean_nat_add(v___x_5532_, v_size_5682_);
v___x_5749_ = lean_nat_add(v___x_5748_, v_size_5695_);
lean_dec(v___x_5748_);
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 4, v_tree_5679_);
lean_ctor_set(v___x_5676_, 3, v_r_5526_);
lean_ctor_set(v___x_5676_, 2, v_v_5681_);
lean_ctor_set(v___x_5676_, 1, v_k_5680_);
lean_ctor_set(v___x_5676_, 0, v___x_5749_);
v___x_5751_ = v___x_5676_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v___x_5749_);
lean_ctor_set(v_reuseFailAlloc_5755_, 1, v_k_5680_);
lean_ctor_set(v_reuseFailAlloc_5755_, 2, v_v_5681_);
lean_ctor_set(v_reuseFailAlloc_5755_, 3, v_r_5526_);
lean_ctor_set(v_reuseFailAlloc_5755_, 4, v_tree_5679_);
v___x_5751_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
lean_object* v___x_5753_; 
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 4, v___x_5751_);
lean_ctor_set(v___x_5692_, 0, v___x_5747_);
v___x_5753_ = v___x_5692_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5747_);
lean_ctor_set(v_reuseFailAlloc_5754_, 1, v_k_5523_);
lean_ctor_set(v_reuseFailAlloc_5754_, 2, v_v_5524_);
lean_ctor_set(v_reuseFailAlloc_5754_, 3, v_l_5525_);
lean_ctor_set(v_reuseFailAlloc_5754_, 4, v___x_5751_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_5525_) == 0)
{
lean_object* v___x_5763_; uint8_t v_isShared_5764_; uint8_t v_isSharedCheck_5785_; 
lean_inc_ref(v_l_5525_);
lean_inc(v_v_5524_);
lean_inc(v_k_5523_);
lean_inc(v_size_5522_);
v_isSharedCheck_5785_ = !lean_is_exclusive(v_l_5342_);
if (v_isSharedCheck_5785_ == 0)
{
lean_object* v_unused_5786_; lean_object* v_unused_5787_; lean_object* v_unused_5788_; lean_object* v_unused_5789_; lean_object* v_unused_5790_; 
v_unused_5786_ = lean_ctor_get(v_l_5342_, 4);
lean_dec(v_unused_5786_);
v_unused_5787_ = lean_ctor_get(v_l_5342_, 3);
lean_dec(v_unused_5787_);
v_unused_5788_ = lean_ctor_get(v_l_5342_, 2);
lean_dec(v_unused_5788_);
v_unused_5789_ = lean_ctor_get(v_l_5342_, 1);
lean_dec(v_unused_5789_);
v_unused_5790_ = lean_ctor_get(v_l_5342_, 0);
lean_dec(v_unused_5790_);
v___x_5763_ = v_l_5342_;
v_isShared_5764_ = v_isSharedCheck_5785_;
goto v_resetjp_5762_;
}
else
{
lean_dec(v_l_5342_);
v___x_5763_ = lean_box(0);
v_isShared_5764_ = v_isSharedCheck_5785_;
goto v_resetjp_5762_;
}
v_resetjp_5762_:
{
if (lean_obj_tag(v_r_5526_) == 0)
{
lean_object* v_k_5765_; lean_object* v_v_5766_; lean_object* v_size_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5771_; 
v_k_5765_ = lean_ctor_get(v___x_5678_, 0);
lean_inc(v_k_5765_);
v_v_5766_ = lean_ctor_get(v___x_5678_, 1);
lean_inc(v_v_5766_);
lean_dec_ref(v___x_5678_);
v_size_5767_ = lean_ctor_get(v_r_5526_, 0);
v___x_5768_ = lean_nat_add(v___x_5532_, v_size_5522_);
lean_dec(v_size_5522_);
v___x_5769_ = lean_nat_add(v___x_5532_, v_size_5767_);
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 4, v_tree_5679_);
lean_ctor_set(v___x_5676_, 3, v_r_5526_);
lean_ctor_set(v___x_5676_, 2, v_v_5766_);
lean_ctor_set(v___x_5676_, 1, v_k_5765_);
lean_ctor_set(v___x_5676_, 0, v___x_5769_);
v___x_5771_ = v___x_5676_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5769_);
lean_ctor_set(v_reuseFailAlloc_5775_, 1, v_k_5765_);
lean_ctor_set(v_reuseFailAlloc_5775_, 2, v_v_5766_);
lean_ctor_set(v_reuseFailAlloc_5775_, 3, v_r_5526_);
lean_ctor_set(v_reuseFailAlloc_5775_, 4, v_tree_5679_);
v___x_5771_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
lean_object* v___x_5773_; 
if (v_isShared_5764_ == 0)
{
lean_ctor_set(v___x_5763_, 4, v___x_5771_);
lean_ctor_set(v___x_5763_, 0, v___x_5768_);
v___x_5773_ = v___x_5763_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v___x_5768_);
lean_ctor_set(v_reuseFailAlloc_5774_, 1, v_k_5523_);
lean_ctor_set(v_reuseFailAlloc_5774_, 2, v_v_5524_);
lean_ctor_set(v_reuseFailAlloc_5774_, 3, v_l_5525_);
lean_ctor_set(v_reuseFailAlloc_5774_, 4, v___x_5771_);
v___x_5773_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
return v___x_5773_;
}
}
}
else
{
lean_object* v_k_5776_; lean_object* v_v_5777_; lean_object* v___x_5778_; lean_object* v___x_5780_; 
lean_dec(v_size_5522_);
v_k_5776_ = lean_ctor_get(v___x_5678_, 0);
lean_inc(v_k_5776_);
v_v_5777_ = lean_ctor_get(v___x_5678_, 1);
lean_inc(v_v_5777_);
lean_dec_ref(v___x_5678_);
v___x_5778_ = lean_unsigned_to_nat(3u);
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 4, v_r_5526_);
lean_ctor_set(v___x_5676_, 3, v_r_5526_);
lean_ctor_set(v___x_5676_, 2, v_v_5777_);
lean_ctor_set(v___x_5676_, 1, v_k_5776_);
lean_ctor_set(v___x_5676_, 0, v___x_5532_);
v___x_5780_ = v___x_5676_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5784_, 1, v_k_5776_);
lean_ctor_set(v_reuseFailAlloc_5784_, 2, v_v_5777_);
lean_ctor_set(v_reuseFailAlloc_5784_, 3, v_r_5526_);
lean_ctor_set(v_reuseFailAlloc_5784_, 4, v_r_5526_);
v___x_5780_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
lean_object* v___x_5782_; 
if (v_isShared_5764_ == 0)
{
lean_ctor_set(v___x_5763_, 4, v___x_5780_);
lean_ctor_set(v___x_5763_, 0, v___x_5778_);
v___x_5782_ = v___x_5763_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v___x_5778_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v_k_5523_);
lean_ctor_set(v_reuseFailAlloc_5783_, 2, v_v_5524_);
lean_ctor_set(v_reuseFailAlloc_5783_, 3, v_l_5525_);
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
else
{
if (lean_obj_tag(v_r_5526_) == 0)
{
lean_object* v___x_5792_; uint8_t v_isShared_5793_; uint8_t v_isSharedCheck_5815_; 
lean_inc(v_l_5525_);
lean_inc(v_v_5524_);
lean_inc(v_k_5523_);
v_isSharedCheck_5815_ = !lean_is_exclusive(v_l_5342_);
if (v_isSharedCheck_5815_ == 0)
{
lean_object* v_unused_5816_; lean_object* v_unused_5817_; lean_object* v_unused_5818_; lean_object* v_unused_5819_; lean_object* v_unused_5820_; 
v_unused_5816_ = lean_ctor_get(v_l_5342_, 4);
lean_dec(v_unused_5816_);
v_unused_5817_ = lean_ctor_get(v_l_5342_, 3);
lean_dec(v_unused_5817_);
v_unused_5818_ = lean_ctor_get(v_l_5342_, 2);
lean_dec(v_unused_5818_);
v_unused_5819_ = lean_ctor_get(v_l_5342_, 1);
lean_dec(v_unused_5819_);
v_unused_5820_ = lean_ctor_get(v_l_5342_, 0);
lean_dec(v_unused_5820_);
v___x_5792_ = v_l_5342_;
v_isShared_5793_ = v_isSharedCheck_5815_;
goto v_resetjp_5791_;
}
else
{
lean_dec(v_l_5342_);
v___x_5792_ = lean_box(0);
v_isShared_5793_ = v_isSharedCheck_5815_;
goto v_resetjp_5791_;
}
v_resetjp_5791_:
{
lean_object* v_k_5794_; lean_object* v_v_5795_; lean_object* v_k_5796_; lean_object* v_v_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5811_; 
v_k_5794_ = lean_ctor_get(v___x_5678_, 0);
lean_inc(v_k_5794_);
v_v_5795_ = lean_ctor_get(v___x_5678_, 1);
lean_inc(v_v_5795_);
lean_dec_ref(v___x_5678_);
v_k_5796_ = lean_ctor_get(v_r_5526_, 1);
v_v_5797_ = lean_ctor_get(v_r_5526_, 2);
v_isSharedCheck_5811_ = !lean_is_exclusive(v_r_5526_);
if (v_isSharedCheck_5811_ == 0)
{
lean_object* v_unused_5812_; lean_object* v_unused_5813_; lean_object* v_unused_5814_; 
v_unused_5812_ = lean_ctor_get(v_r_5526_, 4);
lean_dec(v_unused_5812_);
v_unused_5813_ = lean_ctor_get(v_r_5526_, 3);
lean_dec(v_unused_5813_);
v_unused_5814_ = lean_ctor_get(v_r_5526_, 0);
lean_dec(v_unused_5814_);
v___x_5799_ = v_r_5526_;
v_isShared_5800_ = v_isSharedCheck_5811_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_v_5797_);
lean_inc(v_k_5796_);
lean_dec(v_r_5526_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5811_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5801_; lean_object* v___x_5803_; 
v___x_5801_ = lean_unsigned_to_nat(3u);
if (v_isShared_5800_ == 0)
{
lean_ctor_set(v___x_5799_, 4, v_l_5525_);
lean_ctor_set(v___x_5799_, 3, v_l_5525_);
lean_ctor_set(v___x_5799_, 2, v_v_5524_);
lean_ctor_set(v___x_5799_, 1, v_k_5523_);
lean_ctor_set(v___x_5799_, 0, v___x_5532_);
v___x_5803_ = v___x_5799_;
goto v_reusejp_5802_;
}
else
{
lean_object* v_reuseFailAlloc_5810_; 
v_reuseFailAlloc_5810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5810_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5810_, 1, v_k_5523_);
lean_ctor_set(v_reuseFailAlloc_5810_, 2, v_v_5524_);
lean_ctor_set(v_reuseFailAlloc_5810_, 3, v_l_5525_);
lean_ctor_set(v_reuseFailAlloc_5810_, 4, v_l_5525_);
v___x_5803_ = v_reuseFailAlloc_5810_;
goto v_reusejp_5802_;
}
v_reusejp_5802_:
{
lean_object* v___x_5805_; 
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 4, v_l_5525_);
lean_ctor_set(v___x_5676_, 3, v_l_5525_);
lean_ctor_set(v___x_5676_, 2, v_v_5795_);
lean_ctor_set(v___x_5676_, 1, v_k_5794_);
lean_ctor_set(v___x_5676_, 0, v___x_5532_);
v___x_5805_ = v___x_5676_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5809_; 
v_reuseFailAlloc_5809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5809_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5809_, 1, v_k_5794_);
lean_ctor_set(v_reuseFailAlloc_5809_, 2, v_v_5795_);
lean_ctor_set(v_reuseFailAlloc_5809_, 3, v_l_5525_);
lean_ctor_set(v_reuseFailAlloc_5809_, 4, v_l_5525_);
v___x_5805_ = v_reuseFailAlloc_5809_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
lean_object* v___x_5807_; 
if (v_isShared_5793_ == 0)
{
lean_ctor_set(v___x_5792_, 4, v___x_5805_);
lean_ctor_set(v___x_5792_, 3, v___x_5803_);
lean_ctor_set(v___x_5792_, 2, v_v_5797_);
lean_ctor_set(v___x_5792_, 1, v_k_5796_);
lean_ctor_set(v___x_5792_, 0, v___x_5801_);
v___x_5807_ = v___x_5792_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5808_; 
v_reuseFailAlloc_5808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5808_, 0, v___x_5801_);
lean_ctor_set(v_reuseFailAlloc_5808_, 1, v_k_5796_);
lean_ctor_set(v_reuseFailAlloc_5808_, 2, v_v_5797_);
lean_ctor_set(v_reuseFailAlloc_5808_, 3, v___x_5803_);
lean_ctor_set(v_reuseFailAlloc_5808_, 4, v___x_5805_);
v___x_5807_ = v_reuseFailAlloc_5808_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
return v___x_5807_;
}
}
}
}
}
}
else
{
lean_object* v_k_5821_; lean_object* v_v_5822_; lean_object* v___x_5823_; lean_object* v___x_5825_; 
v_k_5821_ = lean_ctor_get(v___x_5678_, 0);
lean_inc(v_k_5821_);
v_v_5822_ = lean_ctor_get(v___x_5678_, 1);
lean_inc(v_v_5822_);
lean_dec_ref(v___x_5678_);
v___x_5823_ = lean_unsigned_to_nat(2u);
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 4, v_r_5526_);
lean_ctor_set(v___x_5676_, 3, v_l_5342_);
lean_ctor_set(v___x_5676_, 2, v_v_5822_);
lean_ctor_set(v___x_5676_, 1, v_k_5821_);
lean_ctor_set(v___x_5676_, 0, v___x_5823_);
v___x_5825_ = v___x_5676_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v___x_5823_);
lean_ctor_set(v_reuseFailAlloc_5826_, 1, v_k_5821_);
lean_ctor_set(v_reuseFailAlloc_5826_, 2, v_v_5822_);
lean_ctor_set(v_reuseFailAlloc_5826_, 3, v_l_5342_);
lean_ctor_set(v_reuseFailAlloc_5826_, 4, v_r_5526_);
v___x_5825_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
return v___x_5825_;
}
}
}
}
}
}
}
else
{
return v_l_5342_;
}
}
else
{
return v_r_5343_;
}
}
default: 
{
lean_object* v_impl_5833_; lean_object* v___x_5834_; 
v_impl_5833_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5338_, v_r_5343_);
v___x_5834_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5833_) == 0)
{
if (lean_obj_tag(v_l_5342_) == 0)
{
lean_object* v_size_5835_; lean_object* v_size_5836_; lean_object* v_k_5837_; lean_object* v_v_5838_; lean_object* v_l_5839_; lean_object* v_r_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; uint8_t v___x_5843_; 
v_size_5835_ = lean_ctor_get(v_impl_5833_, 0);
lean_inc(v_size_5835_);
v_size_5836_ = lean_ctor_get(v_l_5342_, 0);
v_k_5837_ = lean_ctor_get(v_l_5342_, 1);
v_v_5838_ = lean_ctor_get(v_l_5342_, 2);
v_l_5839_ = lean_ctor_get(v_l_5342_, 3);
v_r_5840_ = lean_ctor_get(v_l_5342_, 4);
lean_inc(v_r_5840_);
v___x_5841_ = lean_unsigned_to_nat(3u);
v___x_5842_ = lean_nat_mul(v___x_5841_, v_size_5835_);
v___x_5843_ = lean_nat_dec_lt(v___x_5842_, v_size_5836_);
lean_dec(v___x_5842_);
if (v___x_5843_ == 0)
{
lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5847_; 
lean_dec(v_r_5840_);
v___x_5844_ = lean_nat_add(v___x_5834_, v_size_5836_);
v___x_5845_ = lean_nat_add(v___x_5844_, v_size_5835_);
lean_dec(v_size_5835_);
lean_dec(v___x_5844_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v_impl_5833_);
lean_ctor_set(v___x_5345_, 0, v___x_5845_);
v___x_5847_ = v___x_5345_;
goto v_reusejp_5846_;
}
else
{
lean_object* v_reuseFailAlloc_5848_; 
v_reuseFailAlloc_5848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5848_, 0, v___x_5845_);
lean_ctor_set(v_reuseFailAlloc_5848_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5848_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5848_, 3, v_l_5342_);
lean_ctor_set(v_reuseFailAlloc_5848_, 4, v_impl_5833_);
v___x_5847_ = v_reuseFailAlloc_5848_;
goto v_reusejp_5846_;
}
v_reusejp_5846_:
{
return v___x_5847_;
}
}
else
{
lean_object* v___x_5850_; uint8_t v_isShared_5851_; uint8_t v_isSharedCheck_5914_; 
lean_inc(v_l_5839_);
lean_inc(v_v_5838_);
lean_inc(v_k_5837_);
lean_inc(v_size_5836_);
v_isSharedCheck_5914_ = !lean_is_exclusive(v_l_5342_);
if (v_isSharedCheck_5914_ == 0)
{
lean_object* v_unused_5915_; lean_object* v_unused_5916_; lean_object* v_unused_5917_; lean_object* v_unused_5918_; lean_object* v_unused_5919_; 
v_unused_5915_ = lean_ctor_get(v_l_5342_, 4);
lean_dec(v_unused_5915_);
v_unused_5916_ = lean_ctor_get(v_l_5342_, 3);
lean_dec(v_unused_5916_);
v_unused_5917_ = lean_ctor_get(v_l_5342_, 2);
lean_dec(v_unused_5917_);
v_unused_5918_ = lean_ctor_get(v_l_5342_, 1);
lean_dec(v_unused_5918_);
v_unused_5919_ = lean_ctor_get(v_l_5342_, 0);
lean_dec(v_unused_5919_);
v___x_5850_ = v_l_5342_;
v_isShared_5851_ = v_isSharedCheck_5914_;
goto v_resetjp_5849_;
}
else
{
lean_dec(v_l_5342_);
v___x_5850_ = lean_box(0);
v_isShared_5851_ = v_isSharedCheck_5914_;
goto v_resetjp_5849_;
}
v_resetjp_5849_:
{
lean_object* v_size_5852_; lean_object* v_size_5853_; lean_object* v_k_5854_; lean_object* v_v_5855_; lean_object* v_l_5856_; lean_object* v_r_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; uint8_t v___x_5860_; 
v_size_5852_ = lean_ctor_get(v_l_5839_, 0);
v_size_5853_ = lean_ctor_get(v_r_5840_, 0);
v_k_5854_ = lean_ctor_get(v_r_5840_, 1);
v_v_5855_ = lean_ctor_get(v_r_5840_, 2);
v_l_5856_ = lean_ctor_get(v_r_5840_, 3);
v_r_5857_ = lean_ctor_get(v_r_5840_, 4);
v___x_5858_ = lean_unsigned_to_nat(2u);
v___x_5859_ = lean_nat_mul(v___x_5858_, v_size_5852_);
v___x_5860_ = lean_nat_dec_lt(v_size_5853_, v___x_5859_);
lean_dec(v___x_5859_);
if (v___x_5860_ == 0)
{
lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5889_; 
lean_inc(v_r_5857_);
lean_inc(v_l_5856_);
lean_inc(v_v_5855_);
lean_inc(v_k_5854_);
v_isSharedCheck_5889_ = !lean_is_exclusive(v_r_5840_);
if (v_isSharedCheck_5889_ == 0)
{
lean_object* v_unused_5890_; lean_object* v_unused_5891_; lean_object* v_unused_5892_; lean_object* v_unused_5893_; lean_object* v_unused_5894_; 
v_unused_5890_ = lean_ctor_get(v_r_5840_, 4);
lean_dec(v_unused_5890_);
v_unused_5891_ = lean_ctor_get(v_r_5840_, 3);
lean_dec(v_unused_5891_);
v_unused_5892_ = lean_ctor_get(v_r_5840_, 2);
lean_dec(v_unused_5892_);
v_unused_5893_ = lean_ctor_get(v_r_5840_, 1);
lean_dec(v_unused_5893_);
v_unused_5894_ = lean_ctor_get(v_r_5840_, 0);
lean_dec(v_unused_5894_);
v___x_5862_ = v_r_5840_;
v_isShared_5863_ = v_isSharedCheck_5889_;
goto v_resetjp_5861_;
}
else
{
lean_dec(v_r_5840_);
v___x_5862_ = lean_box(0);
v_isShared_5863_ = v_isSharedCheck_5889_;
goto v_resetjp_5861_;
}
v_resetjp_5861_:
{
lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___y_5867_; lean_object* v___y_5868_; lean_object* v___y_5869_; lean_object* v___x_5877_; lean_object* v___y_5879_; 
v___x_5864_ = lean_nat_add(v___x_5834_, v_size_5836_);
lean_dec(v_size_5836_);
v___x_5865_ = lean_nat_add(v___x_5864_, v_size_5835_);
lean_dec(v___x_5864_);
v___x_5877_ = lean_nat_add(v___x_5834_, v_size_5852_);
if (lean_obj_tag(v_l_5856_) == 0)
{
lean_object* v_size_5887_; 
v_size_5887_ = lean_ctor_get(v_l_5856_, 0);
lean_inc(v_size_5887_);
v___y_5879_ = v_size_5887_;
goto v___jp_5878_;
}
else
{
lean_object* v___x_5888_; 
v___x_5888_ = lean_unsigned_to_nat(0u);
v___y_5879_ = v___x_5888_;
goto v___jp_5878_;
}
v___jp_5866_:
{
lean_object* v___x_5870_; lean_object* v___x_5872_; 
v___x_5870_ = lean_nat_add(v___y_5867_, v___y_5869_);
lean_dec(v___y_5869_);
lean_dec(v___y_5867_);
if (v_isShared_5863_ == 0)
{
lean_ctor_set(v___x_5862_, 4, v_impl_5833_);
lean_ctor_set(v___x_5862_, 3, v_r_5857_);
lean_ctor_set(v___x_5862_, 2, v_v_5341_);
lean_ctor_set(v___x_5862_, 1, v_k_5340_);
lean_ctor_set(v___x_5862_, 0, v___x_5870_);
v___x_5872_ = v___x_5862_;
goto v_reusejp_5871_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v___x_5870_);
lean_ctor_set(v_reuseFailAlloc_5876_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5876_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5876_, 3, v_r_5857_);
lean_ctor_set(v_reuseFailAlloc_5876_, 4, v_impl_5833_);
v___x_5872_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5871_;
}
v_reusejp_5871_:
{
lean_object* v___x_5874_; 
if (v_isShared_5851_ == 0)
{
lean_ctor_set(v___x_5850_, 4, v___x_5872_);
lean_ctor_set(v___x_5850_, 3, v___y_5868_);
lean_ctor_set(v___x_5850_, 2, v_v_5855_);
lean_ctor_set(v___x_5850_, 1, v_k_5854_);
lean_ctor_set(v___x_5850_, 0, v___x_5865_);
v___x_5874_ = v___x_5850_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v___x_5865_);
lean_ctor_set(v_reuseFailAlloc_5875_, 1, v_k_5854_);
lean_ctor_set(v_reuseFailAlloc_5875_, 2, v_v_5855_);
lean_ctor_set(v_reuseFailAlloc_5875_, 3, v___y_5868_);
lean_ctor_set(v_reuseFailAlloc_5875_, 4, v___x_5872_);
v___x_5874_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
return v___x_5874_;
}
}
}
v___jp_5878_:
{
lean_object* v___x_5880_; lean_object* v___x_5882_; 
v___x_5880_ = lean_nat_add(v___x_5877_, v___y_5879_);
lean_dec(v___y_5879_);
lean_dec(v___x_5877_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v_l_5856_);
lean_ctor_set(v___x_5345_, 3, v_l_5839_);
lean_ctor_set(v___x_5345_, 2, v_v_5838_);
lean_ctor_set(v___x_5345_, 1, v_k_5837_);
lean_ctor_set(v___x_5345_, 0, v___x_5880_);
v___x_5882_ = v___x_5345_;
goto v_reusejp_5881_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v___x_5880_);
lean_ctor_set(v_reuseFailAlloc_5886_, 1, v_k_5837_);
lean_ctor_set(v_reuseFailAlloc_5886_, 2, v_v_5838_);
lean_ctor_set(v_reuseFailAlloc_5886_, 3, v_l_5839_);
lean_ctor_set(v_reuseFailAlloc_5886_, 4, v_l_5856_);
v___x_5882_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5881_;
}
v_reusejp_5881_:
{
lean_object* v___x_5883_; 
v___x_5883_ = lean_nat_add(v___x_5834_, v_size_5835_);
lean_dec(v_size_5835_);
if (lean_obj_tag(v_r_5857_) == 0)
{
lean_object* v_size_5884_; 
v_size_5884_ = lean_ctor_get(v_r_5857_, 0);
lean_inc(v_size_5884_);
v___y_5867_ = v___x_5883_;
v___y_5868_ = v___x_5882_;
v___y_5869_ = v_size_5884_;
goto v___jp_5866_;
}
else
{
lean_object* v___x_5885_; 
v___x_5885_ = lean_unsigned_to_nat(0u);
v___y_5867_ = v___x_5883_;
v___y_5868_ = v___x_5882_;
v___y_5869_ = v___x_5885_;
goto v___jp_5866_;
}
}
}
}
}
else
{
lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5900_; 
lean_del_object(v___x_5345_);
v___x_5895_ = lean_nat_add(v___x_5834_, v_size_5836_);
lean_dec(v_size_5836_);
v___x_5896_ = lean_nat_add(v___x_5895_, v_size_5835_);
lean_dec(v___x_5895_);
v___x_5897_ = lean_nat_add(v___x_5834_, v_size_5835_);
lean_dec(v_size_5835_);
v___x_5898_ = lean_nat_add(v___x_5897_, v_size_5853_);
lean_dec(v___x_5897_);
lean_inc_ref(v_impl_5833_);
if (v_isShared_5851_ == 0)
{
lean_ctor_set(v___x_5850_, 4, v_impl_5833_);
lean_ctor_set(v___x_5850_, 3, v_r_5840_);
lean_ctor_set(v___x_5850_, 2, v_v_5341_);
lean_ctor_set(v___x_5850_, 1, v_k_5340_);
lean_ctor_set(v___x_5850_, 0, v___x_5898_);
v___x_5900_ = v___x_5850_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v___x_5898_);
lean_ctor_set(v_reuseFailAlloc_5913_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5913_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5913_, 3, v_r_5840_);
lean_ctor_set(v_reuseFailAlloc_5913_, 4, v_impl_5833_);
v___x_5900_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5907_; 
v_isSharedCheck_5907_ = !lean_is_exclusive(v_impl_5833_);
if (v_isSharedCheck_5907_ == 0)
{
lean_object* v_unused_5908_; lean_object* v_unused_5909_; lean_object* v_unused_5910_; lean_object* v_unused_5911_; lean_object* v_unused_5912_; 
v_unused_5908_ = lean_ctor_get(v_impl_5833_, 4);
lean_dec(v_unused_5908_);
v_unused_5909_ = lean_ctor_get(v_impl_5833_, 3);
lean_dec(v_unused_5909_);
v_unused_5910_ = lean_ctor_get(v_impl_5833_, 2);
lean_dec(v_unused_5910_);
v_unused_5911_ = lean_ctor_get(v_impl_5833_, 1);
lean_dec(v_unused_5911_);
v_unused_5912_ = lean_ctor_get(v_impl_5833_, 0);
lean_dec(v_unused_5912_);
v___x_5902_ = v_impl_5833_;
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
else
{
lean_dec(v_impl_5833_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v___x_5905_; 
if (v_isShared_5903_ == 0)
{
lean_ctor_set(v___x_5902_, 4, v___x_5900_);
lean_ctor_set(v___x_5902_, 3, v_l_5839_);
lean_ctor_set(v___x_5902_, 2, v_v_5838_);
lean_ctor_set(v___x_5902_, 1, v_k_5837_);
lean_ctor_set(v___x_5902_, 0, v___x_5896_);
v___x_5905_ = v___x_5902_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5906_; 
v_reuseFailAlloc_5906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5906_, 0, v___x_5896_);
lean_ctor_set(v_reuseFailAlloc_5906_, 1, v_k_5837_);
lean_ctor_set(v_reuseFailAlloc_5906_, 2, v_v_5838_);
lean_ctor_set(v_reuseFailAlloc_5906_, 3, v_l_5839_);
lean_ctor_set(v_reuseFailAlloc_5906_, 4, v___x_5900_);
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
}
else
{
lean_object* v_size_5920_; lean_object* v___x_5921_; lean_object* v___x_5923_; 
v_size_5920_ = lean_ctor_get(v_impl_5833_, 0);
lean_inc(v_size_5920_);
v___x_5921_ = lean_nat_add(v___x_5834_, v_size_5920_);
lean_dec(v_size_5920_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v_impl_5833_);
lean_ctor_set(v___x_5345_, 0, v___x_5921_);
v___x_5923_ = v___x_5345_;
goto v_reusejp_5922_;
}
else
{
lean_object* v_reuseFailAlloc_5924_; 
v_reuseFailAlloc_5924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5924_, 0, v___x_5921_);
lean_ctor_set(v_reuseFailAlloc_5924_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5924_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5924_, 3, v_l_5342_);
lean_ctor_set(v_reuseFailAlloc_5924_, 4, v_impl_5833_);
v___x_5923_ = v_reuseFailAlloc_5924_;
goto v_reusejp_5922_;
}
v_reusejp_5922_:
{
return v___x_5923_;
}
}
}
else
{
if (lean_obj_tag(v_l_5342_) == 0)
{
lean_object* v_l_5925_; 
v_l_5925_ = lean_ctor_get(v_l_5342_, 3);
if (lean_obj_tag(v_l_5925_) == 0)
{
lean_object* v_r_5926_; 
lean_inc_ref(v_l_5925_);
v_r_5926_ = lean_ctor_get(v_l_5342_, 4);
lean_inc(v_r_5926_);
if (lean_obj_tag(v_r_5926_) == 0)
{
lean_object* v_size_5927_; lean_object* v_k_5928_; lean_object* v_v_5929_; lean_object* v___x_5931_; uint8_t v_isShared_5932_; uint8_t v_isSharedCheck_5942_; 
v_size_5927_ = lean_ctor_get(v_l_5342_, 0);
v_k_5928_ = lean_ctor_get(v_l_5342_, 1);
v_v_5929_ = lean_ctor_get(v_l_5342_, 2);
v_isSharedCheck_5942_ = !lean_is_exclusive(v_l_5342_);
if (v_isSharedCheck_5942_ == 0)
{
lean_object* v_unused_5943_; lean_object* v_unused_5944_; 
v_unused_5943_ = lean_ctor_get(v_l_5342_, 4);
lean_dec(v_unused_5943_);
v_unused_5944_ = lean_ctor_get(v_l_5342_, 3);
lean_dec(v_unused_5944_);
v___x_5931_ = v_l_5342_;
v_isShared_5932_ = v_isSharedCheck_5942_;
goto v_resetjp_5930_;
}
else
{
lean_inc(v_v_5929_);
lean_inc(v_k_5928_);
lean_inc(v_size_5927_);
lean_dec(v_l_5342_);
v___x_5931_ = lean_box(0);
v_isShared_5932_ = v_isSharedCheck_5942_;
goto v_resetjp_5930_;
}
v_resetjp_5930_:
{
lean_object* v_size_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5937_; 
v_size_5933_ = lean_ctor_get(v_r_5926_, 0);
v___x_5934_ = lean_nat_add(v___x_5834_, v_size_5927_);
lean_dec(v_size_5927_);
v___x_5935_ = lean_nat_add(v___x_5834_, v_size_5933_);
if (v_isShared_5932_ == 0)
{
lean_ctor_set(v___x_5931_, 4, v_impl_5833_);
lean_ctor_set(v___x_5931_, 3, v_r_5926_);
lean_ctor_set(v___x_5931_, 2, v_v_5341_);
lean_ctor_set(v___x_5931_, 1, v_k_5340_);
lean_ctor_set(v___x_5931_, 0, v___x_5935_);
v___x_5937_ = v___x_5931_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5941_; 
v_reuseFailAlloc_5941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5941_, 0, v___x_5935_);
lean_ctor_set(v_reuseFailAlloc_5941_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5941_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5941_, 3, v_r_5926_);
lean_ctor_set(v_reuseFailAlloc_5941_, 4, v_impl_5833_);
v___x_5937_ = v_reuseFailAlloc_5941_;
goto v_reusejp_5936_;
}
v_reusejp_5936_:
{
lean_object* v___x_5939_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v___x_5937_);
lean_ctor_set(v___x_5345_, 3, v_l_5925_);
lean_ctor_set(v___x_5345_, 2, v_v_5929_);
lean_ctor_set(v___x_5345_, 1, v_k_5928_);
lean_ctor_set(v___x_5345_, 0, v___x_5934_);
v___x_5939_ = v___x_5345_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v___x_5934_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v_k_5928_);
lean_ctor_set(v_reuseFailAlloc_5940_, 2, v_v_5929_);
lean_ctor_set(v_reuseFailAlloc_5940_, 3, v_l_5925_);
lean_ctor_set(v_reuseFailAlloc_5940_, 4, v___x_5937_);
v___x_5939_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
return v___x_5939_;
}
}
}
}
else
{
lean_object* v_k_5945_; lean_object* v_v_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5957_; 
v_k_5945_ = lean_ctor_get(v_l_5342_, 1);
v_v_5946_ = lean_ctor_get(v_l_5342_, 2);
v_isSharedCheck_5957_ = !lean_is_exclusive(v_l_5342_);
if (v_isSharedCheck_5957_ == 0)
{
lean_object* v_unused_5958_; lean_object* v_unused_5959_; lean_object* v_unused_5960_; 
v_unused_5958_ = lean_ctor_get(v_l_5342_, 4);
lean_dec(v_unused_5958_);
v_unused_5959_ = lean_ctor_get(v_l_5342_, 3);
lean_dec(v_unused_5959_);
v_unused_5960_ = lean_ctor_get(v_l_5342_, 0);
lean_dec(v_unused_5960_);
v___x_5948_ = v_l_5342_;
v_isShared_5949_ = v_isSharedCheck_5957_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_v_5946_);
lean_inc(v_k_5945_);
lean_dec(v_l_5342_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5957_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5950_; lean_object* v___x_5952_; 
v___x_5950_ = lean_unsigned_to_nat(3u);
if (v_isShared_5949_ == 0)
{
lean_ctor_set(v___x_5948_, 3, v_r_5926_);
lean_ctor_set(v___x_5948_, 2, v_v_5341_);
lean_ctor_set(v___x_5948_, 1, v_k_5340_);
lean_ctor_set(v___x_5948_, 0, v___x_5834_);
v___x_5952_ = v___x_5948_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5956_; 
v_reuseFailAlloc_5956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5956_, 0, v___x_5834_);
lean_ctor_set(v_reuseFailAlloc_5956_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5956_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5956_, 3, v_r_5926_);
lean_ctor_set(v_reuseFailAlloc_5956_, 4, v_r_5926_);
v___x_5952_ = v_reuseFailAlloc_5956_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
lean_object* v___x_5954_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v___x_5952_);
lean_ctor_set(v___x_5345_, 3, v_l_5925_);
lean_ctor_set(v___x_5345_, 2, v_v_5946_);
lean_ctor_set(v___x_5345_, 1, v_k_5945_);
lean_ctor_set(v___x_5345_, 0, v___x_5950_);
v___x_5954_ = v___x_5345_;
goto v_reusejp_5953_;
}
else
{
lean_object* v_reuseFailAlloc_5955_; 
v_reuseFailAlloc_5955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5955_, 0, v___x_5950_);
lean_ctor_set(v_reuseFailAlloc_5955_, 1, v_k_5945_);
lean_ctor_set(v_reuseFailAlloc_5955_, 2, v_v_5946_);
lean_ctor_set(v_reuseFailAlloc_5955_, 3, v_l_5925_);
lean_ctor_set(v_reuseFailAlloc_5955_, 4, v___x_5952_);
v___x_5954_ = v_reuseFailAlloc_5955_;
goto v_reusejp_5953_;
}
v_reusejp_5953_:
{
return v___x_5954_;
}
}
}
}
}
else
{
lean_object* v_r_5961_; 
v_r_5961_ = lean_ctor_get(v_l_5342_, 4);
lean_inc(v_r_5961_);
if (lean_obj_tag(v_r_5961_) == 0)
{
lean_object* v_k_5962_; lean_object* v_v_5963_; lean_object* v___x_5965_; uint8_t v_isShared_5966_; uint8_t v_isSharedCheck_5986_; 
lean_inc(v_l_5925_);
v_k_5962_ = lean_ctor_get(v_l_5342_, 1);
v_v_5963_ = lean_ctor_get(v_l_5342_, 2);
v_isSharedCheck_5986_ = !lean_is_exclusive(v_l_5342_);
if (v_isSharedCheck_5986_ == 0)
{
lean_object* v_unused_5987_; lean_object* v_unused_5988_; lean_object* v_unused_5989_; 
v_unused_5987_ = lean_ctor_get(v_l_5342_, 4);
lean_dec(v_unused_5987_);
v_unused_5988_ = lean_ctor_get(v_l_5342_, 3);
lean_dec(v_unused_5988_);
v_unused_5989_ = lean_ctor_get(v_l_5342_, 0);
lean_dec(v_unused_5989_);
v___x_5965_ = v_l_5342_;
v_isShared_5966_ = v_isSharedCheck_5986_;
goto v_resetjp_5964_;
}
else
{
lean_inc(v_v_5963_);
lean_inc(v_k_5962_);
lean_dec(v_l_5342_);
v___x_5965_ = lean_box(0);
v_isShared_5966_ = v_isSharedCheck_5986_;
goto v_resetjp_5964_;
}
v_resetjp_5964_:
{
lean_object* v_k_5967_; lean_object* v_v_5968_; lean_object* v___x_5970_; uint8_t v_isShared_5971_; uint8_t v_isSharedCheck_5982_; 
v_k_5967_ = lean_ctor_get(v_r_5961_, 1);
v_v_5968_ = lean_ctor_get(v_r_5961_, 2);
v_isSharedCheck_5982_ = !lean_is_exclusive(v_r_5961_);
if (v_isSharedCheck_5982_ == 0)
{
lean_object* v_unused_5983_; lean_object* v_unused_5984_; lean_object* v_unused_5985_; 
v_unused_5983_ = lean_ctor_get(v_r_5961_, 4);
lean_dec(v_unused_5983_);
v_unused_5984_ = lean_ctor_get(v_r_5961_, 3);
lean_dec(v_unused_5984_);
v_unused_5985_ = lean_ctor_get(v_r_5961_, 0);
lean_dec(v_unused_5985_);
v___x_5970_ = v_r_5961_;
v_isShared_5971_ = v_isSharedCheck_5982_;
goto v_resetjp_5969_;
}
else
{
lean_inc(v_v_5968_);
lean_inc(v_k_5967_);
lean_dec(v_r_5961_);
v___x_5970_ = lean_box(0);
v_isShared_5971_ = v_isSharedCheck_5982_;
goto v_resetjp_5969_;
}
v_resetjp_5969_:
{
lean_object* v___x_5972_; lean_object* v___x_5974_; 
v___x_5972_ = lean_unsigned_to_nat(3u);
if (v_isShared_5971_ == 0)
{
lean_ctor_set(v___x_5970_, 4, v_l_5925_);
lean_ctor_set(v___x_5970_, 3, v_l_5925_);
lean_ctor_set(v___x_5970_, 2, v_v_5963_);
lean_ctor_set(v___x_5970_, 1, v_k_5962_);
lean_ctor_set(v___x_5970_, 0, v___x_5834_);
v___x_5974_ = v___x_5970_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5981_; 
v_reuseFailAlloc_5981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5981_, 0, v___x_5834_);
lean_ctor_set(v_reuseFailAlloc_5981_, 1, v_k_5962_);
lean_ctor_set(v_reuseFailAlloc_5981_, 2, v_v_5963_);
lean_ctor_set(v_reuseFailAlloc_5981_, 3, v_l_5925_);
lean_ctor_set(v_reuseFailAlloc_5981_, 4, v_l_5925_);
v___x_5974_ = v_reuseFailAlloc_5981_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
lean_object* v___x_5976_; 
if (v_isShared_5966_ == 0)
{
lean_ctor_set(v___x_5965_, 4, v_l_5925_);
lean_ctor_set(v___x_5965_, 2, v_v_5341_);
lean_ctor_set(v___x_5965_, 1, v_k_5340_);
lean_ctor_set(v___x_5965_, 0, v___x_5834_);
v___x_5976_ = v___x_5965_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v___x_5834_);
lean_ctor_set(v_reuseFailAlloc_5980_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5980_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5980_, 3, v_l_5925_);
lean_ctor_set(v_reuseFailAlloc_5980_, 4, v_l_5925_);
v___x_5976_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
lean_object* v___x_5978_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v___x_5976_);
lean_ctor_set(v___x_5345_, 3, v___x_5974_);
lean_ctor_set(v___x_5345_, 2, v_v_5968_);
lean_ctor_set(v___x_5345_, 1, v_k_5967_);
lean_ctor_set(v___x_5345_, 0, v___x_5972_);
v___x_5978_ = v___x_5345_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v___x_5972_);
lean_ctor_set(v_reuseFailAlloc_5979_, 1, v_k_5967_);
lean_ctor_set(v_reuseFailAlloc_5979_, 2, v_v_5968_);
lean_ctor_set(v_reuseFailAlloc_5979_, 3, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5979_, 4, v___x_5976_);
v___x_5978_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
return v___x_5978_;
}
}
}
}
}
}
else
{
lean_object* v___x_5990_; lean_object* v___x_5992_; 
v___x_5990_ = lean_unsigned_to_nat(2u);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v_r_5961_);
lean_ctor_set(v___x_5345_, 0, v___x_5990_);
v___x_5992_ = v___x_5345_;
goto v_reusejp_5991_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v___x_5990_);
lean_ctor_set(v_reuseFailAlloc_5993_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5993_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5993_, 3, v_l_5342_);
lean_ctor_set(v_reuseFailAlloc_5993_, 4, v_r_5961_);
v___x_5992_ = v_reuseFailAlloc_5993_;
goto v_reusejp_5991_;
}
v_reusejp_5991_:
{
return v___x_5992_;
}
}
}
}
else
{
lean_object* v___x_5995_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 4, v_l_5342_);
lean_ctor_set(v___x_5345_, 0, v___x_5834_);
v___x_5995_ = v___x_5345_;
goto v_reusejp_5994_;
}
else
{
lean_object* v_reuseFailAlloc_5996_; 
v_reuseFailAlloc_5996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5996_, 0, v___x_5834_);
lean_ctor_set(v_reuseFailAlloc_5996_, 1, v_k_5340_);
lean_ctor_set(v_reuseFailAlloc_5996_, 2, v_v_5341_);
lean_ctor_set(v_reuseFailAlloc_5996_, 3, v_l_5342_);
lean_ctor_set(v_reuseFailAlloc_5996_, 4, v_l_5342_);
v___x_5995_ = v_reuseFailAlloc_5996_;
goto v_reusejp_5994_;
}
v_reusejp_5994_:
{
return v___x_5995_;
}
}
}
}
}
}
}
else
{
return v_t_5339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_5999_, lean_object* v_t_6000_){
_start:
{
lean_object* v_res_6001_; 
v_res_6001_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5999_, v_t_6000_);
lean_dec(v_k_5999_);
return v_res_6001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_6002_, lean_object* v_x_6003_){
_start:
{
if (lean_obj_tag(v_x_6003_) == 0)
{
lean_object* v_k_6004_; lean_object* v_l_6005_; lean_object* v_r_6006_; lean_object* v___x_6007_; lean_object* v_ileans_6008_; lean_object* v_workers_6009_; lean_object* v___x_6011_; uint8_t v_isShared_6012_; uint8_t v_isSharedCheck_6018_; 
v_k_6004_ = lean_ctor_get(v_x_6003_, 1);
v_l_6005_ = lean_ctor_get(v_x_6003_, 3);
v_r_6006_ = lean_ctor_get(v_x_6003_, 4);
v___x_6007_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6002_, v_l_6005_);
v_ileans_6008_ = lean_ctor_get(v___x_6007_, 0);
v_workers_6009_ = lean_ctor_get(v___x_6007_, 1);
v_isSharedCheck_6018_ = !lean_is_exclusive(v___x_6007_);
if (v_isSharedCheck_6018_ == 0)
{
v___x_6011_ = v___x_6007_;
v_isShared_6012_ = v_isSharedCheck_6018_;
goto v_resetjp_6010_;
}
else
{
lean_inc(v_workers_6009_);
lean_inc(v_ileans_6008_);
lean_dec(v___x_6007_);
v___x_6011_ = lean_box(0);
v_isShared_6012_ = v_isSharedCheck_6018_;
goto v_resetjp_6010_;
}
v_resetjp_6010_:
{
lean_object* v___x_6013_; lean_object* v___x_6015_; 
v___x_6013_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6004_, v_ileans_6008_);
if (v_isShared_6012_ == 0)
{
lean_ctor_set(v___x_6011_, 0, v___x_6013_);
v___x_6015_ = v___x_6011_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6017_; 
v_reuseFailAlloc_6017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6017_, 0, v___x_6013_);
lean_ctor_set(v_reuseFailAlloc_6017_, 1, v_workers_6009_);
v___x_6015_ = v_reuseFailAlloc_6017_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
v_init_6002_ = v___x_6015_;
v_x_6003_ = v_r_6006_;
goto _start;
}
}
}
else
{
return v_init_6002_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_6019_, lean_object* v_x_6020_){
_start:
{
lean_object* v_res_6021_; 
v_res_6021_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6019_, v_x_6020_);
lean_dec(v_x_6020_);
return v_res_6021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_6022_, lean_object* v_path_6023_){
_start:
{
lean_object* v_ileans_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; 
v_ileans_6024_ = lean_ctor_get(v_self_6022_, 0);
lean_inc(v_ileans_6024_);
v___x_6025_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6023_, v_ileans_6024_);
v___x_6026_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_6022_, v___x_6025_);
lean_dec(v___x_6025_);
return v___x_6026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_6027_, lean_object* v_path_6028_){
_start:
{
lean_object* v_res_6029_; 
v_res_6029_ = l_Lean_Server_References_removeIlean(v_self_6027_, v_path_6028_);
lean_dec_ref(v_path_6028_);
return v_res_6029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_6030_, lean_object* v_k_6031_, lean_object* v_t_6032_, lean_object* v_h_6033_){
_start:
{
lean_object* v___x_6034_; 
v___x_6034_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6031_, v_t_6032_);
return v___x_6034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_6035_, lean_object* v_k_6036_, lean_object* v_t_6037_, lean_object* v_h_6038_){
_start:
{
lean_object* v_res_6039_; 
v_res_6039_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_6035_, v_k_6036_, v_t_6037_, v_h_6038_);
lean_dec(v_k_6036_);
return v_res_6039_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_6040_, lean_object* v_t_6041_, lean_object* v_hl_6042_){
_start:
{
lean_object* v___x_6043_; 
v___x_6043_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6040_, v_t_6041_);
return v___x_6043_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_6044_, lean_object* v_t_6045_, lean_object* v_hl_6046_){
_start:
{
lean_object* v_res_6047_; 
v_res_6047_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_6044_, v_t_6045_, v_hl_6046_);
lean_dec_ref(v_path_6044_);
return v_res_6047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_6048_, lean_object* v_t_6049_){
_start:
{
lean_object* v___x_6050_; 
v___x_6050_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6048_, v_t_6049_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_6051_, lean_object* v_t_6052_){
_start:
{
lean_object* v_res_6053_; 
v_res_6053_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_6051_, v_t_6052_);
lean_dec(v_t_6052_);
return v_res_6053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_6054_, lean_object* v_k_6055_){
_start:
{
if (lean_obj_tag(v_t_6054_) == 0)
{
lean_object* v_k_6056_; lean_object* v_v_6057_; lean_object* v_l_6058_; lean_object* v_r_6059_; uint8_t v___x_6060_; 
v_k_6056_ = lean_ctor_get(v_t_6054_, 1);
v_v_6057_ = lean_ctor_get(v_t_6054_, 2);
v_l_6058_ = lean_ctor_get(v_t_6054_, 3);
v_r_6059_ = lean_ctor_get(v_t_6054_, 4);
v___x_6060_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6055_, v_k_6056_);
switch(v___x_6060_)
{
case 0:
{
v_t_6054_ = v_l_6058_;
goto _start;
}
case 1:
{
lean_object* v___x_6062_; 
lean_inc(v_v_6057_);
v___x_6062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6062_, 0, v_v_6057_);
return v___x_6062_;
}
default: 
{
v_t_6054_ = v_r_6059_;
goto _start;
}
}
}
else
{
lean_object* v___x_6064_; 
v___x_6064_ = lean_box(0);
return v___x_6064_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_6065_, lean_object* v_k_6066_){
_start:
{
lean_object* v_res_6067_; 
v_res_6067_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6065_, v_k_6066_);
lean_dec(v_k_6066_);
lean_dec(v_t_6065_);
return v_res_6067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_6068_, lean_object* v_name_6069_, lean_object* v_moduleUri_6070_, lean_object* v_version_6071_, lean_object* v_directImports_6072_, uint8_t v_isSetupFailure_6073_){
_start:
{
lean_object* v___x_6075_; 
v___x_6075_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_6072_);
if (lean_obj_tag(v___x_6075_) == 0)
{
lean_object* v_a_6076_; lean_object* v___x_6078_; uint8_t v_isShared_6079_; uint8_t v_isSharedCheck_6142_; 
v_a_6076_ = lean_ctor_get(v___x_6075_, 0);
v_isSharedCheck_6142_ = !lean_is_exclusive(v___x_6075_);
if (v_isSharedCheck_6142_ == 0)
{
v___x_6078_ = v___x_6075_;
v_isShared_6079_ = v_isSharedCheck_6142_;
goto v_resetjp_6077_;
}
else
{
lean_inc(v_a_6076_);
lean_dec(v___x_6075_);
v___x_6078_ = lean_box(0);
v_isShared_6079_ = v_isSharedCheck_6142_;
goto v_resetjp_6077_;
}
v_resetjp_6077_:
{
lean_object* v_ileans_6080_; lean_object* v_workers_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; 
v_ileans_6080_ = lean_ctor_get(v_self_6068_, 0);
v_workers_6081_ = lean_ctor_get(v_self_6068_, 1);
v___x_6082_ = lean_box(1);
v___x_6083_ = lean_box(v_isSetupFailure_6073_);
v___x_6084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6083_);
v___x_6085_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6081_, v_name_6069_);
if (lean_obj_tag(v___x_6085_) == 1)
{
lean_object* v_val_6086_; lean_object* v_version_6087_; lean_object* v_refs_6088_; lean_object* v_decls_6089_; lean_object* v___x_6091_; uint8_t v_isShared_6092_; uint8_t v_isSharedCheck_6124_; 
v_val_6086_ = lean_ctor_get(v___x_6085_, 0);
lean_inc(v_val_6086_);
lean_dec_ref(v___x_6085_);
v_version_6087_ = lean_ctor_get(v_val_6086_, 1);
v_refs_6088_ = lean_ctor_get(v_val_6086_, 4);
v_decls_6089_ = lean_ctor_get(v_val_6086_, 5);
v_isSharedCheck_6124_ = !lean_is_exclusive(v_val_6086_);
if (v_isSharedCheck_6124_ == 0)
{
lean_object* v_unused_6125_; lean_object* v_unused_6126_; lean_object* v_unused_6127_; 
v_unused_6125_ = lean_ctor_get(v_val_6086_, 3);
lean_dec(v_unused_6125_);
v_unused_6126_ = lean_ctor_get(v_val_6086_, 2);
lean_dec(v_unused_6126_);
v_unused_6127_ = lean_ctor_get(v_val_6086_, 0);
lean_dec(v_unused_6127_);
v___x_6091_ = v_val_6086_;
v_isShared_6092_ = v_isSharedCheck_6124_;
goto v_resetjp_6090_;
}
else
{
lean_inc(v_decls_6089_);
lean_inc(v_refs_6088_);
lean_inc(v_version_6087_);
lean_dec(v_val_6086_);
v___x_6091_ = lean_box(0);
v_isShared_6092_ = v_isSharedCheck_6124_;
goto v_resetjp_6090_;
}
v_resetjp_6090_:
{
uint8_t v___x_6093_; 
v___x_6093_ = lean_nat_dec_lt(v_version_6071_, v_version_6087_);
if (v___x_6093_ == 0)
{
lean_object* v___x_6095_; uint8_t v_isShared_6096_; uint8_t v_isSharedCheck_6118_; 
lean_inc(v_workers_6081_);
lean_inc(v_ileans_6080_);
v_isSharedCheck_6118_ = !lean_is_exclusive(v_self_6068_);
if (v_isSharedCheck_6118_ == 0)
{
lean_object* v_unused_6119_; lean_object* v_unused_6120_; 
v_unused_6119_ = lean_ctor_get(v_self_6068_, 1);
lean_dec(v_unused_6119_);
v_unused_6120_ = lean_ctor_get(v_self_6068_, 0);
lean_dec(v_unused_6120_);
v___x_6095_ = v_self_6068_;
v_isShared_6096_ = v_isSharedCheck_6118_;
goto v_resetjp_6094_;
}
else
{
lean_dec(v_self_6068_);
v___x_6095_ = lean_box(0);
v_isShared_6096_ = v_isSharedCheck_6118_;
goto v_resetjp_6094_;
}
v_resetjp_6094_:
{
uint8_t v___x_6097_; 
v___x_6097_ = lean_nat_dec_eq(v_version_6071_, v_version_6087_);
lean_dec(v_version_6087_);
if (v___x_6097_ == 0)
{
lean_object* v___x_6099_; 
lean_dec(v_decls_6089_);
lean_dec(v_refs_6088_);
if (v_isShared_6092_ == 0)
{
lean_ctor_set(v___x_6091_, 5, v___x_6082_);
lean_ctor_set(v___x_6091_, 4, v___x_6082_);
lean_ctor_set(v___x_6091_, 3, v___x_6084_);
lean_ctor_set(v___x_6091_, 2, v_a_6076_);
lean_ctor_set(v___x_6091_, 1, v_version_6071_);
lean_ctor_set(v___x_6091_, 0, v_moduleUri_6070_);
v___x_6099_ = v___x_6091_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6107_; 
v_reuseFailAlloc_6107_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6107_, 0, v_moduleUri_6070_);
lean_ctor_set(v_reuseFailAlloc_6107_, 1, v_version_6071_);
lean_ctor_set(v_reuseFailAlloc_6107_, 2, v_a_6076_);
lean_ctor_set(v_reuseFailAlloc_6107_, 3, v___x_6084_);
lean_ctor_set(v_reuseFailAlloc_6107_, 4, v___x_6082_);
lean_ctor_set(v_reuseFailAlloc_6107_, 5, v___x_6082_);
v___x_6099_ = v_reuseFailAlloc_6107_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
lean_object* v___x_6100_; lean_object* v___x_6102_; 
v___x_6100_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6069_, v___x_6099_, v_workers_6081_);
if (v_isShared_6096_ == 0)
{
lean_ctor_set(v___x_6095_, 1, v___x_6100_);
v___x_6102_ = v___x_6095_;
goto v_reusejp_6101_;
}
else
{
lean_object* v_reuseFailAlloc_6106_; 
v_reuseFailAlloc_6106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6106_, 0, v_ileans_6080_);
lean_ctor_set(v_reuseFailAlloc_6106_, 1, v___x_6100_);
v___x_6102_ = v_reuseFailAlloc_6106_;
goto v_reusejp_6101_;
}
v_reusejp_6101_:
{
lean_object* v___x_6104_; 
if (v_isShared_6079_ == 0)
{
lean_ctor_set(v___x_6078_, 0, v___x_6102_);
v___x_6104_ = v___x_6078_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v___x_6102_);
v___x_6104_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
return v___x_6104_;
}
}
}
}
else
{
lean_object* v___x_6109_; 
if (v_isShared_6092_ == 0)
{
lean_ctor_set(v___x_6091_, 3, v___x_6084_);
lean_ctor_set(v___x_6091_, 2, v_a_6076_);
lean_ctor_set(v___x_6091_, 1, v_version_6071_);
lean_ctor_set(v___x_6091_, 0, v_moduleUri_6070_);
v___x_6109_ = v___x_6091_;
goto v_reusejp_6108_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_moduleUri_6070_);
lean_ctor_set(v_reuseFailAlloc_6117_, 1, v_version_6071_);
lean_ctor_set(v_reuseFailAlloc_6117_, 2, v_a_6076_);
lean_ctor_set(v_reuseFailAlloc_6117_, 3, v___x_6084_);
lean_ctor_set(v_reuseFailAlloc_6117_, 4, v_refs_6088_);
lean_ctor_set(v_reuseFailAlloc_6117_, 5, v_decls_6089_);
v___x_6109_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6108_;
}
v_reusejp_6108_:
{
lean_object* v___x_6110_; lean_object* v___x_6112_; 
v___x_6110_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6069_, v___x_6109_, v_workers_6081_);
if (v_isShared_6096_ == 0)
{
lean_ctor_set(v___x_6095_, 1, v___x_6110_);
v___x_6112_ = v___x_6095_;
goto v_reusejp_6111_;
}
else
{
lean_object* v_reuseFailAlloc_6116_; 
v_reuseFailAlloc_6116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_ileans_6080_);
lean_ctor_set(v_reuseFailAlloc_6116_, 1, v___x_6110_);
v___x_6112_ = v_reuseFailAlloc_6116_;
goto v_reusejp_6111_;
}
v_reusejp_6111_:
{
lean_object* v___x_6114_; 
if (v_isShared_6079_ == 0)
{
lean_ctor_set(v___x_6078_, 0, v___x_6112_);
v___x_6114_ = v___x_6078_;
goto v_reusejp_6113_;
}
else
{
lean_object* v_reuseFailAlloc_6115_; 
v_reuseFailAlloc_6115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6115_, 0, v___x_6112_);
v___x_6114_ = v_reuseFailAlloc_6115_;
goto v_reusejp_6113_;
}
v_reusejp_6113_:
{
return v___x_6114_;
}
}
}
}
}
}
else
{
lean_object* v___x_6122_; 
lean_del_object(v___x_6091_);
lean_dec(v_decls_6089_);
lean_dec(v_refs_6088_);
lean_dec(v_version_6087_);
lean_dec_ref(v___x_6084_);
lean_dec(v_a_6076_);
lean_dec(v_version_6071_);
lean_dec_ref(v_moduleUri_6070_);
lean_dec(v_name_6069_);
if (v_isShared_6079_ == 0)
{
lean_ctor_set(v___x_6078_, 0, v_self_6068_);
v___x_6122_ = v___x_6078_;
goto v_reusejp_6121_;
}
else
{
lean_object* v_reuseFailAlloc_6123_; 
v_reuseFailAlloc_6123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6123_, 0, v_self_6068_);
v___x_6122_ = v_reuseFailAlloc_6123_;
goto v_reusejp_6121_;
}
v_reusejp_6121_:
{
return v___x_6122_;
}
}
}
}
else
{
lean_object* v___x_6129_; uint8_t v_isShared_6130_; uint8_t v_isSharedCheck_6139_; 
lean_inc(v_workers_6081_);
lean_inc(v_ileans_6080_);
lean_dec(v___x_6085_);
v_isSharedCheck_6139_ = !lean_is_exclusive(v_self_6068_);
if (v_isSharedCheck_6139_ == 0)
{
lean_object* v_unused_6140_; lean_object* v_unused_6141_; 
v_unused_6140_ = lean_ctor_get(v_self_6068_, 1);
lean_dec(v_unused_6140_);
v_unused_6141_ = lean_ctor_get(v_self_6068_, 0);
lean_dec(v_unused_6141_);
v___x_6129_ = v_self_6068_;
v_isShared_6130_ = v_isSharedCheck_6139_;
goto v_resetjp_6128_;
}
else
{
lean_dec(v_self_6068_);
v___x_6129_ = lean_box(0);
v_isShared_6130_ = v_isSharedCheck_6139_;
goto v_resetjp_6128_;
}
v_resetjp_6128_:
{
lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6134_; 
v___x_6131_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6131_, 0, v_moduleUri_6070_);
lean_ctor_set(v___x_6131_, 1, v_version_6071_);
lean_ctor_set(v___x_6131_, 2, v_a_6076_);
lean_ctor_set(v___x_6131_, 3, v___x_6084_);
lean_ctor_set(v___x_6131_, 4, v___x_6082_);
lean_ctor_set(v___x_6131_, 5, v___x_6082_);
v___x_6132_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6069_, v___x_6131_, v_workers_6081_);
if (v_isShared_6130_ == 0)
{
lean_ctor_set(v___x_6129_, 1, v___x_6132_);
v___x_6134_ = v___x_6129_;
goto v_reusejp_6133_;
}
else
{
lean_object* v_reuseFailAlloc_6138_; 
v_reuseFailAlloc_6138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6138_, 0, v_ileans_6080_);
lean_ctor_set(v_reuseFailAlloc_6138_, 1, v___x_6132_);
v___x_6134_ = v_reuseFailAlloc_6138_;
goto v_reusejp_6133_;
}
v_reusejp_6133_:
{
lean_object* v___x_6136_; 
if (v_isShared_6079_ == 0)
{
lean_ctor_set(v___x_6078_, 0, v___x_6134_);
v___x_6136_ = v___x_6078_;
goto v_reusejp_6135_;
}
else
{
lean_object* v_reuseFailAlloc_6137_; 
v_reuseFailAlloc_6137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6137_, 0, v___x_6134_);
v___x_6136_ = v_reuseFailAlloc_6137_;
goto v_reusejp_6135_;
}
v_reusejp_6135_:
{
return v___x_6136_;
}
}
}
}
}
}
else
{
lean_object* v_a_6143_; lean_object* v___x_6145_; uint8_t v_isShared_6146_; uint8_t v_isSharedCheck_6150_; 
lean_dec(v_version_6071_);
lean_dec_ref(v_moduleUri_6070_);
lean_dec(v_name_6069_);
lean_dec_ref(v_self_6068_);
v_a_6143_ = lean_ctor_get(v___x_6075_, 0);
v_isSharedCheck_6150_ = !lean_is_exclusive(v___x_6075_);
if (v_isSharedCheck_6150_ == 0)
{
v___x_6145_ = v___x_6075_;
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
else
{
lean_inc(v_a_6143_);
lean_dec(v___x_6075_);
v___x_6145_ = lean_box(0);
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
v_resetjp_6144_:
{
lean_object* v___x_6148_; 
if (v_isShared_6146_ == 0)
{
v___x_6148_ = v___x_6145_;
goto v_reusejp_6147_;
}
else
{
lean_object* v_reuseFailAlloc_6149_; 
v_reuseFailAlloc_6149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6149_, 0, v_a_6143_);
v___x_6148_ = v_reuseFailAlloc_6149_;
goto v_reusejp_6147_;
}
v_reusejp_6147_:
{
return v___x_6148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6151_, lean_object* v_name_6152_, lean_object* v_moduleUri_6153_, lean_object* v_version_6154_, lean_object* v_directImports_6155_, lean_object* v_isSetupFailure_6156_, lean_object* v_a_6157_){
_start:
{
uint8_t v_isSetupFailure_boxed_6158_; lean_object* v_res_6159_; 
v_isSetupFailure_boxed_6158_ = lean_unbox(v_isSetupFailure_6156_);
v_res_6159_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6151_, v_name_6152_, v_moduleUri_6153_, v_version_6154_, v_directImports_6155_, v_isSetupFailure_boxed_6158_);
lean_dec_ref(v_directImports_6155_);
return v_res_6159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6160_, lean_object* v_t_6161_, lean_object* v_k_6162_){
_start:
{
lean_object* v___x_6163_; 
v___x_6163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6161_, v_k_6162_);
return v___x_6163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6164_, lean_object* v_t_6165_, lean_object* v_k_6166_){
_start:
{
lean_object* v_res_6167_; 
v_res_6167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6164_, v_t_6165_, v_k_6166_);
lean_dec(v_k_6166_);
lean_dec(v_t_6165_);
return v_res_6167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6168_, lean_object* v_____s_6169_){
_start:
{
lean_object* v_fst_6170_; lean_object* v_snd_6171_; lean_object* v_r_6172_; lean_object* v___x_6173_; 
v_fst_6170_ = lean_ctor_get(v_x_6168_, 0);
lean_inc(v_fst_6170_);
v_snd_6171_ = lean_ctor_get(v_x_6168_, 1);
lean_inc(v_snd_6171_);
lean_dec_ref(v_x_6168_);
v_r_6172_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6170_, v_snd_6171_, v_____s_6169_);
v___x_6173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6173_, 0, v_r_6172_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6174_, lean_object* v_k_6175_, lean_object* v_fallback_6176_){
_start:
{
if (lean_obj_tag(v_t_6174_) == 0)
{
lean_object* v_k_6177_; lean_object* v_v_6178_; lean_object* v_l_6179_; lean_object* v_r_6180_; uint8_t v___x_6181_; 
v_k_6177_ = lean_ctor_get(v_t_6174_, 1);
v_v_6178_ = lean_ctor_get(v_t_6174_, 2);
v_l_6179_ = lean_ctor_get(v_t_6174_, 3);
v_r_6180_ = lean_ctor_get(v_t_6174_, 4);
v___x_6181_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6175_, v_k_6177_);
switch(v___x_6181_)
{
case 0:
{
v_t_6174_ = v_l_6179_;
goto _start;
}
case 1:
{
lean_inc(v_v_6178_);
return v_v_6178_;
}
default: 
{
v_t_6174_ = v_r_6180_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6176_);
return v_fallback_6176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6184_, lean_object* v_k_6185_, lean_object* v_fallback_6186_){
_start:
{
lean_object* v_res_6187_; 
v_res_6187_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6184_, v_k_6185_, v_fallback_6186_);
lean_dec(v_fallback_6186_);
lean_dec_ref(v_k_6185_);
lean_dec(v_t_6184_);
return v_res_6187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6188_, lean_object* v_x_6189_){
_start:
{
if (lean_obj_tag(v_x_6189_) == 0)
{
lean_object* v_k_6190_; lean_object* v_v_6191_; lean_object* v_l_6192_; lean_object* v_r_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; 
v_k_6190_ = lean_ctor_get(v_x_6189_, 1);
lean_inc(v_k_6190_);
v_v_6191_ = lean_ctor_get(v_x_6189_, 2);
lean_inc(v_v_6191_);
v_l_6192_ = lean_ctor_get(v_x_6189_, 3);
lean_inc(v_l_6192_);
v_r_6193_ = lean_ctor_get(v_x_6189_, 4);
lean_inc(v_r_6193_);
lean_dec_ref(v_x_6189_);
v___x_6194_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6188_, v_l_6192_);
v___x_6195_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6196_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6194_, v_k_6190_, v___x_6195_);
v___x_6197_ = l_Lean_Lsp_RefInfo_merge(v___x_6196_, v_v_6191_);
v___x_6198_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6190_, v___x_6197_, v___x_6194_);
v_init_6188_ = v___x_6198_;
v_x_6189_ = v_r_6193_;
goto _start;
}
else
{
return v_init_6188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6201_, lean_object* v_name_6202_, lean_object* v_moduleUri_6203_, lean_object* v_version_6204_, lean_object* v_refs_6205_, lean_object* v_decls_6206_){
_start:
{
lean_object* v_ileans_6208_; lean_object* v_workers_6209_; lean_object* v___x_6210_; 
v_ileans_6208_ = lean_ctor_get(v_self_6201_, 0);
v_workers_6209_ = lean_ctor_get(v_self_6201_, 1);
v___x_6210_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6209_, v_name_6202_);
if (lean_obj_tag(v___x_6210_) == 1)
{
lean_object* v_val_6211_; lean_object* v___x_6213_; uint8_t v_isShared_6214_; uint8_t v_isSharedCheck_6259_; 
v_val_6211_ = lean_ctor_get(v___x_6210_, 0);
v_isSharedCheck_6259_ = !lean_is_exclusive(v___x_6210_);
if (v_isSharedCheck_6259_ == 0)
{
v___x_6213_ = v___x_6210_;
v_isShared_6214_ = v_isSharedCheck_6259_;
goto v_resetjp_6212_;
}
else
{
lean_inc(v_val_6211_);
lean_dec(v___x_6210_);
v___x_6213_ = lean_box(0);
v_isShared_6214_ = v_isSharedCheck_6259_;
goto v_resetjp_6212_;
}
v_resetjp_6212_:
{
lean_object* v_version_6215_; lean_object* v_directImports_6216_; lean_object* v_isSetupFailure_x3f_6217_; lean_object* v_refs_6218_; lean_object* v_decls_6219_; lean_object* v___x_6221_; uint8_t v_isShared_6222_; uint8_t v_isSharedCheck_6257_; 
v_version_6215_ = lean_ctor_get(v_val_6211_, 1);
v_directImports_6216_ = lean_ctor_get(v_val_6211_, 2);
v_isSetupFailure_x3f_6217_ = lean_ctor_get(v_val_6211_, 3);
v_refs_6218_ = lean_ctor_get(v_val_6211_, 4);
v_decls_6219_ = lean_ctor_get(v_val_6211_, 5);
v_isSharedCheck_6257_ = !lean_is_exclusive(v_val_6211_);
if (v_isSharedCheck_6257_ == 0)
{
lean_object* v_unused_6258_; 
v_unused_6258_ = lean_ctor_get(v_val_6211_, 0);
lean_dec(v_unused_6258_);
v___x_6221_ = v_val_6211_;
v_isShared_6222_ = v_isSharedCheck_6257_;
goto v_resetjp_6220_;
}
else
{
lean_inc(v_decls_6219_);
lean_inc(v_refs_6218_);
lean_inc(v_isSetupFailure_x3f_6217_);
lean_inc(v_directImports_6216_);
lean_inc(v_version_6215_);
lean_dec(v_val_6211_);
v___x_6221_ = lean_box(0);
v_isShared_6222_ = v_isSharedCheck_6257_;
goto v_resetjp_6220_;
}
v_resetjp_6220_:
{
uint8_t v___x_6223_; 
v___x_6223_ = lean_nat_dec_lt(v_version_6204_, v_version_6215_);
if (v___x_6223_ == 0)
{
lean_object* v___x_6225_; uint8_t v_isShared_6226_; uint8_t v_isSharedCheck_6251_; 
lean_inc(v_workers_6209_);
lean_inc(v_ileans_6208_);
v_isSharedCheck_6251_ = !lean_is_exclusive(v_self_6201_);
if (v_isSharedCheck_6251_ == 0)
{
lean_object* v_unused_6252_; lean_object* v_unused_6253_; 
v_unused_6252_ = lean_ctor_get(v_self_6201_, 1);
lean_dec(v_unused_6252_);
v_unused_6253_ = lean_ctor_get(v_self_6201_, 0);
lean_dec(v_unused_6253_);
v___x_6225_ = v_self_6201_;
v_isShared_6226_ = v_isSharedCheck_6251_;
goto v_resetjp_6224_;
}
else
{
lean_dec(v_self_6201_);
v___x_6225_ = lean_box(0);
v_isShared_6226_ = v_isSharedCheck_6251_;
goto v_resetjp_6224_;
}
v_resetjp_6224_:
{
uint8_t v___x_6227_; 
v___x_6227_ = lean_nat_dec_eq(v_version_6204_, v_version_6215_);
lean_dec(v_version_6215_);
if (v___x_6227_ == 0)
{
lean_object* v___x_6229_; 
lean_dec(v_decls_6219_);
lean_dec(v_refs_6218_);
if (v_isShared_6222_ == 0)
{
lean_ctor_set(v___x_6221_, 5, v_decls_6206_);
lean_ctor_set(v___x_6221_, 4, v_refs_6205_);
lean_ctor_set(v___x_6221_, 1, v_version_6204_);
lean_ctor_set(v___x_6221_, 0, v_moduleUri_6203_);
v___x_6229_ = v___x_6221_;
goto v_reusejp_6228_;
}
else
{
lean_object* v_reuseFailAlloc_6237_; 
v_reuseFailAlloc_6237_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6237_, 0, v_moduleUri_6203_);
lean_ctor_set(v_reuseFailAlloc_6237_, 1, v_version_6204_);
lean_ctor_set(v_reuseFailAlloc_6237_, 2, v_directImports_6216_);
lean_ctor_set(v_reuseFailAlloc_6237_, 3, v_isSetupFailure_x3f_6217_);
lean_ctor_set(v_reuseFailAlloc_6237_, 4, v_refs_6205_);
lean_ctor_set(v_reuseFailAlloc_6237_, 5, v_decls_6206_);
v___x_6229_ = v_reuseFailAlloc_6237_;
goto v_reusejp_6228_;
}
v_reusejp_6228_:
{
lean_object* v___x_6230_; lean_object* v___x_6232_; 
v___x_6230_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6202_, v___x_6229_, v_workers_6209_);
if (v_isShared_6226_ == 0)
{
lean_ctor_set(v___x_6225_, 1, v___x_6230_);
v___x_6232_ = v___x_6225_;
goto v_reusejp_6231_;
}
else
{
lean_object* v_reuseFailAlloc_6236_; 
v_reuseFailAlloc_6236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6236_, 0, v_ileans_6208_);
lean_ctor_set(v_reuseFailAlloc_6236_, 1, v___x_6230_);
v___x_6232_ = v_reuseFailAlloc_6236_;
goto v_reusejp_6231_;
}
v_reusejp_6231_:
{
lean_object* v___x_6234_; 
if (v_isShared_6214_ == 0)
{
lean_ctor_set_tag(v___x_6213_, 0);
lean_ctor_set(v___x_6213_, 0, v___x_6232_);
v___x_6234_ = v___x_6213_;
goto v_reusejp_6233_;
}
else
{
lean_object* v_reuseFailAlloc_6235_; 
v_reuseFailAlloc_6235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6235_, 0, v___x_6232_);
v___x_6234_ = v_reuseFailAlloc_6235_;
goto v_reusejp_6233_;
}
v_reusejp_6233_:
{
return v___x_6234_;
}
}
}
}
else
{
lean_object* v___f_6238_; lean_object* v_mergedRefs_6239_; lean_object* v_mergedDecls_6240_; lean_object* v___x_6242_; 
v___f_6238_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6239_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6218_, v_refs_6205_);
v_mergedDecls_6240_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6206_, v_decls_6219_, v___f_6238_);
lean_dec(v_decls_6206_);
if (v_isShared_6222_ == 0)
{
lean_ctor_set(v___x_6221_, 5, v_mergedDecls_6240_);
lean_ctor_set(v___x_6221_, 4, v_mergedRefs_6239_);
lean_ctor_set(v___x_6221_, 1, v_version_6204_);
lean_ctor_set(v___x_6221_, 0, v_moduleUri_6203_);
v___x_6242_ = v___x_6221_;
goto v_reusejp_6241_;
}
else
{
lean_object* v_reuseFailAlloc_6250_; 
v_reuseFailAlloc_6250_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6250_, 0, v_moduleUri_6203_);
lean_ctor_set(v_reuseFailAlloc_6250_, 1, v_version_6204_);
lean_ctor_set(v_reuseFailAlloc_6250_, 2, v_directImports_6216_);
lean_ctor_set(v_reuseFailAlloc_6250_, 3, v_isSetupFailure_x3f_6217_);
lean_ctor_set(v_reuseFailAlloc_6250_, 4, v_mergedRefs_6239_);
lean_ctor_set(v_reuseFailAlloc_6250_, 5, v_mergedDecls_6240_);
v___x_6242_ = v_reuseFailAlloc_6250_;
goto v_reusejp_6241_;
}
v_reusejp_6241_:
{
lean_object* v___x_6243_; lean_object* v___x_6245_; 
v___x_6243_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6202_, v___x_6242_, v_workers_6209_);
if (v_isShared_6226_ == 0)
{
lean_ctor_set(v___x_6225_, 1, v___x_6243_);
v___x_6245_ = v___x_6225_;
goto v_reusejp_6244_;
}
else
{
lean_object* v_reuseFailAlloc_6249_; 
v_reuseFailAlloc_6249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6249_, 0, v_ileans_6208_);
lean_ctor_set(v_reuseFailAlloc_6249_, 1, v___x_6243_);
v___x_6245_ = v_reuseFailAlloc_6249_;
goto v_reusejp_6244_;
}
v_reusejp_6244_:
{
lean_object* v___x_6247_; 
if (v_isShared_6214_ == 0)
{
lean_ctor_set_tag(v___x_6213_, 0);
lean_ctor_set(v___x_6213_, 0, v___x_6245_);
v___x_6247_ = v___x_6213_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6248_; 
v_reuseFailAlloc_6248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6248_, 0, v___x_6245_);
v___x_6247_ = v_reuseFailAlloc_6248_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
return v___x_6247_;
}
}
}
}
}
}
else
{
lean_object* v___x_6255_; 
lean_del_object(v___x_6221_);
lean_dec(v_decls_6219_);
lean_dec(v_refs_6218_);
lean_dec(v_isSetupFailure_x3f_6217_);
lean_dec_ref(v_directImports_6216_);
lean_dec(v_version_6215_);
lean_dec(v_decls_6206_);
lean_dec(v_refs_6205_);
lean_dec(v_version_6204_);
lean_dec_ref(v_moduleUri_6203_);
lean_dec(v_name_6202_);
if (v_isShared_6214_ == 0)
{
lean_ctor_set_tag(v___x_6213_, 0);
lean_ctor_set(v___x_6213_, 0, v_self_6201_);
v___x_6255_ = v___x_6213_;
goto v_reusejp_6254_;
}
else
{
lean_object* v_reuseFailAlloc_6256_; 
v_reuseFailAlloc_6256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6256_, 0, v_self_6201_);
v___x_6255_ = v_reuseFailAlloc_6256_;
goto v_reusejp_6254_;
}
v_reusejp_6254_:
{
return v___x_6255_;
}
}
}
}
}
else
{
lean_object* v___x_6261_; uint8_t v_isShared_6262_; uint8_t v_isSharedCheck_6271_; 
lean_inc(v_workers_6209_);
lean_inc(v_ileans_6208_);
lean_dec(v___x_6210_);
v_isSharedCheck_6271_ = !lean_is_exclusive(v_self_6201_);
if (v_isSharedCheck_6271_ == 0)
{
lean_object* v_unused_6272_; lean_object* v_unused_6273_; 
v_unused_6272_ = lean_ctor_get(v_self_6201_, 1);
lean_dec(v_unused_6272_);
v_unused_6273_ = lean_ctor_get(v_self_6201_, 0);
lean_dec(v_unused_6273_);
v___x_6261_ = v_self_6201_;
v_isShared_6262_ = v_isSharedCheck_6271_;
goto v_resetjp_6260_;
}
else
{
lean_dec(v_self_6201_);
v___x_6261_ = lean_box(0);
v_isShared_6262_ = v_isSharedCheck_6271_;
goto v_resetjp_6260_;
}
v_resetjp_6260_:
{
lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6268_; 
v___x_6263_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6264_ = lean_box(0);
v___x_6265_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6265_, 0, v_moduleUri_6203_);
lean_ctor_set(v___x_6265_, 1, v_version_6204_);
lean_ctor_set(v___x_6265_, 2, v___x_6263_);
lean_ctor_set(v___x_6265_, 3, v___x_6264_);
lean_ctor_set(v___x_6265_, 4, v_refs_6205_);
lean_ctor_set(v___x_6265_, 5, v_decls_6206_);
v___x_6266_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6202_, v___x_6265_, v_workers_6209_);
if (v_isShared_6262_ == 0)
{
lean_ctor_set(v___x_6261_, 1, v___x_6266_);
v___x_6268_ = v___x_6261_;
goto v_reusejp_6267_;
}
else
{
lean_object* v_reuseFailAlloc_6270_; 
v_reuseFailAlloc_6270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6270_, 0, v_ileans_6208_);
lean_ctor_set(v_reuseFailAlloc_6270_, 1, v___x_6266_);
v___x_6268_ = v_reuseFailAlloc_6270_;
goto v_reusejp_6267_;
}
v_reusejp_6267_:
{
lean_object* v___x_6269_; 
v___x_6269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6269_, 0, v___x_6268_);
return v___x_6269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6274_, lean_object* v_name_6275_, lean_object* v_moduleUri_6276_, lean_object* v_version_6277_, lean_object* v_refs_6278_, lean_object* v_decls_6279_, lean_object* v_a_6280_){
_start:
{
lean_object* v_res_6281_; 
v_res_6281_ = l_Lean_Server_References_updateWorkerRefs(v_self_6274_, v_name_6275_, v_moduleUri_6276_, v_version_6277_, v_refs_6278_, v_decls_6279_);
return v_res_6281_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6282_, lean_object* v_t_6283_, lean_object* v_k_6284_, lean_object* v_fallback_6285_){
_start:
{
lean_object* v___x_6286_; 
v___x_6286_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6283_, v_k_6284_, v_fallback_6285_);
return v___x_6286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6287_, lean_object* v_t_6288_, lean_object* v_k_6289_, lean_object* v_fallback_6290_){
_start:
{
lean_object* v_res_6291_; 
v_res_6291_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6287_, v_t_6288_, v_k_6289_, v_fallback_6290_);
lean_dec(v_fallback_6290_);
lean_dec_ref(v_k_6289_);
lean_dec(v_t_6288_);
return v_res_6291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6292_, lean_object* v_t_6293_){
_start:
{
lean_object* v___x_6294_; 
v___x_6294_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6292_, v_t_6293_);
return v___x_6294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6295_, lean_object* v_name_6296_, lean_object* v_moduleUri_6297_, lean_object* v_version_6298_, lean_object* v_refs_6299_, lean_object* v_decls_6300_){
_start:
{
lean_object* v_ileans_6302_; lean_object* v_workers_6303_; lean_object* v___x_6304_; 
v_ileans_6302_ = lean_ctor_get(v_self_6295_, 0);
v_workers_6303_ = lean_ctor_get(v_self_6295_, 1);
v___x_6304_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6303_, v_name_6296_);
if (lean_obj_tag(v___x_6304_) == 1)
{
lean_object* v_val_6305_; lean_object* v___x_6307_; uint8_t v_isShared_6308_; uint8_t v_isSharedCheck_6339_; 
v_val_6305_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6339_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6339_ == 0)
{
v___x_6307_ = v___x_6304_;
v_isShared_6308_ = v_isSharedCheck_6339_;
goto v_resetjp_6306_;
}
else
{
lean_inc(v_val_6305_);
lean_dec(v___x_6304_);
v___x_6307_ = lean_box(0);
v_isShared_6308_ = v_isSharedCheck_6339_;
goto v_resetjp_6306_;
}
v_resetjp_6306_:
{
lean_object* v_version_6309_; lean_object* v_directImports_6310_; lean_object* v_isSetupFailure_x3f_6311_; lean_object* v___x_6313_; uint8_t v_isShared_6314_; uint8_t v_isSharedCheck_6335_; 
v_version_6309_ = lean_ctor_get(v_val_6305_, 1);
v_directImports_6310_ = lean_ctor_get(v_val_6305_, 2);
v_isSetupFailure_x3f_6311_ = lean_ctor_get(v_val_6305_, 3);
v_isSharedCheck_6335_ = !lean_is_exclusive(v_val_6305_);
if (v_isSharedCheck_6335_ == 0)
{
lean_object* v_unused_6336_; lean_object* v_unused_6337_; lean_object* v_unused_6338_; 
v_unused_6336_ = lean_ctor_get(v_val_6305_, 5);
lean_dec(v_unused_6336_);
v_unused_6337_ = lean_ctor_get(v_val_6305_, 4);
lean_dec(v_unused_6337_);
v_unused_6338_ = lean_ctor_get(v_val_6305_, 0);
lean_dec(v_unused_6338_);
v___x_6313_ = v_val_6305_;
v_isShared_6314_ = v_isSharedCheck_6335_;
goto v_resetjp_6312_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6311_);
lean_inc(v_directImports_6310_);
lean_inc(v_version_6309_);
lean_dec(v_val_6305_);
v___x_6313_ = lean_box(0);
v_isShared_6314_ = v_isSharedCheck_6335_;
goto v_resetjp_6312_;
}
v_resetjp_6312_:
{
uint8_t v___x_6315_; 
v___x_6315_ = lean_nat_dec_lt(v_version_6298_, v_version_6309_);
lean_dec(v_version_6309_);
if (v___x_6315_ == 0)
{
lean_object* v___x_6317_; uint8_t v_isShared_6318_; uint8_t v_isSharedCheck_6329_; 
lean_inc(v_workers_6303_);
lean_inc(v_ileans_6302_);
v_isSharedCheck_6329_ = !lean_is_exclusive(v_self_6295_);
if (v_isSharedCheck_6329_ == 0)
{
lean_object* v_unused_6330_; lean_object* v_unused_6331_; 
v_unused_6330_ = lean_ctor_get(v_self_6295_, 1);
lean_dec(v_unused_6330_);
v_unused_6331_ = lean_ctor_get(v_self_6295_, 0);
lean_dec(v_unused_6331_);
v___x_6317_ = v_self_6295_;
v_isShared_6318_ = v_isSharedCheck_6329_;
goto v_resetjp_6316_;
}
else
{
lean_dec(v_self_6295_);
v___x_6317_ = lean_box(0);
v_isShared_6318_ = v_isSharedCheck_6329_;
goto v_resetjp_6316_;
}
v_resetjp_6316_:
{
lean_object* v___x_6320_; 
if (v_isShared_6314_ == 0)
{
lean_ctor_set(v___x_6313_, 5, v_decls_6300_);
lean_ctor_set(v___x_6313_, 4, v_refs_6299_);
lean_ctor_set(v___x_6313_, 1, v_version_6298_);
lean_ctor_set(v___x_6313_, 0, v_moduleUri_6297_);
v___x_6320_ = v___x_6313_;
goto v_reusejp_6319_;
}
else
{
lean_object* v_reuseFailAlloc_6328_; 
v_reuseFailAlloc_6328_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6328_, 0, v_moduleUri_6297_);
lean_ctor_set(v_reuseFailAlloc_6328_, 1, v_version_6298_);
lean_ctor_set(v_reuseFailAlloc_6328_, 2, v_directImports_6310_);
lean_ctor_set(v_reuseFailAlloc_6328_, 3, v_isSetupFailure_x3f_6311_);
lean_ctor_set(v_reuseFailAlloc_6328_, 4, v_refs_6299_);
lean_ctor_set(v_reuseFailAlloc_6328_, 5, v_decls_6300_);
v___x_6320_ = v_reuseFailAlloc_6328_;
goto v_reusejp_6319_;
}
v_reusejp_6319_:
{
lean_object* v___x_6321_; lean_object* v___x_6323_; 
v___x_6321_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6296_, v___x_6320_, v_workers_6303_);
if (v_isShared_6318_ == 0)
{
lean_ctor_set(v___x_6317_, 1, v___x_6321_);
v___x_6323_ = v___x_6317_;
goto v_reusejp_6322_;
}
else
{
lean_object* v_reuseFailAlloc_6327_; 
v_reuseFailAlloc_6327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6327_, 0, v_ileans_6302_);
lean_ctor_set(v_reuseFailAlloc_6327_, 1, v___x_6321_);
v___x_6323_ = v_reuseFailAlloc_6327_;
goto v_reusejp_6322_;
}
v_reusejp_6322_:
{
lean_object* v___x_6325_; 
if (v_isShared_6308_ == 0)
{
lean_ctor_set_tag(v___x_6307_, 0);
lean_ctor_set(v___x_6307_, 0, v___x_6323_);
v___x_6325_ = v___x_6307_;
goto v_reusejp_6324_;
}
else
{
lean_object* v_reuseFailAlloc_6326_; 
v_reuseFailAlloc_6326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6326_, 0, v___x_6323_);
v___x_6325_ = v_reuseFailAlloc_6326_;
goto v_reusejp_6324_;
}
v_reusejp_6324_:
{
return v___x_6325_;
}
}
}
}
}
else
{
lean_object* v___x_6333_; 
lean_del_object(v___x_6313_);
lean_dec(v_isSetupFailure_x3f_6311_);
lean_dec_ref(v_directImports_6310_);
lean_dec(v_decls_6300_);
lean_dec(v_refs_6299_);
lean_dec(v_version_6298_);
lean_dec_ref(v_moduleUri_6297_);
lean_dec(v_name_6296_);
if (v_isShared_6308_ == 0)
{
lean_ctor_set_tag(v___x_6307_, 0);
lean_ctor_set(v___x_6307_, 0, v_self_6295_);
v___x_6333_ = v___x_6307_;
goto v_reusejp_6332_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v_self_6295_);
v___x_6333_ = v_reuseFailAlloc_6334_;
goto v_reusejp_6332_;
}
v_reusejp_6332_:
{
return v___x_6333_;
}
}
}
}
}
else
{
lean_object* v___x_6341_; uint8_t v_isShared_6342_; uint8_t v_isSharedCheck_6351_; 
lean_inc(v_workers_6303_);
lean_inc(v_ileans_6302_);
lean_dec(v___x_6304_);
v_isSharedCheck_6351_ = !lean_is_exclusive(v_self_6295_);
if (v_isSharedCheck_6351_ == 0)
{
lean_object* v_unused_6352_; lean_object* v_unused_6353_; 
v_unused_6352_ = lean_ctor_get(v_self_6295_, 1);
lean_dec(v_unused_6352_);
v_unused_6353_ = lean_ctor_get(v_self_6295_, 0);
lean_dec(v_unused_6353_);
v___x_6341_ = v_self_6295_;
v_isShared_6342_ = v_isSharedCheck_6351_;
goto v_resetjp_6340_;
}
else
{
lean_dec(v_self_6295_);
v___x_6341_ = lean_box(0);
v_isShared_6342_ = v_isSharedCheck_6351_;
goto v_resetjp_6340_;
}
v_resetjp_6340_:
{
lean_object* v___x_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6348_; 
v___x_6343_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6344_ = lean_box(0);
v___x_6345_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6345_, 0, v_moduleUri_6297_);
lean_ctor_set(v___x_6345_, 1, v_version_6298_);
lean_ctor_set(v___x_6345_, 2, v___x_6343_);
lean_ctor_set(v___x_6345_, 3, v___x_6344_);
lean_ctor_set(v___x_6345_, 4, v_refs_6299_);
lean_ctor_set(v___x_6345_, 5, v_decls_6300_);
v___x_6346_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6296_, v___x_6345_, v_workers_6303_);
if (v_isShared_6342_ == 0)
{
lean_ctor_set(v___x_6341_, 1, v___x_6346_);
v___x_6348_ = v___x_6341_;
goto v_reusejp_6347_;
}
else
{
lean_object* v_reuseFailAlloc_6350_; 
v_reuseFailAlloc_6350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6350_, 0, v_ileans_6302_);
lean_ctor_set(v_reuseFailAlloc_6350_, 1, v___x_6346_);
v___x_6348_ = v_reuseFailAlloc_6350_;
goto v_reusejp_6347_;
}
v_reusejp_6347_:
{
lean_object* v___x_6349_; 
v___x_6349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6349_, 0, v___x_6348_);
return v___x_6349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6354_, lean_object* v_name_6355_, lean_object* v_moduleUri_6356_, lean_object* v_version_6357_, lean_object* v_refs_6358_, lean_object* v_decls_6359_, lean_object* v_a_6360_){
_start:
{
lean_object* v_res_6361_; 
v_res_6361_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6354_, v_name_6355_, v_moduleUri_6356_, v_version_6357_, v_refs_6358_, v_decls_6359_);
return v_res_6361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6362_, lean_object* v_name_6363_){
_start:
{
lean_object* v_ileans_6364_; lean_object* v_workers_6365_; lean_object* v___x_6367_; uint8_t v_isShared_6368_; uint8_t v_isSharedCheck_6373_; 
v_ileans_6364_ = lean_ctor_get(v_self_6362_, 0);
v_workers_6365_ = lean_ctor_get(v_self_6362_, 1);
v_isSharedCheck_6373_ = !lean_is_exclusive(v_self_6362_);
if (v_isSharedCheck_6373_ == 0)
{
v___x_6367_ = v_self_6362_;
v_isShared_6368_ = v_isSharedCheck_6373_;
goto v_resetjp_6366_;
}
else
{
lean_inc(v_workers_6365_);
lean_inc(v_ileans_6364_);
lean_dec(v_self_6362_);
v___x_6367_ = lean_box(0);
v_isShared_6368_ = v_isSharedCheck_6373_;
goto v_resetjp_6366_;
}
v_resetjp_6366_:
{
lean_object* v___x_6369_; lean_object* v___x_6371_; 
v___x_6369_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6363_, v_workers_6365_);
if (v_isShared_6368_ == 0)
{
lean_ctor_set(v___x_6367_, 1, v___x_6369_);
v___x_6371_ = v___x_6367_;
goto v_reusejp_6370_;
}
else
{
lean_object* v_reuseFailAlloc_6372_; 
v_reuseFailAlloc_6372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_ileans_6364_);
lean_ctor_set(v_reuseFailAlloc_6372_, 1, v___x_6369_);
v___x_6371_ = v_reuseFailAlloc_6372_;
goto v_reusejp_6370_;
}
v_reusejp_6370_:
{
return v___x_6371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6374_, lean_object* v_name_6375_){
_start:
{
lean_object* v_res_6376_; 
v_res_6376_ = l_Lean_Server_References_removeWorkerRefs(v_self_6374_, v_name_6375_);
lean_dec(v_name_6375_);
return v_res_6376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6377_, lean_object* v_x_6378_){
_start:
{
if (lean_obj_tag(v_x_6378_) == 0)
{
lean_object* v_v_6379_; lean_object* v_k_6380_; lean_object* v_l_6381_; lean_object* v_r_6382_; lean_object* v_moduleUri_6383_; lean_object* v_refs_6384_; lean_object* v_decls_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; 
v_v_6379_ = lean_ctor_get(v_x_6378_, 2);
lean_inc(v_v_6379_);
v_k_6380_ = lean_ctor_get(v_x_6378_, 1);
lean_inc(v_k_6380_);
v_l_6381_ = lean_ctor_get(v_x_6378_, 3);
lean_inc(v_l_6381_);
v_r_6382_ = lean_ctor_get(v_x_6378_, 4);
lean_inc(v_r_6382_);
lean_dec_ref(v_x_6378_);
v_moduleUri_6383_ = lean_ctor_get(v_v_6379_, 0);
lean_inc_ref(v_moduleUri_6383_);
v_refs_6384_ = lean_ctor_get(v_v_6379_, 3);
lean_inc(v_refs_6384_);
v_decls_6385_ = lean_ctor_get(v_v_6379_, 4);
lean_inc(v_decls_6385_);
lean_dec(v_v_6379_);
v___x_6386_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6377_, v_l_6381_);
v___x_6387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6387_, 0, v_refs_6384_);
lean_ctor_set(v___x_6387_, 1, v_decls_6385_);
v___x_6388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6388_, 0, v_moduleUri_6383_);
lean_ctor_set(v___x_6388_, 1, v___x_6387_);
v___x_6389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6380_, v___x_6388_, v___x_6386_);
v_init_6377_ = v___x_6389_;
v_x_6378_ = v_r_6382_;
goto _start;
}
else
{
return v_init_6377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6391_, lean_object* v_x_6392_){
_start:
{
if (lean_obj_tag(v_x_6392_) == 0)
{
lean_object* v_v_6393_; lean_object* v_k_6394_; lean_object* v_l_6395_; lean_object* v_r_6396_; lean_object* v_moduleUri_6397_; lean_object* v_refs_6398_; lean_object* v_decls_6399_; lean_object* v___x_6400_; uint8_t v___x_6401_; 
v_v_6393_ = lean_ctor_get(v_x_6392_, 2);
lean_inc(v_v_6393_);
v_k_6394_ = lean_ctor_get(v_x_6392_, 1);
lean_inc(v_k_6394_);
v_l_6395_ = lean_ctor_get(v_x_6392_, 3);
lean_inc(v_l_6395_);
v_r_6396_ = lean_ctor_get(v_x_6392_, 4);
lean_inc(v_r_6396_);
lean_dec_ref(v_x_6392_);
v_moduleUri_6397_ = lean_ctor_get(v_v_6393_, 0);
lean_inc_ref(v_moduleUri_6397_);
v_refs_6398_ = lean_ctor_get(v_v_6393_, 4);
lean_inc(v_refs_6398_);
v_decls_6399_ = lean_ctor_get(v_v_6393_, 5);
lean_inc(v_decls_6399_);
v___x_6400_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6391_, v_l_6395_);
v___x_6401_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6393_);
lean_dec(v_v_6393_);
if (v___x_6401_ == 0)
{
lean_dec(v_decls_6399_);
lean_dec(v_refs_6398_);
lean_dec_ref(v_moduleUri_6397_);
lean_dec(v_k_6394_);
v_init_6391_ = v___x_6400_;
v_x_6392_ = v_r_6396_;
goto _start;
}
else
{
lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6403_, 0, v_refs_6398_);
lean_ctor_set(v___x_6403_, 1, v_decls_6399_);
v___x_6404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6404_, 0, v_moduleUri_6397_);
lean_ctor_set(v___x_6404_, 1, v___x_6403_);
v___x_6405_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6394_, v___x_6404_, v___x_6400_);
v_init_6391_ = v___x_6405_;
v_x_6392_ = v_r_6396_;
goto _start;
}
}
else
{
return v_init_6391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6407_){
_start:
{
lean_object* v_ileans_6408_; lean_object* v_workers_6409_; lean_object* v___x_6410_; lean_object* v_ileanRefs_6411_; lean_object* v___x_6412_; 
v_ileans_6408_ = lean_ctor_get(v_self_6407_, 0);
lean_inc(v_ileans_6408_);
v_workers_6409_ = lean_ctor_get(v_self_6407_, 1);
lean_inc(v_workers_6409_);
lean_dec_ref(v_self_6407_);
v___x_6410_ = lean_box(1);
v_ileanRefs_6411_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6410_, v_ileans_6408_);
v___x_6412_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6411_, v_workers_6409_);
return v___x_6412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6413_, lean_object* v_t_6414_){
_start:
{
lean_object* v___x_6415_; 
v___x_6415_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6413_, v_t_6414_);
return v___x_6415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6416_, lean_object* v_t_6417_){
_start:
{
lean_object* v___x_6418_; 
v___x_6418_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6416_, v_t_6417_);
return v___x_6418_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6419_, lean_object* v_x_6420_){
_start:
{
if (lean_obj_tag(v_x_6420_) == 0)
{
lean_object* v_k_6421_; lean_object* v_v_6422_; lean_object* v_l_6423_; lean_object* v_r_6424_; lean_object* v___x_6425_; lean_object* v_a_6426_; uint8_t v___x_6427_; 
v_k_6421_ = lean_ctor_get(v_x_6420_, 1);
lean_inc(v_k_6421_);
v_v_6422_ = lean_ctor_get(v_x_6420_, 2);
lean_inc(v_v_6422_);
v_l_6423_ = lean_ctor_get(v_x_6420_, 3);
lean_inc(v_l_6423_);
v_r_6424_ = lean_ctor_get(v_x_6420_, 4);
lean_inc(v_r_6424_);
lean_dec_ref(v_x_6420_);
v___x_6425_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6419_, v_l_6423_);
v_a_6426_ = lean_ctor_get(v___x_6425_, 0);
lean_inc(v_a_6426_);
v___x_6427_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6422_);
if (v___x_6427_ == 0)
{
lean_object* v_a_6428_; 
lean_dec(v_a_6426_);
lean_dec(v_v_6422_);
lean_dec(v_k_6421_);
v_a_6428_ = lean_ctor_get(v___x_6425_, 0);
lean_inc(v_a_6428_);
lean_dec_ref(v___x_6425_);
v_init_6419_ = v_a_6428_;
v_x_6420_ = v_r_6424_;
goto _start;
}
else
{
lean_object* v_moduleUri_6430_; lean_object* v_directImports_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; 
lean_dec_ref(v___x_6425_);
v_moduleUri_6430_ = lean_ctor_get(v_v_6422_, 0);
lean_inc_ref(v_moduleUri_6430_);
v_directImports_6431_ = lean_ctor_get(v_v_6422_, 2);
lean_inc_ref(v_directImports_6431_);
lean_dec(v_v_6422_);
v___x_6432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6432_, 0, v_moduleUri_6430_);
lean_ctor_set(v___x_6432_, 1, v_directImports_6431_);
v___x_6433_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6421_, v___x_6432_, v_a_6426_);
v_init_6419_ = v___x_6433_;
v_x_6420_ = v_r_6424_;
goto _start;
}
}
else
{
lean_object* v___x_6435_; 
v___x_6435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6435_, 0, v_init_6419_);
return v___x_6435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6436_, lean_object* v_x_6437_){
_start:
{
if (lean_obj_tag(v_x_6437_) == 0)
{
lean_object* v_k_6438_; lean_object* v_v_6439_; lean_object* v_l_6440_; lean_object* v_r_6441_; lean_object* v___x_6442_; lean_object* v_a_6443_; lean_object* v_moduleUri_6444_; lean_object* v_directImports_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; 
v_k_6438_ = lean_ctor_get(v_x_6437_, 1);
lean_inc(v_k_6438_);
v_v_6439_ = lean_ctor_get(v_x_6437_, 2);
lean_inc(v_v_6439_);
v_l_6440_ = lean_ctor_get(v_x_6437_, 3);
lean_inc(v_l_6440_);
v_r_6441_ = lean_ctor_get(v_x_6437_, 4);
lean_inc(v_r_6441_);
lean_dec_ref(v_x_6437_);
v___x_6442_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6436_, v_l_6440_);
v_a_6443_ = lean_ctor_get(v___x_6442_, 0);
lean_inc(v_a_6443_);
lean_dec_ref(v___x_6442_);
v_moduleUri_6444_ = lean_ctor_get(v_v_6439_, 0);
lean_inc_ref(v_moduleUri_6444_);
v_directImports_6445_ = lean_ctor_get(v_v_6439_, 2);
lean_inc_ref(v_directImports_6445_);
lean_dec(v_v_6439_);
v___x_6446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6446_, 0, v_moduleUri_6444_);
lean_ctor_set(v___x_6446_, 1, v_directImports_6445_);
v___x_6447_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6438_, v___x_6446_, v_a_6443_);
v_init_6436_ = v___x_6447_;
v_x_6437_ = v_r_6441_;
goto _start;
}
else
{
lean_object* v___x_6449_; 
v___x_6449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6449_, 0, v_init_6436_);
return v___x_6449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6450_){
_start:
{
lean_object* v_ileans_6451_; lean_object* v_workers_6452_; lean_object* v___y_6454_; lean_object* v_allDirectImports_6457_; lean_object* v___x_6458_; lean_object* v_a_6459_; 
v_ileans_6451_ = lean_ctor_get(v_self_6450_, 0);
lean_inc(v_ileans_6451_);
v_workers_6452_ = lean_ctor_get(v_self_6450_, 1);
lean_inc(v_workers_6452_);
lean_dec_ref(v_self_6450_);
v_allDirectImports_6457_ = lean_box(1);
v___x_6458_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6457_, v_ileans_6451_);
v_a_6459_ = lean_ctor_get(v___x_6458_, 0);
lean_inc(v_a_6459_);
lean_dec_ref(v___x_6458_);
v___y_6454_ = v_a_6459_;
goto v___jp_6453_;
v___jp_6453_:
{
lean_object* v___x_6455_; lean_object* v_a_6456_; 
v___x_6455_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6454_, v_workers_6452_);
v_a_6456_ = lean_ctor_get(v___x_6455_, 0);
lean_inc(v_a_6456_);
lean_dec_ref(v___x_6455_);
return v_a_6456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6460_, lean_object* v_mod_6461_){
_start:
{
lean_object* v_ileans_6462_; lean_object* v_workers_6463_; lean_object* v___x_6465_; uint8_t v_isShared_6466_; uint8_t v_isSharedCheck_6500_; 
v_ileans_6462_ = lean_ctor_get(v_self_6460_, 0);
v_workers_6463_ = lean_ctor_get(v_self_6460_, 1);
v_isSharedCheck_6500_ = !lean_is_exclusive(v_self_6460_);
if (v_isSharedCheck_6500_ == 0)
{
v___x_6465_ = v_self_6460_;
v_isShared_6466_ = v_isSharedCheck_6500_;
goto v_resetjp_6464_;
}
else
{
lean_inc(v_workers_6463_);
lean_inc(v_ileans_6462_);
lean_dec(v_self_6460_);
v___x_6465_ = lean_box(0);
v_isShared_6466_ = v_isSharedCheck_6500_;
goto v_resetjp_6464_;
}
v_resetjp_6464_:
{
lean_object* v___x_6485_; 
v___x_6485_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6463_, v_mod_6461_);
lean_dec(v_workers_6463_);
if (lean_obj_tag(v___x_6485_) == 1)
{
lean_object* v_val_6486_; lean_object* v___x_6488_; uint8_t v_isShared_6489_; uint8_t v_isSharedCheck_6499_; 
v_val_6486_ = lean_ctor_get(v___x_6485_, 0);
v_isSharedCheck_6499_ = !lean_is_exclusive(v___x_6485_);
if (v_isSharedCheck_6499_ == 0)
{
v___x_6488_ = v___x_6485_;
v_isShared_6489_ = v_isSharedCheck_6499_;
goto v_resetjp_6487_;
}
else
{
lean_inc(v_val_6486_);
lean_dec(v___x_6485_);
v___x_6488_ = lean_box(0);
v_isShared_6489_ = v_isSharedCheck_6499_;
goto v_resetjp_6487_;
}
v_resetjp_6487_:
{
uint8_t v___x_6490_; 
v___x_6490_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6486_);
if (v___x_6490_ == 0)
{
lean_del_object(v___x_6488_);
lean_dec(v_val_6486_);
goto v___jp_6467_;
}
else
{
lean_object* v_moduleUri_6491_; lean_object* v_refs_6492_; lean_object* v_decls_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v___x_6497_; 
lean_del_object(v___x_6465_);
lean_dec(v_ileans_6462_);
v_moduleUri_6491_ = lean_ctor_get(v_val_6486_, 0);
lean_inc_ref(v_moduleUri_6491_);
v_refs_6492_ = lean_ctor_get(v_val_6486_, 4);
lean_inc(v_refs_6492_);
v_decls_6493_ = lean_ctor_get(v_val_6486_, 5);
lean_inc(v_decls_6493_);
lean_dec(v_val_6486_);
v___x_6494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6494_, 0, v_refs_6492_);
lean_ctor_set(v___x_6494_, 1, v_decls_6493_);
v___x_6495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6495_, 0, v_moduleUri_6491_);
lean_ctor_set(v___x_6495_, 1, v___x_6494_);
if (v_isShared_6489_ == 0)
{
lean_ctor_set(v___x_6488_, 0, v___x_6495_);
v___x_6497_ = v___x_6488_;
goto v_reusejp_6496_;
}
else
{
lean_object* v_reuseFailAlloc_6498_; 
v_reuseFailAlloc_6498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6498_, 0, v___x_6495_);
v___x_6497_ = v_reuseFailAlloc_6498_;
goto v_reusejp_6496_;
}
v_reusejp_6496_:
{
return v___x_6497_;
}
}
}
}
else
{
lean_dec(v___x_6485_);
goto v___jp_6467_;
}
v___jp_6467_:
{
lean_object* v___x_6468_; 
v___x_6468_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6462_, v_mod_6461_);
lean_dec(v_ileans_6462_);
if (lean_obj_tag(v___x_6468_) == 1)
{
lean_object* v_val_6469_; lean_object* v___x_6471_; uint8_t v_isShared_6472_; uint8_t v_isSharedCheck_6483_; 
v_val_6469_ = lean_ctor_get(v___x_6468_, 0);
v_isSharedCheck_6483_ = !lean_is_exclusive(v___x_6468_);
if (v_isSharedCheck_6483_ == 0)
{
v___x_6471_ = v___x_6468_;
v_isShared_6472_ = v_isSharedCheck_6483_;
goto v_resetjp_6470_;
}
else
{
lean_inc(v_val_6469_);
lean_dec(v___x_6468_);
v___x_6471_ = lean_box(0);
v_isShared_6472_ = v_isSharedCheck_6483_;
goto v_resetjp_6470_;
}
v_resetjp_6470_:
{
lean_object* v_moduleUri_6473_; lean_object* v_refs_6474_; lean_object* v_decls_6475_; lean_object* v___x_6477_; 
v_moduleUri_6473_ = lean_ctor_get(v_val_6469_, 0);
lean_inc_ref(v_moduleUri_6473_);
v_refs_6474_ = lean_ctor_get(v_val_6469_, 3);
lean_inc(v_refs_6474_);
v_decls_6475_ = lean_ctor_get(v_val_6469_, 4);
lean_inc(v_decls_6475_);
lean_dec(v_val_6469_);
if (v_isShared_6466_ == 0)
{
lean_ctor_set(v___x_6465_, 1, v_decls_6475_);
lean_ctor_set(v___x_6465_, 0, v_refs_6474_);
v___x_6477_ = v___x_6465_;
goto v_reusejp_6476_;
}
else
{
lean_object* v_reuseFailAlloc_6482_; 
v_reuseFailAlloc_6482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6482_, 0, v_refs_6474_);
lean_ctor_set(v_reuseFailAlloc_6482_, 1, v_decls_6475_);
v___x_6477_ = v_reuseFailAlloc_6482_;
goto v_reusejp_6476_;
}
v_reusejp_6476_:
{
lean_object* v___x_6478_; lean_object* v___x_6480_; 
v___x_6478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6478_, 0, v_moduleUri_6473_);
lean_ctor_set(v___x_6478_, 1, v___x_6477_);
if (v_isShared_6472_ == 0)
{
lean_ctor_set(v___x_6471_, 0, v___x_6478_);
v___x_6480_ = v___x_6471_;
goto v_reusejp_6479_;
}
else
{
lean_object* v_reuseFailAlloc_6481_; 
v_reuseFailAlloc_6481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6481_, 0, v___x_6478_);
v___x_6480_ = v_reuseFailAlloc_6481_;
goto v_reusejp_6479_;
}
v_reusejp_6479_:
{
return v___x_6480_;
}
}
}
}
else
{
lean_object* v___x_6484_; 
lean_dec(v___x_6468_);
lean_del_object(v___x_6465_);
v___x_6484_ = lean_box(0);
return v___x_6484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6501_, lean_object* v_mod_6502_){
_start:
{
lean_object* v_res_6503_; 
v_res_6503_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6501_, v_mod_6502_);
lean_dec(v_mod_6502_);
return v_res_6503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6504_, lean_object* v_mod_6505_){
_start:
{
lean_object* v_ileans_6506_; lean_object* v_workers_6507_; lean_object* v___x_6520_; 
v_ileans_6506_ = lean_ctor_get(v_self_6504_, 0);
v_workers_6507_ = lean_ctor_get(v_self_6504_, 1);
v___x_6520_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6507_, v_mod_6505_);
if (lean_obj_tag(v___x_6520_) == 1)
{
lean_object* v_val_6521_; lean_object* v___x_6523_; uint8_t v_isShared_6524_; uint8_t v_isSharedCheck_6530_; 
v_val_6521_ = lean_ctor_get(v___x_6520_, 0);
v_isSharedCheck_6530_ = !lean_is_exclusive(v___x_6520_);
if (v_isSharedCheck_6530_ == 0)
{
v___x_6523_ = v___x_6520_;
v_isShared_6524_ = v_isSharedCheck_6530_;
goto v_resetjp_6522_;
}
else
{
lean_inc(v_val_6521_);
lean_dec(v___x_6520_);
v___x_6523_ = lean_box(0);
v_isShared_6524_ = v_isSharedCheck_6530_;
goto v_resetjp_6522_;
}
v_resetjp_6522_:
{
uint8_t v___x_6525_; 
v___x_6525_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6521_);
if (v___x_6525_ == 0)
{
lean_del_object(v___x_6523_);
lean_dec(v_val_6521_);
goto v___jp_6508_;
}
else
{
lean_object* v_directImports_6526_; lean_object* v___x_6528_; 
v_directImports_6526_ = lean_ctor_get(v_val_6521_, 2);
lean_inc_ref(v_directImports_6526_);
lean_dec(v_val_6521_);
if (v_isShared_6524_ == 0)
{
lean_ctor_set(v___x_6523_, 0, v_directImports_6526_);
v___x_6528_ = v___x_6523_;
goto v_reusejp_6527_;
}
else
{
lean_object* v_reuseFailAlloc_6529_; 
v_reuseFailAlloc_6529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6529_, 0, v_directImports_6526_);
v___x_6528_ = v_reuseFailAlloc_6529_;
goto v_reusejp_6527_;
}
v_reusejp_6527_:
{
return v___x_6528_;
}
}
}
}
else
{
lean_dec(v___x_6520_);
goto v___jp_6508_;
}
v___jp_6508_:
{
lean_object* v___x_6509_; 
v___x_6509_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6506_, v_mod_6505_);
if (lean_obj_tag(v___x_6509_) == 1)
{
lean_object* v_val_6510_; lean_object* v___x_6512_; uint8_t v_isShared_6513_; uint8_t v_isSharedCheck_6518_; 
v_val_6510_ = lean_ctor_get(v___x_6509_, 0);
v_isSharedCheck_6518_ = !lean_is_exclusive(v___x_6509_);
if (v_isSharedCheck_6518_ == 0)
{
v___x_6512_ = v___x_6509_;
v_isShared_6513_ = v_isSharedCheck_6518_;
goto v_resetjp_6511_;
}
else
{
lean_inc(v_val_6510_);
lean_dec(v___x_6509_);
v___x_6512_ = lean_box(0);
v_isShared_6513_ = v_isSharedCheck_6518_;
goto v_resetjp_6511_;
}
v_resetjp_6511_:
{
lean_object* v_directImports_6514_; lean_object* v___x_6516_; 
v_directImports_6514_ = lean_ctor_get(v_val_6510_, 2);
lean_inc_ref(v_directImports_6514_);
lean_dec(v_val_6510_);
if (v_isShared_6513_ == 0)
{
lean_ctor_set(v___x_6512_, 0, v_directImports_6514_);
v___x_6516_ = v___x_6512_;
goto v_reusejp_6515_;
}
else
{
lean_object* v_reuseFailAlloc_6517_; 
v_reuseFailAlloc_6517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6517_, 0, v_directImports_6514_);
v___x_6516_ = v_reuseFailAlloc_6517_;
goto v_reusejp_6515_;
}
v_reusejp_6515_:
{
return v___x_6516_;
}
}
}
else
{
lean_object* v___x_6519_; 
lean_dec(v___x_6509_);
v___x_6519_ = lean_box(0);
return v___x_6519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6531_, lean_object* v_mod_6532_){
_start:
{
lean_object* v_res_6533_; 
v_res_6533_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6531_, v_mod_6532_);
lean_dec(v_mod_6532_);
lean_dec_ref(v_self_6531_);
return v_res_6533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6534_, lean_object* v_mod_6535_){
_start:
{
lean_object* v_ileans_6536_; lean_object* v_workers_6537_; lean_object* v___x_6550_; 
v_ileans_6536_ = lean_ctor_get(v_self_6534_, 0);
v_workers_6537_ = lean_ctor_get(v_self_6534_, 1);
v___x_6550_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6537_, v_mod_6535_);
if (lean_obj_tag(v___x_6550_) == 1)
{
lean_object* v_val_6551_; lean_object* v___x_6553_; uint8_t v_isShared_6554_; uint8_t v_isSharedCheck_6560_; 
v_val_6551_ = lean_ctor_get(v___x_6550_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v___x_6550_);
if (v_isSharedCheck_6560_ == 0)
{
v___x_6553_ = v___x_6550_;
v_isShared_6554_ = v_isSharedCheck_6560_;
goto v_resetjp_6552_;
}
else
{
lean_inc(v_val_6551_);
lean_dec(v___x_6550_);
v___x_6553_ = lean_box(0);
v_isShared_6554_ = v_isSharedCheck_6560_;
goto v_resetjp_6552_;
}
v_resetjp_6552_:
{
uint8_t v___x_6555_; 
v___x_6555_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6551_);
if (v___x_6555_ == 0)
{
lean_del_object(v___x_6553_);
lean_dec(v_val_6551_);
goto v___jp_6538_;
}
else
{
lean_object* v_decls_6556_; lean_object* v___x_6558_; 
v_decls_6556_ = lean_ctor_get(v_val_6551_, 5);
lean_inc(v_decls_6556_);
lean_dec(v_val_6551_);
if (v_isShared_6554_ == 0)
{
lean_ctor_set(v___x_6553_, 0, v_decls_6556_);
v___x_6558_ = v___x_6553_;
goto v_reusejp_6557_;
}
else
{
lean_object* v_reuseFailAlloc_6559_; 
v_reuseFailAlloc_6559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_decls_6556_);
v___x_6558_ = v_reuseFailAlloc_6559_;
goto v_reusejp_6557_;
}
v_reusejp_6557_:
{
return v___x_6558_;
}
}
}
}
else
{
lean_dec(v___x_6550_);
goto v___jp_6538_;
}
v___jp_6538_:
{
lean_object* v___x_6539_; 
v___x_6539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6536_, v_mod_6535_);
if (lean_obj_tag(v___x_6539_) == 1)
{
lean_object* v_val_6540_; lean_object* v___x_6542_; uint8_t v_isShared_6543_; uint8_t v_isSharedCheck_6548_; 
v_val_6540_ = lean_ctor_get(v___x_6539_, 0);
v_isSharedCheck_6548_ = !lean_is_exclusive(v___x_6539_);
if (v_isSharedCheck_6548_ == 0)
{
v___x_6542_ = v___x_6539_;
v_isShared_6543_ = v_isSharedCheck_6548_;
goto v_resetjp_6541_;
}
else
{
lean_inc(v_val_6540_);
lean_dec(v___x_6539_);
v___x_6542_ = lean_box(0);
v_isShared_6543_ = v_isSharedCheck_6548_;
goto v_resetjp_6541_;
}
v_resetjp_6541_:
{
lean_object* v_decls_6544_; lean_object* v___x_6546_; 
v_decls_6544_ = lean_ctor_get(v_val_6540_, 4);
lean_inc(v_decls_6544_);
lean_dec(v_val_6540_);
if (v_isShared_6543_ == 0)
{
lean_ctor_set(v___x_6542_, 0, v_decls_6544_);
v___x_6546_ = v___x_6542_;
goto v_reusejp_6545_;
}
else
{
lean_object* v_reuseFailAlloc_6547_; 
v_reuseFailAlloc_6547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6547_, 0, v_decls_6544_);
v___x_6546_ = v_reuseFailAlloc_6547_;
goto v_reusejp_6545_;
}
v_reusejp_6545_:
{
return v___x_6546_;
}
}
}
else
{
lean_object* v___x_6549_; 
lean_dec(v___x_6539_);
v___x_6549_ = lean_box(0);
return v___x_6549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6561_, lean_object* v_mod_6562_){
_start:
{
lean_object* v_res_6563_; 
v_res_6563_ = l_Lean_Server_References_getDecls_x3f(v_self_6561_, v_mod_6562_);
lean_dec(v_mod_6562_);
lean_dec_ref(v_self_6561_);
return v_res_6563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6564_, lean_object* v_x_6565_){
_start:
{
if (lean_obj_tag(v_x_6565_) == 0)
{
lean_object* v_k_6566_; lean_object* v_v_6567_; lean_object* v_l_6568_; lean_object* v_r_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; 
v_k_6566_ = lean_ctor_get(v_x_6565_, 1);
v_v_6567_ = lean_ctor_get(v_x_6565_, 2);
v_l_6568_ = lean_ctor_get(v_x_6565_, 3);
v_r_6569_ = lean_ctor_get(v_x_6565_, 4);
v___x_6570_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6564_, v_l_6568_);
lean_inc(v_v_6567_);
lean_inc(v_k_6566_);
v___x_6571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6571_, 0, v_k_6566_);
lean_ctor_set(v___x_6571_, 1, v_v_6567_);
v___x_6572_ = lean_array_push(v___x_6570_, v___x_6571_);
v_init_6564_ = v___x_6572_;
v_x_6565_ = v_r_6569_;
goto _start;
}
else
{
return v_init_6564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6574_, lean_object* v_x_6575_){
_start:
{
lean_object* v_res_6576_; 
v_res_6576_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6574_, v_x_6575_);
lean_dec(v_x_6575_);
return v_res_6576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6577_, lean_object* v_k_6578_){
_start:
{
if (lean_obj_tag(v_t_6577_) == 0)
{
lean_object* v_k_6579_; lean_object* v_v_6580_; lean_object* v_l_6581_; lean_object* v_r_6582_; uint8_t v___x_6583_; 
v_k_6579_ = lean_ctor_get(v_t_6577_, 1);
v_v_6580_ = lean_ctor_get(v_t_6577_, 2);
v_l_6581_ = lean_ctor_get(v_t_6577_, 3);
v_r_6582_ = lean_ctor_get(v_t_6577_, 4);
v___x_6583_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6578_, v_k_6579_);
switch(v___x_6583_)
{
case 0:
{
v_t_6577_ = v_l_6581_;
goto _start;
}
case 1:
{
lean_object* v___x_6585_; 
lean_inc(v_v_6580_);
v___x_6585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6585_, 0, v_v_6580_);
return v___x_6585_;
}
default: 
{
v_t_6577_ = v_r_6582_;
goto _start;
}
}
}
else
{
lean_object* v___x_6587_; 
v___x_6587_ = lean_box(0);
return v___x_6587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6588_, lean_object* v_k_6589_){
_start:
{
lean_object* v_res_6590_; 
v_res_6590_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6588_, v_k_6589_);
lean_dec_ref(v_k_6589_);
lean_dec(v_t_6588_);
return v_res_6590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6591_, lean_object* v_as_6592_, size_t v_sz_6593_, size_t v_i_6594_, lean_object* v_b_6595_){
_start:
{
lean_object* v_a_6597_; uint8_t v___x_6601_; 
v___x_6601_ = lean_usize_dec_lt(v_i_6594_, v_sz_6593_);
if (v___x_6601_ == 0)
{
return v_b_6595_;
}
else
{
lean_object* v_a_6602_; lean_object* v_snd_6603_; lean_object* v_snd_6604_; lean_object* v_fst_6605_; lean_object* v___x_6607_; uint8_t v_isShared_6608_; uint8_t v_isSharedCheck_6633_; 
v_a_6602_ = lean_array_uget(v_as_6592_, v_i_6594_);
v_snd_6603_ = lean_ctor_get(v_a_6602_, 1);
lean_inc(v_snd_6603_);
v_snd_6604_ = lean_ctor_get(v_snd_6603_, 1);
lean_inc(v_snd_6604_);
v_fst_6605_ = lean_ctor_get(v_a_6602_, 0);
v_isSharedCheck_6633_ = !lean_is_exclusive(v_a_6602_);
if (v_isSharedCheck_6633_ == 0)
{
lean_object* v_unused_6634_; 
v_unused_6634_ = lean_ctor_get(v_a_6602_, 1);
lean_dec(v_unused_6634_);
v___x_6607_ = v_a_6602_;
v_isShared_6608_ = v_isSharedCheck_6633_;
goto v_resetjp_6606_;
}
else
{
lean_inc(v_fst_6605_);
lean_dec(v_a_6602_);
v___x_6607_ = lean_box(0);
v_isShared_6608_ = v_isSharedCheck_6633_;
goto v_resetjp_6606_;
}
v_resetjp_6606_:
{
lean_object* v_fst_6609_; lean_object* v___x_6611_; uint8_t v_isShared_6612_; uint8_t v_isSharedCheck_6631_; 
v_fst_6609_ = lean_ctor_get(v_snd_6603_, 0);
v_isSharedCheck_6631_ = !lean_is_exclusive(v_snd_6603_);
if (v_isSharedCheck_6631_ == 0)
{
lean_object* v_unused_6632_; 
v_unused_6632_ = lean_ctor_get(v_snd_6603_, 1);
lean_dec(v_unused_6632_);
v___x_6611_ = v_snd_6603_;
v_isShared_6612_ = v_isSharedCheck_6631_;
goto v_resetjp_6610_;
}
else
{
lean_inc(v_fst_6609_);
lean_dec(v_snd_6603_);
v___x_6611_ = lean_box(0);
v_isShared_6612_ = v_isSharedCheck_6631_;
goto v_resetjp_6610_;
}
v_resetjp_6610_:
{
lean_object* v_fst_6613_; lean_object* v_snd_6614_; lean_object* v___x_6616_; uint8_t v_isShared_6617_; uint8_t v_isSharedCheck_6630_; 
v_fst_6613_ = lean_ctor_get(v_snd_6604_, 0);
v_snd_6614_ = lean_ctor_get(v_snd_6604_, 1);
v_isSharedCheck_6630_ = !lean_is_exclusive(v_snd_6604_);
if (v_isSharedCheck_6630_ == 0)
{
v___x_6616_ = v_snd_6604_;
v_isShared_6617_ = v_isSharedCheck_6630_;
goto v_resetjp_6615_;
}
else
{
lean_inc(v_snd_6614_);
lean_inc(v_fst_6613_);
lean_dec(v_snd_6604_);
v___x_6616_ = lean_box(0);
v_isShared_6617_ = v_isSharedCheck_6630_;
goto v_resetjp_6615_;
}
v_resetjp_6615_:
{
lean_object* v___x_6618_; 
v___x_6618_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6613_, v_ident_6591_);
lean_dec(v_fst_6613_);
if (lean_obj_tag(v___x_6618_) == 1)
{
lean_object* v_val_6619_; lean_object* v___x_6621_; 
v_val_6619_ = lean_ctor_get(v___x_6618_, 0);
lean_inc(v_val_6619_);
lean_dec_ref(v___x_6618_);
if (v_isShared_6617_ == 0)
{
lean_ctor_set(v___x_6616_, 0, v_val_6619_);
v___x_6621_ = v___x_6616_;
goto v_reusejp_6620_;
}
else
{
lean_object* v_reuseFailAlloc_6629_; 
v_reuseFailAlloc_6629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6629_, 0, v_val_6619_);
lean_ctor_set(v_reuseFailAlloc_6629_, 1, v_snd_6614_);
v___x_6621_ = v_reuseFailAlloc_6629_;
goto v_reusejp_6620_;
}
v_reusejp_6620_:
{
lean_object* v___x_6623_; 
if (v_isShared_6612_ == 0)
{
lean_ctor_set(v___x_6611_, 1, v___x_6621_);
lean_ctor_set(v___x_6611_, 0, v_fst_6605_);
v___x_6623_ = v___x_6611_;
goto v_reusejp_6622_;
}
else
{
lean_object* v_reuseFailAlloc_6628_; 
v_reuseFailAlloc_6628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6628_, 0, v_fst_6605_);
lean_ctor_set(v_reuseFailAlloc_6628_, 1, v___x_6621_);
v___x_6623_ = v_reuseFailAlloc_6628_;
goto v_reusejp_6622_;
}
v_reusejp_6622_:
{
lean_object* v___x_6625_; 
if (v_isShared_6608_ == 0)
{
lean_ctor_set(v___x_6607_, 1, v___x_6623_);
lean_ctor_set(v___x_6607_, 0, v_fst_6609_);
v___x_6625_ = v___x_6607_;
goto v_reusejp_6624_;
}
else
{
lean_object* v_reuseFailAlloc_6627_; 
v_reuseFailAlloc_6627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6627_, 0, v_fst_6609_);
lean_ctor_set(v_reuseFailAlloc_6627_, 1, v___x_6623_);
v___x_6625_ = v_reuseFailAlloc_6627_;
goto v_reusejp_6624_;
}
v_reusejp_6624_:
{
lean_object* v___x_6626_; 
v___x_6626_ = lean_array_push(v_b_6595_, v___x_6625_);
v_a_6597_ = v___x_6626_;
goto v___jp_6596_;
}
}
}
}
else
{
lean_dec(v___x_6618_);
lean_del_object(v___x_6616_);
lean_dec(v_snd_6614_);
lean_del_object(v___x_6611_);
lean_dec(v_fst_6609_);
lean_del_object(v___x_6607_);
lean_dec(v_fst_6605_);
v_a_6597_ = v_b_6595_;
goto v___jp_6596_;
}
}
}
}
}
v___jp_6596_:
{
size_t v___x_6598_; size_t v___x_6599_; 
v___x_6598_ = ((size_t)1ULL);
v___x_6599_ = lean_usize_add(v_i_6594_, v___x_6598_);
v_i_6594_ = v___x_6599_;
v_b_6595_ = v_a_6597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6635_, lean_object* v_as_6636_, lean_object* v_sz_6637_, lean_object* v_i_6638_, lean_object* v_b_6639_){
_start:
{
size_t v_sz_boxed_6640_; size_t v_i_boxed_6641_; lean_object* v_res_6642_; 
v_sz_boxed_6640_ = lean_unbox_usize(v_sz_6637_);
lean_dec(v_sz_6637_);
v_i_boxed_6641_ = lean_unbox_usize(v_i_6638_);
lean_dec(v_i_6638_);
v_res_6642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6635_, v_as_6636_, v_sz_boxed_6640_, v_i_boxed_6641_, v_b_6639_);
lean_dec_ref(v_as_6636_);
lean_dec_ref(v_ident_6635_);
return v_res_6642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6649_, lean_object* v_ident_6650_){
_start:
{
lean_object* v___y_6652_; 
if (lean_obj_tag(v_ident_6650_) == 0)
{
lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; 
v___x_6657_ = l_Lean_Server_References_allRefs(v_self_6649_);
v___x_6658_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6659_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6658_, v___x_6657_);
lean_dec(v___x_6657_);
v___y_6652_ = v___x_6659_;
goto v___jp_6651_;
}
else
{
lean_object* v_moduleName_6660_; lean_object* v_identModuleName_6661_; lean_object* v___x_6662_; 
v_moduleName_6660_ = lean_ctor_get(v_ident_6650_, 0);
lean_inc_ref(v_moduleName_6660_);
v_identModuleName_6661_ = l_String_toName(v_moduleName_6660_);
v___x_6662_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6649_, v_identModuleName_6661_);
if (lean_obj_tag(v___x_6662_) == 0)
{
lean_object* v___x_6663_; 
lean_dec(v_identModuleName_6661_);
v___x_6663_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6652_ = v___x_6663_;
goto v___jp_6651_;
}
else
{
lean_object* v_val_6664_; lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; 
v_val_6664_ = lean_ctor_get(v___x_6662_, 0);
lean_inc(v_val_6664_);
lean_dec_ref(v___x_6662_);
v___x_6665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6665_, 0, v_identModuleName_6661_);
lean_ctor_set(v___x_6665_, 1, v_val_6664_);
v___x_6666_ = lean_unsigned_to_nat(1u);
v___x_6667_ = lean_mk_empty_array_with_capacity(v___x_6666_);
v___x_6668_ = lean_array_push(v___x_6667_, v___x_6665_);
v___y_6652_ = v___x_6668_;
goto v___jp_6651_;
}
}
v___jp_6651_:
{
lean_object* v_result_6653_; size_t v_sz_6654_; size_t v___x_6655_; lean_object* v___x_6656_; 
v_result_6653_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6654_ = lean_array_size(v___y_6652_);
v___x_6655_ = ((size_t)0ULL);
v___x_6656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6650_, v___y_6652_, v_sz_6654_, v___x_6655_, v_result_6653_);
lean_dec_ref(v___y_6652_);
lean_dec_ref(v_ident_6650_);
return v___x_6656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6669_, lean_object* v_t_6670_, lean_object* v_k_6671_){
_start:
{
lean_object* v___x_6672_; 
v___x_6672_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6670_, v_k_6671_);
return v___x_6672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6673_, lean_object* v_t_6674_, lean_object* v_k_6675_){
_start:
{
lean_object* v_res_6676_; 
v_res_6676_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6673_, v_t_6674_, v_k_6675_);
lean_dec_ref(v_k_6675_);
lean_dec(v_t_6674_);
return v_res_6676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6677_, lean_object* v_t_6678_){
_start:
{
lean_object* v___x_6679_; 
v___x_6679_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6677_, v_t_6678_);
return v___x_6679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6680_, lean_object* v_t_6681_){
_start:
{
lean_object* v_res_6682_; 
v_res_6682_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6680_, v_t_6681_);
lean_dec(v_t_6681_);
return v_res_6682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6683_, lean_object* v_module_6684_, lean_object* v_pos_6685_, uint8_t v_includeStop_6686_){
_start:
{
lean_object* v___x_6687_; 
v___x_6687_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6683_, v_module_6684_);
if (lean_obj_tag(v___x_6687_) == 1)
{
lean_object* v_val_6688_; lean_object* v_snd_6689_; lean_object* v_fst_6690_; lean_object* v___x_6691_; 
v_val_6688_ = lean_ctor_get(v___x_6687_, 0);
lean_inc(v_val_6688_);
lean_dec_ref(v___x_6687_);
v_snd_6689_ = lean_ctor_get(v_val_6688_, 1);
lean_inc(v_snd_6689_);
lean_dec(v_val_6688_);
v_fst_6690_ = lean_ctor_get(v_snd_6689_, 0);
lean_inc(v_fst_6690_);
lean_dec(v_snd_6689_);
v___x_6691_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6690_, v_pos_6685_, v_includeStop_6686_);
return v___x_6691_;
}
else
{
lean_object* v___x_6692_; 
lean_dec(v___x_6687_);
v___x_6692_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6693_, lean_object* v_module_6694_, lean_object* v_pos_6695_, lean_object* v_includeStop_6696_){
_start:
{
uint8_t v_includeStop_boxed_6697_; lean_object* v_res_6698_; 
v_includeStop_boxed_6697_ = lean_unbox(v_includeStop_6696_);
v_res_6698_ = l_Lean_Server_References_findAt(v_self_6693_, v_module_6694_, v_pos_6695_, v_includeStop_boxed_6697_);
lean_dec_ref(v_pos_6695_);
lean_dec(v_module_6694_);
return v_res_6698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6699_, lean_object* v_module_6700_, lean_object* v_pos_6701_, uint8_t v_includeStop_6702_){
_start:
{
lean_object* v___x_6703_; 
v___x_6703_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6699_, v_module_6700_);
if (lean_obj_tag(v___x_6703_) == 0)
{
lean_object* v___x_6704_; 
v___x_6704_ = lean_box(0);
return v___x_6704_;
}
else
{
lean_object* v_val_6705_; lean_object* v_snd_6706_; lean_object* v_fst_6707_; lean_object* v___x_6708_; 
v_val_6705_ = lean_ctor_get(v___x_6703_, 0);
lean_inc(v_val_6705_);
lean_dec_ref(v___x_6703_);
v_snd_6706_ = lean_ctor_get(v_val_6705_, 1);
lean_inc(v_snd_6706_);
lean_dec(v_val_6705_);
v_fst_6707_ = lean_ctor_get(v_snd_6706_, 0);
lean_inc(v_fst_6707_);
lean_dec(v_snd_6706_);
v___x_6708_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6707_, v_pos_6701_, v_includeStop_6702_);
lean_dec(v_fst_6707_);
return v___x_6708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6709_, lean_object* v_module_6710_, lean_object* v_pos_6711_, lean_object* v_includeStop_6712_){
_start:
{
uint8_t v_includeStop_boxed_6713_; lean_object* v_res_6714_; 
v_includeStop_boxed_6713_ = lean_unbox(v_includeStop_6712_);
v_res_6714_ = l_Lean_Server_References_findRange_x3f(v_self_6709_, v_module_6710_, v_pos_6711_, v_includeStop_boxed_6713_);
lean_dec_ref(v_pos_6711_);
lean_dec(v_module_6710_);
return v_res_6714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6715_, lean_object* v_k_6716_){
_start:
{
if (lean_obj_tag(v_t_6715_) == 0)
{
lean_object* v_k_6717_; lean_object* v_v_6718_; lean_object* v_l_6719_; lean_object* v_r_6720_; uint8_t v___x_6721_; 
v_k_6717_ = lean_ctor_get(v_t_6715_, 1);
v_v_6718_ = lean_ctor_get(v_t_6715_, 2);
v_l_6719_ = lean_ctor_get(v_t_6715_, 3);
v_r_6720_ = lean_ctor_get(v_t_6715_, 4);
v___x_6721_ = lean_string_dec_lt(v_k_6716_, v_k_6717_);
if (v___x_6721_ == 0)
{
uint8_t v___x_6722_; 
v___x_6722_ = lean_string_dec_eq(v_k_6716_, v_k_6717_);
if (v___x_6722_ == 0)
{
v_t_6715_ = v_r_6720_;
goto _start;
}
else
{
lean_object* v___x_6724_; 
lean_inc(v_v_6718_);
v___x_6724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6724_, 0, v_v_6718_);
return v___x_6724_;
}
}
else
{
v_t_6715_ = v_l_6719_;
goto _start;
}
}
else
{
lean_object* v___x_6726_; 
v___x_6726_ = lean_box(0);
return v___x_6726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6727_, lean_object* v_k_6728_){
_start:
{
lean_object* v_res_6729_; 
v_res_6729_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6727_, v_k_6728_);
lean_dec_ref(v_k_6728_);
lean_dec(v_t_6727_);
return v_res_6729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6730_, lean_object* v_name_6731_){
_start:
{
lean_object* v___x_6732_; 
v___x_6732_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6730_, v_name_6731_);
if (lean_obj_tag(v___x_6732_) == 0)
{
lean_object* v___x_6733_; 
lean_dec_ref(v_name_6731_);
v___x_6733_ = lean_box(0);
return v___x_6733_;
}
else
{
lean_object* v_val_6734_; lean_object* v___x_6736_; uint8_t v_isShared_6737_; uint8_t v_isSharedCheck_6744_; 
v_val_6734_ = lean_ctor_get(v___x_6732_, 0);
v_isSharedCheck_6744_ = !lean_is_exclusive(v___x_6732_);
if (v_isSharedCheck_6744_ == 0)
{
v___x_6736_ = v___x_6732_;
v_isShared_6737_ = v_isSharedCheck_6744_;
goto v_resetjp_6735_;
}
else
{
lean_inc(v_val_6734_);
lean_dec(v___x_6732_);
v___x_6736_ = lean_box(0);
v_isShared_6737_ = v_isSharedCheck_6744_;
goto v_resetjp_6735_;
}
v_resetjp_6735_:
{
lean_object* v___x_6738_; lean_object* v___x_6739_; lean_object* v___x_6740_; lean_object* v___x_6742_; 
v___x_6738_ = l_Lean_Lsp_DeclInfo_range(v_val_6734_);
v___x_6739_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6734_);
lean_dec(v_val_6734_);
v___x_6740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6740_, 0, v_name_6731_);
lean_ctor_set(v___x_6740_, 1, v___x_6738_);
lean_ctor_set(v___x_6740_, 2, v___x_6739_);
if (v_isShared_6737_ == 0)
{
lean_ctor_set(v___x_6736_, 0, v___x_6740_);
v___x_6742_ = v___x_6736_;
goto v_reusejp_6741_;
}
else
{
lean_object* v_reuseFailAlloc_6743_; 
v_reuseFailAlloc_6743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6743_, 0, v___x_6740_);
v___x_6742_ = v_reuseFailAlloc_6743_;
goto v_reusejp_6741_;
}
v_reusejp_6741_:
{
return v___x_6742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6745_, lean_object* v_name_6746_){
_start:
{
lean_object* v_res_6747_; 
v_res_6747_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6745_, v_name_6746_);
lean_dec(v_ds_6745_);
return v_res_6747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6748_, lean_object* v_t_6749_, lean_object* v_k_6750_){
_start:
{
lean_object* v___x_6751_; 
v___x_6751_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6749_, v_k_6750_);
return v___x_6751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6752_, lean_object* v_t_6753_, lean_object* v_k_6754_){
_start:
{
lean_object* v_res_6755_; 
v_res_6755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6752_, v_t_6753_, v_k_6754_);
lean_dec_ref(v_k_6754_);
lean_dec(v_t_6753_);
return v_res_6755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6756_, lean_object* v_fst_6757_, lean_object* v_snd_6758_, lean_object* v_as_6759_, size_t v_sz_6760_, size_t v_i_6761_, lean_object* v_b_6762_){
_start:
{
uint8_t v___x_6763_; 
v___x_6763_ = lean_usize_dec_lt(v_i_6761_, v_sz_6760_);
if (v___x_6763_ == 0)
{
lean_dec(v_fst_6757_);
lean_dec_ref(v_fst_6756_);
return v_b_6762_;
}
else
{
lean_object* v_a_6764_; lean_object* v___y_6766_; lean_object* v___x_6774_; 
v_a_6764_ = lean_array_uget_borrowed(v_as_6759_, v_i_6761_);
v___x_6774_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6764_);
if (lean_obj_tag(v___x_6774_) == 0)
{
lean_object* v___x_6775_; 
v___x_6775_ = lean_box(0);
v___y_6766_ = v___x_6775_;
goto v___jp_6765_;
}
else
{
lean_object* v_val_6776_; lean_object* v___x_6777_; 
v_val_6776_ = lean_ctor_get(v___x_6774_, 0);
lean_inc(v_val_6776_);
lean_dec_ref(v___x_6774_);
v___x_6777_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6758_, v_val_6776_);
v___y_6766_ = v___x_6777_;
goto v___jp_6765_;
}
v___jp_6765_:
{
lean_object* v___x_6767_; lean_object* v___x_6768_; lean_object* v___x_6769_; lean_object* v___x_6770_; size_t v___x_6771_; size_t v___x_6772_; 
v___x_6767_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6764_);
lean_inc_ref(v_fst_6756_);
v___x_6768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6768_, 0, v_fst_6756_);
lean_ctor_set(v___x_6768_, 1, v___x_6767_);
lean_inc(v_fst_6757_);
v___x_6769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6769_, 0, v___x_6768_);
lean_ctor_set(v___x_6769_, 1, v_fst_6757_);
lean_ctor_set(v___x_6769_, 2, v___y_6766_);
v___x_6770_ = lean_array_push(v_b_6762_, v___x_6769_);
v___x_6771_ = ((size_t)1ULL);
v___x_6772_ = lean_usize_add(v_i_6761_, v___x_6771_);
v_i_6761_ = v___x_6772_;
v_b_6762_ = v___x_6770_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6778_, lean_object* v_fst_6779_, lean_object* v_snd_6780_, lean_object* v_as_6781_, lean_object* v_sz_6782_, lean_object* v_i_6783_, lean_object* v_b_6784_){
_start:
{
size_t v_sz_boxed_6785_; size_t v_i_boxed_6786_; lean_object* v_res_6787_; 
v_sz_boxed_6785_ = lean_unbox_usize(v_sz_6782_);
lean_dec(v_sz_6782_);
v_i_boxed_6786_ = lean_unbox_usize(v_i_6783_);
lean_dec(v_i_6783_);
v_res_6787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6778_, v_fst_6779_, v_snd_6780_, v_as_6781_, v_sz_boxed_6785_, v_i_boxed_6786_, v_b_6784_);
lean_dec_ref(v_as_6781_);
lean_dec(v_snd_6780_);
return v_res_6787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6788_, lean_object* v_as_6789_, size_t v_sz_6790_, size_t v_i_6791_, lean_object* v_b_6792_){
_start:
{
uint8_t v___x_6793_; 
v___x_6793_ = lean_usize_dec_lt(v_i_6791_, v_sz_6790_);
if (v___x_6793_ == 0)
{
return v_b_6792_;
}
else
{
lean_object* v_a_6794_; lean_object* v_snd_6795_; lean_object* v_snd_6796_; lean_object* v_fst_6797_; lean_object* v_fst_6798_; lean_object* v_fst_6799_; lean_object* v_snd_6800_; lean_object* v___x_6802_; uint8_t v_isShared_6803_; uint8_t v_isSharedCheck_6827_; 
v_a_6794_ = lean_array_uget_borrowed(v_as_6789_, v_i_6791_);
v_snd_6795_ = lean_ctor_get(v_a_6794_, 1);
v_snd_6796_ = lean_ctor_get(v_snd_6795_, 1);
lean_inc(v_snd_6796_);
v_fst_6797_ = lean_ctor_get(v_a_6794_, 0);
v_fst_6798_ = lean_ctor_get(v_snd_6795_, 0);
v_fst_6799_ = lean_ctor_get(v_snd_6796_, 0);
v_snd_6800_ = lean_ctor_get(v_snd_6796_, 1);
v_isSharedCheck_6827_ = !lean_is_exclusive(v_snd_6796_);
if (v_isSharedCheck_6827_ == 0)
{
v___x_6802_ = v_snd_6796_;
v_isShared_6803_ = v_isSharedCheck_6827_;
goto v_resetjp_6801_;
}
else
{
lean_inc(v_snd_6800_);
lean_inc(v_fst_6799_);
lean_dec(v_snd_6796_);
v___x_6802_ = lean_box(0);
v_isShared_6803_ = v_isSharedCheck_6827_;
goto v_resetjp_6801_;
}
v_resetjp_6801_:
{
lean_object* v_result_6805_; 
if (v_includeDefinition_6788_ == 0)
{
lean_del_object(v___x_6802_);
v_result_6805_ = v_b_6792_;
goto v___jp_6804_;
}
else
{
lean_object* v_definition_x3f_6813_; 
v_definition_x3f_6813_ = lean_ctor_get(v_fst_6799_, 0);
if (lean_obj_tag(v_definition_x3f_6813_) == 1)
{
lean_object* v_val_6814_; lean_object* v___y_6816_; lean_object* v___x_6823_; 
v_val_6814_ = lean_ctor_get(v_definition_x3f_6813_, 0);
v___x_6823_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6814_);
if (lean_obj_tag(v___x_6823_) == 0)
{
lean_object* v___x_6824_; 
v___x_6824_ = lean_box(0);
v___y_6816_ = v___x_6824_;
goto v___jp_6815_;
}
else
{
lean_object* v_val_6825_; lean_object* v___x_6826_; 
v_val_6825_ = lean_ctor_get(v___x_6823_, 0);
lean_inc(v_val_6825_);
lean_dec_ref(v___x_6823_);
v___x_6826_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6800_, v_val_6825_);
v___y_6816_ = v___x_6826_;
goto v___jp_6815_;
}
v___jp_6815_:
{
lean_object* v___x_6817_; lean_object* v___x_6819_; 
v___x_6817_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6814_);
lean_inc(v_fst_6797_);
if (v_isShared_6803_ == 0)
{
lean_ctor_set(v___x_6802_, 1, v___x_6817_);
lean_ctor_set(v___x_6802_, 0, v_fst_6797_);
v___x_6819_ = v___x_6802_;
goto v_reusejp_6818_;
}
else
{
lean_object* v_reuseFailAlloc_6822_; 
v_reuseFailAlloc_6822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6822_, 0, v_fst_6797_);
lean_ctor_set(v_reuseFailAlloc_6822_, 1, v___x_6817_);
v___x_6819_ = v_reuseFailAlloc_6822_;
goto v_reusejp_6818_;
}
v_reusejp_6818_:
{
lean_object* v___x_6820_; lean_object* v___x_6821_; 
lean_inc(v_fst_6798_);
v___x_6820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6820_, 0, v___x_6819_);
lean_ctor_set(v___x_6820_, 1, v_fst_6798_);
lean_ctor_set(v___x_6820_, 2, v___y_6816_);
v___x_6821_ = lean_array_push(v_b_6792_, v___x_6820_);
v_result_6805_ = v___x_6821_;
goto v___jp_6804_;
}
}
}
else
{
lean_del_object(v___x_6802_);
v_result_6805_ = v_b_6792_;
goto v___jp_6804_;
}
}
v___jp_6804_:
{
lean_object* v_usages_6806_; size_t v_sz_6807_; size_t v___x_6808_; lean_object* v___x_6809_; size_t v___x_6810_; size_t v___x_6811_; 
v_usages_6806_ = lean_ctor_get(v_fst_6799_, 1);
lean_inc_ref(v_usages_6806_);
lean_dec(v_fst_6799_);
v_sz_6807_ = lean_array_size(v_usages_6806_);
v___x_6808_ = ((size_t)0ULL);
lean_inc(v_fst_6798_);
lean_inc(v_fst_6797_);
v___x_6809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6797_, v_fst_6798_, v_snd_6800_, v_usages_6806_, v_sz_6807_, v___x_6808_, v_result_6805_);
lean_dec_ref(v_usages_6806_);
lean_dec(v_snd_6800_);
v___x_6810_ = ((size_t)1ULL);
v___x_6811_ = lean_usize_add(v_i_6791_, v___x_6810_);
v_i_6791_ = v___x_6811_;
v_b_6792_ = v___x_6809_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6828_, lean_object* v_as_6829_, lean_object* v_sz_6830_, lean_object* v_i_6831_, lean_object* v_b_6832_){
_start:
{
uint8_t v_includeDefinition_boxed_6833_; size_t v_sz_boxed_6834_; size_t v_i_boxed_6835_; lean_object* v_res_6836_; 
v_includeDefinition_boxed_6833_ = lean_unbox(v_includeDefinition_6828_);
v_sz_boxed_6834_ = lean_unbox_usize(v_sz_6830_);
lean_dec(v_sz_6830_);
v_i_boxed_6835_ = lean_unbox_usize(v_i_6831_);
lean_dec(v_i_6831_);
v_res_6836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6833_, v_as_6829_, v_sz_boxed_6834_, v_i_boxed_6835_, v_b_6832_);
lean_dec_ref(v_as_6829_);
return v_res_6836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6839_, lean_object* v_ident_6840_, uint8_t v_includeDefinition_6841_){
_start:
{
lean_object* v_result_6842_; lean_object* v___x_6843_; size_t v_sz_6844_; size_t v___x_6845_; lean_object* v___x_6846_; 
v_result_6842_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6843_ = l_Lean_Server_References_allRefsFor(v_self_6839_, v_ident_6840_);
v_sz_6844_ = lean_array_size(v___x_6843_);
v___x_6845_ = ((size_t)0ULL);
v___x_6846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6841_, v___x_6843_, v_sz_6844_, v___x_6845_, v_result_6842_);
lean_dec_ref(v___x_6843_);
return v___x_6846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6847_, lean_object* v_ident_6848_, lean_object* v_includeDefinition_6849_){
_start:
{
uint8_t v_includeDefinition_boxed_6850_; lean_object* v_res_6851_; 
v_includeDefinition_boxed_6850_ = lean_unbox(v_includeDefinition_6849_);
v_res_6851_ = l_Lean_Server_References_referringTo(v_self_6847_, v_ident_6848_, v_includeDefinition_boxed_6850_);
return v_res_6851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6855_, size_t v_sz_6856_, size_t v_i_6857_, lean_object* v_b_6858_){
_start:
{
uint8_t v___x_6859_; 
v___x_6859_ = lean_usize_dec_lt(v_i_6857_, v_sz_6856_);
if (v___x_6859_ == 0)
{
lean_inc_ref(v_b_6858_);
return v_b_6858_;
}
else
{
lean_object* v_a_6860_; lean_object* v_snd_6861_; lean_object* v_snd_6862_; lean_object* v_fst_6863_; lean_object* v_fst_6864_; lean_object* v_fst_6865_; lean_object* v_snd_6866_; lean_object* v___x_6868_; uint8_t v_isShared_6869_; uint8_t v_isSharedCheck_6904_; 
v_a_6860_ = lean_array_uget_borrowed(v_as_6855_, v_i_6857_);
v_snd_6861_ = lean_ctor_get(v_a_6860_, 1);
v_snd_6862_ = lean_ctor_get(v_snd_6861_, 1);
lean_inc(v_snd_6862_);
v_fst_6863_ = lean_ctor_get(v_snd_6862_, 0);
lean_inc(v_fst_6863_);
v_fst_6864_ = lean_ctor_get(v_a_6860_, 0);
v_fst_6865_ = lean_ctor_get(v_snd_6861_, 0);
v_snd_6866_ = lean_ctor_get(v_snd_6862_, 1);
v_isSharedCheck_6904_ = !lean_is_exclusive(v_snd_6862_);
if (v_isSharedCheck_6904_ == 0)
{
lean_object* v_unused_6905_; 
v_unused_6905_ = lean_ctor_get(v_snd_6862_, 0);
lean_dec(v_unused_6905_);
v___x_6868_ = v_snd_6862_;
v_isShared_6869_ = v_isSharedCheck_6904_;
goto v_resetjp_6867_;
}
else
{
lean_inc(v_snd_6866_);
lean_dec(v_snd_6862_);
v___x_6868_ = lean_box(0);
v_isShared_6869_ = v_isSharedCheck_6904_;
goto v_resetjp_6867_;
}
v_resetjp_6867_:
{
lean_object* v_definition_x3f_6870_; lean_object* v___x_6872_; uint8_t v_isShared_6873_; uint8_t v_isSharedCheck_6902_; 
v_definition_x3f_6870_ = lean_ctor_get(v_fst_6863_, 0);
v_isSharedCheck_6902_ = !lean_is_exclusive(v_fst_6863_);
if (v_isSharedCheck_6902_ == 0)
{
lean_object* v_unused_6903_; 
v_unused_6903_ = lean_ctor_get(v_fst_6863_, 1);
lean_dec(v_unused_6903_);
v___x_6872_ = v_fst_6863_;
v_isShared_6873_ = v_isSharedCheck_6902_;
goto v_resetjp_6871_;
}
else
{
lean_inc(v_definition_x3f_6870_);
lean_dec(v_fst_6863_);
v___x_6872_ = lean_box(0);
v_isShared_6873_ = v_isSharedCheck_6902_;
goto v_resetjp_6871_;
}
v_resetjp_6871_:
{
lean_object* v___x_6874_; 
v___x_6874_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6870_) == 1)
{
lean_object* v_val_6875_; lean_object* v___x_6877_; uint8_t v_isShared_6878_; uint8_t v_isSharedCheck_6897_; 
v_val_6875_ = lean_ctor_get(v_definition_x3f_6870_, 0);
v_isSharedCheck_6897_ = !lean_is_exclusive(v_definition_x3f_6870_);
if (v_isSharedCheck_6897_ == 0)
{
v___x_6877_ = v_definition_x3f_6870_;
v_isShared_6878_ = v_isSharedCheck_6897_;
goto v_resetjp_6876_;
}
else
{
lean_inc(v_val_6875_);
lean_dec(v_definition_x3f_6870_);
v___x_6877_ = lean_box(0);
v_isShared_6878_ = v_isSharedCheck_6897_;
goto v_resetjp_6876_;
}
v_resetjp_6876_:
{
lean_object* v___y_6880_; lean_object* v___x_6893_; 
v___x_6893_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6875_);
if (lean_obj_tag(v___x_6893_) == 0)
{
lean_object* v___x_6894_; 
lean_dec(v_snd_6866_);
v___x_6894_ = lean_box(0);
v___y_6880_ = v___x_6894_;
goto v___jp_6879_;
}
else
{
lean_object* v_val_6895_; lean_object* v___x_6896_; 
v_val_6895_ = lean_ctor_get(v___x_6893_, 0);
lean_inc(v_val_6895_);
lean_dec_ref(v___x_6893_);
v___x_6896_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6866_, v_val_6895_);
lean_dec(v_snd_6866_);
v___y_6880_ = v___x_6896_;
goto v___jp_6879_;
}
v___jp_6879_:
{
lean_object* v___x_6881_; lean_object* v___x_6883_; 
v___x_6881_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6875_);
lean_dec(v_val_6875_);
lean_inc(v_fst_6864_);
if (v_isShared_6873_ == 0)
{
lean_ctor_set(v___x_6872_, 1, v___x_6881_);
lean_ctor_set(v___x_6872_, 0, v_fst_6864_);
v___x_6883_ = v___x_6872_;
goto v_reusejp_6882_;
}
else
{
lean_object* v_reuseFailAlloc_6892_; 
v_reuseFailAlloc_6892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6892_, 0, v_fst_6864_);
lean_ctor_set(v_reuseFailAlloc_6892_, 1, v___x_6881_);
v___x_6883_ = v_reuseFailAlloc_6892_;
goto v_reusejp_6882_;
}
v_reusejp_6882_:
{
lean_object* v___x_6884_; lean_object* v___x_6886_; 
lean_inc(v_fst_6865_);
v___x_6884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6884_, 0, v___x_6883_);
lean_ctor_set(v___x_6884_, 1, v_fst_6865_);
lean_ctor_set(v___x_6884_, 2, v___y_6880_);
if (v_isShared_6878_ == 0)
{
lean_ctor_set(v___x_6877_, 0, v___x_6884_);
v___x_6886_ = v___x_6877_;
goto v_reusejp_6885_;
}
else
{
lean_object* v_reuseFailAlloc_6891_; 
v_reuseFailAlloc_6891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6891_, 0, v___x_6884_);
v___x_6886_ = v_reuseFailAlloc_6891_;
goto v_reusejp_6885_;
}
v_reusejp_6885_:
{
lean_object* v___x_6887_; lean_object* v___x_6889_; 
v___x_6887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6887_, 0, v___x_6886_);
if (v_isShared_6869_ == 0)
{
lean_ctor_set(v___x_6868_, 1, v___x_6874_);
lean_ctor_set(v___x_6868_, 0, v___x_6887_);
v___x_6889_ = v___x_6868_;
goto v_reusejp_6888_;
}
else
{
lean_object* v_reuseFailAlloc_6890_; 
v_reuseFailAlloc_6890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6890_, 0, v___x_6887_);
lean_ctor_set(v_reuseFailAlloc_6890_, 1, v___x_6874_);
v___x_6889_ = v_reuseFailAlloc_6890_;
goto v_reusejp_6888_;
}
v_reusejp_6888_:
{
return v___x_6889_;
}
}
}
}
}
}
else
{
lean_object* v___x_6898_; size_t v___x_6899_; size_t v___x_6900_; 
lean_del_object(v___x_6872_);
lean_dec(v_definition_x3f_6870_);
lean_del_object(v___x_6868_);
lean_dec(v_snd_6866_);
v___x_6898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6899_ = ((size_t)1ULL);
v___x_6900_ = lean_usize_add(v_i_6857_, v___x_6899_);
v_i_6857_ = v___x_6900_;
v_b_6858_ = v___x_6898_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6906_, lean_object* v_sz_6907_, lean_object* v_i_6908_, lean_object* v_b_6909_){
_start:
{
size_t v_sz_boxed_6910_; size_t v_i_boxed_6911_; lean_object* v_res_6912_; 
v_sz_boxed_6910_ = lean_unbox_usize(v_sz_6907_);
lean_dec(v_sz_6907_);
v_i_boxed_6911_ = lean_unbox_usize(v_i_6908_);
lean_dec(v_i_6908_);
v_res_6912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6906_, v_sz_boxed_6910_, v_i_boxed_6911_, v_b_6909_);
lean_dec_ref(v_b_6909_);
lean_dec_ref(v_as_6906_);
return v_res_6912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6913_, lean_object* v_ident_6914_){
_start:
{
lean_object* v___x_6915_; lean_object* v___x_6916_; lean_object* v___x_6917_; size_t v_sz_6918_; size_t v___x_6919_; lean_object* v___x_6920_; lean_object* v_fst_6921_; 
v___x_6915_ = l_Lean_Server_References_allRefsFor(v_self_6913_, v_ident_6914_);
v___x_6916_ = lean_box(0);
v___x_6917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6918_ = lean_array_size(v___x_6915_);
v___x_6919_ = ((size_t)0ULL);
v___x_6920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6915_, v_sz_6918_, v___x_6919_, v___x_6917_);
lean_dec_ref(v___x_6915_);
v_fst_6921_ = lean_ctor_get(v___x_6920_, 0);
lean_inc(v_fst_6921_);
lean_dec_ref(v___x_6920_);
if (lean_obj_tag(v_fst_6921_) == 0)
{
return v___x_6916_;
}
else
{
lean_object* v_val_6922_; 
v_val_6922_ = lean_ctor_get(v_fst_6921_, 0);
lean_inc(v_val_6922_);
lean_dec_ref(v_fst_6921_);
return v_val_6922_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6923_, lean_object* v_a_6924_, lean_object* v_fst_6925_, lean_object* v_init_6926_, lean_object* v_x_6927_){
_start:
{
lean_object* v_d_6930_; 
if (lean_obj_tag(v_x_6927_) == 0)
{
lean_object* v_k_6932_; lean_object* v_v_6933_; lean_object* v_l_6934_; lean_object* v_r_6935_; lean_object* v___y_6937_; lean_object* v___x_6941_; 
v_k_6932_ = lean_ctor_get(v_x_6927_, 1);
lean_inc(v_k_6932_);
v_v_6933_ = lean_ctor_get(v_x_6927_, 2);
lean_inc(v_v_6933_);
v_l_6934_ = lean_ctor_get(v_x_6927_, 3);
lean_inc(v_l_6934_);
v_r_6935_ = lean_ctor_get(v_x_6927_, 4);
lean_inc(v_r_6935_);
lean_dec_ref(v_x_6927_);
lean_inc_ref(v_fst_6925_);
lean_inc(v_a_6924_);
lean_inc_ref(v_filterMapIdent_6923_);
v___x_6941_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6923_, v_a_6924_, v_fst_6925_, v_init_6926_, v_l_6934_);
if (lean_obj_tag(v___x_6941_) == 0)
{
lean_object* v_a_6942_; 
lean_dec(v_r_6935_);
lean_dec(v_v_6933_);
lean_dec(v_k_6932_);
lean_dec_ref(v_fst_6925_);
lean_dec(v_a_6924_);
lean_dec_ref(v_filterMapIdent_6923_);
v_a_6942_ = lean_ctor_get(v___x_6941_, 0);
lean_inc(v_a_6942_);
lean_dec_ref(v___x_6941_);
v_d_6930_ = v_a_6942_;
goto v___jp_6929_;
}
else
{
if (lean_obj_tag(v_k_6932_) == 0)
{
lean_object* v_definition_x3f_6943_; 
v_definition_x3f_6943_ = lean_ctor_get(v_v_6933_, 0);
lean_inc(v_definition_x3f_6943_);
lean_dec(v_v_6933_);
if (lean_obj_tag(v_definition_x3f_6943_) == 1)
{
lean_object* v_a_6944_; lean_object* v_identName_6945_; lean_object* v_val_6946_; lean_object* v___x_6947_; lean_object* v___x_6948_; 
v_a_6944_ = lean_ctor_get(v___x_6941_, 0);
lean_inc(v_a_6944_);
v_identName_6945_ = lean_ctor_get(v_k_6932_, 1);
lean_inc_ref(v_identName_6945_);
lean_dec_ref(v_k_6932_);
v_val_6946_ = lean_ctor_get(v_definition_x3f_6943_, 0);
lean_inc(v_val_6946_);
lean_dec_ref(v_definition_x3f_6943_);
v___x_6947_ = l_String_toName(v_identName_6945_);
lean_inc_ref(v_filterMapIdent_6923_);
v___x_6948_ = lean_apply_1(v_filterMapIdent_6923_, v___x_6947_);
if (lean_obj_tag(v___x_6948_) == 1)
{
lean_object* v_val_6949_; lean_object* v___x_6950_; lean_object* v___x_6951_; lean_object* v___x_6952_; 
lean_dec_ref(v___x_6941_);
v_val_6949_ = lean_ctor_get(v___x_6948_, 0);
lean_inc(v_val_6949_);
lean_dec_ref(v___x_6948_);
v___x_6950_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6946_);
lean_dec(v_val_6946_);
lean_inc_ref(v_fst_6925_);
lean_inc(v_a_6924_);
v___x_6951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6951_, 0, v_a_6924_);
lean_ctor_set(v___x_6951_, 1, v_fst_6925_);
lean_ctor_set(v___x_6951_, 2, v_val_6949_);
lean_ctor_set(v___x_6951_, 3, v___x_6950_);
v___x_6952_ = lean_array_push(v_a_6944_, v___x_6951_);
v_init_6926_ = v___x_6952_;
v_x_6927_ = v_r_6935_;
goto _start;
}
else
{
lean_dec(v___x_6948_);
lean_dec(v_val_6946_);
lean_dec(v_a_6944_);
v___y_6937_ = v___x_6941_;
goto v___jp_6936_;
}
}
else
{
lean_dec(v_definition_x3f_6943_);
lean_dec_ref(v_k_6932_);
v___y_6937_ = v___x_6941_;
goto v___jp_6936_;
}
}
else
{
lean_dec(v_v_6933_);
lean_dec(v_k_6932_);
v___y_6937_ = v___x_6941_;
goto v___jp_6936_;
}
}
v___jp_6936_:
{
if (lean_obj_tag(v___y_6937_) == 0)
{
lean_object* v_a_6938_; 
lean_dec(v_r_6935_);
lean_dec_ref(v_fst_6925_);
lean_dec(v_a_6924_);
lean_dec_ref(v_filterMapIdent_6923_);
v_a_6938_ = lean_ctor_get(v___y_6937_, 0);
lean_inc(v_a_6938_);
lean_dec_ref(v___y_6937_);
v_d_6930_ = v_a_6938_;
goto v___jp_6929_;
}
else
{
lean_object* v_a_6939_; 
v_a_6939_ = lean_ctor_get(v___y_6937_, 0);
lean_inc(v_a_6939_);
lean_dec_ref(v___y_6937_);
v_init_6926_ = v_a_6939_;
v_x_6927_ = v_r_6935_;
goto _start;
}
}
}
else
{
lean_object* v___x_6954_; 
lean_dec_ref(v_fst_6925_);
lean_dec(v_a_6924_);
lean_dec_ref(v_filterMapIdent_6923_);
v___x_6954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6954_, 0, v_init_6926_);
return v___x_6954_;
}
v___jp_6929_:
{
lean_object* v___x_6931_; 
v___x_6931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6931_, 0, v_d_6930_);
return v___x_6931_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6955_, lean_object* v_a_6956_, lean_object* v_fst_6957_, lean_object* v_init_6958_, lean_object* v_x_6959_, lean_object* v___y_6960_){
_start:
{
lean_object* v_res_6961_; 
v_res_6961_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6955_, v_a_6956_, v_fst_6957_, v_init_6958_, v_x_6959_);
return v_res_6961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6962_, lean_object* v_cancelTk_x3f_6963_, lean_object* v_init_6964_, lean_object* v_x_6965_){
_start:
{
lean_object* v_d_6968_; 
if (lean_obj_tag(v_x_6965_) == 0)
{
lean_object* v_k_6970_; lean_object* v_v_6971_; lean_object* v_l_6972_; lean_object* v_r_6973_; lean_object* v___x_6974_; 
v_k_6970_ = lean_ctor_get(v_x_6965_, 1);
lean_inc(v_k_6970_);
v_v_6971_ = lean_ctor_get(v_x_6965_, 2);
lean_inc(v_v_6971_);
v_l_6972_ = lean_ctor_get(v_x_6965_, 3);
lean_inc(v_l_6972_);
v_r_6973_ = lean_ctor_get(v_x_6965_, 4);
lean_inc(v_r_6973_);
lean_dec_ref(v_x_6965_);
lean_inc(v_cancelTk_x3f_6963_);
lean_inc_ref(v_filterMapIdent_6962_);
v___x_6974_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6962_, v_cancelTk_x3f_6963_, v_init_6964_, v_l_6972_);
if (lean_obj_tag(v___x_6974_) == 0)
{
lean_object* v_a_6975_; 
lean_dec(v_r_6973_);
lean_dec(v_v_6971_);
lean_dec(v_k_6970_);
lean_dec(v_cancelTk_x3f_6963_);
lean_dec_ref(v_filterMapIdent_6962_);
v_a_6975_ = lean_ctor_get(v___x_6974_, 0);
lean_inc(v_a_6975_);
lean_dec_ref(v___x_6974_);
v_d_6968_ = v_a_6975_;
goto v___jp_6967_;
}
else
{
lean_object* v_snd_6976_; lean_object* v_a_6977_; lean_object* v_fst_6978_; lean_object* v_fst_6979_; lean_object* v___x_6981_; uint8_t v_isShared_6982_; uint8_t v_isSharedCheck_7012_; 
v_snd_6976_ = lean_ctor_get(v_v_6971_, 1);
lean_inc(v_snd_6976_);
v_a_6977_ = lean_ctor_get(v___x_6974_, 0);
lean_inc(v_a_6977_);
lean_dec_ref(v___x_6974_);
v_fst_6978_ = lean_ctor_get(v_v_6971_, 0);
lean_inc(v_fst_6978_);
lean_dec(v_v_6971_);
v_fst_6979_ = lean_ctor_get(v_snd_6976_, 0);
v_isSharedCheck_7012_ = !lean_is_exclusive(v_snd_6976_);
if (v_isSharedCheck_7012_ == 0)
{
lean_object* v_unused_7013_; 
v_unused_7013_ = lean_ctor_get(v_snd_6976_, 1);
lean_dec(v_unused_7013_);
v___x_6981_ = v_snd_6976_;
v_isShared_6982_ = v_isSharedCheck_7012_;
goto v_resetjp_6980_;
}
else
{
lean_inc(v_fst_6979_);
lean_dec(v_snd_6976_);
v___x_6981_ = lean_box(0);
v_isShared_6982_ = v_isSharedCheck_7012_;
goto v_resetjp_6980_;
}
v_resetjp_6980_:
{
lean_object* v_snd_6983_; lean_object* v___x_6985_; uint8_t v_isShared_6986_; uint8_t v_isSharedCheck_7010_; 
v_snd_6983_ = lean_ctor_get(v_a_6977_, 1);
v_isSharedCheck_7010_ = !lean_is_exclusive(v_a_6977_);
if (v_isSharedCheck_7010_ == 0)
{
lean_object* v_unused_7011_; 
v_unused_7011_ = lean_ctor_get(v_a_6977_, 0);
lean_dec(v_unused_7011_);
v___x_6985_ = v_a_6977_;
v_isShared_6986_ = v_isSharedCheck_7010_;
goto v_resetjp_6984_;
}
else
{
lean_inc(v_snd_6983_);
lean_dec(v_a_6977_);
v___x_6985_ = lean_box(0);
v_isShared_6986_ = v_isSharedCheck_7010_;
goto v_resetjp_6984_;
}
v_resetjp_6984_:
{
lean_object* v___x_6987_; lean_object* v_val_6989_; 
v___x_6987_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_6963_) == 1)
{
lean_object* v_val_6997_; uint8_t v___x_6998_; 
v_val_6997_ = lean_ctor_get(v_cancelTk_x3f_6963_, 0);
v___x_6998_ = l_IO_CancelToken_isSet(v_val_6997_);
if (v___x_6998_ == 0)
{
lean_del_object(v___x_6981_);
goto v___jp_6994_;
}
else
{
lean_object* v___x_7000_; uint8_t v_isShared_7001_; uint8_t v_isSharedCheck_7008_; 
lean_del_object(v___x_6985_);
lean_dec(v_fst_6979_);
lean_dec(v_fst_6978_);
lean_dec(v_r_6973_);
lean_dec(v_k_6970_);
lean_dec_ref(v_filterMapIdent_6962_);
v_isSharedCheck_7008_ = !lean_is_exclusive(v_cancelTk_x3f_6963_);
if (v_isSharedCheck_7008_ == 0)
{
lean_object* v_unused_7009_; 
v_unused_7009_ = lean_ctor_get(v_cancelTk_x3f_6963_, 0);
lean_dec(v_unused_7009_);
v___x_7000_ = v_cancelTk_x3f_6963_;
v_isShared_7001_ = v_isSharedCheck_7008_;
goto v_resetjp_6999_;
}
else
{
lean_dec(v_cancelTk_x3f_6963_);
v___x_7000_ = lean_box(0);
v_isShared_7001_ = v_isSharedCheck_7008_;
goto v_resetjp_6999_;
}
v_resetjp_6999_:
{
lean_object* v___x_7003_; 
lean_inc(v_snd_6983_);
if (v_isShared_7001_ == 0)
{
lean_ctor_set(v___x_7000_, 0, v_snd_6983_);
v___x_7003_ = v___x_7000_;
goto v_reusejp_7002_;
}
else
{
lean_object* v_reuseFailAlloc_7007_; 
v_reuseFailAlloc_7007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7007_, 0, v_snd_6983_);
v___x_7003_ = v_reuseFailAlloc_7007_;
goto v_reusejp_7002_;
}
v_reusejp_7002_:
{
lean_object* v___x_7005_; 
if (v_isShared_6982_ == 0)
{
lean_ctor_set(v___x_6981_, 1, v_snd_6983_);
lean_ctor_set(v___x_6981_, 0, v___x_7003_);
v___x_7005_ = v___x_6981_;
goto v_reusejp_7004_;
}
else
{
lean_object* v_reuseFailAlloc_7006_; 
v_reuseFailAlloc_7006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7006_, 0, v___x_7003_);
lean_ctor_set(v_reuseFailAlloc_7006_, 1, v_snd_6983_);
v___x_7005_ = v_reuseFailAlloc_7006_;
goto v_reusejp_7004_;
}
v_reusejp_7004_:
{
v_d_6968_ = v___x_7005_;
goto v___jp_6967_;
}
}
}
}
}
else
{
lean_del_object(v___x_6981_);
goto v___jp_6994_;
}
v___jp_6988_:
{
lean_object* v___x_6991_; 
if (v_isShared_6986_ == 0)
{
lean_ctor_set(v___x_6985_, 1, v_val_6989_);
lean_ctor_set(v___x_6985_, 0, v___x_6987_);
v___x_6991_ = v___x_6985_;
goto v_reusejp_6990_;
}
else
{
lean_object* v_reuseFailAlloc_6993_; 
v_reuseFailAlloc_6993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6993_, 0, v___x_6987_);
lean_ctor_set(v_reuseFailAlloc_6993_, 1, v_val_6989_);
v___x_6991_ = v_reuseFailAlloc_6993_;
goto v_reusejp_6990_;
}
v_reusejp_6990_:
{
v_init_6964_ = v___x_6991_;
v_x_6965_ = v_r_6973_;
goto _start;
}
}
v___jp_6994_:
{
lean_object* v___x_6995_; lean_object* v_a_6996_; 
lean_inc_ref(v_filterMapIdent_6962_);
v___x_6995_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6962_, v_k_6970_, v_fst_6978_, v_snd_6983_, v_fst_6979_);
v_a_6996_ = lean_ctor_get(v___x_6995_, 0);
lean_inc(v_a_6996_);
lean_dec_ref(v___x_6995_);
v_val_6989_ = v_a_6996_;
goto v___jp_6988_;
}
}
}
}
}
else
{
lean_object* v___x_7014_; 
lean_dec(v_cancelTk_x3f_6963_);
lean_dec_ref(v_filterMapIdent_6962_);
v___x_7014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7014_, 0, v_init_6964_);
return v___x_7014_;
}
v___jp_6967_:
{
lean_object* v___x_6969_; 
v___x_6969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6969_, 0, v_d_6968_);
return v___x_6969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_7015_, lean_object* v_cancelTk_x3f_7016_, lean_object* v_init_7017_, lean_object* v_x_7018_, lean_object* v___y_7019_){
_start:
{
lean_object* v_res_7020_; 
v_res_7020_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7015_, v_cancelTk_x3f_7016_, v_init_7017_, v_x_7018_);
return v_res_7020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_7026_, lean_object* v_filterMapIdent_7027_, lean_object* v_cancelTk_x3f_7028_){
_start:
{
lean_object* v___x_7030_; lean_object* v___x_7031_; lean_object* v___x_7032_; lean_object* v_val_7034_; lean_object* v_a_7038_; 
v___x_7030_ = l_Lean_Server_References_allRefs(v_self_7026_);
v___x_7031_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_7032_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7027_, v_cancelTk_x3f_7028_, v___x_7031_, v___x_7030_);
v_a_7038_ = lean_ctor_get(v___x_7032_, 0);
lean_inc(v_a_7038_);
lean_dec_ref(v___x_7032_);
v_val_7034_ = v_a_7038_;
goto v___jp_7033_;
v___jp_7033_:
{
lean_object* v_fst_7035_; 
v_fst_7035_ = lean_ctor_get(v_val_7034_, 0);
if (lean_obj_tag(v_fst_7035_) == 0)
{
lean_object* v_snd_7036_; 
v_snd_7036_ = lean_ctor_get(v_val_7034_, 1);
lean_inc(v_snd_7036_);
lean_dec_ref(v_val_7034_);
return v_snd_7036_;
}
else
{
lean_object* v_val_7037_; 
lean_inc_ref(v_fst_7035_);
lean_dec_ref(v_val_7034_);
v_val_7037_ = lean_ctor_get(v_fst_7035_, 0);
lean_inc(v_val_7037_);
lean_dec_ref(v_fst_7035_);
return v_val_7037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_7039_, lean_object* v_filterMapIdent_7040_, lean_object* v_cancelTk_x3f_7041_, lean_object* v_a_7042_){
_start:
{
lean_object* v_res_7043_; 
v_res_7043_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7039_, v_filterMapIdent_7040_, v_cancelTk_x3f_7041_);
return v_res_7043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_7044_, lean_object* v_self_7045_, lean_object* v_filterMapIdent_7046_, lean_object* v_cancelTk_x3f_7047_){
_start:
{
lean_object* v___x_7049_; 
v___x_7049_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7045_, v_filterMapIdent_7046_, v_cancelTk_x3f_7047_);
return v___x_7049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_7050_, lean_object* v_self_7051_, lean_object* v_filterMapIdent_7052_, lean_object* v_cancelTk_x3f_7053_, lean_object* v_a_7054_){
_start:
{
lean_object* v_res_7055_; 
v_res_7055_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_7050_, v_self_7051_, v_filterMapIdent_7052_, v_cancelTk_x3f_7053_);
return v_res_7055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_7056_, lean_object* v_filterMapIdent_7057_, lean_object* v_a_7058_, lean_object* v_fst_7059_, lean_object* v_init_7060_, lean_object* v_x_7061_){
_start:
{
lean_object* v___x_7063_; 
v___x_7063_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_7057_, v_a_7058_, v_fst_7059_, v_init_7060_, v_x_7061_);
return v___x_7063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_7064_, lean_object* v_filterMapIdent_7065_, lean_object* v_a_7066_, lean_object* v_fst_7067_, lean_object* v_init_7068_, lean_object* v_x_7069_, lean_object* v___y_7070_){
_start:
{
lean_object* v_res_7071_; 
v_res_7071_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_7064_, v_filterMapIdent_7065_, v_a_7066_, v_fst_7067_, v_init_7068_, v_x_7069_);
return v_res_7071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_7072_, lean_object* v_filterMapIdent_7073_, lean_object* v_cancelTk_x3f_7074_, lean_object* v_init_7075_, lean_object* v_x_7076_){
_start:
{
lean_object* v___x_7078_; 
v___x_7078_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7073_, v_cancelTk_x3f_7074_, v_init_7075_, v_x_7076_);
return v___x_7078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7079_, lean_object* v_filterMapIdent_7080_, lean_object* v_cancelTk_x3f_7081_, lean_object* v_init_7082_, lean_object* v_x_7083_, lean_object* v___y_7084_){
_start:
{
lean_object* v_res_7085_; 
v_res_7085_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7079_, v_filterMapIdent_7080_, v_cancelTk_x3f_7081_, v_init_7082_, v_x_7083_);
return v_res_7085_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7086_){
_start:
{
lean_object* v___x_7087_; lean_object* v___x_7088_; 
v___x_7087_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7088_ = lean_panic_fn_borrowed(v___x_7087_, v_msg_7086_);
return v___x_7088_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7092_; lean_object* v___x_7093_; lean_object* v___x_7094_; lean_object* v___x_7095_; lean_object* v___x_7096_; lean_object* v___x_7097_; 
v___x_7092_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7093_ = lean_unsigned_to_nat(14u);
v___x_7094_ = lean_unsigned_to_nat(22u);
v___x_7095_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7096_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7097_ = l_mkPanicMessageWithDecl(v___x_7096_, v___x_7095_, v___x_7094_, v___x_7093_, v___x_7092_);
return v___x_7097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7098_, lean_object* v_init_7099_, lean_object* v_x_7100_){
_start:
{
if (lean_obj_tag(v_x_7100_) == 0)
{
lean_object* v_k_7101_; lean_object* v_v_7102_; lean_object* v_l_7103_; lean_object* v_r_7104_; lean_object* v___x_7105_; lean_object* v_a_7106_; lean_object* v_fst_7107_; lean_object* v_snd_7108_; lean_object* v___y_7110_; lean_object* v_index_7125_; lean_object* v___x_7126_; 
v_k_7101_ = lean_ctor_get(v_x_7100_, 1);
v_v_7102_ = lean_ctor_get(v_x_7100_, 2);
v_l_7103_ = lean_ctor_get(v_x_7100_, 3);
v_r_7104_ = lean_ctor_get(v_x_7100_, 4);
v___x_7105_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7098_, v_init_7099_, v_l_7103_);
v_a_7106_ = lean_ctor_get(v___x_7105_, 0);
lean_inc(v_a_7106_);
v_fst_7107_ = lean_ctor_get(v_v_7102_, 0);
v_snd_7108_ = lean_ctor_get(v_v_7102_, 1);
v_index_7125_ = lean_ctor_get(v_snd_7108_, 1);
v___x_7126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7125_, v_requestedMod_7098_);
if (lean_obj_tag(v___x_7126_) == 1)
{
lean_object* v_val_7127_; lean_object* v___x_7128_; 
lean_dec_ref(v___x_7105_);
v_val_7127_ = lean_ctor_get(v___x_7126_, 0);
lean_inc(v_val_7127_);
lean_dec_ref(v___x_7126_);
v___x_7128_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7127_);
lean_dec(v_val_7127_);
if (lean_obj_tag(v___x_7128_) == 0)
{
lean_object* v___x_7129_; lean_object* v___x_7130_; 
v___x_7129_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7130_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7129_);
v___y_7110_ = v___x_7130_;
goto v___jp_7109_;
}
else
{
lean_object* v_val_7131_; 
v_val_7131_ = lean_ctor_get(v___x_7128_, 0);
lean_inc(v_val_7131_);
lean_dec_ref(v___x_7128_);
v___y_7110_ = v_val_7131_;
goto v___jp_7109_;
}
}
else
{
lean_object* v_a_7132_; 
lean_dec(v___x_7126_);
lean_dec(v_a_7106_);
v_a_7132_ = lean_ctor_get(v___x_7105_, 0);
lean_inc(v_a_7132_);
lean_dec_ref(v___x_7105_);
v_init_7099_ = v_a_7132_;
v_x_7100_ = v_r_7104_;
goto _start;
}
v___jp_7109_:
{
uint8_t v_isAll_7111_; uint8_t v_isPrivate_7112_; uint8_t v_metaKind_7113_; lean_object* v___x_7115_; uint8_t v_isShared_7116_; uint8_t v_isSharedCheck_7122_; 
v_isAll_7111_ = lean_ctor_get_uint8(v___y_7110_, sizeof(void*)*2);
v_isPrivate_7112_ = lean_ctor_get_uint8(v___y_7110_, sizeof(void*)*2 + 1);
v_metaKind_7113_ = lean_ctor_get_uint8(v___y_7110_, sizeof(void*)*2 + 2);
v_isSharedCheck_7122_ = !lean_is_exclusive(v___y_7110_);
if (v_isSharedCheck_7122_ == 0)
{
lean_object* v_unused_7123_; lean_object* v_unused_7124_; 
v_unused_7123_ = lean_ctor_get(v___y_7110_, 1);
lean_dec(v_unused_7123_);
v_unused_7124_ = lean_ctor_get(v___y_7110_, 0);
lean_dec(v_unused_7124_);
v___x_7115_ = v___y_7110_;
v_isShared_7116_ = v_isSharedCheck_7122_;
goto v_resetjp_7114_;
}
else
{
lean_dec(v___y_7110_);
v___x_7115_ = lean_box(0);
v_isShared_7116_ = v_isSharedCheck_7122_;
goto v_resetjp_7114_;
}
v_resetjp_7114_:
{
lean_object* v___x_7118_; 
lean_inc(v_fst_7107_);
lean_inc(v_k_7101_);
if (v_isShared_7116_ == 0)
{
lean_ctor_set(v___x_7115_, 1, v_fst_7107_);
lean_ctor_set(v___x_7115_, 0, v_k_7101_);
v___x_7118_ = v___x_7115_;
goto v_reusejp_7117_;
}
else
{
lean_object* v_reuseFailAlloc_7121_; 
v_reuseFailAlloc_7121_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7121_, 0, v_k_7101_);
lean_ctor_set(v_reuseFailAlloc_7121_, 1, v_fst_7107_);
lean_ctor_set_uint8(v_reuseFailAlloc_7121_, sizeof(void*)*2, v_isAll_7111_);
lean_ctor_set_uint8(v_reuseFailAlloc_7121_, sizeof(void*)*2 + 1, v_isPrivate_7112_);
lean_ctor_set_uint8(v_reuseFailAlloc_7121_, sizeof(void*)*2 + 2, v_metaKind_7113_);
v___x_7118_ = v_reuseFailAlloc_7121_;
goto v_reusejp_7117_;
}
v_reusejp_7117_:
{
lean_object* v___x_7119_; 
v___x_7119_ = lean_array_push(v_a_7106_, v___x_7118_);
v_init_7099_ = v___x_7119_;
v_x_7100_ = v_r_7104_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7134_; 
v___x_7134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7134_, 0, v_init_7099_);
return v___x_7134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object* v_requestedMod_7135_, lean_object* v_init_7136_, lean_object* v_x_7137_){
_start:
{
lean_object* v_res_7138_; 
v_res_7138_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7135_, v_init_7136_, v_x_7137_);
lean_dec(v_x_7137_);
lean_dec(v_requestedMod_7135_);
return v_res_7138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object* v_self_7139_, lean_object* v_requestedMod_7140_){
_start:
{
lean_object* v_result_7141_; lean_object* v___x_7142_; lean_object* v___x_7143_; lean_object* v_a_7144_; 
v_result_7141_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_7142_ = l_Lean_Server_References_allDirectImports(v_self_7139_);
v___x_7143_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7140_, v_result_7141_, v___x_7142_);
lean_dec(v___x_7142_);
v_a_7144_ = lean_ctor_get(v___x_7143_, 0);
lean_inc(v_a_7144_);
lean_dec_ref(v___x_7143_);
return v_a_7144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object* v_self_7145_, lean_object* v_requestedMod_7146_){
_start:
{
lean_object* v_res_7147_; 
v_res_7147_ = l_Lean_Server_References_importedBy(v_self_7145_, v_requestedMod_7146_);
lean_dec(v_requestedMod_7146_);
return v_res_7147_;
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

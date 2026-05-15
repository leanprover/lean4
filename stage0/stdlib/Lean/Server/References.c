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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(lean_object* v_idMap_2790_, lean_object* v_a_2791_){
_start:
{
uint8_t v___x_2792_; 
v___x_2792_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_idMap_2790_, v_a_2791_);
if (v___x_2792_ == 0)
{
return v_a_2791_;
}
else
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_idMap_2790_, v_a_2791_);
lean_dec_ref(v_a_2791_);
v_a_2791_ = v___x_2793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg___boxed(lean_object* v_idMap_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2795_, v_a_2796_);
lean_dec_ref(v_idMap_2795_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object* v_idMap_2798_, lean_object* v_id_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2798_, v_id_2799_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object* v_idMap_2823_, lean_object* v_inst_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2823_, v_a_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object* v_idMap_2827_, lean_object* v_inst_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2827_, v_inst_2828_, v_a_2829_);
lean_dec_ref(v_idMap_2827_);
return v_res_2830_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(lean_object* v_00_u03b2_2831_, lean_object* v_a_2832_, lean_object* v_x_2833_){
_start:
{
uint8_t v___x_2834_; 
v___x_2834_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2832_, v_x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2835_, lean_object* v_a_2836_, lean_object* v_x_2837_){
_start:
{
uint8_t v_res_2838_; lean_object* v_r_2839_; 
v_res_2838_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(v_00_u03b2_2835_, v_a_2836_, v_x_2837_);
lean_dec(v_x_2837_);
lean_dec_ref(v_a_2836_);
v_r_2839_ = lean_box(v_res_2838_);
return v_r_2839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(lean_object* v_00_u03b2_2840_, lean_object* v_a_2841_, lean_object* v_x_2842_, lean_object* v_x_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2841_, v_x_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2845_, lean_object* v_a_2846_, lean_object* v_x_2847_, lean_object* v_x_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(v_00_u03b2_2845_, v_a_2846_, v_x_2847_, v_x_2848_);
lean_dec(v_x_2847_);
lean_dec_ref(v_a_2846_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
if (lean_obj_tag(v_a_2850_) == 0)
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_a_2851_);
return v___x_2852_;
}
else
{
if (lean_obj_tag(v_a_2851_) == 0)
{
lean_object* v_tail_2853_; 
v_tail_2853_ = lean_ctor_get(v_a_2850_, 2);
lean_inc(v_tail_2853_);
lean_dec_ref(v_a_2850_);
v_a_2850_ = v_tail_2853_;
goto _start;
}
else
{
lean_object* v_key_2855_; 
v_key_2855_ = lean_ctor_get(v_a_2850_, 0);
if (lean_obj_tag(v_key_2855_) == 0)
{
lean_object* v_tail_2856_; 
lean_inc_ref(v_key_2855_);
lean_dec_ref(v_a_2851_);
v_tail_2856_ = lean_ctor_get(v_a_2850_, 2);
lean_inc(v_tail_2856_);
lean_dec_ref(v_a_2850_);
v_a_2850_ = v_tail_2856_;
v_a_2851_ = v_key_2855_;
goto _start;
}
else
{
lean_object* v_tail_2858_; 
v_tail_2858_ = lean_ctor_get(v_a_2850_, 2);
lean_inc(v_tail_2858_);
lean_dec_ref(v_a_2850_);
v_a_2850_ = v_tail_2858_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(lean_object* v_as_2860_, size_t v_sz_2861_, size_t v_i_2862_, lean_object* v_b_2863_){
_start:
{
uint8_t v___x_2864_; 
v___x_2864_ = lean_usize_dec_lt(v_i_2862_, v_sz_2861_);
if (v___x_2864_ == 0)
{
return v_b_2863_;
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2866_; 
v_a_2865_ = lean_array_uget_borrowed(v_as_2860_, v_i_2862_);
lean_inc(v_a_2865_);
v___x_2866_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(v_a_2865_, v_b_2863_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
return v_a_2867_;
}
else
{
lean_object* v_a_2868_; size_t v___x_2869_; size_t v___x_2870_; 
v_a_2868_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2868_);
lean_dec_ref(v___x_2866_);
v___x_2869_ = ((size_t)1ULL);
v___x_2870_ = lean_usize_add(v_i_2862_, v___x_2869_);
v_i_2862_ = v___x_2870_;
v_b_2863_ = v_a_2868_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5___boxed(lean_object* v_as_2872_, lean_object* v_sz_2873_, lean_object* v_i_2874_, lean_object* v_b_2875_){
_start:
{
size_t v_sz_boxed_2876_; size_t v_i_boxed_2877_; lean_object* v_res_2878_; 
v_sz_boxed_2876_ = lean_unbox_usize(v_sz_2873_);
lean_dec(v_sz_2873_);
v_i_boxed_2877_ = lean_unbox_usize(v_i_2874_);
lean_dec(v_i_2874_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_as_2872_, v_sz_boxed_2876_, v_i_boxed_2877_, v_b_2875_);
lean_dec_ref(v_as_2872_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(lean_object* v_a_2879_, lean_object* v_b_2880_, lean_object* v_x_2881_){
_start:
{
if (lean_obj_tag(v_x_2881_) == 0)
{
lean_dec(v_b_2880_);
lean_dec_ref(v_a_2879_);
return v_x_2881_;
}
else
{
lean_object* v_key_2882_; lean_object* v_value_2883_; lean_object* v_tail_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2896_; 
v_key_2882_ = lean_ctor_get(v_x_2881_, 0);
v_value_2883_ = lean_ctor_get(v_x_2881_, 1);
v_tail_2884_ = lean_ctor_get(v_x_2881_, 2);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_x_2881_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2886_ = v_x_2881_;
v_isShared_2887_ = v_isSharedCheck_2896_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_tail_2884_);
lean_inc(v_value_2883_);
lean_inc(v_key_2882_);
lean_dec(v_x_2881_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2896_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
uint8_t v___x_2888_; 
v___x_2888_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2882_, v_a_2879_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2879_, v_b_2880_, v_tail_2884_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 2, v___x_2889_);
v___x_2891_ = v___x_2886_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_key_2882_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_value_2883_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
else
{
lean_object* v___x_2894_; 
lean_dec(v_value_2883_);
lean_dec(v_key_2882_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 1, v_b_2880_);
lean_ctor_set(v___x_2886_, 0, v_a_2879_);
v___x_2894_ = v___x_2886_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2879_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_b_2880_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_tail_2884_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(lean_object* v_x_2897_, lean_object* v_x_2898_){
_start:
{
if (lean_obj_tag(v_x_2898_) == 0)
{
return v_x_2897_;
}
else
{
lean_object* v_key_2899_; lean_object* v_value_2900_; lean_object* v_tail_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2924_; 
v_key_2899_ = lean_ctor_get(v_x_2898_, 0);
v_value_2900_ = lean_ctor_get(v_x_2898_, 1);
v_tail_2901_ = lean_ctor_get(v_x_2898_, 2);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_x_2898_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2903_ = v_x_2898_;
v_isShared_2904_ = v_isSharedCheck_2924_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_tail_2901_);
lean_inc(v_value_2900_);
lean_inc(v_key_2899_);
lean_dec(v_x_2898_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2924_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; uint64_t v___x_2906_; uint64_t v___x_2907_; uint64_t v___x_2908_; uint64_t v_fold_2909_; uint64_t v___x_2910_; uint64_t v___x_2911_; uint64_t v___x_2912_; size_t v___x_2913_; size_t v___x_2914_; size_t v___x_2915_; size_t v___x_2916_; size_t v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2905_ = lean_array_get_size(v_x_2897_);
v___x_2906_ = l_Lean_Lsp_instHashableRefIdent_hash(v_key_2899_);
v___x_2907_ = 32ULL;
v___x_2908_ = lean_uint64_shift_right(v___x_2906_, v___x_2907_);
v_fold_2909_ = lean_uint64_xor(v___x_2906_, v___x_2908_);
v___x_2910_ = 16ULL;
v___x_2911_ = lean_uint64_shift_right(v_fold_2909_, v___x_2910_);
v___x_2912_ = lean_uint64_xor(v_fold_2909_, v___x_2911_);
v___x_2913_ = lean_uint64_to_usize(v___x_2912_);
v___x_2914_ = lean_usize_of_nat(v___x_2905_);
v___x_2915_ = ((size_t)1ULL);
v___x_2916_ = lean_usize_sub(v___x_2914_, v___x_2915_);
v___x_2917_ = lean_usize_land(v___x_2913_, v___x_2916_);
v___x_2918_ = lean_array_uget_borrowed(v_x_2897_, v___x_2917_);
lean_inc(v___x_2918_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 2, v___x_2918_);
v___x_2920_ = v___x_2903_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_key_2899_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_value_2900_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_array_uset(v_x_2897_, v___x_2917_, v___x_2920_);
v_x_2897_ = v___x_2921_;
v_x_2898_ = v_tail_2901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(lean_object* v_i_2925_, lean_object* v_source_2926_, lean_object* v_target_2927_){
_start:
{
lean_object* v___x_2928_; uint8_t v___x_2929_; 
v___x_2928_ = lean_array_get_size(v_source_2926_);
v___x_2929_ = lean_nat_dec_lt(v_i_2925_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_dec_ref(v_source_2926_);
lean_dec(v_i_2925_);
return v_target_2927_;
}
else
{
lean_object* v_es_2930_; lean_object* v___x_2931_; lean_object* v_source_2932_; lean_object* v_target_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_es_2930_ = lean_array_fget(v_source_2926_, v_i_2925_);
v___x_2931_ = lean_box(0);
v_source_2932_ = lean_array_fset(v_source_2926_, v_i_2925_, v___x_2931_);
v_target_2933_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_target_2927_, v_es_2930_);
v___x_2934_ = lean_unsigned_to_nat(1u);
v___x_2935_ = lean_nat_add(v_i_2925_, v___x_2934_);
lean_dec(v_i_2925_);
v_i_2925_ = v___x_2935_;
v_source_2926_ = v_source_2932_;
v_target_2927_ = v_target_2933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(lean_object* v_data_2937_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_nbuckets_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2938_ = lean_array_get_size(v_data_2937_);
v___x_2939_ = lean_unsigned_to_nat(2u);
v_nbuckets_2940_ = lean_nat_mul(v___x_2938_, v___x_2939_);
v___x_2941_ = lean_unsigned_to_nat(0u);
v___x_2942_ = lean_box(0);
v___x_2943_ = lean_mk_array(v_nbuckets_2940_, v___x_2942_);
v___x_2944_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2941_, v_data_2937_, v___x_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object* v_m_2945_, lean_object* v_a_2946_, lean_object* v_b_2947_){
_start:
{
lean_object* v_size_2948_; lean_object* v_buckets_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2992_; 
v_size_2948_ = lean_ctor_get(v_m_2945_, 0);
v_buckets_2949_ = lean_ctor_get(v_m_2945_, 1);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_m_2945_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2951_ = v_m_2945_;
v_isShared_2952_ = v_isSharedCheck_2992_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_buckets_2949_);
lean_inc(v_size_2948_);
lean_dec(v_m_2945_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2992_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; uint64_t v___x_2954_; uint64_t v___x_2955_; uint64_t v___x_2956_; uint64_t v_fold_2957_; uint64_t v___x_2958_; uint64_t v___x_2959_; uint64_t v___x_2960_; size_t v___x_2961_; size_t v___x_2962_; size_t v___x_2963_; size_t v___x_2964_; size_t v___x_2965_; lean_object* v_bkt_2966_; uint8_t v___x_2967_; 
v___x_2953_ = lean_array_get_size(v_buckets_2949_);
v___x_2954_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2946_);
v___x_2955_ = 32ULL;
v___x_2956_ = lean_uint64_shift_right(v___x_2954_, v___x_2955_);
v_fold_2957_ = lean_uint64_xor(v___x_2954_, v___x_2956_);
v___x_2958_ = 16ULL;
v___x_2959_ = lean_uint64_shift_right(v_fold_2957_, v___x_2958_);
v___x_2960_ = lean_uint64_xor(v_fold_2957_, v___x_2959_);
v___x_2961_ = lean_uint64_to_usize(v___x_2960_);
v___x_2962_ = lean_usize_of_nat(v___x_2953_);
v___x_2963_ = ((size_t)1ULL);
v___x_2964_ = lean_usize_sub(v___x_2962_, v___x_2963_);
v___x_2965_ = lean_usize_land(v___x_2961_, v___x_2964_);
v_bkt_2966_ = lean_array_uget_borrowed(v_buckets_2949_, v___x_2965_);
v___x_2967_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2946_, v_bkt_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v_size_x27_2969_; lean_object* v___x_2970_; lean_object* v_buckets_x27_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2968_ = lean_unsigned_to_nat(1u);
v_size_x27_2969_ = lean_nat_add(v_size_2948_, v___x_2968_);
lean_dec(v_size_2948_);
lean_inc(v_bkt_2966_);
v___x_2970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2970_, 0, v_a_2946_);
lean_ctor_set(v___x_2970_, 1, v_b_2947_);
lean_ctor_set(v___x_2970_, 2, v_bkt_2966_);
v_buckets_x27_2971_ = lean_array_uset(v_buckets_2949_, v___x_2965_, v___x_2970_);
v___x_2972_ = lean_unsigned_to_nat(4u);
v___x_2973_ = lean_nat_mul(v_size_x27_2969_, v___x_2972_);
v___x_2974_ = lean_unsigned_to_nat(3u);
v___x_2975_ = lean_nat_div(v___x_2973_, v___x_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_array_get_size(v_buckets_x27_2971_);
v___x_2977_ = lean_nat_dec_le(v___x_2975_, v___x_2976_);
lean_dec(v___x_2975_);
if (v___x_2977_ == 0)
{
lean_object* v_val_2978_; lean_object* v___x_2980_; 
v_val_2978_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_2971_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v_val_2978_);
lean_ctor_set(v___x_2951_, 0, v_size_x27_2969_);
v___x_2980_ = v___x_2951_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_size_x27_2969_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_val_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
else
{
lean_object* v___x_2983_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v_buckets_x27_2971_);
lean_ctor_set(v___x_2951_, 0, v_size_x27_2969_);
v___x_2983_ = v___x_2951_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_size_x27_2969_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_buckets_x27_2971_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
else
{
lean_object* v___x_2985_; lean_object* v_buckets_x27_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
lean_inc(v_bkt_2966_);
v___x_2985_ = lean_box(0);
v_buckets_x27_2986_ = lean_array_uset(v_buckets_2949_, v___x_2965_, v___x_2985_);
v___x_2987_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2946_, v_b_2947_, v_bkt_2966_);
v___x_2988_ = lean_array_uset(v_buckets_x27_2986_, v___x_2965_, v___x_2987_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_2988_);
v___x_2990_ = v___x_2951_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_size_2948_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object* v___x_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
if (lean_obj_tag(v_a_2994_) == 0)
{
lean_object* v___x_2996_; 
lean_dec_ref(v___x_2993_);
v___x_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2996_, 0, v_a_2995_);
return v___x_2996_;
}
else
{
lean_object* v_key_2997_; lean_object* v_tail_2998_; uint8_t v___x_2999_; 
v_key_2997_ = lean_ctor_get(v_a_2994_, 0);
lean_inc(v_key_2997_);
v_tail_2998_ = lean_ctor_get(v_a_2994_, 2);
lean_inc(v_tail_2998_);
lean_dec_ref(v_a_2994_);
v___x_2999_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2997_, v___x_2993_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
lean_inc_ref(v___x_2993_);
v___x_3000_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_2995_, v_key_2997_, v___x_2993_);
v_a_2994_ = v_tail_2998_;
v_a_2995_ = v___x_3000_;
goto _start;
}
else
{
lean_dec(v_key_2997_);
v_a_2994_ = v_tail_2998_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object* v___x_3003_, lean_object* v_as_3004_, size_t v_sz_3005_, size_t v_i_3006_, lean_object* v_b_3007_){
_start:
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_usize_dec_lt(v_i_3006_, v_sz_3005_);
if (v___x_3008_ == 0)
{
lean_dec_ref(v___x_3003_);
return v_b_3007_;
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3009_ = lean_array_uget_borrowed(v_as_3004_, v_i_3006_);
lean_inc(v_a_3009_);
lean_inc_ref(v___x_3003_);
v___x_3010_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(v___x_3003_, v_a_3009_, v_b_3007_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; 
lean_dec_ref(v___x_3003_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
return v_a_3011_;
}
else
{
lean_object* v_a_3012_; size_t v___x_3013_; size_t v___x_3014_; 
v_a_3012_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3012_);
lean_dec_ref(v___x_3010_);
v___x_3013_ = ((size_t)1ULL);
v___x_3014_ = lean_usize_add(v_i_3006_, v___x_3013_);
v_i_3006_ = v___x_3014_;
v_b_3007_ = v_a_3012_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object* v___x_3016_, lean_object* v_as_3017_, lean_object* v_sz_3018_, lean_object* v_i_3019_, lean_object* v_b_3020_){
_start:
{
size_t v_sz_boxed_3021_; size_t v_i_boxed_3022_; lean_object* v_res_3023_; 
v_sz_boxed_3021_ = lean_unbox_usize(v_sz_3018_);
lean_dec(v_sz_3018_);
v_i_boxed_3022_ = lean_unbox_usize(v_i_3019_);
lean_dec(v_i_3019_);
v_res_3023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3016_, v_as_3017_, v_sz_boxed_3021_, v_i_boxed_3022_, v_b_3020_);
lean_dec_ref(v_as_3017_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
if (lean_obj_tag(v_a_3024_) == 0)
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_a_3025_);
return v___x_3026_;
}
else
{
lean_object* v_value_3027_; lean_object* v_key_3028_; lean_object* v_tail_3029_; lean_object* v_buckets_3030_; size_t v_sz_3031_; size_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_value_3027_ = lean_ctor_get(v_a_3024_, 1);
lean_inc(v_value_3027_);
v_key_3028_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_key_3028_);
v_tail_3029_ = lean_ctor_get(v_a_3024_, 2);
lean_inc(v_tail_3029_);
lean_dec_ref(v_a_3024_);
v_buckets_3030_ = lean_ctor_get(v_value_3027_, 1);
lean_inc_ref(v_buckets_3030_);
lean_dec(v_value_3027_);
v_sz_3031_ = lean_array_size(v_buckets_3030_);
v___x_3032_ = ((size_t)0ULL);
v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_buckets_3030_, v_sz_3031_, v___x_3032_, v_key_3028_);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3033_, v_buckets_3030_, v_sz_3031_, v___x_3032_, v_a_3025_);
lean_dec_ref(v_buckets_3030_);
v_a_3024_ = v_tail_3029_;
v_a_3025_ = v___x_3034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object* v_as_3036_, size_t v_sz_3037_, size_t v_i_3038_, lean_object* v_b_3039_){
_start:
{
uint8_t v___x_3040_; 
v___x_3040_ = lean_usize_dec_lt(v_i_3038_, v_sz_3037_);
if (v___x_3040_ == 0)
{
return v_b_3039_;
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3042_; 
v_a_3041_ = lean_array_uget_borrowed(v_as_3036_, v_i_3038_);
lean_inc(v_a_3041_);
v___x_3042_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(v_a_3041_, v_b_3039_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
return v_a_3043_;
}
else
{
lean_object* v_a_3044_; size_t v___x_3045_; size_t v___x_3046_; 
v_a_3044_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3044_);
lean_dec_ref(v___x_3042_);
v___x_3045_ = ((size_t)1ULL);
v___x_3046_ = lean_usize_add(v_i_3038_, v___x_3045_);
v_i_3038_ = v___x_3046_;
v_b_3039_ = v_a_3044_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object* v_as_3048_, lean_object* v_sz_3049_, lean_object* v_i_3050_, lean_object* v_b_3051_){
_start:
{
size_t v_sz_boxed_3052_; size_t v_i_boxed_3053_; lean_object* v_res_3054_; 
v_sz_boxed_3052_ = lean_unbox_usize(v_sz_3049_);
lean_dec(v_sz_3049_);
v_i_boxed_3053_ = lean_unbox_usize(v_i_3050_);
lean_dec(v_i_3050_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_as_3048_, v_sz_boxed_3052_, v_i_boxed_3053_, v_b_3051_);
lean_dec_ref(v_as_3048_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object* v_a_3055_, lean_object* v_x_3056_){
_start:
{
if (lean_obj_tag(v_x_3056_) == 0)
{
return v_x_3056_;
}
else
{
lean_object* v_key_3057_; lean_object* v_value_3058_; lean_object* v_tail_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3068_; 
v_key_3057_ = lean_ctor_get(v_x_3056_, 0);
v_value_3058_ = lean_ctor_get(v_x_3056_, 1);
v_tail_3059_ = lean_ctor_get(v_x_3056_, 2);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_x_3056_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3061_ = v_x_3056_;
v_isShared_3062_ = v_isSharedCheck_3068_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_tail_3059_);
lean_inc(v_value_3058_);
lean_inc(v_key_3057_);
lean_dec(v_x_3056_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3068_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
uint8_t v___x_3063_; 
v___x_3063_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3057_, v_a_3055_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3066_; 
v___x_3064_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3055_, v_tail_3059_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 2, v___x_3064_);
v___x_3066_ = v___x_3061_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_key_3057_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_value_3058_);
lean_ctor_set(v_reuseFailAlloc_3067_, 2, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
else
{
lean_del_object(v___x_3061_);
lean_dec(v_value_3058_);
lean_dec(v_key_3057_);
return v_tail_3059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object* v_a_3069_, lean_object* v_x_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3069_, v_x_3070_);
lean_dec_ref(v_a_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object* v_m_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_size_3074_; lean_object* v_buckets_3075_; lean_object* v___x_3076_; uint64_t v___x_3077_; uint64_t v___x_3078_; uint64_t v___x_3079_; uint64_t v_fold_3080_; uint64_t v___x_3081_; uint64_t v___x_3082_; uint64_t v___x_3083_; size_t v___x_3084_; size_t v___x_3085_; size_t v___x_3086_; size_t v___x_3087_; size_t v___x_3088_; lean_object* v_bkt_3089_; uint8_t v___x_3090_; 
v_size_3074_ = lean_ctor_get(v_m_3072_, 0);
v_buckets_3075_ = lean_ctor_get(v_m_3072_, 1);
v___x_3076_ = lean_array_get_size(v_buckets_3075_);
v___x_3077_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3073_);
v___x_3078_ = 32ULL;
v___x_3079_ = lean_uint64_shift_right(v___x_3077_, v___x_3078_);
v_fold_3080_ = lean_uint64_xor(v___x_3077_, v___x_3079_);
v___x_3081_ = 16ULL;
v___x_3082_ = lean_uint64_shift_right(v_fold_3080_, v___x_3081_);
v___x_3083_ = lean_uint64_xor(v_fold_3080_, v___x_3082_);
v___x_3084_ = lean_uint64_to_usize(v___x_3083_);
v___x_3085_ = lean_usize_of_nat(v___x_3076_);
v___x_3086_ = ((size_t)1ULL);
v___x_3087_ = lean_usize_sub(v___x_3085_, v___x_3086_);
v___x_3088_ = lean_usize_land(v___x_3084_, v___x_3087_);
v_bkt_3089_ = lean_array_uget_borrowed(v_buckets_3075_, v___x_3088_);
v___x_3090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3073_, v_bkt_3089_);
if (v___x_3090_ == 0)
{
return v_m_3072_;
}
else
{
lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3103_; 
lean_inc(v_bkt_3089_);
lean_inc_ref(v_buckets_3075_);
lean_inc(v_size_3074_);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_m_3072_);
if (v_isSharedCheck_3103_ == 0)
{
lean_object* v_unused_3104_; lean_object* v_unused_3105_; 
v_unused_3104_ = lean_ctor_get(v_m_3072_, 1);
lean_dec(v_unused_3104_);
v_unused_3105_ = lean_ctor_get(v_m_3072_, 0);
lean_dec(v_unused_3105_);
v___x_3092_ = v_m_3072_;
v_isShared_3093_ = v_isSharedCheck_3103_;
goto v_resetjp_3091_;
}
else
{
lean_dec(v_m_3072_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3103_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v_buckets_x27_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3094_ = lean_box(0);
v_buckets_x27_3095_ = lean_array_uset(v_buckets_3075_, v___x_3088_, v___x_3094_);
v___x_3096_ = lean_unsigned_to_nat(1u);
v___x_3097_ = lean_nat_sub(v_size_3074_, v___x_3096_);
lean_dec(v_size_3074_);
v___x_3098_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3073_, v_bkt_3089_);
v___x_3099_ = lean_array_uset(v_buckets_x27_3095_, v___x_3088_, v___x_3098_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v___x_3099_);
lean_ctor_set(v___x_3092_, 0, v___x_3097_);
v___x_3101_ = v___x_3092_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object* v_m_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3106_, v_a_3107_);
lean_dec_ref(v_a_3107_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object* v_m_3109_, lean_object* v_a_3110_, lean_object* v_b_3111_){
_start:
{
lean_object* v_size_3112_; lean_object* v_buckets_3113_; lean_object* v___x_3114_; uint64_t v___x_3115_; uint64_t v___x_3116_; uint64_t v___x_3117_; uint64_t v_fold_3118_; uint64_t v___x_3119_; uint64_t v___x_3120_; uint64_t v___x_3121_; size_t v___x_3122_; size_t v___x_3123_; size_t v___x_3124_; size_t v___x_3125_; size_t v___x_3126_; lean_object* v_bkt_3127_; uint8_t v___x_3128_; 
v_size_3112_ = lean_ctor_get(v_m_3109_, 0);
v_buckets_3113_ = lean_ctor_get(v_m_3109_, 1);
v___x_3114_ = lean_array_get_size(v_buckets_3113_);
v___x_3115_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3110_);
v___x_3116_ = 32ULL;
v___x_3117_ = lean_uint64_shift_right(v___x_3115_, v___x_3116_);
v_fold_3118_ = lean_uint64_xor(v___x_3115_, v___x_3117_);
v___x_3119_ = 16ULL;
v___x_3120_ = lean_uint64_shift_right(v_fold_3118_, v___x_3119_);
v___x_3121_ = lean_uint64_xor(v_fold_3118_, v___x_3120_);
v___x_3122_ = lean_uint64_to_usize(v___x_3121_);
v___x_3123_ = lean_usize_of_nat(v___x_3114_);
v___x_3124_ = ((size_t)1ULL);
v___x_3125_ = lean_usize_sub(v___x_3123_, v___x_3124_);
v___x_3126_ = lean_usize_land(v___x_3122_, v___x_3125_);
v_bkt_3127_ = lean_array_uget_borrowed(v_buckets_3113_, v___x_3126_);
v___x_3128_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3110_, v_bkt_3127_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3149_; 
lean_inc_ref(v_buckets_3113_);
lean_inc(v_size_3112_);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_m_3109_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; lean_object* v_unused_3151_; 
v_unused_3150_ = lean_ctor_get(v_m_3109_, 1);
lean_dec(v_unused_3150_);
v_unused_3151_ = lean_ctor_get(v_m_3109_, 0);
lean_dec(v_unused_3151_);
v___x_3130_ = v_m_3109_;
v_isShared_3131_ = v_isSharedCheck_3149_;
goto v_resetjp_3129_;
}
else
{
lean_dec(v_m_3109_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3149_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v_size_x27_3133_; lean_object* v___x_3134_; lean_object* v_buckets_x27_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3132_ = lean_unsigned_to_nat(1u);
v_size_x27_3133_ = lean_nat_add(v_size_3112_, v___x_3132_);
lean_dec(v_size_3112_);
lean_inc(v_bkt_3127_);
v___x_3134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3134_, 0, v_a_3110_);
lean_ctor_set(v___x_3134_, 1, v_b_3111_);
lean_ctor_set(v___x_3134_, 2, v_bkt_3127_);
v_buckets_x27_3135_ = lean_array_uset(v_buckets_3113_, v___x_3126_, v___x_3134_);
v___x_3136_ = lean_unsigned_to_nat(4u);
v___x_3137_ = lean_nat_mul(v_size_x27_3133_, v___x_3136_);
v___x_3138_ = lean_unsigned_to_nat(3u);
v___x_3139_ = lean_nat_div(v___x_3137_, v___x_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_array_get_size(v_buckets_x27_3135_);
v___x_3141_ = lean_nat_dec_le(v___x_3139_, v___x_3140_);
lean_dec(v___x_3139_);
if (v___x_3141_ == 0)
{
lean_object* v_val_3142_; lean_object* v___x_3144_; 
v_val_3142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3135_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 1, v_val_3142_);
lean_ctor_set(v___x_3130_, 0, v_size_x27_3133_);
v___x_3144_ = v___x_3130_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_size_x27_3133_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_val_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
else
{
lean_object* v___x_3147_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 1, v_buckets_x27_3135_);
lean_ctor_set(v___x_3130_, 0, v_size_x27_3133_);
v___x_3147_ = v___x_3130_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_size_x27_3133_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_buckets_x27_3135_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_dec(v_b_3111_);
lean_dec_ref(v_a_3110_);
return v_m_3109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object* v_a_3152_, lean_object* v_fallback_3153_, lean_object* v_x_3154_){
_start:
{
if (lean_obj_tag(v_x_3154_) == 0)
{
lean_inc(v_fallback_3153_);
return v_fallback_3153_;
}
else
{
lean_object* v_key_3155_; lean_object* v_value_3156_; lean_object* v_tail_3157_; uint8_t v___x_3158_; 
v_key_3155_ = lean_ctor_get(v_x_3154_, 0);
v_value_3156_ = lean_ctor_get(v_x_3154_, 1);
v_tail_3157_ = lean_ctor_get(v_x_3154_, 2);
v___x_3158_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3155_, v_a_3152_);
if (v___x_3158_ == 0)
{
v_x_3154_ = v_tail_3157_;
goto _start;
}
else
{
lean_inc(v_value_3156_);
return v_value_3156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object* v_a_3160_, lean_object* v_fallback_3161_, lean_object* v_x_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3160_, v_fallback_3161_, v_x_3162_);
lean_dec(v_x_3162_);
lean_dec(v_fallback_3161_);
lean_dec_ref(v_a_3160_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object* v_m_3164_, lean_object* v_a_3165_, lean_object* v_fallback_3166_){
_start:
{
lean_object* v_buckets_3167_; lean_object* v___x_3168_; uint64_t v___x_3169_; uint64_t v___x_3170_; uint64_t v___x_3171_; uint64_t v_fold_3172_; uint64_t v___x_3173_; uint64_t v___x_3174_; uint64_t v___x_3175_; size_t v___x_3176_; size_t v___x_3177_; size_t v___x_3178_; size_t v___x_3179_; size_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_buckets_3167_ = lean_ctor_get(v_m_3164_, 1);
v___x_3168_ = lean_array_get_size(v_buckets_3167_);
v___x_3169_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3165_);
v___x_3170_ = 32ULL;
v___x_3171_ = lean_uint64_shift_right(v___x_3169_, v___x_3170_);
v_fold_3172_ = lean_uint64_xor(v___x_3169_, v___x_3171_);
v___x_3173_ = 16ULL;
v___x_3174_ = lean_uint64_shift_right(v_fold_3172_, v___x_3173_);
v___x_3175_ = lean_uint64_xor(v_fold_3172_, v___x_3174_);
v___x_3176_ = lean_uint64_to_usize(v___x_3175_);
v___x_3177_ = lean_usize_of_nat(v___x_3168_);
v___x_3178_ = ((size_t)1ULL);
v___x_3179_ = lean_usize_sub(v___x_3177_, v___x_3178_);
v___x_3180_ = lean_usize_land(v___x_3176_, v___x_3179_);
v___x_3181_ = lean_array_uget_borrowed(v_buckets_3167_, v___x_3180_);
v___x_3182_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3165_, v_fallback_3166_, v___x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object* v_m_3183_, lean_object* v_a_3184_, lean_object* v_fallback_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3183_, v_a_3184_, v_fallback_3185_);
lean_dec(v_fallback_3185_);
lean_dec_ref(v_a_3184_);
lean_dec_ref(v_m_3183_);
return v_res_3186_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = lean_box(0);
v___x_3188_ = lean_unsigned_to_nat(16u);
v___x_3189_ = lean_mk_array(v___x_3188_, v___x_3187_);
return v___x_3189_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0);
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v___x_3190_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object* v_idMap_3193_, lean_object* v_classesById_3194_, lean_object* v_id_3195_){
_start:
{
lean_object* v_representative_3196_; lean_object* v___x_3197_; lean_object* v_class_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v_class_3201_; lean_object* v___x_3202_; 
lean_inc_ref(v_id_3195_);
v_representative_3196_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_3193_, v_id_3195_);
v___x_3197_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_class_3198_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_classesById_3194_, v_representative_3196_, v___x_3197_);
v___x_3199_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_classesById_3194_, v_representative_3196_);
v___x_3200_ = lean_box(0);
v_class_3201_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_class_3198_, v_id_3195_, v___x_3200_);
v___x_3202_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v___x_3199_, v_representative_3196_, v_class_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object* v_idMap_3203_, lean_object* v_classesById_3204_, lean_object* v_id_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3203_, v_classesById_3204_, v_id_3205_);
lean_dec_ref(v_idMap_3203_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object* v_idMap_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
if (lean_obj_tag(v_a_3208_) == 0)
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_a_3209_);
return v___x_3210_;
}
else
{
lean_object* v_key_3211_; lean_object* v_value_3212_; lean_object* v_tail_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v_key_3211_ = lean_ctor_get(v_a_3208_, 0);
lean_inc(v_key_3211_);
v_value_3212_ = lean_ctor_get(v_a_3208_, 1);
lean_inc(v_value_3212_);
v_tail_3213_ = lean_ctor_get(v_a_3208_, 2);
lean_inc(v_tail_3213_);
lean_dec_ref(v_a_3208_);
v___x_3214_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3207_, v_a_3209_, v_key_3211_);
v___x_3215_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3207_, v___x_3214_, v_value_3212_);
v_a_3208_ = v_tail_3213_;
v_a_3209_ = v___x_3215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object* v_idMap_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3217_, v_a_3218_, v_a_3219_);
lean_dec_ref(v_idMap_3217_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object* v_idMap_3221_, lean_object* v_as_3222_, size_t v_sz_3223_, size_t v_i_3224_, lean_object* v_b_3225_){
_start:
{
uint8_t v___x_3226_; 
v___x_3226_ = lean_usize_dec_lt(v_i_3224_, v_sz_3223_);
if (v___x_3226_ == 0)
{
return v_b_3225_;
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3228_; 
v_a_3227_ = lean_array_uget_borrowed(v_as_3222_, v_i_3224_);
lean_inc(v_a_3227_);
v___x_3228_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3221_, v_a_3227_, v_b_3225_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref(v___x_3228_);
return v_a_3229_;
}
else
{
lean_object* v_a_3230_; size_t v___x_3231_; size_t v___x_3232_; 
v_a_3230_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3230_);
lean_dec_ref(v___x_3228_);
v___x_3231_ = ((size_t)1ULL);
v___x_3232_ = lean_usize_add(v_i_3224_, v___x_3231_);
v_i_3224_ = v___x_3232_;
v_b_3225_ = v_a_3230_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object* v_idMap_3234_, lean_object* v_as_3235_, lean_object* v_sz_3236_, lean_object* v_i_3237_, lean_object* v_b_3238_){
_start:
{
size_t v_sz_boxed_3239_; size_t v_i_boxed_3240_; lean_object* v_res_3241_; 
v_sz_boxed_3239_ = lean_unbox_usize(v_sz_3236_);
lean_dec(v_sz_3236_);
v_i_boxed_3240_ = lean_unbox_usize(v_i_3237_);
lean_dec(v_i_3237_);
v_res_3241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3234_, v_as_3235_, v_sz_boxed_3239_, v_i_boxed_3240_, v_b_3238_);
lean_dec_ref(v_as_3235_);
lean_dec_ref(v_idMap_3234_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object* v_idMap_3242_){
_start:
{
lean_object* v_buckets_3243_; lean_object* v_classesById_3244_; size_t v_sz_3245_; size_t v___x_3246_; lean_object* v___x_3247_; lean_object* v_buckets_3248_; size_t v_sz_3249_; lean_object* v___x_3250_; 
v_buckets_3243_ = lean_ctor_get(v_idMap_3242_, 1);
v_classesById_3244_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_sz_3245_ = lean_array_size(v_buckets_3243_);
v___x_3246_ = ((size_t)0ULL);
v___x_3247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3242_, v_buckets_3243_, v_sz_3245_, v___x_3246_, v_classesById_3244_);
v_buckets_3248_ = lean_ctor_get(v___x_3247_, 1);
lean_inc_ref(v_buckets_3248_);
lean_dec_ref(v___x_3247_);
v_sz_3249_ = lean_array_size(v_buckets_3248_);
v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_buckets_3248_, v_sz_3249_, v___x_3246_, v_classesById_3244_);
lean_dec_ref(v_buckets_3248_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object* v_idMap_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v_idMap_3251_);
lean_dec_ref(v_idMap_3251_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object* v_00_u03b2_3253_, lean_object* v_m_3254_, lean_object* v_a_3255_, lean_object* v_fallback_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3254_, v_a_3255_, v_fallback_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object* v_00_u03b2_3258_, lean_object* v_m_3259_, lean_object* v_a_3260_, lean_object* v_fallback_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(v_00_u03b2_3258_, v_m_3259_, v_a_3260_, v_fallback_3261_);
lean_dec(v_fallback_3261_);
lean_dec_ref(v_a_3260_);
lean_dec_ref(v_m_3259_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object* v_00_u03b2_3263_, lean_object* v_m_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3264_, v_a_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object* v_00_u03b2_3267_, lean_object* v_m_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(v_00_u03b2_3267_, v_m_3268_, v_a_3269_);
lean_dec_ref(v_a_3269_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object* v_00_u03b2_3271_, lean_object* v_m_3272_, lean_object* v_a_3273_, lean_object* v_b_3274_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_m_3272_, v_a_3273_, v_b_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object* v_00_u03b2_3276_, lean_object* v_m_3277_, lean_object* v_a_3278_, lean_object* v_b_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_m_3277_, v_a_3278_, v_b_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object* v_00_u03b2_3281_, lean_object* v_a_3282_, lean_object* v_fallback_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3282_, v_fallback_3283_, v_x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3286_, lean_object* v_a_3287_, lean_object* v_fallback_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(v_00_u03b2_3286_, v_a_3287_, v_fallback_3288_, v_x_3289_);
lean_dec(v_x_3289_);
lean_dec(v_fallback_3288_);
lean_dec_ref(v_a_3287_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object* v_00_u03b2_3291_, lean_object* v_a_3292_, lean_object* v_x_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3292_, v_x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3295_, lean_object* v_a_3296_, lean_object* v_x_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(v_00_u03b2_3295_, v_a_3296_, v_x_3297_);
lean_dec_ref(v_a_3296_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object* v_00_u03b2_3299_, lean_object* v_data_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_data_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object* v_00_u03b2_3302_, lean_object* v_a_3303_, lean_object* v_b_3304_, lean_object* v_x_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_3303_, v_b_3304_, v_x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3307_, lean_object* v_i_3308_, lean_object* v_source_3309_, lean_object* v_target_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v_i_3308_, v_source_3309_, v_target_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object* v_00_u03b2_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_x_3313_, v_x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object* v_id_3316_, lean_object* v_baseId_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3319_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3318_, v_id_3316_);
v___x_3320_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3318_, v_baseId_3317_);
v___x_3321_ = l_Lean_Lsp_instBEqRefIdent_beq(v___x_3320_, v___x_3319_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = lean_box(0);
v___x_3323_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3318_, v___x_3319_, v___x_3320_);
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
return v___x_3324_;
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec_ref(v___x_3320_);
lean_dec_ref(v___x_3319_);
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
lean_ctor_set(v___x_3326_, 1, v_a_3318_);
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object* v_ci_3327_, lean_object* v_info_3328_, lean_object* v_x_3329_, lean_object* v___y_3330_){
_start:
{
if (lean_obj_tag(v_info_3328_) == 11)
{
lean_object* v_toCommandContextInfo_3331_; lean_object* v_i_3332_; lean_object* v_env_3333_; lean_object* v___x_3334_; lean_object* v_mainModule_3335_; lean_object* v_id_3336_; lean_object* v_baseId_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_toCommandContextInfo_3331_ = lean_ctor_get(v_ci_3327_, 0);
v_i_3332_ = lean_ctor_get(v_info_3328_, 0);
lean_inc_ref(v_i_3332_);
lean_dec_ref(v_info_3328_);
v_env_3333_ = lean_ctor_get(v_toCommandContextInfo_3331_, 0);
v___x_3334_ = l_Lean_Environment_header(v_env_3333_);
v_mainModule_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_mainModule_3335_);
lean_dec_ref(v___x_3334_);
v_id_3336_ = lean_ctor_get(v_i_3332_, 1);
lean_inc(v_id_3336_);
v_baseId_3337_ = lean_ctor_get(v_i_3332_, 2);
lean_inc(v_baseId_3337_);
lean_dec_ref(v_i_3332_);
v___x_3338_ = 1;
v___x_3339_ = l_Lean_Name_toString(v_mainModule_3335_, v___x_3338_);
v___x_3340_ = l_Lean_Name_toString(v_id_3336_, v___x_3338_);
lean_inc_ref(v___x_3339_);
v___x_3341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3339_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_Lean_Name_toString(v_baseId_3337_, v___x_3338_);
v___x_3343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3339_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v___x_3341_, v___x_3343_, v___y_3330_);
return v___x_3344_;
}
else
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_dec_ref(v_info_3328_);
v___x_3345_ = lean_box(0);
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
lean_ctor_set(v___x_3346_, 1, v___y_3330_);
return v___x_3346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object* v_ci_3347_, lean_object* v_info_3348_, lean_object* v_x_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(v_ci_3347_, v_info_3348_, v_x_3349_, v___y_3350_);
lean_dec_ref(v_x_3349_);
lean_dec_ref(v_ci_3347_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_, lean_object* v___y_3355_){
_start:
{
uint8_t v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = 1;
v___x_3357_ = lean_box(v___x_3356_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v___y_3355_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object* v_x_3359_, lean_object* v_x_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(v_x_3359_, v_x_3360_, v_x_3361_, v___y_3362_);
lean_dec_ref(v_x_3361_);
lean_dec_ref(v_x_3360_);
lean_dec_ref(v_x_3359_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3364_, lean_object* v_ci_3365_, lean_object* v_i_3366_, lean_object* v_cs_3367_, lean_object* v_x_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_apply_4(v_postNode_3364_, v_ci_3365_, v_i_3366_, v_cs_3367_, v___y_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3371_, lean_object* v_ci_3372_, lean_object* v_i_3373_, lean_object* v_cs_3374_, lean_object* v_x_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3371_, v_ci_3372_, v_i_3373_, v_cs_3374_, v_x_3375_, v___y_3376_);
lean_dec(v_x_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___f_3380_; lean_object* v___f_3381_; lean_object* v___f_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___f_3385_; lean_object* v___f_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___f_3390_; lean_object* v___f_3391_; lean_object* v___f_3392_; lean_object* v___f_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3784__overap_3402_; lean_object* v___x_3403_; 
v___f_3380_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3381_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3382_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3383_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3384_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3385_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3386_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___f_3380_);
lean_ctor_set(v___x_3387_, 1, v___f_3381_);
v___x_3388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___f_3382_);
lean_ctor_set(v___x_3388_, 2, v___f_3383_);
lean_ctor_set(v___x_3388_, 3, v___f_3384_);
lean_ctor_set(v___x_3388_, 4, v___f_3385_);
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v___f_3386_);
lean_inc_ref_n(v___x_3389_, 6);
v___f_3390_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3390_, 0, v___x_3389_);
v___f_3391_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3391_, 0, v___x_3389_);
v___f_3392_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3392_, 0, v___x_3389_);
v___f_3393_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3393_, 0, v___x_3389_);
v___x_3394_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3394_, 0, lean_box(0));
lean_closure_set(v___x_3394_, 1, lean_box(0));
lean_closure_set(v___x_3394_, 2, v___x_3389_);
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v___f_3390_);
v___x_3396_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3396_, 0, lean_box(0));
lean_closure_set(v___x_3396_, 1, lean_box(0));
lean_closure_set(v___x_3396_, 2, v___x_3389_);
v___x_3397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
lean_ctor_set(v___x_3397_, 2, v___f_3391_);
lean_ctor_set(v___x_3397_, 3, v___f_3392_);
lean_ctor_set(v___x_3397_, 4, v___f_3393_);
v___x_3398_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3398_, 0, lean_box(0));
lean_closure_set(v___x_3398_, 1, lean_box(0));
lean_closure_set(v___x_3398_, 2, v___x_3389_);
v___x_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = lean_box(0);
v___x_3401_ = l_instInhabitedOfMonad___redArg(v___x_3399_, v___x_3400_);
v___x_3784__overap_3402_ = lean_panic_fn_borrowed(v___x_3401_, v_msg_3378_);
lean_dec(v___x_3401_);
v___x_3403_ = lean_apply_1(v___x_3784__overap_3402_, v___y_3379_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3404_, lean_object* v_postNode_3405_, lean_object* v_x_3406_, lean_object* v_x_3407_, lean_object* v___y_3408_){
_start:
{
switch(lean_obj_tag(v_x_3407_))
{
case 0:
{
lean_object* v_i_3409_; lean_object* v_t_3410_; lean_object* v___x_3411_; 
v_i_3409_ = lean_ctor_get(v_x_3407_, 0);
lean_inc_ref(v_i_3409_);
v_t_3410_ = lean_ctor_get(v_x_3407_, 1);
lean_inc_ref(v_t_3410_);
lean_dec_ref(v_x_3407_);
v___x_3411_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3409_, v_x_3406_);
v_x_3406_ = v___x_3411_;
v_x_3407_ = v_t_3410_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3406_) == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec_ref(v_x_3407_);
lean_dec_ref(v_postNode_3405_);
lean_dec_ref(v_preNode_3404_);
v___x_3413_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3414_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3413_, v___y_3408_);
return v___x_3414_;
}
else
{
lean_object* v_i_3415_; lean_object* v_children_3416_; lean_object* v_val_3417_; lean_object* v___x_3418_; lean_object* v_fst_3419_; uint8_t v___x_3420_; 
v_i_3415_ = lean_ctor_get(v_x_3407_, 0);
lean_inc_ref_n(v_i_3415_, 2);
v_children_3416_ = lean_ctor_get(v_x_3407_, 1);
lean_inc_ref_n(v_children_3416_, 2);
lean_dec_ref(v_x_3407_);
v_val_3417_ = lean_ctor_get(v_x_3406_, 0);
lean_inc_n(v_val_3417_, 2);
lean_inc_ref(v_preNode_3404_);
v___x_3418_ = lean_apply_4(v_preNode_3404_, v_val_3417_, v_i_3415_, v_children_3416_, v___y_3408_);
v_fst_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_fst_3419_);
v___x_3420_ = lean_unbox(v_fst_3419_);
lean_dec(v_fst_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3439_; 
lean_dec_ref(v_preNode_3404_);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_x_3406_);
if (v_isSharedCheck_3439_ == 0)
{
lean_object* v_unused_3440_; 
v_unused_3440_ = lean_ctor_get(v_x_3406_, 0);
lean_dec(v_unused_3440_);
v___x_3422_ = v_x_3406_;
v_isShared_3423_ = v_isSharedCheck_3439_;
goto v_resetjp_3421_;
}
else
{
lean_dec(v_x_3406_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3439_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v_snd_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_fst_3427_; lean_object* v_snd_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3438_; 
v_snd_3424_ = lean_ctor_get(v___x_3418_, 1);
lean_inc(v_snd_3424_);
lean_dec_ref(v___x_3418_);
v___x_3425_ = lean_box(0);
v___x_3426_ = lean_apply_5(v_postNode_3405_, v_val_3417_, v_i_3415_, v_children_3416_, v___x_3425_, v_snd_3424_);
v_fst_3427_ = lean_ctor_get(v___x_3426_, 0);
v_snd_3428_ = lean_ctor_get(v___x_3426_, 1);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3430_ = v___x_3426_;
v_isShared_3431_ = v_isSharedCheck_3438_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_snd_3428_);
lean_inc(v_fst_3427_);
lean_dec(v___x_3426_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3438_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v_fst_3427_);
v___x_3433_ = v___x_3422_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_fst_3427_);
v___x_3433_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3435_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3433_);
v___x_3435_ = v___x_3430_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_snd_3428_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
else
{
lean_object* v_snd_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v_fst_3446_; lean_object* v_snd_3447_; lean_object* v___x_3448_; lean_object* v_fst_3449_; lean_object* v_snd_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3458_; 
v_snd_3441_ = lean_ctor_get(v___x_3418_, 1);
lean_inc(v_snd_3441_);
lean_dec_ref(v___x_3418_);
v___x_3442_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3406_, v_i_3415_);
v___x_3443_ = l_Lean_PersistentArray_toList___redArg(v_children_3416_);
v___x_3444_ = lean_box(0);
lean_inc_ref(v_postNode_3405_);
v___x_3445_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3404_, v_postNode_3405_, v___x_3442_, v___x_3443_, v___x_3444_, v_snd_3441_);
v_fst_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_fst_3446_);
v_snd_3447_ = lean_ctor_get(v___x_3445_, 1);
lean_inc(v_snd_3447_);
lean_dec_ref(v___x_3445_);
v___x_3448_ = lean_apply_5(v_postNode_3405_, v_val_3417_, v_i_3415_, v_children_3416_, v_fst_3446_, v_snd_3447_);
v_fst_3449_ = lean_ctor_get(v___x_3448_, 0);
v_snd_3450_ = lean_ctor_get(v___x_3448_, 1);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3452_ = v___x_3448_;
v_isShared_3453_ = v_isSharedCheck_3458_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_snd_3450_);
lean_inc(v_fst_3449_);
lean_dec(v___x_3448_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3458_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3454_, 0, v_fst_3449_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3454_);
v___x_3456_ = v___x_3452_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_snd_3450_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
default: 
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_dec_ref(v_x_3407_);
lean_dec(v_x_3406_);
lean_dec_ref(v_postNode_3405_);
lean_dec_ref(v_preNode_3404_);
v___x_3459_ = lean_box(0);
v___x_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
lean_ctor_set(v___x_3460_, 1, v___y_3408_);
return v___x_3460_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3461_, lean_object* v_postNode_3462_, lean_object* v___x_3463_, lean_object* v_x_3464_, lean_object* v_x_3465_, lean_object* v___y_3466_){
_start:
{
if (lean_obj_tag(v_x_3464_) == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
lean_dec(v___x_3463_);
lean_dec_ref(v_postNode_3462_);
lean_dec_ref(v_preNode_3461_);
v___x_3467_ = l_List_reverse___redArg(v_x_3465_);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
lean_ctor_set(v___x_3468_, 1, v___y_3466_);
return v___x_3468_;
}
else
{
lean_object* v_head_3469_; lean_object* v_tail_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3481_; 
v_head_3469_ = lean_ctor_get(v_x_3464_, 0);
v_tail_3470_ = lean_ctor_get(v_x_3464_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_x_3464_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3472_ = v_x_3464_;
v_isShared_3473_ = v_isSharedCheck_3481_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_tail_3470_);
lean_inc(v_head_3469_);
lean_dec(v_x_3464_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3481_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3474_; lean_object* v_fst_3475_; lean_object* v_snd_3476_; lean_object* v___x_3478_; 
lean_inc(v___x_3463_);
lean_inc_ref(v_postNode_3462_);
lean_inc_ref(v_preNode_3461_);
v___x_3474_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3461_, v_postNode_3462_, v___x_3463_, v_head_3469_, v___y_3466_);
v_fst_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_fst_3475_);
v_snd_3476_ = lean_ctor_get(v___x_3474_, 1);
lean_inc(v_snd_3476_);
lean_dec_ref(v___x_3474_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 1, v_x_3465_);
lean_ctor_set(v___x_3472_, 0, v_fst_3475_);
v___x_3478_ = v___x_3472_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_fst_3475_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_x_3465_);
v___x_3478_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
v_x_3464_ = v_tail_3470_;
v_x_3465_ = v___x_3478_;
v___y_3466_ = v_snd_3476_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3482_, lean_object* v_postNode_3483_, lean_object* v_ctx_x3f_3484_, lean_object* v_t_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v___f_3487_; lean_object* v___x_3488_; lean_object* v_snd_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3497_; 
v___f_3487_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3487_, 0, v_postNode_3483_);
v___x_3488_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3482_, v___f_3487_, v_ctx_x3f_3484_, v_t_3485_, v___y_3486_);
v_snd_3489_ = lean_ctor_get(v___x_3488_, 1);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; 
v_unused_3498_ = lean_ctor_get(v___x_3488_, 0);
lean_dec(v_unused_3498_);
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3497_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_snd_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3497_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
v___x_3493_ = lean_box(0);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3493_);
v___x_3495_ = v___x_3491_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_snd_3489_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(lean_object* v_as_3501_, size_t v_i_3502_, size_t v_stop_3503_, lean_object* v_b_3504_, lean_object* v___y_3505_){
_start:
{
uint8_t v___x_3506_; 
v___x_3506_ = lean_usize_dec_eq(v_i_3502_, v_stop_3503_);
if (v___x_3506_ == 0)
{
lean_object* v___f_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v_fst_3512_; lean_object* v_snd_3513_; size_t v___x_3514_; size_t v___x_3515_; 
v___f_3507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0));
v___f_3508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1));
v___x_3509_ = lean_array_uget_borrowed(v_as_3501_, v_i_3502_);
v___x_3510_ = lean_box(0);
lean_inc(v___x_3509_);
v___x_3511_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(v___f_3507_, v___f_3508_, v___x_3510_, v___x_3509_, v___y_3505_);
v_fst_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_fst_3512_);
v_snd_3513_ = lean_ctor_get(v___x_3511_, 1);
lean_inc(v_snd_3513_);
lean_dec_ref(v___x_3511_);
v___x_3514_ = ((size_t)1ULL);
v___x_3515_ = lean_usize_add(v_i_3502_, v___x_3514_);
v_i_3502_ = v___x_3515_;
v_b_3504_ = v_fst_3512_;
v___y_3505_ = v_snd_3513_;
goto _start;
}
else
{
lean_object* v___x_3517_; 
v___x_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3517_, 0, v_b_3504_);
lean_ctor_set(v___x_3517_, 1, v___y_3505_);
return v___x_3517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___boxed(lean_object* v_as_3518_, lean_object* v_i_3519_, lean_object* v_stop_3520_, lean_object* v_b_3521_, lean_object* v___y_3522_){
_start:
{
size_t v_i_boxed_3523_; size_t v_stop_boxed_3524_; lean_object* v_res_3525_; 
v_i_boxed_3523_ = lean_unbox_usize(v_i_3519_);
lean_dec(v_i_3519_);
v_stop_boxed_3524_ = lean_unbox_usize(v_stop_3520_);
lean_dec(v_stop_3520_);
v_res_3525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_as_3518_, v_i_boxed_3523_, v_stop_boxed_3524_, v_b_3521_, v___y_3522_);
lean_dec_ref(v_as_3518_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(lean_object* v_a_3526_, lean_object* v_x_3527_){
_start:
{
if (lean_obj_tag(v_x_3527_) == 0)
{
lean_object* v___x_3528_; 
v___x_3528_ = lean_box(0);
return v___x_3528_;
}
else
{
lean_object* v_key_3529_; lean_object* v_value_3530_; lean_object* v_tail_3531_; uint8_t v___x_3532_; 
v_key_3529_ = lean_ctor_get(v_x_3527_, 0);
v_value_3530_ = lean_ctor_get(v_x_3527_, 1);
v_tail_3531_ = lean_ctor_get(v_x_3527_, 2);
v___x_3532_ = l_Lean_Lsp_instBEqRange_beq(v_key_3529_, v_a_3526_);
if (v___x_3532_ == 0)
{
v_x_3527_ = v_tail_3531_;
goto _start;
}
else
{
lean_object* v___x_3534_; 
lean_inc(v_value_3530_);
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v_value_3530_);
return v___x_3534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_3535_, lean_object* v_x_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3535_, v_x_3536_);
lean_dec(v_x_3536_);
lean_dec_ref(v_a_3535_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(lean_object* v_m_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v_buckets_3540_; lean_object* v___x_3541_; uint64_t v___x_3542_; uint64_t v___x_3543_; uint64_t v___x_3544_; uint64_t v_fold_3545_; uint64_t v___x_3546_; uint64_t v___x_3547_; uint64_t v___x_3548_; size_t v___x_3549_; size_t v___x_3550_; size_t v___x_3551_; size_t v___x_3552_; size_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_buckets_3540_ = lean_ctor_get(v_m_3538_, 1);
v___x_3541_ = lean_array_get_size(v_buckets_3540_);
v___x_3542_ = l_Lean_Lsp_instHashableRange_hash(v_a_3539_);
v___x_3543_ = 32ULL;
v___x_3544_ = lean_uint64_shift_right(v___x_3542_, v___x_3543_);
v_fold_3545_ = lean_uint64_xor(v___x_3542_, v___x_3544_);
v___x_3546_ = 16ULL;
v___x_3547_ = lean_uint64_shift_right(v_fold_3545_, v___x_3546_);
v___x_3548_ = lean_uint64_xor(v_fold_3545_, v___x_3547_);
v___x_3549_ = lean_uint64_to_usize(v___x_3548_);
v___x_3550_ = lean_usize_of_nat(v___x_3541_);
v___x_3551_ = ((size_t)1ULL);
v___x_3552_ = lean_usize_sub(v___x_3550_, v___x_3551_);
v___x_3553_ = lean_usize_land(v___x_3549_, v___x_3552_);
v___x_3554_ = lean_array_uget_borrowed(v_buckets_3540_, v___x_3553_);
v___x_3555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3539_, v___x_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg___boxed(lean_object* v_m_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3556_, v_a_3557_);
lean_dec_ref(v_a_3557_);
lean_dec_ref(v_m_3556_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(lean_object* v_posMap_3559_, lean_object* v_as_3560_, size_t v_sz_3561_, size_t v_i_3562_, lean_object* v_b_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_a_3566_; lean_object* v_snd_3567_; uint8_t v___x_3571_; 
v___x_3571_ = lean_usize_dec_lt(v_i_3562_, v_sz_3561_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; 
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v_b_3563_);
lean_ctor_set(v___x_3572_, 1, v___y_3564_);
return v___x_3572_;
}
else
{
lean_object* v_a_3573_; lean_object* v_ident_3574_; lean_object* v_range_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v_a_3573_ = lean_array_uget_borrowed(v_as_3560_, v_i_3562_);
v_ident_3574_ = lean_ctor_get(v_a_3573_, 0);
v_range_3575_ = lean_ctor_get(v_a_3573_, 2);
v___x_3576_ = lean_box(0);
v___x_3577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_posMap_3559_, v_range_3575_);
if (lean_obj_tag(v___x_3577_) == 1)
{
lean_object* v_val_3578_; lean_object* v___x_3579_; lean_object* v_snd_3580_; 
v_val_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_val_3578_);
lean_dec_ref(v___x_3577_);
lean_inc_ref(v_ident_3574_);
v___x_3579_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v_val_3578_, v_ident_3574_, v___y_3564_);
v_snd_3580_ = lean_ctor_get(v___x_3579_, 1);
lean_inc(v_snd_3580_);
lean_dec_ref(v___x_3579_);
v_a_3566_ = v___x_3576_;
v_snd_3567_ = v_snd_3580_;
goto v___jp_3565_;
}
else
{
lean_dec(v___x_3577_);
v_a_3566_ = v___x_3576_;
v_snd_3567_ = v___y_3564_;
goto v___jp_3565_;
}
}
v___jp_3565_:
{
size_t v___x_3568_; size_t v___x_3569_; 
v___x_3568_ = ((size_t)1ULL);
v___x_3569_ = lean_usize_add(v_i_3562_, v___x_3568_);
v_i_3562_ = v___x_3569_;
v_b_3563_ = v_a_3566_;
v___y_3564_ = v_snd_3567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2___boxed(lean_object* v_posMap_3581_, lean_object* v_as_3582_, lean_object* v_sz_3583_, lean_object* v_i_3584_, lean_object* v_b_3585_, lean_object* v___y_3586_){
_start:
{
size_t v_sz_boxed_3587_; size_t v_i_boxed_3588_; lean_object* v_res_3589_; 
v_sz_boxed_3587_ = lean_unbox_usize(v_sz_3583_);
lean_dec(v_sz_3583_);
v_i_boxed_3588_ = lean_unbox_usize(v_i_3584_);
lean_dec(v_i_3584_);
v_res_3589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3581_, v_as_3582_, v_sz_boxed_3587_, v_i_boxed_3588_, v_b_3585_, v___y_3586_);
lean_dec_ref(v_as_3582_);
lean_dec_ref(v_posMap_3581_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(lean_object* v_trees_3590_, lean_object* v_refs_3591_, lean_object* v_posMap_3592_){
_start:
{
lean_object* v___x_3593_; size_t v_sz_3594_; size_t v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v_snd_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3593_ = lean_box(0);
v_sz_3594_ = lean_array_size(v_refs_3591_);
v___x_3595_ = ((size_t)0ULL);
v___x_3596_ = lean_unsigned_to_nat(0u);
v___x_3597_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v___x_3598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3592_, v_refs_3591_, v_sz_3594_, v___x_3595_, v___x_3593_, v___x_3597_);
v_snd_3599_ = lean_ctor_get(v___x_3598_, 1);
lean_inc(v_snd_3599_);
lean_dec_ref(v___x_3598_);
v___x_3600_ = lean_array_get_size(v_trees_3590_);
v___x_3601_ = lean_nat_dec_lt(v___x_3596_, v___x_3600_);
if (v___x_3601_ == 0)
{
return v_snd_3599_;
}
else
{
uint8_t v___x_3602_; 
v___x_3602_ = lean_nat_dec_le(v___x_3600_, v___x_3600_);
if (v___x_3602_ == 0)
{
if (v___x_3601_ == 0)
{
return v_snd_3599_;
}
else
{
size_t v___x_3603_; lean_object* v___x_3604_; lean_object* v_snd_3605_; 
v___x_3603_ = lean_usize_of_nat(v___x_3600_);
v___x_3604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3590_, v___x_3595_, v___x_3603_, v___x_3593_, v_snd_3599_);
v_snd_3605_ = lean_ctor_get(v___x_3604_, 1);
lean_inc(v_snd_3605_);
lean_dec_ref(v___x_3604_);
return v_snd_3605_;
}
}
else
{
size_t v___x_3606_; lean_object* v___x_3607_; lean_object* v_snd_3608_; 
v___x_3606_ = lean_usize_of_nat(v___x_3600_);
v___x_3607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3590_, v___x_3595_, v___x_3606_, v___x_3593_, v_snd_3599_);
v_snd_3608_ = lean_ctor_get(v___x_3607_, 1);
lean_inc(v_snd_3608_);
lean_dec_ref(v___x_3607_);
return v_snd_3608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap___boxed(lean_object* v_trees_3609_, lean_object* v_refs_3610_, lean_object* v_posMap_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3609_, v_refs_3610_, v_posMap_3611_);
lean_dec_ref(v_posMap_3611_);
lean_dec_ref(v_refs_3610_);
lean_dec_ref(v_trees_3609_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(lean_object* v_00_u03b2_3613_, lean_object* v_m_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3614_, v_a_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___boxed(lean_object* v_00_u03b2_3617_, lean_object* v_m_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(v_00_u03b2_3617_, v_m_3618_, v_a_3619_);
lean_dec_ref(v_a_3619_);
lean_dec_ref(v_m_3618_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3621_, lean_object* v_msg_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v_msg_3622_, v___y_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object* v_00_u03b1_3625_, lean_object* v_preNode_3626_, lean_object* v_postNode_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3626_, v_postNode_3627_, v_x_3628_, v_x_3629_, v___y_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object* v_00_u03b2_3632_, lean_object* v_a_3633_, lean_object* v_x_3634_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3633_, v_x_3634_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3636_, lean_object* v_a_3637_, lean_object* v_x_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(v_00_u03b2_3636_, v_a_3637_, v_x_3638_);
lean_dec(v_x_3638_);
lean_dec_ref(v_a_3637_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3640_, lean_object* v_preNode_3641_, lean_object* v_postNode_3642_, lean_object* v___x_3643_, lean_object* v_x_3644_, lean_object* v_x_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3641_, v_postNode_3642_, v___x_3643_, v_x_3644_, v_x_3645_, v___y_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(lean_object* v_a_3648_, lean_object* v_b_3649_, lean_object* v_x_3650_){
_start:
{
if (lean_obj_tag(v_x_3650_) == 0)
{
lean_dec(v_b_3649_);
lean_dec_ref(v_a_3648_);
return v_x_3650_;
}
else
{
lean_object* v_key_3651_; lean_object* v_value_3652_; lean_object* v_tail_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3665_; 
v_key_3651_ = lean_ctor_get(v_x_3650_, 0);
v_value_3652_ = lean_ctor_get(v_x_3650_, 1);
v_tail_3653_ = lean_ctor_get(v_x_3650_, 2);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_x_3650_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3655_ = v_x_3650_;
v_isShared_3656_ = v_isSharedCheck_3665_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_tail_3653_);
lean_inc(v_value_3652_);
lean_inc(v_key_3651_);
lean_dec(v_x_3650_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3665_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
uint8_t v___x_3657_; 
v___x_3657_ = l_Lean_Lsp_instBEqRange_beq(v_key_3651_, v_a_3648_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3658_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3648_, v_b_3649_, v_tail_3653_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 2, v___x_3658_);
v___x_3660_ = v___x_3655_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_key_3651_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_value_3652_);
lean_ctor_set(v_reuseFailAlloc_3661_, 2, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
else
{
lean_object* v___x_3663_; 
lean_dec(v_value_3652_);
lean_dec(v_key_3651_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 1, v_b_3649_);
lean_ctor_set(v___x_3655_, 0, v_a_3648_);
v___x_3663_ = v___x_3655_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3648_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_b_3649_);
lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_tail_3653_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_3666_, lean_object* v_x_3667_){
_start:
{
if (lean_obj_tag(v_x_3667_) == 0)
{
return v_x_3666_;
}
else
{
lean_object* v_key_3668_; lean_object* v_value_3669_; lean_object* v_tail_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3693_; 
v_key_3668_ = lean_ctor_get(v_x_3667_, 0);
v_value_3669_ = lean_ctor_get(v_x_3667_, 1);
v_tail_3670_ = lean_ctor_get(v_x_3667_, 2);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_x_3667_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3672_ = v_x_3667_;
v_isShared_3673_ = v_isSharedCheck_3693_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_tail_3670_);
lean_inc(v_value_3669_);
lean_inc(v_key_3668_);
lean_dec(v_x_3667_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3693_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; uint64_t v___x_3675_; uint64_t v___x_3676_; uint64_t v___x_3677_; uint64_t v_fold_3678_; uint64_t v___x_3679_; uint64_t v___x_3680_; uint64_t v___x_3681_; size_t v___x_3682_; size_t v___x_3683_; size_t v___x_3684_; size_t v___x_3685_; size_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3689_; 
v___x_3674_ = lean_array_get_size(v_x_3666_);
v___x_3675_ = l_Lean_Lsp_instHashableRange_hash(v_key_3668_);
v___x_3676_ = 32ULL;
v___x_3677_ = lean_uint64_shift_right(v___x_3675_, v___x_3676_);
v_fold_3678_ = lean_uint64_xor(v___x_3675_, v___x_3677_);
v___x_3679_ = 16ULL;
v___x_3680_ = lean_uint64_shift_right(v_fold_3678_, v___x_3679_);
v___x_3681_ = lean_uint64_xor(v_fold_3678_, v___x_3680_);
v___x_3682_ = lean_uint64_to_usize(v___x_3681_);
v___x_3683_ = lean_usize_of_nat(v___x_3674_);
v___x_3684_ = ((size_t)1ULL);
v___x_3685_ = lean_usize_sub(v___x_3683_, v___x_3684_);
v___x_3686_ = lean_usize_land(v___x_3682_, v___x_3685_);
v___x_3687_ = lean_array_uget_borrowed(v_x_3666_, v___x_3686_);
lean_inc(v___x_3687_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 2, v___x_3687_);
v___x_3689_ = v___x_3672_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_key_3668_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_value_3669_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_array_uset(v_x_3666_, v___x_3686_, v___x_3689_);
v_x_3666_ = v___x_3690_;
v_x_3667_ = v_tail_3670_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3694_, lean_object* v_source_3695_, lean_object* v_target_3696_){
_start:
{
lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___x_3697_ = lean_array_get_size(v_source_3695_);
v___x_3698_ = lean_nat_dec_lt(v_i_3694_, v___x_3697_);
if (v___x_3698_ == 0)
{
lean_dec_ref(v_source_3695_);
lean_dec(v_i_3694_);
return v_target_3696_;
}
else
{
lean_object* v_es_3699_; lean_object* v___x_3700_; lean_object* v_source_3701_; lean_object* v_target_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v_es_3699_ = lean_array_fget(v_source_3695_, v_i_3694_);
v___x_3700_ = lean_box(0);
v_source_3701_ = lean_array_fset(v_source_3695_, v_i_3694_, v___x_3700_);
v_target_3702_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3696_, v_es_3699_);
v___x_3703_ = lean_unsigned_to_nat(1u);
v___x_3704_ = lean_nat_add(v_i_3694_, v___x_3703_);
lean_dec(v_i_3694_);
v_i_3694_ = v___x_3704_;
v_source_3695_ = v_source_3701_;
v_target_3696_ = v_target_3702_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(lean_object* v_data_3706_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v_nbuckets_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3707_ = lean_array_get_size(v_data_3706_);
v___x_3708_ = lean_unsigned_to_nat(2u);
v_nbuckets_3709_ = lean_nat_mul(v___x_3707_, v___x_3708_);
v___x_3710_ = lean_unsigned_to_nat(0u);
v___x_3711_ = lean_box(0);
v___x_3712_ = lean_mk_array(v_nbuckets_3709_, v___x_3711_);
v___x_3713_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v___x_3710_, v_data_3706_, v___x_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object* v_a_3714_, lean_object* v_x_3715_){
_start:
{
if (lean_obj_tag(v_x_3715_) == 0)
{
uint8_t v___x_3716_; 
v___x_3716_ = 0;
return v___x_3716_;
}
else
{
lean_object* v_key_3717_; lean_object* v_tail_3718_; uint8_t v___x_3719_; 
v_key_3717_ = lean_ctor_get(v_x_3715_, 0);
v_tail_3718_ = lean_ctor_get(v_x_3715_, 2);
v___x_3719_ = l_Lean_Lsp_instBEqRange_beq(v_key_3717_, v_a_3714_);
if (v___x_3719_ == 0)
{
v_x_3715_ = v_tail_3718_;
goto _start;
}
else
{
return v___x_3719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object* v_a_3721_, lean_object* v_x_3722_){
_start:
{
uint8_t v_res_3723_; lean_object* v_r_3724_; 
v_res_3723_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3721_, v_x_3722_);
lean_dec(v_x_3722_);
lean_dec_ref(v_a_3721_);
v_r_3724_ = lean_box(v_res_3723_);
return v_r_3724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object* v_m_3725_, lean_object* v_a_3726_, lean_object* v_b_3727_){
_start:
{
lean_object* v_size_3728_; lean_object* v_buckets_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3772_; 
v_size_3728_ = lean_ctor_get(v_m_3725_, 0);
v_buckets_3729_ = lean_ctor_get(v_m_3725_, 1);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_m_3725_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3731_ = v_m_3725_;
v_isShared_3732_ = v_isSharedCheck_3772_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_buckets_3729_);
lean_inc(v_size_3728_);
lean_dec(v_m_3725_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3772_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3733_; uint64_t v___x_3734_; uint64_t v___x_3735_; uint64_t v___x_3736_; uint64_t v_fold_3737_; uint64_t v___x_3738_; uint64_t v___x_3739_; uint64_t v___x_3740_; size_t v___x_3741_; size_t v___x_3742_; size_t v___x_3743_; size_t v___x_3744_; size_t v___x_3745_; lean_object* v_bkt_3746_; uint8_t v___x_3747_; 
v___x_3733_ = lean_array_get_size(v_buckets_3729_);
v___x_3734_ = l_Lean_Lsp_instHashableRange_hash(v_a_3726_);
v___x_3735_ = 32ULL;
v___x_3736_ = lean_uint64_shift_right(v___x_3734_, v___x_3735_);
v_fold_3737_ = lean_uint64_xor(v___x_3734_, v___x_3736_);
v___x_3738_ = 16ULL;
v___x_3739_ = lean_uint64_shift_right(v_fold_3737_, v___x_3738_);
v___x_3740_ = lean_uint64_xor(v_fold_3737_, v___x_3739_);
v___x_3741_ = lean_uint64_to_usize(v___x_3740_);
v___x_3742_ = lean_usize_of_nat(v___x_3733_);
v___x_3743_ = ((size_t)1ULL);
v___x_3744_ = lean_usize_sub(v___x_3742_, v___x_3743_);
v___x_3745_ = lean_usize_land(v___x_3741_, v___x_3744_);
v_bkt_3746_ = lean_array_uget_borrowed(v_buckets_3729_, v___x_3745_);
v___x_3747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3726_, v_bkt_3746_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; lean_object* v_size_x27_3749_; lean_object* v___x_3750_; lean_object* v_buckets_x27_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3748_ = lean_unsigned_to_nat(1u);
v_size_x27_3749_ = lean_nat_add(v_size_3728_, v___x_3748_);
lean_dec(v_size_3728_);
lean_inc(v_bkt_3746_);
v___x_3750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3750_, 0, v_a_3726_);
lean_ctor_set(v___x_3750_, 1, v_b_3727_);
lean_ctor_set(v___x_3750_, 2, v_bkt_3746_);
v_buckets_x27_3751_ = lean_array_uset(v_buckets_3729_, v___x_3745_, v___x_3750_);
v___x_3752_ = lean_unsigned_to_nat(4u);
v___x_3753_ = lean_nat_mul(v_size_x27_3749_, v___x_3752_);
v___x_3754_ = lean_unsigned_to_nat(3u);
v___x_3755_ = lean_nat_div(v___x_3753_, v___x_3754_);
lean_dec(v___x_3753_);
v___x_3756_ = lean_array_get_size(v_buckets_x27_3751_);
v___x_3757_ = lean_nat_dec_le(v___x_3755_, v___x_3756_);
lean_dec(v___x_3755_);
if (v___x_3757_ == 0)
{
lean_object* v_val_3758_; lean_object* v___x_3760_; 
v_val_3758_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_buckets_x27_3751_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 1, v_val_3758_);
lean_ctor_set(v___x_3731_, 0, v_size_x27_3749_);
v___x_3760_ = v___x_3731_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_size_x27_3749_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_val_3758_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
else
{
lean_object* v___x_3763_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 1, v_buckets_x27_3751_);
lean_ctor_set(v___x_3731_, 0, v_size_x27_3749_);
v___x_3763_ = v___x_3731_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_size_x27_3749_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_buckets_x27_3751_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
else
{
lean_object* v___x_3765_; lean_object* v_buckets_x27_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
lean_inc(v_bkt_3746_);
v___x_3765_ = lean_box(0);
v_buckets_x27_3766_ = lean_array_uset(v_buckets_3729_, v___x_3745_, v___x_3765_);
v___x_3767_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3726_, v_b_3727_, v_bkt_3746_);
v___x_3768_ = lean_array_uset(v_buckets_x27_3766_, v___x_3745_, v___x_3767_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 1, v___x_3768_);
v___x_3770_ = v___x_3731_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_size_3728_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object* v_as_3773_, size_t v_sz_3774_, size_t v_i_3775_, lean_object* v_b_3776_){
_start:
{
lean_object* v_a_3778_; uint8_t v___x_3782_; 
v___x_3782_ = lean_usize_dec_lt(v_i_3775_, v_sz_3774_);
if (v___x_3782_ == 0)
{
return v_b_3776_;
}
else
{
lean_object* v_a_3783_; uint8_t v_isBinder_3784_; 
v_a_3783_ = lean_array_uget_borrowed(v_as_3773_, v_i_3775_);
v_isBinder_3784_ = lean_ctor_get_uint8(v_a_3783_, sizeof(void*)*6);
if (v_isBinder_3784_ == 1)
{
lean_object* v_ident_3785_; lean_object* v_range_3786_; lean_object* v___x_3787_; 
v_ident_3785_ = lean_ctor_get(v_a_3783_, 0);
v_range_3786_ = lean_ctor_get(v_a_3783_, 2);
lean_inc_ref(v_ident_3785_);
lean_inc_ref(v_range_3786_);
v___x_3787_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_b_3776_, v_range_3786_, v_ident_3785_);
v_a_3778_ = v___x_3787_;
goto v___jp_3777_;
}
else
{
v_a_3778_ = v_b_3776_;
goto v___jp_3777_;
}
}
v___jp_3777_:
{
size_t v___x_3779_; size_t v___x_3780_; 
v___x_3779_ = ((size_t)1ULL);
v___x_3780_ = lean_usize_add(v_i_3775_, v___x_3779_);
v_i_3775_ = v___x_3780_;
v_b_3776_ = v_a_3778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object* v_as_3788_, lean_object* v_sz_3789_, lean_object* v_i_3790_, lean_object* v_b_3791_){
_start:
{
size_t v_sz_boxed_3792_; size_t v_i_boxed_3793_; lean_object* v_res_3794_; 
v_sz_boxed_3792_ = lean_unbox_usize(v_sz_3789_);
lean_dec(v_sz_3789_);
v_i_boxed_3793_ = lean_unbox_usize(v_i_3790_);
lean_dec(v_i_3790_);
v_res_3794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_as_3788_, v_sz_boxed_3792_, v_i_boxed_3793_, v_b_3791_);
lean_dec_ref(v_as_3788_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object* v___x_3795_, lean_object* v_as_3796_, size_t v_sz_3797_, size_t v_i_3798_, lean_object* v_b_3799_){
_start:
{
lean_object* v_a_3801_; uint8_t v___x_3805_; 
v___x_3805_ = lean_usize_dec_lt(v_i_3798_, v_sz_3797_);
if (v___x_3805_ == 0)
{
return v_b_3799_;
}
else
{
lean_object* v_a_3806_; lean_object* v_ident_3809_; lean_object* v_range_3810_; lean_object* v_stx_3811_; lean_object* v_ci_3812_; lean_object* v_info_3813_; uint8_t v_isBinder_3814_; uint8_t v___x_3815_; 
v_a_3806_ = lean_array_uget(v_as_3796_, v_i_3798_);
v_ident_3809_ = lean_ctor_get(v_a_3806_, 0);
v_range_3810_ = lean_ctor_get(v_a_3806_, 2);
v_stx_3811_ = lean_ctor_get(v_a_3806_, 3);
v_ci_3812_ = lean_ctor_get(v_a_3806_, 4);
v_info_3813_ = lean_ctor_get(v_a_3806_, 5);
v_isBinder_3814_ = lean_ctor_get_uint8(v_a_3806_, sizeof(void*)*6);
v___x_3815_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v___x_3795_, v_ident_3809_);
if (v___x_3815_ == 0)
{
if (v___x_3815_ == 0)
{
goto v___jp_3807_;
}
else
{
if (v___x_3815_ == 0)
{
lean_dec(v_a_3806_);
v_a_3801_ = v_b_3799_;
goto v___jp_3800_;
}
else
{
goto v___jp_3807_;
}
}
}
else
{
lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3827_; 
lean_inc_ref(v_info_3813_);
lean_inc_ref(v_ci_3812_);
lean_inc(v_stx_3811_);
lean_inc_ref(v_range_3810_);
lean_inc_ref(v_ident_3809_);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_a_3806_);
if (v_isSharedCheck_3827_ == 0)
{
lean_object* v_unused_3828_; lean_object* v_unused_3829_; lean_object* v_unused_3830_; lean_object* v_unused_3831_; lean_object* v_unused_3832_; lean_object* v_unused_3833_; 
v_unused_3828_ = lean_ctor_get(v_a_3806_, 5);
lean_dec(v_unused_3828_);
v_unused_3829_ = lean_ctor_get(v_a_3806_, 4);
lean_dec(v_unused_3829_);
v_unused_3830_ = lean_ctor_get(v_a_3806_, 3);
lean_dec(v_unused_3830_);
v_unused_3831_ = lean_ctor_get(v_a_3806_, 2);
lean_dec(v_unused_3831_);
v_unused_3832_ = lean_ctor_get(v_a_3806_, 1);
lean_dec(v_unused_3832_);
v_unused_3833_ = lean_ctor_get(v_a_3806_, 0);
lean_dec(v_unused_3833_);
v___x_3817_ = v_a_3806_;
v_isShared_3818_ = v_isSharedCheck_3827_;
goto v_resetjp_3816_;
}
else
{
lean_dec(v_a_3806_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3827_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3824_; 
lean_inc_ref(v_ident_3809_);
v___x_3819_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v___x_3795_, v_ident_3809_);
v___x_3820_ = lean_unsigned_to_nat(1u);
v___x_3821_ = lean_mk_empty_array_with_capacity(v___x_3820_);
v___x_3822_ = lean_array_push(v___x_3821_, v_ident_3809_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 1, v___x_3822_);
lean_ctor_set(v___x_3817_, 0, v___x_3819_);
v___x_3824_ = v___x_3817_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3819_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3826_, 2, v_range_3810_);
lean_ctor_set(v_reuseFailAlloc_3826_, 3, v_stx_3811_);
lean_ctor_set(v_reuseFailAlloc_3826_, 4, v_ci_3812_);
lean_ctor_set(v_reuseFailAlloc_3826_, 5, v_info_3813_);
lean_ctor_set_uint8(v_reuseFailAlloc_3826_, sizeof(void*)*6, v_isBinder_3814_);
v___x_3824_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3825_; 
v___x_3825_ = lean_array_push(v_b_3799_, v___x_3824_);
v_a_3801_ = v___x_3825_;
goto v___jp_3800_;
}
}
}
v___jp_3807_:
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_array_push(v_b_3799_, v_a_3806_);
v_a_3801_ = v___x_3808_;
goto v___jp_3800_;
}
}
v___jp_3800_:
{
size_t v___x_3802_; size_t v___x_3803_; 
v___x_3802_ = ((size_t)1ULL);
v___x_3803_ = lean_usize_add(v_i_3798_, v___x_3802_);
v_i_3798_ = v___x_3803_;
v_b_3799_ = v_a_3801_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object* v___x_3834_, lean_object* v_as_3835_, lean_object* v_sz_3836_, lean_object* v_i_3837_, lean_object* v_b_3838_){
_start:
{
size_t v_sz_boxed_3839_; size_t v_i_boxed_3840_; lean_object* v_res_3841_; 
v_sz_boxed_3839_ = lean_unbox_usize(v_sz_3836_);
lean_dec(v_sz_3836_);
v_i_boxed_3840_ = lean_unbox_usize(v_i_3837_);
lean_dec(v_i_3837_);
v_res_3841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3834_, v_as_3835_, v_sz_boxed_3839_, v_i_boxed_3840_, v_b_3838_);
lean_dec_ref(v_as_3835_);
lean_dec_ref(v___x_3834_);
return v_res_3841_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__0(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3842_ = lean_box(0);
v___x_3843_ = lean_unsigned_to_nat(16u);
v___x_3844_ = lean_mk_array(v___x_3843_, v___x_3842_);
return v___x_3844_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__1(void){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v_posMap_3847_; 
v___x_3845_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__0, &l_Lean_Server_combineIdents___closed__0_once, _init_l_Lean_Server_combineIdents___closed__0);
v___x_3846_ = lean_unsigned_to_nat(0u);
v_posMap_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_posMap_3847_, 0, v___x_3846_);
lean_ctor_set(v_posMap_3847_, 1, v___x_3845_);
return v_posMap_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object* v_trees_3848_, lean_object* v_refs_3849_){
_start:
{
lean_object* v_posMap_3850_; size_t v_sz_3851_; size_t v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v_posMap_3850_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__1, &l_Lean_Server_combineIdents___closed__1_once, _init_l_Lean_Server_combineIdents___closed__1);
v_sz_3851_ = lean_array_size(v_refs_3849_);
v___x_3852_ = ((size_t)0ULL);
v___x_3853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_refs_3849_, v_sz_3851_, v___x_3852_, v_posMap_3850_);
v___x_3854_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3848_, v_refs_3849_, v___x_3853_);
lean_dec_ref(v___x_3853_);
v___x_3855_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v___x_3854_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_3857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3855_, v_refs_3849_, v_sz_3851_, v___x_3852_, v___x_3856_);
lean_dec_ref(v___x_3855_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object* v_trees_3858_, lean_object* v_refs_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_Server_combineIdents(v_trees_3858_, v_refs_3859_);
lean_dec_ref(v_refs_3859_);
lean_dec_ref(v_trees_3858_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object* v_00_u03b2_3861_, lean_object* v_m_3862_, lean_object* v_a_3863_, lean_object* v_b_3864_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_m_3862_, v_a_3863_, v_b_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object* v_00_u03b2_3866_, lean_object* v_a_3867_, lean_object* v_x_3868_){
_start:
{
uint8_t v___x_3869_; 
v___x_3869_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3867_, v_x_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3870_, lean_object* v_a_3871_, lean_object* v_x_3872_){
_start:
{
uint8_t v_res_3873_; lean_object* v_r_3874_; 
v_res_3873_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(v_00_u03b2_3870_, v_a_3871_, v_x_3872_);
lean_dec(v_x_3872_);
lean_dec_ref(v_a_3871_);
v_r_3874_ = lean_box(v_res_3873_);
return v_r_3874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object* v_00_u03b2_3875_, lean_object* v_data_3876_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_data_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object* v_00_u03b2_3878_, lean_object* v_a_3879_, lean_object* v_b_3880_, lean_object* v_x_3881_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3879_, v_b_3880_, v_x_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3883_, lean_object* v_i_3884_, lean_object* v_source_3885_, lean_object* v_target_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v_i_3884_, v_source_3885_, v_target_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3889_, v_x_3890_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object* v_hi_3892_, lean_object* v_pivot_3893_, lean_object* v_as_3894_, lean_object* v_i_3895_, lean_object* v_k_3896_){
_start:
{
uint8_t v___x_3901_; 
v___x_3901_ = lean_nat_dec_lt(v_k_3896_, v_hi_3892_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec(v_k_3896_);
v___x_3902_ = lean_array_fswap(v_as_3894_, v_i_3895_, v_hi_3892_);
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v_i_3895_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
return v___x_3903_;
}
else
{
lean_object* v___x_3904_; lean_object* v_range_3905_; lean_object* v_range_3906_; uint8_t v___x_3907_; 
v___x_3904_ = lean_array_fget_borrowed(v_as_3894_, v_k_3896_);
v_range_3905_ = lean_ctor_get(v___x_3904_, 2);
v_range_3906_ = lean_ctor_get(v_pivot_3893_, 2);
v___x_3907_ = l_Lean_Lsp_instOrdRange_ord(v_range_3905_, v_range_3906_);
if (v___x_3907_ == 0)
{
if (v___x_3901_ == 0)
{
goto v___jp_3897_;
}
else
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3908_ = lean_array_fswap(v_as_3894_, v_i_3895_, v_k_3896_);
v___x_3909_ = lean_unsigned_to_nat(1u);
v___x_3910_ = lean_nat_add(v_i_3895_, v___x_3909_);
lean_dec(v_i_3895_);
v___x_3911_ = lean_nat_add(v_k_3896_, v___x_3909_);
lean_dec(v_k_3896_);
v_as_3894_ = v___x_3908_;
v_i_3895_ = v___x_3910_;
v_k_3896_ = v___x_3911_;
goto _start;
}
}
else
{
goto v___jp_3897_;
}
}
v___jp_3897_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_unsigned_to_nat(1u);
v___x_3899_ = lean_nat_add(v_k_3896_, v___x_3898_);
lean_dec(v_k_3896_);
v_k_3896_ = v___x_3899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object* v_hi_3913_, lean_object* v_pivot_3914_, lean_object* v_as_3915_, lean_object* v_i_3916_, lean_object* v_k_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3913_, v_pivot_3914_, v_as_3915_, v_i_3916_, v_k_3917_);
lean_dec_ref(v_pivot_3914_);
lean_dec(v_hi_3913_);
return v_res_3918_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3919_, lean_object* v_x1_3920_, lean_object* v_x2_3921_){
_start:
{
lean_object* v_range_3922_; lean_object* v_range_3923_; uint8_t v___x_3924_; 
v_range_3922_ = lean_ctor_get(v_x1_3920_, 2);
v_range_3923_ = lean_ctor_get(v_x2_3921_, 2);
v___x_3924_ = l_Lean_Lsp_instOrdRange_ord(v_range_3922_, v_range_3923_);
if (v___x_3924_ == 0)
{
return v___x_3919_;
}
else
{
uint8_t v___x_3925_; 
v___x_3925_ = 0;
return v___x_3925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3926_, lean_object* v_x1_3927_, lean_object* v_x2_3928_){
_start:
{
uint8_t v___x_2063__boxed_3929_; uint8_t v_res_3930_; lean_object* v_r_3931_; 
v___x_2063__boxed_3929_ = lean_unbox(v___x_3926_);
v_res_3930_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_2063__boxed_3929_, v_x1_3927_, v_x2_3928_);
lean_dec_ref(v_x2_3928_);
lean_dec_ref(v_x1_3927_);
v_r_3931_ = lean_box(v_res_3930_);
return v_r_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_n_3932_, lean_object* v_as_3933_, lean_object* v_lo_3934_, lean_object* v_hi_3935_){
_start:
{
lean_object* v___y_3937_; uint8_t v___x_3947_; 
v___x_3947_ = lean_nat_dec_lt(v_lo_3934_, v_hi_3935_);
if (v___x_3947_ == 0)
{
lean_dec(v_lo_3934_);
return v_as_3933_;
}
else
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v_mid_3950_; lean_object* v___y_3952_; lean_object* v___y_3958_; lean_object* v___x_3963_; lean_object* v___x_3964_; uint8_t v___x_3965_; 
v___x_3948_ = lean_nat_add(v_lo_3934_, v_hi_3935_);
v___x_3949_ = lean_unsigned_to_nat(1u);
v_mid_3950_ = lean_nat_shiftr(v___x_3948_, v___x_3949_);
lean_dec(v___x_3948_);
v___x_3963_ = lean_array_fget_borrowed(v_as_3933_, v_mid_3950_);
v___x_3964_ = lean_array_fget_borrowed(v_as_3933_, v_lo_3934_);
v___x_3965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3947_, v___x_3963_, v___x_3964_);
if (v___x_3965_ == 0)
{
v___y_3958_ = v_as_3933_;
goto v___jp_3957_;
}
else
{
lean_object* v___x_3966_; 
v___x_3966_ = lean_array_fswap(v_as_3933_, v_lo_3934_, v_mid_3950_);
v___y_3958_ = v___x_3966_;
goto v___jp_3957_;
}
v___jp_3951_:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3953_ = lean_array_fget_borrowed(v___y_3952_, v_mid_3950_);
v___x_3954_ = lean_array_fget_borrowed(v___y_3952_, v_hi_3935_);
v___x_3955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3947_, v___x_3953_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_dec(v_mid_3950_);
v___y_3937_ = v___y_3952_;
goto v___jp_3936_;
}
else
{
lean_object* v___x_3956_; 
v___x_3956_ = lean_array_fswap(v___y_3952_, v_mid_3950_, v_hi_3935_);
lean_dec(v_mid_3950_);
v___y_3937_ = v___x_3956_;
goto v___jp_3936_;
}
}
v___jp_3957_:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; uint8_t v___x_3961_; 
v___x_3959_ = lean_array_fget_borrowed(v___y_3958_, v_hi_3935_);
v___x_3960_ = lean_array_fget_borrowed(v___y_3958_, v_lo_3934_);
v___x_3961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3947_, v___x_3959_, v___x_3960_);
if (v___x_3961_ == 0)
{
v___y_3952_ = v___y_3958_;
goto v___jp_3951_;
}
else
{
lean_object* v___x_3962_; 
v___x_3962_ = lean_array_fswap(v___y_3958_, v_lo_3934_, v_hi_3935_);
v___y_3952_ = v___x_3962_;
goto v___jp_3951_;
}
}
}
v___jp_3936_:
{
lean_object* v_pivot_3938_; lean_object* v___x_3939_; lean_object* v_fst_3940_; lean_object* v_snd_3941_; uint8_t v___x_3942_; 
v_pivot_3938_ = lean_array_fget(v___y_3937_, v_hi_3935_);
lean_inc_n(v_lo_3934_, 2);
v___x_3939_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3935_, v_pivot_3938_, v___y_3937_, v_lo_3934_, v_lo_3934_);
lean_dec(v_pivot_3938_);
v_fst_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_fst_3940_);
v_snd_3941_ = lean_ctor_get(v___x_3939_, 1);
lean_inc(v_snd_3941_);
lean_dec_ref(v___x_3939_);
v___x_3942_ = lean_nat_dec_le(v_hi_3935_, v_fst_3940_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3943_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3932_, v_snd_3941_, v_lo_3934_, v_fst_3940_);
v___x_3944_ = lean_unsigned_to_nat(1u);
v___x_3945_ = lean_nat_add(v_fst_3940_, v___x_3944_);
lean_dec(v_fst_3940_);
v_as_3933_ = v___x_3943_;
v_lo_3934_ = v___x_3945_;
goto _start;
}
else
{
lean_dec(v_fst_3940_);
lean_dec(v_lo_3934_);
return v_snd_3941_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_n_3967_, lean_object* v_as_3968_, lean_object* v_lo_3969_, lean_object* v_hi_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3967_, v_as_3968_, v_lo_3969_, v_hi_3970_);
lean_dec(v_hi_3970_);
lean_dec(v_n_3967_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object* v_x_3972_, lean_object* v_x_3973_){
_start:
{
if (lean_obj_tag(v_x_3973_) == 0)
{
return v_x_3972_;
}
else
{
lean_object* v_key_3974_; lean_object* v_snd_3975_; lean_object* v_value_3976_; lean_object* v_tail_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4017_; 
v_key_3974_ = lean_ctor_get(v_x_3973_, 0);
lean_inc(v_key_3974_);
v_snd_3975_ = lean_ctor_get(v_key_3974_, 1);
v_value_3976_ = lean_ctor_get(v_x_3973_, 1);
v_tail_3977_ = lean_ctor_get(v_x_3973_, 2);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_x_3973_);
if (v_isSharedCheck_4017_ == 0)
{
lean_object* v_unused_4018_; 
v_unused_4018_ = lean_ctor_get(v_x_3973_, 0);
lean_dec(v_unused_4018_);
v___x_3979_ = v_x_3973_;
v_isShared_3980_ = v_isSharedCheck_4017_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_tail_3977_);
lean_inc(v_value_3976_);
lean_dec(v_x_3973_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4017_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v_fst_3981_; lean_object* v_fst_3982_; lean_object* v_snd_3983_; lean_object* v___x_3984_; uint64_t v___x_3985_; uint64_t v___y_3987_; uint64_t v___y_4009_; 
v_fst_3981_ = lean_ctor_get(v_key_3974_, 0);
v_fst_3982_ = lean_ctor_get(v_snd_3975_, 0);
v_snd_3983_ = lean_ctor_get(v_snd_3975_, 1);
v___x_3984_ = lean_array_get_size(v_x_3972_);
v___x_3985_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_3981_);
if (lean_obj_tag(v_fst_3982_) == 0)
{
uint64_t v___x_4012_; 
v___x_4012_ = 11ULL;
v___y_3987_ = v___x_4012_;
goto v___jp_3986_;
}
else
{
lean_object* v_val_4013_; uint8_t v___x_4014_; 
v_val_4013_ = lean_ctor_get(v_fst_3982_, 0);
v___x_4014_ = lean_unbox(v_val_4013_);
if (v___x_4014_ == 0)
{
uint64_t v___x_4015_; 
v___x_4015_ = 13ULL;
v___y_4009_ = v___x_4015_;
goto v___jp_4008_;
}
else
{
uint64_t v___x_4016_; 
v___x_4016_ = 11ULL;
v___y_4009_ = v___x_4016_;
goto v___jp_4008_;
}
}
v___jp_3986_:
{
uint64_t v___x_3988_; uint64_t v___x_3989_; uint64_t v___x_3990_; uint64_t v___x_3991_; uint64_t v___x_3992_; uint64_t v_fold_3993_; uint64_t v___x_3994_; uint64_t v___x_3995_; uint64_t v___x_3996_; size_t v___x_3997_; size_t v___x_3998_; size_t v___x_3999_; size_t v___x_4000_; size_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4004_; 
v___x_3988_ = l_Lean_Lsp_instHashableRange_hash(v_snd_3983_);
v___x_3989_ = lean_uint64_mix_hash(v___y_3987_, v___x_3988_);
v___x_3990_ = lean_uint64_mix_hash(v___x_3985_, v___x_3989_);
v___x_3991_ = 32ULL;
v___x_3992_ = lean_uint64_shift_right(v___x_3990_, v___x_3991_);
v_fold_3993_ = lean_uint64_xor(v___x_3990_, v___x_3992_);
v___x_3994_ = 16ULL;
v___x_3995_ = lean_uint64_shift_right(v_fold_3993_, v___x_3994_);
v___x_3996_ = lean_uint64_xor(v_fold_3993_, v___x_3995_);
v___x_3997_ = lean_uint64_to_usize(v___x_3996_);
v___x_3998_ = lean_usize_of_nat(v___x_3984_);
v___x_3999_ = ((size_t)1ULL);
v___x_4000_ = lean_usize_sub(v___x_3998_, v___x_3999_);
v___x_4001_ = lean_usize_land(v___x_3997_, v___x_4000_);
v___x_4002_ = lean_array_uget_borrowed(v_x_3972_, v___x_4001_);
lean_inc(v___x_4002_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 2, v___x_4002_);
v___x_4004_ = v___x_3979_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_key_3974_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_value_3976_);
lean_ctor_set(v_reuseFailAlloc_4007_, 2, v___x_4002_);
v___x_4004_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4005_; 
v___x_4005_ = lean_array_uset(v_x_3972_, v___x_4001_, v___x_4004_);
v_x_3972_ = v___x_4005_;
v_x_3973_ = v_tail_3977_;
goto _start;
}
}
v___jp_4008_:
{
uint64_t v___x_4010_; uint64_t v___x_4011_; 
v___x_4010_ = 13ULL;
v___x_4011_ = lean_uint64_mix_hash(v___y_4009_, v___x_4010_);
v___y_3987_ = v___x_4011_;
goto v___jp_3986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object* v_i_4019_, lean_object* v_source_4020_, lean_object* v_target_4021_){
_start:
{
lean_object* v___x_4022_; uint8_t v___x_4023_; 
v___x_4022_ = lean_array_get_size(v_source_4020_);
v___x_4023_ = lean_nat_dec_lt(v_i_4019_, v___x_4022_);
if (v___x_4023_ == 0)
{
lean_dec_ref(v_source_4020_);
lean_dec(v_i_4019_);
return v_target_4021_;
}
else
{
lean_object* v_es_4024_; lean_object* v___x_4025_; lean_object* v_source_4026_; lean_object* v_target_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_es_4024_ = lean_array_fget(v_source_4020_, v_i_4019_);
v___x_4025_ = lean_box(0);
v_source_4026_ = lean_array_fset(v_source_4020_, v_i_4019_, v___x_4025_);
v_target_4027_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_target_4021_, v_es_4024_);
v___x_4028_ = lean_unsigned_to_nat(1u);
v___x_4029_ = lean_nat_add(v_i_4019_, v___x_4028_);
lean_dec(v_i_4019_);
v_i_4019_ = v___x_4029_;
v_source_4020_ = v_source_4026_;
v_target_4021_ = v_target_4027_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object* v_data_4031_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v_nbuckets_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4032_ = lean_array_get_size(v_data_4031_);
v___x_4033_ = lean_unsigned_to_nat(2u);
v_nbuckets_4034_ = lean_nat_mul(v___x_4032_, v___x_4033_);
v___x_4035_ = lean_unsigned_to_nat(0u);
v___x_4036_ = lean_box(0);
v___x_4037_ = lean_mk_array(v_nbuckets_4034_, v___x_4036_);
v___x_4038_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v___x_4035_, v_data_4031_, v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object* v_x_4039_, lean_object* v_x_4040_){
_start:
{
if (lean_obj_tag(v_x_4039_) == 0)
{
if (lean_obj_tag(v_x_4040_) == 0)
{
uint8_t v___x_4041_; 
v___x_4041_ = 1;
return v___x_4041_;
}
else
{
uint8_t v___x_4042_; 
v___x_4042_ = 0;
return v___x_4042_;
}
}
else
{
if (lean_obj_tag(v_x_4040_) == 0)
{
uint8_t v___x_4043_; 
v___x_4043_ = 0;
return v___x_4043_;
}
else
{
lean_object* v_val_4044_; uint8_t v___x_4045_; 
v_val_4044_ = lean_ctor_get(v_x_4039_, 0);
v___x_4045_ = lean_unbox(v_val_4044_);
if (v___x_4045_ == 0)
{
lean_object* v_val_4046_; uint8_t v___x_4047_; 
v_val_4046_ = lean_ctor_get(v_x_4040_, 0);
v___x_4047_ = lean_unbox(v_val_4046_);
if (v___x_4047_ == 0)
{
uint8_t v___x_4048_; 
v___x_4048_ = 1;
return v___x_4048_;
}
else
{
uint8_t v___x_4049_; 
v___x_4049_ = lean_unbox(v_val_4044_);
return v___x_4049_;
}
}
else
{
lean_object* v_val_4050_; uint8_t v___x_4051_; 
v_val_4050_ = lean_ctor_get(v_x_4040_, 0);
v___x_4051_ = lean_unbox(v_val_4050_);
return v___x_4051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object* v_x_4052_, lean_object* v_x_4053_){
_start:
{
uint8_t v_res_4054_; lean_object* v_r_4055_; 
v_res_4054_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_x_4052_, v_x_4053_);
lean_dec(v_x_4053_);
lean_dec(v_x_4052_);
v_r_4055_ = lean_box(v_res_4054_);
return v_r_4055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object* v_a_4056_, lean_object* v_x_4057_){
_start:
{
if (lean_obj_tag(v_x_4057_) == 0)
{
lean_object* v___x_4058_; 
v___x_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4058_, 0, v_a_4056_);
return v___x_4058_;
}
else
{
lean_object* v_val_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4087_; 
v_val_4059_ = lean_ctor_get(v_x_4057_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_x_4057_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4061_ = v_x_4057_;
v_isShared_4062_ = v_isSharedCheck_4087_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_val_4059_);
lean_dec(v_x_4057_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4087_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v_ident_4063_; lean_object* v_aliases_4064_; lean_object* v_range_4065_; lean_object* v_stx_4066_; lean_object* v_ci_4067_; lean_object* v_info_4068_; uint8_t v_isBinder_4069_; lean_object* v_aliases_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4081_; 
v_ident_4063_ = lean_ctor_get(v_val_4059_, 0);
lean_inc_ref(v_ident_4063_);
v_aliases_4064_ = lean_ctor_get(v_val_4059_, 1);
lean_inc_ref(v_aliases_4064_);
v_range_4065_ = lean_ctor_get(v_val_4059_, 2);
lean_inc_ref(v_range_4065_);
v_stx_4066_ = lean_ctor_get(v_val_4059_, 3);
lean_inc(v_stx_4066_);
v_ci_4067_ = lean_ctor_get(v_val_4059_, 4);
lean_inc_ref(v_ci_4067_);
v_info_4068_ = lean_ctor_get(v_val_4059_, 5);
lean_inc_ref(v_info_4068_);
v_isBinder_4069_ = lean_ctor_get_uint8(v_val_4059_, sizeof(void*)*6);
lean_dec(v_val_4059_);
v_aliases_4070_ = lean_ctor_get(v_a_4056_, 1);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_a_4056_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; lean_object* v_unused_4083_; lean_object* v_unused_4084_; lean_object* v_unused_4085_; lean_object* v_unused_4086_; 
v_unused_4082_ = lean_ctor_get(v_a_4056_, 5);
lean_dec(v_unused_4082_);
v_unused_4083_ = lean_ctor_get(v_a_4056_, 4);
lean_dec(v_unused_4083_);
v_unused_4084_ = lean_ctor_get(v_a_4056_, 3);
lean_dec(v_unused_4084_);
v_unused_4085_ = lean_ctor_get(v_a_4056_, 2);
lean_dec(v_unused_4085_);
v_unused_4086_ = lean_ctor_get(v_a_4056_, 0);
lean_dec(v_unused_4086_);
v___x_4072_ = v_a_4056_;
v_isShared_4073_ = v_isSharedCheck_4081_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_aliases_4070_);
lean_dec(v_a_4056_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4081_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4074_; lean_object* v___x_4076_; 
v___x_4074_ = l_Array_append___redArg(v_aliases_4064_, v_aliases_4070_);
lean_dec_ref(v_aliases_4070_);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 5, v_info_4068_);
lean_ctor_set(v___x_4072_, 4, v_ci_4067_);
lean_ctor_set(v___x_4072_, 3, v_stx_4066_);
lean_ctor_set(v___x_4072_, 2, v_range_4065_);
lean_ctor_set(v___x_4072_, 1, v___x_4074_);
lean_ctor_set(v___x_4072_, 0, v_ident_4063_);
v___x_4076_ = v___x_4072_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_ident_4063_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v___x_4074_);
lean_ctor_set(v_reuseFailAlloc_4080_, 2, v_range_4065_);
lean_ctor_set(v_reuseFailAlloc_4080_, 3, v_stx_4066_);
lean_ctor_set(v_reuseFailAlloc_4080_, 4, v_ci_4067_);
lean_ctor_set(v_reuseFailAlloc_4080_, 5, v_info_4068_);
v___x_4076_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4078_; 
lean_ctor_set_uint8(v___x_4076_, sizeof(void*)*6, v_isBinder_4069_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 0, v___x_4076_);
v___x_4078_ = v___x_4061_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_x_4090_){
_start:
{
if (lean_obj_tag(v_x_4090_) == 0)
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v_val_4093_; lean_object* v___x_4094_; 
v___x_4091_ = lean_box(0);
v___x_4092_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4088_, v___x_4091_);
v_val_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_val_4093_);
lean_dec(v___x_4092_);
v___x_4094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4094_, 0, v_a_4089_);
lean_ctor_set(v___x_4094_, 1, v_val_4093_);
lean_ctor_set(v___x_4094_, 2, v_x_4090_);
return v___x_4094_;
}
else
{
lean_object* v_key_4095_; lean_object* v_value_4096_; lean_object* v_tail_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4124_; 
v_key_4095_ = lean_ctor_get(v_x_4090_, 0);
v_value_4096_ = lean_ctor_get(v_x_4090_, 1);
v_tail_4097_ = lean_ctor_get(v_x_4090_, 2);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_x_4090_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4099_ = v_x_4090_;
v_isShared_4100_ = v_isSharedCheck_4124_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_tail_4097_);
lean_inc(v_value_4096_);
lean_inc(v_key_4095_);
lean_dec(v_x_4090_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4124_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
uint8_t v___y_4102_; lean_object* v_fst_4113_; lean_object* v_snd_4114_; lean_object* v_fst_4115_; lean_object* v_snd_4116_; uint8_t v___x_4117_; 
v_fst_4113_ = lean_ctor_get(v_key_4095_, 0);
v_snd_4114_ = lean_ctor_get(v_key_4095_, 1);
v_fst_4115_ = lean_ctor_get(v_a_4089_, 0);
v_snd_4116_ = lean_ctor_get(v_a_4089_, 1);
v___x_4117_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4113_, v_fst_4115_);
if (v___x_4117_ == 0)
{
v___y_4102_ = v___x_4117_;
goto v___jp_4101_;
}
else
{
lean_object* v_fst_4118_; lean_object* v_snd_4119_; lean_object* v_fst_4120_; lean_object* v_snd_4121_; uint8_t v___x_4122_; 
v_fst_4118_ = lean_ctor_get(v_snd_4114_, 0);
v_snd_4119_ = lean_ctor_get(v_snd_4114_, 1);
v_fst_4120_ = lean_ctor_get(v_snd_4116_, 0);
v_snd_4121_ = lean_ctor_get(v_snd_4116_, 1);
v___x_4122_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4118_, v_fst_4120_);
if (v___x_4122_ == 0)
{
v___y_4102_ = v___x_4122_;
goto v___jp_4101_;
}
else
{
uint8_t v___x_4123_; 
v___x_4123_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4119_, v_snd_4121_);
v___y_4102_ = v___x_4123_;
goto v___jp_4101_;
}
}
v___jp_4101_:
{
if (v___y_4102_ == 0)
{
lean_object* v_tail_4103_; lean_object* v___x_4105_; 
v_tail_4103_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4088_, v_a_4089_, v_tail_4097_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 2, v_tail_4103_);
v___x_4105_ = v___x_4099_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_key_4095_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_value_4096_);
lean_ctor_set(v_reuseFailAlloc_4106_, 2, v_tail_4103_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v_val_4109_; lean_object* v___x_4111_; 
lean_dec(v_key_4095_);
v___x_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_value_4096_);
v___x_4108_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4088_, v___x_4107_);
v_val_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_val_4109_);
lean_dec(v___x_4108_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 1, v_val_4109_);
lean_ctor_set(v___x_4099_, 0, v_a_4089_);
v___x_4111_ = v___x_4099_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4089_);
lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_val_4109_);
lean_ctor_set(v_reuseFailAlloc_4112_, 2, v_tail_4097_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_a_4125_, lean_object* v_x_4126_){
_start:
{
if (lean_obj_tag(v_x_4126_) == 0)
{
uint8_t v___x_4127_; 
v___x_4127_ = 0;
return v___x_4127_;
}
else
{
lean_object* v_key_4128_; lean_object* v_tail_4129_; uint8_t v___y_4131_; lean_object* v_fst_4133_; lean_object* v_snd_4134_; lean_object* v_fst_4135_; lean_object* v_snd_4136_; uint8_t v___x_4137_; 
v_key_4128_ = lean_ctor_get(v_x_4126_, 0);
v_tail_4129_ = lean_ctor_get(v_x_4126_, 2);
v_fst_4133_ = lean_ctor_get(v_key_4128_, 0);
v_snd_4134_ = lean_ctor_get(v_key_4128_, 1);
v_fst_4135_ = lean_ctor_get(v_a_4125_, 0);
v_snd_4136_ = lean_ctor_get(v_a_4125_, 1);
v___x_4137_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4133_, v_fst_4135_);
if (v___x_4137_ == 0)
{
v___y_4131_ = v___x_4137_;
goto v___jp_4130_;
}
else
{
lean_object* v_fst_4138_; lean_object* v_snd_4139_; lean_object* v_fst_4140_; lean_object* v_snd_4141_; uint8_t v___x_4142_; 
v_fst_4138_ = lean_ctor_get(v_snd_4134_, 0);
v_snd_4139_ = lean_ctor_get(v_snd_4134_, 1);
v_fst_4140_ = lean_ctor_get(v_snd_4136_, 0);
v_snd_4141_ = lean_ctor_get(v_snd_4136_, 1);
v___x_4142_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4138_, v_fst_4140_);
if (v___x_4142_ == 0)
{
v___y_4131_ = v___x_4142_;
goto v___jp_4130_;
}
else
{
uint8_t v___x_4143_; 
v___x_4143_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4139_, v_snd_4141_);
v___y_4131_ = v___x_4143_;
goto v___jp_4130_;
}
}
v___jp_4130_:
{
if (v___y_4131_ == 0)
{
v_x_4126_ = v_tail_4129_;
goto _start;
}
else
{
return v___y_4131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object* v_a_4144_, lean_object* v_x_4145_){
_start:
{
uint8_t v_res_4146_; lean_object* v_r_4147_; 
v_res_4146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4144_, v_x_4145_);
lean_dec(v_x_4145_);
lean_dec_ref(v_a_4144_);
v_r_4147_ = lean_box(v_res_4146_);
return v_r_4147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4148_, lean_object* v_m_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v___y_4152_; size_t v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v_snd_4158_; lean_object* v_size_4159_; lean_object* v_buckets_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4219_; 
v_snd_4158_ = lean_ctor_get(v_a_4150_, 1);
v_size_4159_ = lean_ctor_get(v_m_4149_, 0);
v_buckets_4160_ = lean_ctor_get(v_m_4149_, 1);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_m_4149_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4162_ = v_m_4149_;
v_isShared_4163_ = v_isSharedCheck_4219_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_buckets_4160_);
lean_inc(v_size_4159_);
lean_dec(v_m_4149_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4219_;
goto v_resetjp_4161_;
}
v___jp_4151_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_array_uset(v___y_4154_, v___y_4153_, v___y_4152_);
v___x_4157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___y_4155_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
return v___x_4157_;
}
v_resetjp_4161_:
{
lean_object* v_fst_4164_; lean_object* v_fst_4165_; lean_object* v_snd_4166_; lean_object* v___x_4167_; uint64_t v___x_4168_; uint64_t v___y_4170_; uint64_t v___y_4211_; 
v_fst_4164_ = lean_ctor_get(v_a_4150_, 0);
v_fst_4165_ = lean_ctor_get(v_snd_4158_, 0);
v_snd_4166_ = lean_ctor_get(v_snd_4158_, 1);
v___x_4167_ = lean_array_get_size(v_buckets_4160_);
v___x_4168_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4164_);
if (lean_obj_tag(v_fst_4165_) == 0)
{
uint64_t v___x_4214_; 
v___x_4214_ = 11ULL;
v___y_4170_ = v___x_4214_;
goto v___jp_4169_;
}
else
{
lean_object* v_val_4215_; uint8_t v___x_4216_; 
v_val_4215_ = lean_ctor_get(v_fst_4165_, 0);
v___x_4216_ = lean_unbox(v_val_4215_);
if (v___x_4216_ == 0)
{
uint64_t v___x_4217_; 
v___x_4217_ = 13ULL;
v___y_4211_ = v___x_4217_;
goto v___jp_4210_;
}
else
{
uint64_t v___x_4218_; 
v___x_4218_ = 11ULL;
v___y_4211_ = v___x_4218_;
goto v___jp_4210_;
}
}
v___jp_4169_:
{
uint64_t v___x_4171_; uint64_t v___x_4172_; uint64_t v___x_4173_; uint64_t v___x_4174_; uint64_t v___x_4175_; uint64_t v_fold_4176_; uint64_t v___x_4177_; uint64_t v___x_4178_; uint64_t v___x_4179_; size_t v___x_4180_; size_t v___x_4181_; size_t v___x_4182_; size_t v___x_4183_; size_t v___x_4184_; lean_object* v_bkt_4185_; uint8_t v___x_4186_; 
v___x_4171_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4166_);
v___x_4172_ = lean_uint64_mix_hash(v___y_4170_, v___x_4171_);
v___x_4173_ = lean_uint64_mix_hash(v___x_4168_, v___x_4172_);
v___x_4174_ = 32ULL;
v___x_4175_ = lean_uint64_shift_right(v___x_4173_, v___x_4174_);
v_fold_4176_ = lean_uint64_xor(v___x_4173_, v___x_4175_);
v___x_4177_ = 16ULL;
v___x_4178_ = lean_uint64_shift_right(v_fold_4176_, v___x_4177_);
v___x_4179_ = lean_uint64_xor(v_fold_4176_, v___x_4178_);
v___x_4180_ = lean_uint64_to_usize(v___x_4179_);
v___x_4181_ = lean_usize_of_nat(v___x_4167_);
v___x_4182_ = ((size_t)1ULL);
v___x_4183_ = lean_usize_sub(v___x_4181_, v___x_4182_);
v___x_4184_ = lean_usize_land(v___x_4180_, v___x_4183_);
v_bkt_4185_ = lean_array_uget_borrowed(v_buckets_4160_, v___x_4184_);
v___x_4186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4150_, v_bkt_4185_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; lean_object* v_size_x27_4188_; lean_object* v___x_4189_; lean_object* v_buckets_x27_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; uint8_t v___x_4196_; 
v___x_4187_ = lean_unsigned_to_nat(1u);
v_size_x27_4188_ = lean_nat_add(v_size_4159_, v___x_4187_);
lean_dec(v_size_4159_);
lean_inc(v_bkt_4185_);
v___x_4189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4189_, 0, v_a_4150_);
lean_ctor_set(v___x_4189_, 1, v_a_4148_);
lean_ctor_set(v___x_4189_, 2, v_bkt_4185_);
v_buckets_x27_4190_ = lean_array_uset(v_buckets_4160_, v___x_4184_, v___x_4189_);
v___x_4191_ = lean_unsigned_to_nat(4u);
v___x_4192_ = lean_nat_mul(v_size_x27_4188_, v___x_4191_);
v___x_4193_ = lean_unsigned_to_nat(3u);
v___x_4194_ = lean_nat_div(v___x_4192_, v___x_4193_);
lean_dec(v___x_4192_);
v___x_4195_ = lean_array_get_size(v_buckets_x27_4190_);
v___x_4196_ = lean_nat_dec_le(v___x_4194_, v___x_4195_);
lean_dec(v___x_4194_);
if (v___x_4196_ == 0)
{
lean_object* v_val_4197_; lean_object* v___x_4199_; 
v_val_4197_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_buckets_x27_4190_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 1, v_val_4197_);
lean_ctor_set(v___x_4162_, 0, v_size_x27_4188_);
v___x_4199_ = v___x_4162_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_size_x27_4188_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_val_4197_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
else
{
lean_object* v___x_4202_; 
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 1, v_buckets_x27_4190_);
lean_ctor_set(v___x_4162_, 0, v_size_x27_4188_);
v___x_4202_ = v___x_4162_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_size_x27_4188_);
lean_ctor_set(v_reuseFailAlloc_4203_, 1, v_buckets_x27_4190_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
else
{
lean_object* v___x_4204_; lean_object* v_buckets_x27_4205_; lean_object* v_bkt_x27_4206_; uint8_t v___x_4207_; 
lean_inc(v_bkt_4185_);
lean_del_object(v___x_4162_);
v___x_4204_ = lean_box(0);
v_buckets_x27_4205_ = lean_array_uset(v_buckets_4160_, v___x_4184_, v___x_4204_);
lean_inc_ref(v_a_4150_);
v_bkt_x27_4206_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4148_, v_a_4150_, v_bkt_4185_);
v___x_4207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4150_, v_bkt_x27_4206_);
lean_dec_ref(v_a_4150_);
if (v___x_4207_ == 0)
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = lean_unsigned_to_nat(1u);
v___x_4209_ = lean_nat_sub(v_size_4159_, v___x_4208_);
lean_dec(v_size_4159_);
v___y_4152_ = v_bkt_x27_4206_;
v___y_4153_ = v___x_4184_;
v___y_4154_ = v_buckets_x27_4205_;
v___y_4155_ = v___x_4209_;
goto v___jp_4151_;
}
else
{
v___y_4152_ = v_bkt_x27_4206_;
v___y_4153_ = v___x_4184_;
v___y_4154_ = v_buckets_x27_4205_;
v___y_4155_ = v_size_4159_;
goto v___jp_4151_;
}
}
}
v___jp_4210_:
{
uint64_t v___x_4212_; uint64_t v___x_4213_; 
v___x_4212_ = 13ULL;
v___x_4213_ = lean_uint64_mix_hash(v___y_4211_, v___x_4212_);
v___y_4170_ = v___x_4213_;
goto v___jp_4169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4220_, lean_object* v_as_4221_, size_t v_sz_4222_, size_t v_i_4223_, lean_object* v_b_4224_){
_start:
{
uint8_t v___x_4225_; 
v___x_4225_ = lean_usize_dec_lt(v_i_4223_, v_sz_4222_);
if (v___x_4225_ == 0)
{
return v_b_4224_;
}
else
{
lean_object* v_a_4226_; lean_object* v___y_4228_; 
v_a_4226_ = lean_array_uget_borrowed(v_as_4221_, v_i_4223_);
if (v_allowSimultaneousBinderUse_4220_ == 0)
{
lean_object* v___x_4237_; 
v___x_4237_ = lean_box(0);
v___y_4228_ = v___x_4237_;
goto v___jp_4227_;
}
else
{
uint8_t v_isBinder_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v_isBinder_4238_ = lean_ctor_get_uint8(v_a_4226_, sizeof(void*)*6);
v___x_4239_ = lean_box(v_isBinder_4238_);
v___x_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
v___y_4228_ = v___x_4240_;
goto v___jp_4227_;
}
v___jp_4227_:
{
lean_object* v_ident_4229_; lean_object* v_range_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; size_t v___x_4234_; size_t v___x_4235_; 
v_ident_4229_ = lean_ctor_get(v_a_4226_, 0);
v_range_4230_ = lean_ctor_get(v_a_4226_, 2);
lean_inc_ref(v_range_4230_);
v___x_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___y_4228_);
lean_ctor_set(v___x_4231_, 1, v_range_4230_);
lean_inc_ref(v_ident_4229_);
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v_ident_4229_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
lean_inc(v_a_4226_);
v___x_4233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4226_, v_b_4224_, v___x_4232_);
v___x_4234_ = ((size_t)1ULL);
v___x_4235_ = lean_usize_add(v_i_4223_, v___x_4234_);
v_i_4223_ = v___x_4235_;
v_b_4224_ = v___x_4233_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4241_, lean_object* v_as_4242_, lean_object* v_sz_4243_, lean_object* v_i_4244_, lean_object* v_b_4245_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4246_; size_t v_sz_boxed_4247_; size_t v_i_boxed_4248_; lean_object* v_res_4249_; 
v_allowSimultaneousBinderUse_boxed_4246_ = lean_unbox(v_allowSimultaneousBinderUse_4241_);
v_sz_boxed_4247_ = lean_unbox_usize(v_sz_4243_);
lean_dec(v_sz_4243_);
v_i_boxed_4248_ = lean_unbox_usize(v_i_4244_);
lean_dec(v_i_4244_);
v_res_4249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4246_, v_as_4242_, v_sz_boxed_4247_, v_i_boxed_4248_, v_b_4245_);
lean_dec_ref(v_as_4242_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4250_, lean_object* v_x_4251_){
_start:
{
if (lean_obj_tag(v_x_4251_) == 0)
{
return v_x_4250_;
}
else
{
lean_object* v_value_4252_; lean_object* v_tail_4253_; lean_object* v___x_4254_; 
v_value_4252_ = lean_ctor_get(v_x_4251_, 1);
lean_inc(v_value_4252_);
v_tail_4253_ = lean_ctor_get(v_x_4251_, 2);
lean_inc(v_tail_4253_);
lean_dec_ref(v_x_4251_);
v___x_4254_ = lean_array_push(v_x_4250_, v_value_4252_);
v_x_4250_ = v___x_4254_;
v_x_4251_ = v_tail_4253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4256_, size_t v_i_4257_, size_t v_stop_4258_, lean_object* v_b_4259_){
_start:
{
uint8_t v___x_4260_; 
v___x_4260_ = lean_usize_dec_eq(v_i_4257_, v_stop_4258_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; lean_object* v___x_4262_; size_t v___x_4263_; size_t v___x_4264_; 
v___x_4261_ = lean_array_uget_borrowed(v_as_4256_, v_i_4257_);
lean_inc(v___x_4261_);
v___x_4262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4259_, v___x_4261_);
v___x_4263_ = ((size_t)1ULL);
v___x_4264_ = lean_usize_add(v_i_4257_, v___x_4263_);
v_i_4257_ = v___x_4264_;
v_b_4259_ = v___x_4262_;
goto _start;
}
else
{
return v_b_4259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4266_, lean_object* v_i_4267_, lean_object* v_stop_4268_, lean_object* v_b_4269_){
_start:
{
size_t v_i_boxed_4270_; size_t v_stop_boxed_4271_; lean_object* v_res_4272_; 
v_i_boxed_4270_ = lean_unbox_usize(v_i_4267_);
lean_dec(v_i_4267_);
v_stop_boxed_4271_ = lean_unbox_usize(v_stop_4268_);
lean_dec(v_stop_4268_);
v_res_4272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4266_, v_i_boxed_4270_, v_stop_boxed_4271_, v_b_4269_);
lean_dec_ref(v_as_4266_);
return v_res_4272_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4273_ = lean_box(0);
v___x_4274_ = lean_unsigned_to_nat(16u);
v___x_4275_ = lean_mk_array(v___x_4274_, v___x_4273_);
return v___x_4275_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v_refsByIdAndRange_4278_; 
v___x_4276_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4277_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4278_, 0, v___x_4277_);
lean_ctor_set(v_refsByIdAndRange_4278_, 1, v___x_4276_);
return v_refsByIdAndRange_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4279_, uint8_t v_allowSimultaneousBinderUse_4280_){
_start:
{
lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4290_; lean_object* v___x_4297_; lean_object* v_refsByIdAndRange_4298_; size_t v_sz_4299_; size_t v___x_4300_; lean_object* v___x_4301_; lean_object* v_buckets_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; uint8_t v___x_4305_; 
v___x_4297_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4298_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4299_ = lean_array_size(v_refs_4279_);
v___x_4300_ = ((size_t)0ULL);
v___x_4301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4280_, v_refs_4279_, v_sz_4299_, v___x_4300_, v_refsByIdAndRange_4298_);
v_buckets_4302_ = lean_ctor_get(v___x_4301_, 1);
lean_inc_ref(v_buckets_4302_);
lean_dec_ref(v___x_4301_);
v___x_4303_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4304_ = lean_array_get_size(v_buckets_4302_);
v___x_4305_ = lean_nat_dec_lt(v___x_4297_, v___x_4304_);
if (v___x_4305_ == 0)
{
lean_dec_ref(v_buckets_4302_);
v___y_4290_ = v___x_4303_;
goto v___jp_4289_;
}
else
{
uint8_t v___x_4306_; 
v___x_4306_ = lean_nat_dec_le(v___x_4304_, v___x_4304_);
if (v___x_4306_ == 0)
{
if (v___x_4305_ == 0)
{
lean_dec_ref(v_buckets_4302_);
v___y_4290_ = v___x_4303_;
goto v___jp_4289_;
}
else
{
size_t v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = lean_usize_of_nat(v___x_4304_);
v___x_4308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4302_, v___x_4300_, v___x_4307_, v___x_4303_);
lean_dec_ref(v_buckets_4302_);
v___y_4290_ = v___x_4308_;
goto v___jp_4289_;
}
}
else
{
size_t v___x_4309_; lean_object* v___x_4310_; 
v___x_4309_ = lean_usize_of_nat(v___x_4304_);
v___x_4310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4302_, v___x_4300_, v___x_4309_, v___x_4303_);
lean_dec_ref(v_buckets_4302_);
v___y_4290_ = v___x_4310_;
goto v___jp_4289_;
}
}
v___jp_4281_:
{
uint8_t v___x_4286_; 
v___x_4286_ = lean_nat_dec_le(v___y_4285_, v___y_4284_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; 
lean_dec(v___y_4284_);
lean_inc(v___y_4285_);
v___x_4287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4283_, v___y_4282_, v___y_4285_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec(v___y_4283_);
return v___x_4287_;
}
else
{
lean_object* v___x_4288_; 
v___x_4288_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4283_, v___y_4282_, v___y_4285_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec(v___y_4283_);
return v___x_4288_;
}
}
v___jp_4289_:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; 
v___x_4291_ = lean_array_get_size(v___y_4290_);
v___x_4292_ = lean_unsigned_to_nat(0u);
v___x_4293_ = lean_nat_dec_eq(v___x_4291_, v___x_4292_);
if (v___x_4293_ == 0)
{
lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; 
v___x_4294_ = lean_unsigned_to_nat(1u);
v___x_4295_ = lean_nat_sub(v___x_4291_, v___x_4294_);
v___x_4296_ = lean_nat_dec_le(v___x_4292_, v___x_4295_);
if (v___x_4296_ == 0)
{
lean_inc(v___x_4295_);
v___y_4282_ = v___y_4290_;
v___y_4283_ = v___x_4291_;
v___y_4284_ = v___x_4295_;
v___y_4285_ = v___x_4295_;
goto v___jp_4281_;
}
else
{
v___y_4282_ = v___y_4290_;
v___y_4283_ = v___x_4291_;
v___y_4284_ = v___x_4295_;
v___y_4285_ = v___x_4292_;
goto v___jp_4281_;
}
}
else
{
return v___y_4290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object* v_refs_4311_, lean_object* v_allowSimultaneousBinderUse_4312_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4313_; lean_object* v_res_4314_; 
v_allowSimultaneousBinderUse_boxed_4313_ = lean_unbox(v_allowSimultaneousBinderUse_4312_);
v_res_4314_ = l_Lean_Server_dedupReferences(v_refs_4311_, v_allowSimultaneousBinderUse_boxed_4313_);
lean_dec_ref(v_refs_4311_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object* v_n_4315_, lean_object* v_as_4316_, lean_object* v_lo_4317_, lean_object* v_hi_4318_, lean_object* v_w_4319_, lean_object* v_hlo_4320_, lean_object* v_hhi_4321_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4315_, v_as_4316_, v_lo_4317_, v_hi_4318_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object* v_n_4323_, lean_object* v_as_4324_, lean_object* v_lo_4325_, lean_object* v_hi_4326_, lean_object* v_w_4327_, lean_object* v_hlo_4328_, lean_object* v_hhi_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(v_n_4323_, v_as_4324_, v_lo_4325_, v_hi_4326_, v_w_4327_, v_hlo_4328_, v_hhi_4329_);
lean_dec(v_hi_4326_);
lean_dec(v_n_4323_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(lean_object* v_n_4331_, lean_object* v_lo_4332_, lean_object* v_hi_4333_, lean_object* v_hhi_4334_, lean_object* v_pivot_4335_, lean_object* v_as_4336_, lean_object* v_i_4337_, lean_object* v_k_4338_, lean_object* v_ilo_4339_, lean_object* v_ik_4340_, lean_object* v_w_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_4333_, v_pivot_4335_, v_as_4336_, v_i_4337_, v_k_4338_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___boxed(lean_object* v_n_4343_, lean_object* v_lo_4344_, lean_object* v_hi_4345_, lean_object* v_hhi_4346_, lean_object* v_pivot_4347_, lean_object* v_as_4348_, lean_object* v_i_4349_, lean_object* v_k_4350_, lean_object* v_ilo_4351_, lean_object* v_ik_4352_, lean_object* v_w_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(v_n_4343_, v_lo_4344_, v_hi_4345_, v_hhi_4346_, v_pivot_4347_, v_as_4348_, v_i_4349_, v_k_4350_, v_ilo_4351_, v_ik_4352_, v_w_4353_);
lean_dec_ref(v_pivot_4347_);
lean_dec(v_hi_4345_);
lean_dec(v_lo_4344_);
lean_dec(v_n_4343_);
return v_res_4354_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object* v_00_u03b2_4355_, lean_object* v_a_4356_, lean_object* v_x_4357_){
_start:
{
uint8_t v___x_4358_; 
v___x_4358_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4356_, v_x_4357_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4359_, lean_object* v_a_4360_, lean_object* v_x_4361_){
_start:
{
uint8_t v_res_4362_; lean_object* v_r_4363_; 
v_res_4362_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(v_00_u03b2_4359_, v_a_4360_, v_x_4361_);
lean_dec(v_x_4361_);
lean_dec_ref(v_a_4360_);
v_r_4363_ = lean_box(v_res_4362_);
return v_r_4363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object* v_00_u03b2_4364_, lean_object* v_data_4365_){
_start:
{
lean_object* v___x_4366_; 
v___x_4366_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_data_4365_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4367_, lean_object* v_i_4368_, lean_object* v_source_4369_, lean_object* v_target_4370_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v_i_4368_, v_source_4369_, v_target_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4372_, lean_object* v_x_4373_, lean_object* v_x_4374_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_x_4373_, v_x_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object* v_as_4376_, size_t v_i_4377_, size_t v_stop_4378_, lean_object* v_b_4379_){
_start:
{
uint8_t v___x_4380_; 
v___x_4380_ = lean_usize_dec_eq(v_i_4377_, v_stop_4378_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; lean_object* v___x_4382_; size_t v___x_4383_; size_t v___x_4384_; 
v___x_4381_ = lean_array_uget_borrowed(v_as_4376_, v_i_4377_);
lean_inc(v___x_4381_);
v___x_4382_ = l_Lean_Server_ModuleRefs_addRef(v_b_4379_, v___x_4381_);
v___x_4383_ = ((size_t)1ULL);
v___x_4384_ = lean_usize_add(v_i_4377_, v___x_4383_);
v_i_4377_ = v___x_4384_;
v_b_4379_ = v___x_4382_;
goto _start;
}
else
{
return v_b_4379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object* v_as_4386_, lean_object* v_i_4387_, lean_object* v_stop_4388_, lean_object* v_b_4389_){
_start:
{
size_t v_i_boxed_4390_; size_t v_stop_boxed_4391_; lean_object* v_res_4392_; 
v_i_boxed_4390_ = lean_unbox_usize(v_i_4387_);
lean_dec(v_i_4387_);
v_stop_boxed_4391_ = lean_unbox_usize(v_stop_4388_);
lean_dec(v_stop_4388_);
v_res_4392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_as_4386_, v_i_boxed_4390_, v_stop_boxed_4391_, v_b_4389_);
lean_dec_ref(v_as_4386_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object* v_as_4393_, size_t v_i_4394_, size_t v_stop_4395_, lean_object* v_b_4396_){
_start:
{
lean_object* v___y_4398_; uint8_t v___x_4402_; 
v___x_4402_ = lean_usize_dec_eq(v_i_4394_, v_stop_4395_);
if (v___x_4402_ == 0)
{
lean_object* v___x_4403_; lean_object* v_ident_4404_; 
v___x_4403_ = lean_array_uget_borrowed(v_as_4393_, v_i_4394_);
v_ident_4404_ = lean_ctor_get(v___x_4403_, 0);
if (lean_obj_tag(v_ident_4404_) == 1)
{
v___y_4398_ = v_b_4396_;
goto v___jp_4397_;
}
else
{
lean_object* v___x_4405_; 
lean_inc(v___x_4403_);
v___x_4405_ = lean_array_push(v_b_4396_, v___x_4403_);
v___y_4398_ = v___x_4405_;
goto v___jp_4397_;
}
}
else
{
return v_b_4396_;
}
v___jp_4397_:
{
size_t v___x_4399_; size_t v___x_4400_; 
v___x_4399_ = ((size_t)1ULL);
v___x_4400_ = lean_usize_add(v_i_4394_, v___x_4399_);
v_i_4394_ = v___x_4400_;
v_b_4396_ = v___y_4398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object* v_as_4406_, lean_object* v_i_4407_, lean_object* v_stop_4408_, lean_object* v_b_4409_){
_start:
{
size_t v_i_boxed_4410_; size_t v_stop_boxed_4411_; lean_object* v_res_4412_; 
v_i_boxed_4410_ = lean_unbox_usize(v_i_4407_);
lean_dec(v_i_4407_);
v_stop_boxed_4411_ = lean_unbox_usize(v_stop_4408_);
lean_dec(v_stop_4408_);
v_res_4412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_as_4406_, v_i_boxed_4410_, v_stop_boxed_4411_, v_b_4409_);
lean_dec_ref(v_as_4406_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object* v_text_4413_, lean_object* v_trees_4414_, uint8_t v_localVars_4415_, uint8_t v_allowSimultaneousBinderUse_4416_){
_start:
{
lean_object* v_refs_4418_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v_refs_4432_; 
v___x_4430_ = l_Lean_Server_findReferences(v_text_4413_, v_trees_4414_);
v___x_4431_ = l_Lean_Server_combineIdents(v_trees_4414_, v___x_4430_);
lean_dec_ref(v___x_4430_);
v_refs_4432_ = l_Lean_Server_dedupReferences(v___x_4431_, v_allowSimultaneousBinderUse_4416_);
lean_dec_ref(v___x_4431_);
if (v_localVars_4415_ == 0)
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; 
v___x_4433_ = lean_unsigned_to_nat(0u);
v___x_4434_ = lean_array_get_size(v_refs_4432_);
v___x_4435_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4436_ = lean_nat_dec_lt(v___x_4433_, v___x_4434_);
if (v___x_4436_ == 0)
{
lean_dec_ref(v_refs_4432_);
v_refs_4418_ = v___x_4435_;
goto v___jp_4417_;
}
else
{
uint8_t v___x_4437_; 
v___x_4437_ = lean_nat_dec_le(v___x_4434_, v___x_4434_);
if (v___x_4437_ == 0)
{
if (v___x_4436_ == 0)
{
lean_dec_ref(v_refs_4432_);
v_refs_4418_ = v___x_4435_;
goto v___jp_4417_;
}
else
{
size_t v___x_4438_; size_t v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = ((size_t)0ULL);
v___x_4439_ = lean_usize_of_nat(v___x_4434_);
v___x_4440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4432_, v___x_4438_, v___x_4439_, v___x_4435_);
lean_dec_ref(v_refs_4432_);
v_refs_4418_ = v___x_4440_;
goto v___jp_4417_;
}
}
else
{
size_t v___x_4441_; size_t v___x_4442_; lean_object* v___x_4443_; 
v___x_4441_ = ((size_t)0ULL);
v___x_4442_ = lean_usize_of_nat(v___x_4434_);
v___x_4443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4432_, v___x_4441_, v___x_4442_, v___x_4435_);
lean_dec_ref(v_refs_4432_);
v_refs_4418_ = v___x_4443_;
goto v___jp_4417_;
}
}
}
else
{
v_refs_4418_ = v_refs_4432_;
goto v___jp_4417_;
}
v___jp_4417_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; uint8_t v___x_4422_; 
v___x_4419_ = lean_box(1);
v___x_4420_ = lean_unsigned_to_nat(0u);
v___x_4421_ = lean_array_get_size(v_refs_4418_);
v___x_4422_ = lean_nat_dec_lt(v___x_4420_, v___x_4421_);
if (v___x_4422_ == 0)
{
lean_dec_ref(v_refs_4418_);
return v___x_4419_;
}
else
{
uint8_t v___x_4423_; 
v___x_4423_ = lean_nat_dec_le(v___x_4421_, v___x_4421_);
if (v___x_4423_ == 0)
{
if (v___x_4422_ == 0)
{
lean_dec_ref(v_refs_4418_);
return v___x_4419_;
}
else
{
size_t v___x_4424_; size_t v___x_4425_; lean_object* v___x_4426_; 
v___x_4424_ = ((size_t)0ULL);
v___x_4425_ = lean_usize_of_nat(v___x_4421_);
v___x_4426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4418_, v___x_4424_, v___x_4425_, v___x_4419_);
lean_dec_ref(v_refs_4418_);
return v___x_4426_;
}
}
else
{
size_t v___x_4427_; size_t v___x_4428_; lean_object* v___x_4429_; 
v___x_4427_ = ((size_t)0ULL);
v___x_4428_ = lean_usize_of_nat(v___x_4421_);
v___x_4429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4418_, v___x_4427_, v___x_4428_, v___x_4419_);
lean_dec_ref(v_refs_4418_);
return v___x_4429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object* v_text_4444_, lean_object* v_trees_4445_, lean_object* v_localVars_4446_, lean_object* v_allowSimultaneousBinderUse_4447_){
_start:
{
uint8_t v_localVars_boxed_4448_; uint8_t v_allowSimultaneousBinderUse_boxed_4449_; lean_object* v_res_4450_; 
v_localVars_boxed_4448_ = lean_unbox(v_localVars_4446_);
v_allowSimultaneousBinderUse_boxed_4449_ = lean_unbox(v_allowSimultaneousBinderUse_4447_);
v_res_4450_ = l_Lean_Server_findModuleRefs(v_text_4444_, v_trees_4445_, v_localVars_boxed_4448_, v_allowSimultaneousBinderUse_boxed_4449_);
lean_dec_ref(v_trees_4445_);
return v_res_4450_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t v_a_4458_, uint8_t v_a_4459_){
_start:
{
switch(v_a_4458_)
{
case 0:
{
if (v_a_4459_ == 1)
{
uint8_t v___x_4460_; 
v___x_4460_ = 2;
return v___x_4460_;
}
else
{
return v_a_4459_;
}
}
case 1:
{
if (v_a_4459_ == 0)
{
uint8_t v___x_4461_; 
v___x_4461_ = 2;
return v___x_4461_;
}
else
{
return v_a_4459_;
}
}
default: 
{
return v_a_4458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object* v_a_4462_, lean_object* v_a_4463_){
_start:
{
uint8_t v_a_46__boxed_4464_; uint8_t v_a_47__boxed_4465_; uint8_t v_res_4466_; lean_object* v_r_4467_; 
v_a_46__boxed_4464_ = lean_unbox(v_a_4462_);
v_a_47__boxed_4465_ = lean_unbox(v_a_4463_);
v_res_4466_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_a_46__boxed_4464_, v_a_47__boxed_4465_);
v_r_4467_ = lean_box(v_res_4466_);
return v_r_4467_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object* v_upperBound_4468_, lean_object* v_identicalImports_4469_, lean_object* v_a_4470_, lean_object* v_b_4471_){
_start:
{
uint8_t v___x_4472_; 
v___x_4472_ = lean_nat_dec_lt(v_a_4470_, v_upperBound_4468_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; 
lean_dec(v_a_4470_);
v___x_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4473_, 0, v_b_4471_);
return v___x_4473_;
}
else
{
lean_object* v_module_4474_; lean_object* v_uri_4475_; uint8_t v_isAll_4476_; uint8_t v_isPrivate_4477_; uint8_t v_metaKind_4478_; lean_object* v___x_4479_; lean_object* v_module_4480_; lean_object* v_uri_4481_; uint8_t v_isAll_4482_; uint8_t v_isPrivate_4483_; uint8_t v_metaKind_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4504_; 
v_module_4474_ = lean_ctor_get(v_b_4471_, 0);
lean_inc(v_module_4474_);
v_uri_4475_ = lean_ctor_get(v_b_4471_, 1);
lean_inc_ref(v_uri_4475_);
v_isAll_4476_ = lean_ctor_get_uint8(v_b_4471_, sizeof(void*)*2);
v_isPrivate_4477_ = lean_ctor_get_uint8(v_b_4471_, sizeof(void*)*2 + 1);
v_metaKind_4478_ = lean_ctor_get_uint8(v_b_4471_, sizeof(void*)*2 + 2);
lean_dec_ref(v_b_4471_);
v___x_4479_ = lean_array_fget(v_identicalImports_4469_, v_a_4470_);
v_module_4480_ = lean_ctor_get(v___x_4479_, 0);
v_uri_4481_ = lean_ctor_get(v___x_4479_, 1);
v_isAll_4482_ = lean_ctor_get_uint8(v___x_4479_, sizeof(void*)*2);
v_isPrivate_4483_ = lean_ctor_get_uint8(v___x_4479_, sizeof(void*)*2 + 1);
v_metaKind_4484_ = lean_ctor_get_uint8(v___x_4479_, sizeof(void*)*2 + 2);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4486_ = v___x_4479_;
v_isShared_4487_ = v_isSharedCheck_4504_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_uri_4481_);
lean_inc(v_module_4480_);
lean_dec(v___x_4479_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4504_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
uint8_t v___y_4489_; uint8_t v___y_4490_; uint8_t v___y_4499_; uint8_t v___x_4500_; 
v___x_4500_ = lean_name_eq(v_module_4474_, v_module_4480_);
lean_dec(v_module_4480_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4501_; 
lean_del_object(v___x_4486_);
lean_dec_ref(v_uri_4481_);
lean_dec_ref(v_uri_4475_);
lean_dec(v_module_4474_);
lean_dec(v_a_4470_);
v___x_4501_ = lean_box(0);
return v___x_4501_;
}
else
{
uint8_t v___x_4502_; 
v___x_4502_ = lean_string_dec_eq(v_uri_4475_, v_uri_4481_);
lean_dec_ref(v_uri_4481_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4503_; 
lean_del_object(v___x_4486_);
lean_dec_ref(v_uri_4475_);
lean_dec(v_module_4474_);
lean_dec(v_a_4470_);
v___x_4503_ = lean_box(0);
return v___x_4503_;
}
else
{
if (v_isAll_4476_ == 0)
{
v___y_4499_ = v_isAll_4482_;
goto v___jp_4498_;
}
else
{
v___y_4499_ = v_isAll_4476_;
goto v___jp_4498_;
}
}
}
v___jp_4488_:
{
uint8_t v___x_4491_; lean_object* v___x_4493_; 
v___x_4491_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_metaKind_4478_, v_metaKind_4484_);
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 1, v_uri_4475_);
lean_ctor_set(v___x_4486_, 0, v_module_4474_);
v___x_4493_ = v___x_4486_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_module_4474_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_uri_4475_);
v___x_4493_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
lean_ctor_set_uint8(v___x_4493_, sizeof(void*)*2, v___y_4489_);
lean_ctor_set_uint8(v___x_4493_, sizeof(void*)*2 + 1, v___y_4490_);
lean_ctor_set_uint8(v___x_4493_, sizeof(void*)*2 + 2, v___x_4491_);
v___x_4494_ = lean_unsigned_to_nat(1u);
v___x_4495_ = lean_nat_add(v_a_4470_, v___x_4494_);
lean_dec(v_a_4470_);
v_a_4470_ = v___x_4495_;
v_b_4471_ = v___x_4493_;
goto _start;
}
}
v___jp_4498_:
{
if (v_isPrivate_4477_ == 0)
{
v___y_4489_ = v___y_4499_;
v___y_4490_ = v_isPrivate_4477_;
goto v___jp_4488_;
}
else
{
v___y_4489_ = v___y_4499_;
v___y_4490_ = v_isPrivate_4483_;
goto v___jp_4488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_4505_, lean_object* v_identicalImports_4506_, lean_object* v_a_4507_, lean_object* v_b_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4505_, v_identicalImports_4506_, v_a_4507_, v_b_4508_);
lean_dec_ref(v_identicalImports_4506_);
lean_dec(v_upperBound_4505_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object* v_identicalImports_4510_){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4511_ = lean_unsigned_to_nat(0u);
v___x_4512_ = lean_array_get_size(v_identicalImports_4510_);
v___x_4513_ = lean_nat_dec_lt(v___x_4511_, v___x_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; 
v___x_4514_ = lean_box(0);
return v___x_4514_;
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4515_ = lean_unsigned_to_nat(1u);
v___x_4516_ = lean_array_fget_borrowed(v_identicalImports_4510_, v___x_4511_);
lean_inc(v___x_4516_);
v___x_4517_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v___x_4512_, v_identicalImports_4510_, v___x_4515_, v___x_4516_);
return v___x_4517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object* v_identicalImports_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_identicalImports_4518_);
lean_dec_ref(v_identicalImports_4518_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object* v_upperBound_4520_, lean_object* v_identicalImports_4521_, lean_object* v_inst_4522_, lean_object* v_R_4523_, lean_object* v_a_4524_, lean_object* v_b_4525_, lean_object* v_c_4526_){
_start:
{
lean_object* v___x_4527_; 
v___x_4527_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4520_, v_identicalImports_4521_, v_a_4524_, v_b_4525_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object* v_upperBound_4528_, lean_object* v_identicalImports_4529_, lean_object* v_inst_4530_, lean_object* v_R_4531_, lean_object* v_a_4532_, lean_object* v_b_4533_, lean_object* v_c_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(v_upperBound_4528_, v_identicalImports_4529_, v_inst_4530_, v_R_4531_, v_a_4532_, v_b_4533_, v_c_4534_);
lean_dec_ref(v_identicalImports_4529_);
lean_dec(v_upperBound_4528_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object* v_x_4542_){
_start:
{
lean_object* v_module_4543_; 
v_module_4543_ = lean_ctor_get(v_x_4542_, 0);
lean_inc(v_module_4543_);
return v_module_4543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object* v_x_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_Server_DirectImports_convertImportInfos___lam__0(v_x_4544_);
lean_dec_ref(v_x_4544_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object* v_x_4546_, lean_object* v_x_4547_){
_start:
{
if (lean_obj_tag(v_x_4547_) == 0)
{
return v_x_4546_;
}
else
{
lean_object* v_key_4548_; lean_object* v_value_4549_; lean_object* v_tail_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v_key_4548_ = lean_ctor_get(v_x_4547_, 0);
v_value_4549_ = lean_ctor_get(v_x_4547_, 1);
v_tail_4550_ = lean_ctor_get(v_x_4547_, 2);
lean_inc(v_value_4549_);
lean_inc(v_key_4548_);
v___x_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4551_, 0, v_key_4548_);
lean_ctor_set(v___x_4551_, 1, v_value_4549_);
v___x_4552_ = lean_array_push(v_x_4546_, v___x_4551_);
v_x_4546_ = v___x_4552_;
v_x_4547_ = v_tail_4550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object* v_x_4554_, lean_object* v_x_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_x_4554_, v_x_4555_);
lean_dec(v_x_4555_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object* v_as_4557_, size_t v_i_4558_, size_t v_stop_4559_, lean_object* v_b_4560_){
_start:
{
uint8_t v___x_4561_; 
v___x_4561_ = lean_usize_dec_eq(v_i_4558_, v_stop_4559_);
if (v___x_4561_ == 0)
{
lean_object* v___x_4562_; lean_object* v___x_4563_; size_t v___x_4564_; size_t v___x_4565_; 
v___x_4562_ = lean_array_uget_borrowed(v_as_4557_, v_i_4558_);
v___x_4563_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_b_4560_, v___x_4562_);
v___x_4564_ = ((size_t)1ULL);
v___x_4565_ = lean_usize_add(v_i_4558_, v___x_4564_);
v_i_4558_ = v___x_4565_;
v_b_4560_ = v___x_4563_;
goto _start;
}
else
{
return v_b_4560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object* v_as_4567_, lean_object* v_i_4568_, lean_object* v_stop_4569_, lean_object* v_b_4570_){
_start:
{
size_t v_i_boxed_4571_; size_t v_stop_boxed_4572_; lean_object* v_res_4573_; 
v_i_boxed_4571_ = lean_unbox_usize(v_i_4568_);
lean_dec(v_i_4568_);
v_stop_boxed_4572_ = lean_unbox_usize(v_stop_4569_);
lean_dec(v_stop_4569_);
v_res_4573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_as_4567_, v_i_boxed_4571_, v_stop_boxed_4572_, v_b_4570_);
lean_dec_ref(v_as_4567_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object* v_as_4574_, size_t v_i_4575_, size_t v_stop_4576_, lean_object* v_b_4577_){
_start:
{
uint8_t v___x_4579_; 
v___x_4579_ = lean_usize_dec_eq(v_i_4575_, v_stop_4576_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; lean_object* v_module_4581_; uint8_t v_isPrivate_4582_; uint8_t v_isAll_4583_; uint8_t v_isMeta_4584_; lean_object* v_module_4585_; lean_object* v___x_4586_; 
v___x_4580_ = lean_array_uget_borrowed(v_as_4574_, v_i_4575_);
v_module_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isPrivate_4582_ = lean_ctor_get_uint8(v___x_4580_, sizeof(void*)*1);
v_isAll_4583_ = lean_ctor_get_uint8(v___x_4580_, sizeof(void*)*1 + 1);
v_isMeta_4584_ = lean_ctor_get_uint8(v___x_4580_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4581_);
v_module_4585_ = l_String_toName(v_module_4581_);
lean_inc(v_module_4585_);
v___x_4586_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4585_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v_a_4589_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref(v___x_4586_);
if (lean_obj_tag(v_a_4587_) == 1)
{
lean_object* v_val_4593_; uint8_t v___y_4595_; 
v_val_4593_ = lean_ctor_get(v_a_4587_, 0);
lean_inc(v_val_4593_);
lean_dec_ref(v_a_4587_);
if (v_isMeta_4584_ == 0)
{
uint8_t v___x_4598_; 
v___x_4598_ = 0;
v___y_4595_ = v___x_4598_;
goto v___jp_4594_;
}
else
{
uint8_t v___x_4599_; 
v___x_4599_ = 1;
v___y_4595_ = v___x_4599_;
goto v___jp_4594_;
}
v___jp_4594_:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4596_, 0, v_module_4585_);
lean_ctor_set(v___x_4596_, 1, v_val_4593_);
lean_ctor_set_uint8(v___x_4596_, sizeof(void*)*2, v_isAll_4583_);
lean_ctor_set_uint8(v___x_4596_, sizeof(void*)*2 + 1, v_isPrivate_4582_);
lean_ctor_set_uint8(v___x_4596_, sizeof(void*)*2 + 2, v___y_4595_);
v___x_4597_ = lean_array_push(v_b_4577_, v___x_4596_);
v_a_4589_ = v___x_4597_;
goto v___jp_4588_;
}
}
else
{
lean_dec(v_a_4587_);
lean_dec(v_module_4585_);
v_a_4589_ = v_b_4577_;
goto v___jp_4588_;
}
v___jp_4588_:
{
size_t v___x_4590_; size_t v___x_4591_; 
v___x_4590_ = ((size_t)1ULL);
v___x_4591_ = lean_usize_add(v_i_4575_, v___x_4590_);
v_i_4575_ = v___x_4591_;
v_b_4577_ = v_a_4589_;
goto _start;
}
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_dec(v_module_4585_);
lean_dec_ref(v_b_4577_);
v_a_4600_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4586_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4586_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
else
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4608_, 0, v_b_4577_);
return v___x_4608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object* v_as_4609_, lean_object* v_i_4610_, lean_object* v_stop_4611_, lean_object* v_b_4612_, lean_object* v___y_4613_){
_start:
{
size_t v_i_boxed_4614_; size_t v_stop_boxed_4615_; lean_object* v_res_4616_; 
v_i_boxed_4614_ = lean_unbox_usize(v_i_4610_);
lean_dec(v_i_4610_);
v_stop_boxed_4615_ = lean_unbox_usize(v_stop_4611_);
lean_dec(v_stop_4611_);
v_res_4616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4609_, v_i_boxed_4614_, v_stop_boxed_4615_, v_b_4612_);
lean_dec_ref(v_as_4609_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object* v_as_4617_, lean_object* v_start_4618_, lean_object* v_stop_4619_){
_start:
{
lean_object* v___x_4621_; uint8_t v___x_4622_; 
v___x_4621_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_4622_ = lean_nat_dec_lt(v_start_4618_, v_stop_4619_);
if (v___x_4622_ == 0)
{
lean_object* v___x_4623_; 
v___x_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4621_);
return v___x_4623_;
}
else
{
lean_object* v___x_4624_; uint8_t v___x_4625_; 
v___x_4624_ = lean_array_get_size(v_as_4617_);
v___x_4625_ = lean_nat_dec_le(v_stop_4619_, v___x_4624_);
if (v___x_4625_ == 0)
{
uint8_t v___x_4626_; 
v___x_4626_ = lean_nat_dec_lt(v_start_4618_, v___x_4624_);
if (v___x_4626_ == 0)
{
lean_object* v___x_4627_; 
v___x_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4621_);
return v___x_4627_;
}
else
{
size_t v___x_4628_; size_t v___x_4629_; lean_object* v___x_4630_; 
v___x_4628_ = lean_usize_of_nat(v_start_4618_);
v___x_4629_ = lean_usize_of_nat(v___x_4624_);
v___x_4630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4617_, v___x_4628_, v___x_4629_, v___x_4621_);
return v___x_4630_;
}
}
else
{
size_t v___x_4631_; size_t v___x_4632_; lean_object* v___x_4633_; 
v___x_4631_ = lean_usize_of_nat(v_start_4618_);
v___x_4632_ = lean_usize_of_nat(v_stop_4619_);
v___x_4633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4617_, v___x_4631_, v___x_4632_, v___x_4621_);
return v___x_4633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object* v_as_4634_, lean_object* v_start_4635_, lean_object* v_stop_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v_res_4638_; 
v_res_4638_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_as_4634_, v_start_4635_, v_stop_4636_);
lean_dec(v_stop_4636_);
lean_dec(v_start_4635_);
lean_dec_ref(v_as_4634_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object* v_k_4639_, lean_object* v_v_4640_, lean_object* v_t_4641_){
_start:
{
if (lean_obj_tag(v_t_4641_) == 0)
{
lean_object* v_size_4642_; lean_object* v_k_4643_; lean_object* v_v_4644_; lean_object* v_l_4645_; lean_object* v_r_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4926_; 
v_size_4642_ = lean_ctor_get(v_t_4641_, 0);
v_k_4643_ = lean_ctor_get(v_t_4641_, 1);
v_v_4644_ = lean_ctor_get(v_t_4641_, 2);
v_l_4645_ = lean_ctor_get(v_t_4641_, 3);
v_r_4646_ = lean_ctor_get(v_t_4641_, 4);
v_isSharedCheck_4926_ = !lean_is_exclusive(v_t_4641_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4648_ = v_t_4641_;
v_isShared_4649_ = v_isSharedCheck_4926_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_r_4646_);
lean_inc(v_l_4645_);
lean_inc(v_v_4644_);
lean_inc(v_k_4643_);
lean_inc(v_size_4642_);
lean_dec(v_t_4641_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4926_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
uint8_t v___x_4650_; 
v___x_4650_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4639_, v_k_4643_);
switch(v___x_4650_)
{
case 0:
{
lean_object* v_impl_4651_; lean_object* v___x_4652_; 
lean_dec(v_size_4642_);
v_impl_4651_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4639_, v_v_4640_, v_l_4645_);
v___x_4652_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4646_) == 0)
{
lean_object* v_size_4653_; lean_object* v_size_4654_; lean_object* v_k_4655_; lean_object* v_v_4656_; lean_object* v_l_4657_; lean_object* v_r_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v_size_4653_ = lean_ctor_get(v_r_4646_, 0);
v_size_4654_ = lean_ctor_get(v_impl_4651_, 0);
lean_inc(v_size_4654_);
v_k_4655_ = lean_ctor_get(v_impl_4651_, 1);
lean_inc(v_k_4655_);
v_v_4656_ = lean_ctor_get(v_impl_4651_, 2);
lean_inc(v_v_4656_);
v_l_4657_ = lean_ctor_get(v_impl_4651_, 3);
lean_inc(v_l_4657_);
v_r_4658_ = lean_ctor_get(v_impl_4651_, 4);
lean_inc(v_r_4658_);
v___x_4659_ = lean_unsigned_to_nat(3u);
v___x_4660_ = lean_nat_mul(v___x_4659_, v_size_4653_);
v___x_4661_ = lean_nat_dec_lt(v___x_4660_, v_size_4654_);
lean_dec(v___x_4660_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4665_; 
lean_dec(v_r_4658_);
lean_dec(v_l_4657_);
lean_dec(v_v_4656_);
lean_dec(v_k_4655_);
v___x_4662_ = lean_nat_add(v___x_4652_, v_size_4654_);
lean_dec(v_size_4654_);
v___x_4663_ = lean_nat_add(v___x_4662_, v_size_4653_);
lean_dec(v___x_4662_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 3, v_impl_4651_);
lean_ctor_set(v___x_4648_, 0, v___x_4663_);
v___x_4665_ = v___x_4648_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4663_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4666_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4666_, 3, v_impl_4651_);
lean_ctor_set(v_reuseFailAlloc_4666_, 4, v_r_4646_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
else
{
lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4732_; 
v_isSharedCheck_4732_ = !lean_is_exclusive(v_impl_4651_);
if (v_isSharedCheck_4732_ == 0)
{
lean_object* v_unused_4733_; lean_object* v_unused_4734_; lean_object* v_unused_4735_; lean_object* v_unused_4736_; lean_object* v_unused_4737_; 
v_unused_4733_ = lean_ctor_get(v_impl_4651_, 4);
lean_dec(v_unused_4733_);
v_unused_4734_ = lean_ctor_get(v_impl_4651_, 3);
lean_dec(v_unused_4734_);
v_unused_4735_ = lean_ctor_get(v_impl_4651_, 2);
lean_dec(v_unused_4735_);
v_unused_4736_ = lean_ctor_get(v_impl_4651_, 1);
lean_dec(v_unused_4736_);
v_unused_4737_ = lean_ctor_get(v_impl_4651_, 0);
lean_dec(v_unused_4737_);
v___x_4668_ = v_impl_4651_;
v_isShared_4669_ = v_isSharedCheck_4732_;
goto v_resetjp_4667_;
}
else
{
lean_dec(v_impl_4651_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4732_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v_size_4670_; lean_object* v_size_4671_; lean_object* v_k_4672_; lean_object* v_v_4673_; lean_object* v_l_4674_; lean_object* v_r_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v_size_4670_ = lean_ctor_get(v_l_4657_, 0);
v_size_4671_ = lean_ctor_get(v_r_4658_, 0);
v_k_4672_ = lean_ctor_get(v_r_4658_, 1);
v_v_4673_ = lean_ctor_get(v_r_4658_, 2);
v_l_4674_ = lean_ctor_get(v_r_4658_, 3);
v_r_4675_ = lean_ctor_get(v_r_4658_, 4);
v___x_4676_ = lean_unsigned_to_nat(2u);
v___x_4677_ = lean_nat_mul(v___x_4676_, v_size_4670_);
v___x_4678_ = lean_nat_dec_lt(v_size_4671_, v___x_4677_);
lean_dec(v___x_4677_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4707_; 
lean_inc(v_r_4675_);
lean_inc(v_l_4674_);
lean_inc(v_v_4673_);
lean_inc(v_k_4672_);
v_isSharedCheck_4707_ = !lean_is_exclusive(v_r_4658_);
if (v_isSharedCheck_4707_ == 0)
{
lean_object* v_unused_4708_; lean_object* v_unused_4709_; lean_object* v_unused_4710_; lean_object* v_unused_4711_; lean_object* v_unused_4712_; 
v_unused_4708_ = lean_ctor_get(v_r_4658_, 4);
lean_dec(v_unused_4708_);
v_unused_4709_ = lean_ctor_get(v_r_4658_, 3);
lean_dec(v_unused_4709_);
v_unused_4710_ = lean_ctor_get(v_r_4658_, 2);
lean_dec(v_unused_4710_);
v_unused_4711_ = lean_ctor_get(v_r_4658_, 1);
lean_dec(v_unused_4711_);
v_unused_4712_ = lean_ctor_get(v_r_4658_, 0);
lean_dec(v_unused_4712_);
v___x_4680_ = v_r_4658_;
v_isShared_4681_ = v_isSharedCheck_4707_;
goto v_resetjp_4679_;
}
else
{
lean_dec(v_r_4658_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4707_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___x_4695_; lean_object* v___y_4697_; 
v___x_4682_ = lean_nat_add(v___x_4652_, v_size_4654_);
lean_dec(v_size_4654_);
v___x_4683_ = lean_nat_add(v___x_4682_, v_size_4653_);
lean_dec(v___x_4682_);
v___x_4695_ = lean_nat_add(v___x_4652_, v_size_4670_);
if (lean_obj_tag(v_l_4674_) == 0)
{
lean_object* v_size_4705_; 
v_size_4705_ = lean_ctor_get(v_l_4674_, 0);
lean_inc(v_size_4705_);
v___y_4697_ = v_size_4705_;
goto v___jp_4696_;
}
else
{
lean_object* v___x_4706_; 
v___x_4706_ = lean_unsigned_to_nat(0u);
v___y_4697_ = v___x_4706_;
goto v___jp_4696_;
}
v___jp_4684_:
{
lean_object* v___x_4688_; lean_object* v___x_4690_; 
v___x_4688_ = lean_nat_add(v___y_4685_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec(v___y_4685_);
if (v_isShared_4681_ == 0)
{
lean_ctor_set(v___x_4680_, 4, v_r_4646_);
lean_ctor_set(v___x_4680_, 3, v_r_4675_);
lean_ctor_set(v___x_4680_, 2, v_v_4644_);
lean_ctor_set(v___x_4680_, 1, v_k_4643_);
lean_ctor_set(v___x_4680_, 0, v___x_4688_);
v___x_4690_ = v___x_4680_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4688_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4694_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4694_, 3, v_r_4675_);
lean_ctor_set(v_reuseFailAlloc_4694_, 4, v_r_4646_);
v___x_4690_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
lean_object* v___x_4692_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 4, v___x_4690_);
lean_ctor_set(v___x_4668_, 3, v___y_4686_);
lean_ctor_set(v___x_4668_, 2, v_v_4673_);
lean_ctor_set(v___x_4668_, 1, v_k_4672_);
lean_ctor_set(v___x_4668_, 0, v___x_4683_);
v___x_4692_ = v___x_4668_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4683_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4693_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4693_, 3, v___y_4686_);
lean_ctor_set(v_reuseFailAlloc_4693_, 4, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
v___jp_4696_:
{
lean_object* v___x_4698_; lean_object* v___x_4700_; 
v___x_4698_ = lean_nat_add(v___x_4695_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec(v___x_4695_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_l_4674_);
lean_ctor_set(v___x_4648_, 3, v_l_4657_);
lean_ctor_set(v___x_4648_, 2, v_v_4656_);
lean_ctor_set(v___x_4648_, 1, v_k_4655_);
lean_ctor_set(v___x_4648_, 0, v___x_4698_);
v___x_4700_ = v___x_4648_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4704_, 1, v_k_4655_);
lean_ctor_set(v_reuseFailAlloc_4704_, 2, v_v_4656_);
lean_ctor_set(v_reuseFailAlloc_4704_, 3, v_l_4657_);
lean_ctor_set(v_reuseFailAlloc_4704_, 4, v_l_4674_);
v___x_4700_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
lean_object* v___x_4701_; 
v___x_4701_ = lean_nat_add(v___x_4652_, v_size_4653_);
if (lean_obj_tag(v_r_4675_) == 0)
{
lean_object* v_size_4702_; 
v_size_4702_ = lean_ctor_get(v_r_4675_, 0);
lean_inc(v_size_4702_);
v___y_4685_ = v___x_4701_;
v___y_4686_ = v___x_4700_;
v___y_4687_ = v_size_4702_;
goto v___jp_4684_;
}
else
{
lean_object* v___x_4703_; 
v___x_4703_ = lean_unsigned_to_nat(0u);
v___y_4685_ = v___x_4701_;
v___y_4686_ = v___x_4700_;
v___y_4687_ = v___x_4703_;
goto v___jp_4684_;
}
}
}
}
}
else
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4718_; 
lean_del_object(v___x_4648_);
v___x_4713_ = lean_nat_add(v___x_4652_, v_size_4654_);
lean_dec(v_size_4654_);
v___x_4714_ = lean_nat_add(v___x_4713_, v_size_4653_);
lean_dec(v___x_4713_);
v___x_4715_ = lean_nat_add(v___x_4652_, v_size_4653_);
v___x_4716_ = lean_nat_add(v___x_4715_, v_size_4671_);
lean_dec(v___x_4715_);
lean_inc_ref(v_r_4646_);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 4, v_r_4646_);
lean_ctor_set(v___x_4668_, 3, v_r_4658_);
lean_ctor_set(v___x_4668_, 2, v_v_4644_);
lean_ctor_set(v___x_4668_, 1, v_k_4643_);
lean_ctor_set(v___x_4668_, 0, v___x_4716_);
v___x_4718_ = v___x_4668_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4716_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4731_, 3, v_r_4658_);
lean_ctor_set(v_reuseFailAlloc_4731_, 4, v_r_4646_);
v___x_4718_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
v_isSharedCheck_4725_ = !lean_is_exclusive(v_r_4646_);
if (v_isSharedCheck_4725_ == 0)
{
lean_object* v_unused_4726_; lean_object* v_unused_4727_; lean_object* v_unused_4728_; lean_object* v_unused_4729_; lean_object* v_unused_4730_; 
v_unused_4726_ = lean_ctor_get(v_r_4646_, 4);
lean_dec(v_unused_4726_);
v_unused_4727_ = lean_ctor_get(v_r_4646_, 3);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_r_4646_, 2);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_r_4646_, 1);
lean_dec(v_unused_4729_);
v_unused_4730_ = lean_ctor_get(v_r_4646_, 0);
lean_dec(v_unused_4730_);
v___x_4720_ = v_r_4646_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_dec(v_r_4646_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 4, v___x_4718_);
lean_ctor_set(v___x_4720_, 3, v_l_4657_);
lean_ctor_set(v___x_4720_, 2, v_v_4656_);
lean_ctor_set(v___x_4720_, 1, v_k_4655_);
lean_ctor_set(v___x_4720_, 0, v___x_4714_);
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v_k_4655_);
lean_ctor_set(v_reuseFailAlloc_4724_, 2, v_v_4656_);
lean_ctor_set(v_reuseFailAlloc_4724_, 3, v_l_4657_);
lean_ctor_set(v_reuseFailAlloc_4724_, 4, v___x_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4738_; 
v_l_4738_ = lean_ctor_get(v_impl_4651_, 3);
lean_inc(v_l_4738_);
if (lean_obj_tag(v_l_4738_) == 0)
{
lean_object* v_r_4739_; lean_object* v_k_4740_; lean_object* v_v_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4752_; 
v_r_4739_ = lean_ctor_get(v_impl_4651_, 4);
v_k_4740_ = lean_ctor_get(v_impl_4651_, 1);
v_v_4741_ = lean_ctor_get(v_impl_4651_, 2);
v_isSharedCheck_4752_ = !lean_is_exclusive(v_impl_4651_);
if (v_isSharedCheck_4752_ == 0)
{
lean_object* v_unused_4753_; lean_object* v_unused_4754_; 
v_unused_4753_ = lean_ctor_get(v_impl_4651_, 3);
lean_dec(v_unused_4753_);
v_unused_4754_ = lean_ctor_get(v_impl_4651_, 0);
lean_dec(v_unused_4754_);
v___x_4743_ = v_impl_4651_;
v_isShared_4744_ = v_isSharedCheck_4752_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_r_4739_);
lean_inc(v_v_4741_);
lean_inc(v_k_4740_);
lean_dec(v_impl_4651_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4752_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4747_; 
v___x_4745_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4739_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 3, v_r_4739_);
lean_ctor_set(v___x_4743_, 2, v_v_4644_);
lean_ctor_set(v___x_4743_, 1, v_k_4643_);
lean_ctor_set(v___x_4743_, 0, v___x_4652_);
v___x_4747_ = v___x_4743_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4751_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4751_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4751_, 3, v_r_4739_);
lean_ctor_set(v_reuseFailAlloc_4751_, 4, v_r_4739_);
v___x_4747_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4749_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v___x_4747_);
lean_ctor_set(v___x_4648_, 3, v_l_4738_);
lean_ctor_set(v___x_4648_, 2, v_v_4741_);
lean_ctor_set(v___x_4648_, 1, v_k_4740_);
lean_ctor_set(v___x_4648_, 0, v___x_4745_);
v___x_4749_ = v___x_4648_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4745_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_k_4740_);
lean_ctor_set(v_reuseFailAlloc_4750_, 2, v_v_4741_);
lean_ctor_set(v_reuseFailAlloc_4750_, 3, v_l_4738_);
lean_ctor_set(v_reuseFailAlloc_4750_, 4, v___x_4747_);
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
else
{
lean_object* v_r_4755_; 
v_r_4755_ = lean_ctor_get(v_impl_4651_, 4);
lean_inc(v_r_4755_);
if (lean_obj_tag(v_r_4755_) == 0)
{
lean_object* v_k_4756_; lean_object* v_v_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4780_; 
v_k_4756_ = lean_ctor_get(v_impl_4651_, 1);
v_v_4757_ = lean_ctor_get(v_impl_4651_, 2);
v_isSharedCheck_4780_ = !lean_is_exclusive(v_impl_4651_);
if (v_isSharedCheck_4780_ == 0)
{
lean_object* v_unused_4781_; lean_object* v_unused_4782_; lean_object* v_unused_4783_; 
v_unused_4781_ = lean_ctor_get(v_impl_4651_, 4);
lean_dec(v_unused_4781_);
v_unused_4782_ = lean_ctor_get(v_impl_4651_, 3);
lean_dec(v_unused_4782_);
v_unused_4783_ = lean_ctor_get(v_impl_4651_, 0);
lean_dec(v_unused_4783_);
v___x_4759_ = v_impl_4651_;
v_isShared_4760_ = v_isSharedCheck_4780_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_v_4757_);
lean_inc(v_k_4756_);
lean_dec(v_impl_4651_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4780_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v_k_4761_; lean_object* v_v_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4776_; 
v_k_4761_ = lean_ctor_get(v_r_4755_, 1);
v_v_4762_ = lean_ctor_get(v_r_4755_, 2);
v_isSharedCheck_4776_ = !lean_is_exclusive(v_r_4755_);
if (v_isSharedCheck_4776_ == 0)
{
lean_object* v_unused_4777_; lean_object* v_unused_4778_; lean_object* v_unused_4779_; 
v_unused_4777_ = lean_ctor_get(v_r_4755_, 4);
lean_dec(v_unused_4777_);
v_unused_4778_ = lean_ctor_get(v_r_4755_, 3);
lean_dec(v_unused_4778_);
v_unused_4779_ = lean_ctor_get(v_r_4755_, 0);
lean_dec(v_unused_4779_);
v___x_4764_ = v_r_4755_;
v_isShared_4765_ = v_isSharedCheck_4776_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_v_4762_);
lean_inc(v_k_4761_);
lean_dec(v_r_4755_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4776_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4766_; lean_object* v___x_4768_; 
v___x_4766_ = lean_unsigned_to_nat(3u);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 4, v_l_4738_);
lean_ctor_set(v___x_4764_, 3, v_l_4738_);
lean_ctor_set(v___x_4764_, 2, v_v_4757_);
lean_ctor_set(v___x_4764_, 1, v_k_4756_);
lean_ctor_set(v___x_4764_, 0, v___x_4652_);
v___x_4768_ = v___x_4764_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4775_, 1, v_k_4756_);
lean_ctor_set(v_reuseFailAlloc_4775_, 2, v_v_4757_);
lean_ctor_set(v_reuseFailAlloc_4775_, 3, v_l_4738_);
lean_ctor_set(v_reuseFailAlloc_4775_, 4, v_l_4738_);
v___x_4768_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4770_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 4, v_l_4738_);
lean_ctor_set(v___x_4759_, 2, v_v_4644_);
lean_ctor_set(v___x_4759_, 1, v_k_4643_);
lean_ctor_set(v___x_4759_, 0, v___x_4652_);
v___x_4770_ = v___x_4759_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4774_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4774_, 3, v_l_4738_);
lean_ctor_set(v_reuseFailAlloc_4774_, 4, v_l_4738_);
v___x_4770_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
lean_object* v___x_4772_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v___x_4770_);
lean_ctor_set(v___x_4648_, 3, v___x_4768_);
lean_ctor_set(v___x_4648_, 2, v_v_4762_);
lean_ctor_set(v___x_4648_, 1, v_k_4761_);
lean_ctor_set(v___x_4648_, 0, v___x_4766_);
v___x_4772_ = v___x_4648_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4766_);
lean_ctor_set(v_reuseFailAlloc_4773_, 1, v_k_4761_);
lean_ctor_set(v_reuseFailAlloc_4773_, 2, v_v_4762_);
lean_ctor_set(v_reuseFailAlloc_4773_, 3, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4773_, 4, v___x_4770_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
}
}
else
{
lean_object* v___x_4784_; lean_object* v___x_4786_; 
v___x_4784_ = lean_unsigned_to_nat(2u);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_r_4755_);
lean_ctor_set(v___x_4648_, 3, v_impl_4651_);
lean_ctor_set(v___x_4648_, 0, v___x_4784_);
v___x_4786_ = v___x_4648_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4787_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4787_, 3, v_impl_4651_);
lean_ctor_set(v_reuseFailAlloc_4787_, 4, v_r_4755_);
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
case 1:
{
lean_object* v___x_4789_; 
lean_dec(v_v_4644_);
lean_dec(v_k_4643_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 2, v_v_4640_);
lean_ctor_set(v___x_4648_, 1, v_k_4639_);
v___x_4789_ = v___x_4648_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_size_4642_);
lean_ctor_set(v_reuseFailAlloc_4790_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4790_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4790_, 3, v_l_4645_);
lean_ctor_set(v_reuseFailAlloc_4790_, 4, v_r_4646_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
default: 
{
lean_object* v_impl_4791_; lean_object* v___x_4792_; 
lean_dec(v_size_4642_);
v_impl_4791_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4639_, v_v_4640_, v_r_4646_);
v___x_4792_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4645_) == 0)
{
lean_object* v_size_4793_; lean_object* v_size_4794_; lean_object* v_k_4795_; lean_object* v_v_4796_; lean_object* v_l_4797_; lean_object* v_r_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; uint8_t v___x_4801_; 
v_size_4793_ = lean_ctor_get(v_l_4645_, 0);
v_size_4794_ = lean_ctor_get(v_impl_4791_, 0);
lean_inc(v_size_4794_);
v_k_4795_ = lean_ctor_get(v_impl_4791_, 1);
lean_inc(v_k_4795_);
v_v_4796_ = lean_ctor_get(v_impl_4791_, 2);
lean_inc(v_v_4796_);
v_l_4797_ = lean_ctor_get(v_impl_4791_, 3);
lean_inc(v_l_4797_);
v_r_4798_ = lean_ctor_get(v_impl_4791_, 4);
lean_inc(v_r_4798_);
v___x_4799_ = lean_unsigned_to_nat(3u);
v___x_4800_ = lean_nat_mul(v___x_4799_, v_size_4793_);
v___x_4801_ = lean_nat_dec_lt(v___x_4800_, v_size_4794_);
lean_dec(v___x_4800_);
if (v___x_4801_ == 0)
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4805_; 
lean_dec(v_r_4798_);
lean_dec(v_l_4797_);
lean_dec(v_v_4796_);
lean_dec(v_k_4795_);
v___x_4802_ = lean_nat_add(v___x_4792_, v_size_4793_);
v___x_4803_ = lean_nat_add(v___x_4802_, v_size_4794_);
lean_dec(v_size_4794_);
lean_dec(v___x_4802_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_impl_4791_);
lean_ctor_set(v___x_4648_, 0, v___x_4803_);
v___x_4805_ = v___x_4648_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4803_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4806_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4806_, 3, v_l_4645_);
lean_ctor_set(v_reuseFailAlloc_4806_, 4, v_impl_4791_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
else
{
lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4870_; 
v_isSharedCheck_4870_ = !lean_is_exclusive(v_impl_4791_);
if (v_isSharedCheck_4870_ == 0)
{
lean_object* v_unused_4871_; lean_object* v_unused_4872_; lean_object* v_unused_4873_; lean_object* v_unused_4874_; lean_object* v_unused_4875_; 
v_unused_4871_ = lean_ctor_get(v_impl_4791_, 4);
lean_dec(v_unused_4871_);
v_unused_4872_ = lean_ctor_get(v_impl_4791_, 3);
lean_dec(v_unused_4872_);
v_unused_4873_ = lean_ctor_get(v_impl_4791_, 2);
lean_dec(v_unused_4873_);
v_unused_4874_ = lean_ctor_get(v_impl_4791_, 1);
lean_dec(v_unused_4874_);
v_unused_4875_ = lean_ctor_get(v_impl_4791_, 0);
lean_dec(v_unused_4875_);
v___x_4808_ = v_impl_4791_;
v_isShared_4809_ = v_isSharedCheck_4870_;
goto v_resetjp_4807_;
}
else
{
lean_dec(v_impl_4791_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4870_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v_size_4810_; lean_object* v_k_4811_; lean_object* v_v_4812_; lean_object* v_l_4813_; lean_object* v_r_4814_; lean_object* v_size_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v_size_4810_ = lean_ctor_get(v_l_4797_, 0);
v_k_4811_ = lean_ctor_get(v_l_4797_, 1);
v_v_4812_ = lean_ctor_get(v_l_4797_, 2);
v_l_4813_ = lean_ctor_get(v_l_4797_, 3);
v_r_4814_ = lean_ctor_get(v_l_4797_, 4);
v_size_4815_ = lean_ctor_get(v_r_4798_, 0);
v___x_4816_ = lean_unsigned_to_nat(2u);
v___x_4817_ = lean_nat_mul(v___x_4816_, v_size_4815_);
v___x_4818_ = lean_nat_dec_lt(v_size_4810_, v___x_4817_);
lean_dec(v___x_4817_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4846_; 
lean_inc(v_r_4814_);
lean_inc(v_l_4813_);
lean_inc(v_v_4812_);
lean_inc(v_k_4811_);
v_isSharedCheck_4846_ = !lean_is_exclusive(v_l_4797_);
if (v_isSharedCheck_4846_ == 0)
{
lean_object* v_unused_4847_; lean_object* v_unused_4848_; lean_object* v_unused_4849_; lean_object* v_unused_4850_; lean_object* v_unused_4851_; 
v_unused_4847_ = lean_ctor_get(v_l_4797_, 4);
lean_dec(v_unused_4847_);
v_unused_4848_ = lean_ctor_get(v_l_4797_, 3);
lean_dec(v_unused_4848_);
v_unused_4849_ = lean_ctor_get(v_l_4797_, 2);
lean_dec(v_unused_4849_);
v_unused_4850_ = lean_ctor_get(v_l_4797_, 1);
lean_dec(v_unused_4850_);
v_unused_4851_ = lean_ctor_get(v_l_4797_, 0);
lean_dec(v_unused_4851_);
v___x_4820_ = v_l_4797_;
v_isShared_4821_ = v_isSharedCheck_4846_;
goto v_resetjp_4819_;
}
else
{
lean_dec(v_l_4797_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4846_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___y_4825_; lean_object* v___y_4826_; lean_object* v___y_4827_; lean_object* v___y_4836_; 
v___x_4822_ = lean_nat_add(v___x_4792_, v_size_4793_);
v___x_4823_ = lean_nat_add(v___x_4822_, v_size_4794_);
lean_dec(v_size_4794_);
if (lean_obj_tag(v_l_4813_) == 0)
{
lean_object* v_size_4844_; 
v_size_4844_ = lean_ctor_get(v_l_4813_, 0);
lean_inc(v_size_4844_);
v___y_4836_ = v_size_4844_;
goto v___jp_4835_;
}
else
{
lean_object* v___x_4845_; 
v___x_4845_ = lean_unsigned_to_nat(0u);
v___y_4836_ = v___x_4845_;
goto v___jp_4835_;
}
v___jp_4824_:
{
lean_object* v___x_4828_; lean_object* v___x_4830_; 
v___x_4828_ = lean_nat_add(v___y_4826_, v___y_4827_);
lean_dec(v___y_4827_);
lean_dec(v___y_4826_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 4, v_r_4798_);
lean_ctor_set(v___x_4820_, 3, v_r_4814_);
lean_ctor_set(v___x_4820_, 2, v_v_4796_);
lean_ctor_set(v___x_4820_, 1, v_k_4795_);
lean_ctor_set(v___x_4820_, 0, v___x_4828_);
v___x_4830_ = v___x_4820_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v___x_4828_);
lean_ctor_set(v_reuseFailAlloc_4834_, 1, v_k_4795_);
lean_ctor_set(v_reuseFailAlloc_4834_, 2, v_v_4796_);
lean_ctor_set(v_reuseFailAlloc_4834_, 3, v_r_4814_);
lean_ctor_set(v_reuseFailAlloc_4834_, 4, v_r_4798_);
v___x_4830_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_object* v___x_4832_; 
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 4, v___x_4830_);
lean_ctor_set(v___x_4808_, 3, v___y_4825_);
lean_ctor_set(v___x_4808_, 2, v_v_4812_);
lean_ctor_set(v___x_4808_, 1, v_k_4811_);
lean_ctor_set(v___x_4808_, 0, v___x_4823_);
v___x_4832_ = v___x_4808_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4823_);
lean_ctor_set(v_reuseFailAlloc_4833_, 1, v_k_4811_);
lean_ctor_set(v_reuseFailAlloc_4833_, 2, v_v_4812_);
lean_ctor_set(v_reuseFailAlloc_4833_, 3, v___y_4825_);
lean_ctor_set(v_reuseFailAlloc_4833_, 4, v___x_4830_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
v___jp_4835_:
{
lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4837_ = lean_nat_add(v___x_4822_, v___y_4836_);
lean_dec(v___y_4836_);
lean_dec(v___x_4822_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_l_4813_);
lean_ctor_set(v___x_4648_, 0, v___x_4837_);
v___x_4839_ = v___x_4648_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4837_);
lean_ctor_set(v_reuseFailAlloc_4843_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4843_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4843_, 3, v_l_4645_);
lean_ctor_set(v_reuseFailAlloc_4843_, 4, v_l_4813_);
v___x_4839_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
lean_object* v___x_4840_; 
v___x_4840_ = lean_nat_add(v___x_4792_, v_size_4815_);
if (lean_obj_tag(v_r_4814_) == 0)
{
lean_object* v_size_4841_; 
v_size_4841_ = lean_ctor_get(v_r_4814_, 0);
lean_inc(v_size_4841_);
v___y_4825_ = v___x_4839_;
v___y_4826_ = v___x_4840_;
v___y_4827_ = v_size_4841_;
goto v___jp_4824_;
}
else
{
lean_object* v___x_4842_; 
v___x_4842_ = lean_unsigned_to_nat(0u);
v___y_4825_ = v___x_4839_;
v___y_4826_ = v___x_4840_;
v___y_4827_ = v___x_4842_;
goto v___jp_4824_;
}
}
}
}
}
else
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4856_; 
lean_del_object(v___x_4648_);
v___x_4852_ = lean_nat_add(v___x_4792_, v_size_4793_);
v___x_4853_ = lean_nat_add(v___x_4852_, v_size_4794_);
lean_dec(v_size_4794_);
v___x_4854_ = lean_nat_add(v___x_4852_, v_size_4810_);
lean_dec(v___x_4852_);
lean_inc_ref(v_l_4645_);
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 4, v_l_4797_);
lean_ctor_set(v___x_4808_, 3, v_l_4645_);
lean_ctor_set(v___x_4808_, 2, v_v_4644_);
lean_ctor_set(v___x_4808_, 1, v_k_4643_);
lean_ctor_set(v___x_4808_, 0, v___x_4854_);
v___x_4856_ = v___x_4808_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4869_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4869_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4869_, 3, v_l_4645_);
lean_ctor_set(v_reuseFailAlloc_4869_, 4, v_l_4797_);
v___x_4856_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
v_isSharedCheck_4863_ = !lean_is_exclusive(v_l_4645_);
if (v_isSharedCheck_4863_ == 0)
{
lean_object* v_unused_4864_; lean_object* v_unused_4865_; lean_object* v_unused_4866_; lean_object* v_unused_4867_; lean_object* v_unused_4868_; 
v_unused_4864_ = lean_ctor_get(v_l_4645_, 4);
lean_dec(v_unused_4864_);
v_unused_4865_ = lean_ctor_get(v_l_4645_, 3);
lean_dec(v_unused_4865_);
v_unused_4866_ = lean_ctor_get(v_l_4645_, 2);
lean_dec(v_unused_4866_);
v_unused_4867_ = lean_ctor_get(v_l_4645_, 1);
lean_dec(v_unused_4867_);
v_unused_4868_ = lean_ctor_get(v_l_4645_, 0);
lean_dec(v_unused_4868_);
v___x_4858_ = v_l_4645_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_dec(v_l_4645_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 4, v_r_4798_);
lean_ctor_set(v___x_4858_, 3, v___x_4856_);
lean_ctor_set(v___x_4858_, 2, v_v_4796_);
lean_ctor_set(v___x_4858_, 1, v_k_4795_);
lean_ctor_set(v___x_4858_, 0, v___x_4853_);
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4853_);
lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_k_4795_);
lean_ctor_set(v_reuseFailAlloc_4862_, 2, v_v_4796_);
lean_ctor_set(v_reuseFailAlloc_4862_, 3, v___x_4856_);
lean_ctor_set(v_reuseFailAlloc_4862_, 4, v_r_4798_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4876_; 
v_l_4876_ = lean_ctor_get(v_impl_4791_, 3);
lean_inc(v_l_4876_);
if (lean_obj_tag(v_l_4876_) == 0)
{
lean_object* v_r_4877_; lean_object* v_k_4878_; lean_object* v_v_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4902_; 
v_r_4877_ = lean_ctor_get(v_impl_4791_, 4);
v_k_4878_ = lean_ctor_get(v_impl_4791_, 1);
v_v_4879_ = lean_ctor_get(v_impl_4791_, 2);
v_isSharedCheck_4902_ = !lean_is_exclusive(v_impl_4791_);
if (v_isSharedCheck_4902_ == 0)
{
lean_object* v_unused_4903_; lean_object* v_unused_4904_; 
v_unused_4903_ = lean_ctor_get(v_impl_4791_, 3);
lean_dec(v_unused_4903_);
v_unused_4904_ = lean_ctor_get(v_impl_4791_, 0);
lean_dec(v_unused_4904_);
v___x_4881_ = v_impl_4791_;
v_isShared_4882_ = v_isSharedCheck_4902_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_r_4877_);
lean_inc(v_v_4879_);
lean_inc(v_k_4878_);
lean_dec(v_impl_4791_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4902_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v_k_4883_; lean_object* v_v_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4898_; 
v_k_4883_ = lean_ctor_get(v_l_4876_, 1);
v_v_4884_ = lean_ctor_get(v_l_4876_, 2);
v_isSharedCheck_4898_ = !lean_is_exclusive(v_l_4876_);
if (v_isSharedCheck_4898_ == 0)
{
lean_object* v_unused_4899_; lean_object* v_unused_4900_; lean_object* v_unused_4901_; 
v_unused_4899_ = lean_ctor_get(v_l_4876_, 4);
lean_dec(v_unused_4899_);
v_unused_4900_ = lean_ctor_get(v_l_4876_, 3);
lean_dec(v_unused_4900_);
v_unused_4901_ = lean_ctor_get(v_l_4876_, 0);
lean_dec(v_unused_4901_);
v___x_4886_ = v_l_4876_;
v_isShared_4887_ = v_isSharedCheck_4898_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_v_4884_);
lean_inc(v_k_4883_);
lean_dec(v_l_4876_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4898_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4888_; lean_object* v___x_4890_; 
v___x_4888_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4877_, 2);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 4, v_r_4877_);
lean_ctor_set(v___x_4886_, 3, v_r_4877_);
lean_ctor_set(v___x_4886_, 2, v_v_4644_);
lean_ctor_set(v___x_4886_, 1, v_k_4643_);
lean_ctor_set(v___x_4886_, 0, v___x_4792_);
v___x_4890_ = v___x_4886_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4897_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4897_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4897_, 3, v_r_4877_);
lean_ctor_set(v_reuseFailAlloc_4897_, 4, v_r_4877_);
v___x_4890_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
lean_object* v___x_4892_; 
lean_inc(v_r_4877_);
if (v_isShared_4882_ == 0)
{
lean_ctor_set(v___x_4881_, 3, v_r_4877_);
lean_ctor_set(v___x_4881_, 0, v___x_4792_);
v___x_4892_ = v___x_4881_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4896_, 1, v_k_4878_);
lean_ctor_set(v_reuseFailAlloc_4896_, 2, v_v_4879_);
lean_ctor_set(v_reuseFailAlloc_4896_, 3, v_r_4877_);
lean_ctor_set(v_reuseFailAlloc_4896_, 4, v_r_4877_);
v___x_4892_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
lean_object* v___x_4894_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v___x_4892_);
lean_ctor_set(v___x_4648_, 3, v___x_4890_);
lean_ctor_set(v___x_4648_, 2, v_v_4884_);
lean_ctor_set(v___x_4648_, 1, v_k_4883_);
lean_ctor_set(v___x_4648_, 0, v___x_4888_);
v___x_4894_ = v___x_4648_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4888_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v_k_4883_);
lean_ctor_set(v_reuseFailAlloc_4895_, 2, v_v_4884_);
lean_ctor_set(v_reuseFailAlloc_4895_, 3, v___x_4890_);
lean_ctor_set(v_reuseFailAlloc_4895_, 4, v___x_4892_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
}
else
{
lean_object* v_r_4905_; 
v_r_4905_ = lean_ctor_get(v_impl_4791_, 4);
lean_inc(v_r_4905_);
if (lean_obj_tag(v_r_4905_) == 0)
{
lean_object* v_k_4906_; lean_object* v_v_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4918_; 
v_k_4906_ = lean_ctor_get(v_impl_4791_, 1);
v_v_4907_ = lean_ctor_get(v_impl_4791_, 2);
v_isSharedCheck_4918_ = !lean_is_exclusive(v_impl_4791_);
if (v_isSharedCheck_4918_ == 0)
{
lean_object* v_unused_4919_; lean_object* v_unused_4920_; lean_object* v_unused_4921_; 
v_unused_4919_ = lean_ctor_get(v_impl_4791_, 4);
lean_dec(v_unused_4919_);
v_unused_4920_ = lean_ctor_get(v_impl_4791_, 3);
lean_dec(v_unused_4920_);
v_unused_4921_ = lean_ctor_get(v_impl_4791_, 0);
lean_dec(v_unused_4921_);
v___x_4909_ = v_impl_4791_;
v_isShared_4910_ = v_isSharedCheck_4918_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_v_4907_);
lean_inc(v_k_4906_);
lean_dec(v_impl_4791_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4918_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4911_; lean_object* v___x_4913_; 
v___x_4911_ = lean_unsigned_to_nat(3u);
if (v_isShared_4910_ == 0)
{
lean_ctor_set(v___x_4909_, 4, v_l_4876_);
lean_ctor_set(v___x_4909_, 2, v_v_4644_);
lean_ctor_set(v___x_4909_, 1, v_k_4643_);
lean_ctor_set(v___x_4909_, 0, v___x_4792_);
v___x_4913_ = v___x_4909_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4917_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4917_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4917_, 3, v_l_4876_);
lean_ctor_set(v_reuseFailAlloc_4917_, 4, v_l_4876_);
v___x_4913_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
lean_object* v___x_4915_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_r_4905_);
lean_ctor_set(v___x_4648_, 3, v___x_4913_);
lean_ctor_set(v___x_4648_, 2, v_v_4907_);
lean_ctor_set(v___x_4648_, 1, v_k_4906_);
lean_ctor_set(v___x_4648_, 0, v___x_4911_);
v___x_4915_ = v___x_4648_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4911_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v_k_4906_);
lean_ctor_set(v_reuseFailAlloc_4916_, 2, v_v_4907_);
lean_ctor_set(v_reuseFailAlloc_4916_, 3, v___x_4913_);
lean_ctor_set(v_reuseFailAlloc_4916_, 4, v_r_4905_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
else
{
lean_object* v___x_4922_; lean_object* v___x_4924_; 
v___x_4922_ = lean_unsigned_to_nat(2u);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 4, v_impl_4791_);
lean_ctor_set(v___x_4648_, 3, v_r_4905_);
lean_ctor_set(v___x_4648_, 0, v___x_4922_);
v___x_4924_ = v___x_4648_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4922_);
lean_ctor_set(v_reuseFailAlloc_4925_, 1, v_k_4643_);
lean_ctor_set(v_reuseFailAlloc_4925_, 2, v_v_4644_);
lean_ctor_set(v_reuseFailAlloc_4925_, 3, v_r_4905_);
lean_ctor_set(v_reuseFailAlloc_4925_, 4, v_impl_4791_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
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
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = lean_unsigned_to_nat(1u);
v___x_4928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
lean_ctor_set(v___x_4928_, 1, v_k_4639_);
lean_ctor_set(v___x_4928_, 2, v_v_4640_);
lean_ctor_set(v___x_4928_, 3, v_t_4641_);
lean_ctor_set(v___x_4928_, 4, v_t_4641_);
return v___x_4928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object* v_as_4929_, size_t v_sz_4930_, size_t v_i_4931_, lean_object* v_b_4932_){
_start:
{
uint8_t v___x_4933_; 
v___x_4933_ = lean_usize_dec_lt(v_i_4931_, v_sz_4930_);
if (v___x_4933_ == 0)
{
return v_b_4932_;
}
else
{
lean_object* v_a_4934_; lean_object* v_fst_4935_; lean_object* v_snd_4936_; lean_object* v_r_4937_; size_t v___x_4938_; size_t v___x_4939_; 
v_a_4934_ = lean_array_uget_borrowed(v_as_4929_, v_i_4931_);
v_fst_4935_ = lean_ctor_get(v_a_4934_, 0);
v_snd_4936_ = lean_ctor_get(v_a_4934_, 1);
lean_inc(v_snd_4936_);
lean_inc(v_fst_4935_);
v_r_4937_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_fst_4935_, v_snd_4936_, v_b_4932_);
v___x_4938_ = ((size_t)1ULL);
v___x_4939_ = lean_usize_add(v_i_4931_, v___x_4938_);
v_i_4931_ = v___x_4939_;
v_b_4932_ = v_r_4937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object* v_as_4941_, lean_object* v_sz_4942_, lean_object* v_i_4943_, lean_object* v_b_4944_){
_start:
{
size_t v_sz_boxed_4945_; size_t v_i_boxed_4946_; lean_object* v_res_4947_; 
v_sz_boxed_4945_ = lean_unbox_usize(v_sz_4942_);
lean_dec(v_sz_4942_);
v_i_boxed_4946_ = lean_unbox_usize(v_i_4943_);
lean_dec(v_i_4943_);
v_res_4947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v_as_4941_, v_sz_boxed_4945_, v_i_boxed_4946_, v_b_4944_);
lean_dec_ref(v_as_4941_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object* v_a_4950_, lean_object* v_x_4951_){
_start:
{
lean_object* v___y_4953_; 
if (lean_obj_tag(v_x_4951_) == 0)
{
lean_object* v___x_4956_; 
v___x_4956_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___y_4953_ = v___x_4956_;
goto v___jp_4952_;
}
else
{
lean_object* v_val_4957_; 
v_val_4957_ = lean_ctor_get(v_x_4951_, 0);
lean_inc(v_val_4957_);
lean_dec_ref(v_x_4951_);
v___y_4953_ = v_val_4957_;
goto v___jp_4952_;
}
v___jp_4952_:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4954_ = lean_array_push(v___y_4953_, v_a_4950_);
v___x_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
return v___x_4955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_x_4960_){
_start:
{
if (lean_obj_tag(v_x_4960_) == 0)
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v_val_4963_; lean_object* v___x_4964_; 
v___x_4961_ = lean_box(0);
v___x_4962_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4958_, v___x_4961_);
v_val_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_val_4963_);
lean_dec(v___x_4962_);
v___x_4964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4964_, 0, v_a_4959_);
lean_ctor_set(v___x_4964_, 1, v_val_4963_);
lean_ctor_set(v___x_4964_, 2, v_x_4960_);
return v___x_4964_;
}
else
{
lean_object* v_key_4965_; lean_object* v_value_4966_; lean_object* v_tail_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4982_; 
v_key_4965_ = lean_ctor_get(v_x_4960_, 0);
v_value_4966_ = lean_ctor_get(v_x_4960_, 1);
v_tail_4967_ = lean_ctor_get(v_x_4960_, 2);
v_isSharedCheck_4982_ = !lean_is_exclusive(v_x_4960_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4969_ = v_x_4960_;
v_isShared_4970_ = v_isSharedCheck_4982_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_tail_4967_);
lean_inc(v_value_4966_);
lean_inc(v_key_4965_);
lean_dec(v_x_4960_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4982_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
uint8_t v___x_4971_; 
v___x_4971_ = lean_name_eq(v_key_4965_, v_a_4959_);
if (v___x_4971_ == 0)
{
lean_object* v_tail_4972_; lean_object* v___x_4974_; 
v_tail_4972_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4958_, v_a_4959_, v_tail_4967_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set(v___x_4969_, 2, v_tail_4972_);
v___x_4974_ = v___x_4969_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_key_4965_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v_value_4966_);
lean_ctor_set(v_reuseFailAlloc_4975_, 2, v_tail_4972_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
else
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v_val_4978_; lean_object* v___x_4980_; 
lean_dec(v_key_4965_);
v___x_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4976_, 0, v_value_4966_);
v___x_4977_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4958_, v___x_4976_);
v_val_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_val_4978_);
lean_dec(v___x_4977_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set(v___x_4969_, 1, v_val_4978_);
lean_ctor_set(v___x_4969_, 0, v_a_4959_);
v___x_4980_ = v___x_4969_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4959_);
lean_ctor_set(v_reuseFailAlloc_4981_, 1, v_val_4978_);
lean_ctor_set(v_reuseFailAlloc_4981_, 2, v_tail_4967_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
}
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_4983_; uint64_t v___x_4984_; 
v___x_4983_ = lean_unsigned_to_nat(1723u);
v___x_4984_ = lean_uint64_of_nat(v___x_4983_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_4985_, lean_object* v_x_4986_){
_start:
{
if (lean_obj_tag(v_x_4986_) == 0)
{
return v_x_4985_;
}
else
{
lean_object* v_key_4987_; lean_object* v_value_4988_; lean_object* v_tail_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_5015_; 
v_key_4987_ = lean_ctor_get(v_x_4986_, 0);
v_value_4988_ = lean_ctor_get(v_x_4986_, 1);
v_tail_4989_ = lean_ctor_get(v_x_4986_, 2);
v_isSharedCheck_5015_ = !lean_is_exclusive(v_x_4986_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_4991_ = v_x_4986_;
v_isShared_4992_ = v_isSharedCheck_5015_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_tail_4989_);
lean_inc(v_value_4988_);
lean_inc(v_key_4987_);
lean_dec(v_x_4986_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_5015_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4993_; uint64_t v___y_4995_; 
v___x_4993_ = lean_array_get_size(v_x_4985_);
if (lean_obj_tag(v_key_4987_) == 0)
{
uint64_t v___x_5013_; 
v___x_5013_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0);
v___y_4995_ = v___x_5013_;
goto v___jp_4994_;
}
else
{
uint64_t v_hash_5014_; 
v_hash_5014_ = lean_ctor_get_uint64(v_key_4987_, sizeof(void*)*2);
v___y_4995_ = v_hash_5014_;
goto v___jp_4994_;
}
v___jp_4994_:
{
uint64_t v___x_4996_; uint64_t v___x_4997_; uint64_t v_fold_4998_; uint64_t v___x_4999_; uint64_t v___x_5000_; uint64_t v___x_5001_; size_t v___x_5002_; size_t v___x_5003_; size_t v___x_5004_; size_t v___x_5005_; size_t v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5009_; 
v___x_4996_ = 32ULL;
v___x_4997_ = lean_uint64_shift_right(v___y_4995_, v___x_4996_);
v_fold_4998_ = lean_uint64_xor(v___y_4995_, v___x_4997_);
v___x_4999_ = 16ULL;
v___x_5000_ = lean_uint64_shift_right(v_fold_4998_, v___x_4999_);
v___x_5001_ = lean_uint64_xor(v_fold_4998_, v___x_5000_);
v___x_5002_ = lean_uint64_to_usize(v___x_5001_);
v___x_5003_ = lean_usize_of_nat(v___x_4993_);
v___x_5004_ = ((size_t)1ULL);
v___x_5005_ = lean_usize_sub(v___x_5003_, v___x_5004_);
v___x_5006_ = lean_usize_land(v___x_5002_, v___x_5005_);
v___x_5007_ = lean_array_uget_borrowed(v_x_4985_, v___x_5006_);
lean_inc(v___x_5007_);
if (v_isShared_4992_ == 0)
{
lean_ctor_set(v___x_4991_, 2, v___x_5007_);
v___x_5009_ = v___x_4991_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_key_4987_);
lean_ctor_set(v_reuseFailAlloc_5012_, 1, v_value_4988_);
lean_ctor_set(v_reuseFailAlloc_5012_, 2, v___x_5007_);
v___x_5009_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; 
v___x_5010_ = lean_array_uset(v_x_4985_, v___x_5006_, v___x_5009_);
v_x_4985_ = v___x_5010_;
v_x_4986_ = v_tail_4989_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object* v_i_5016_, lean_object* v_source_5017_, lean_object* v_target_5018_){
_start:
{
lean_object* v___x_5019_; uint8_t v___x_5020_; 
v___x_5019_ = lean_array_get_size(v_source_5017_);
v___x_5020_ = lean_nat_dec_lt(v_i_5016_, v___x_5019_);
if (v___x_5020_ == 0)
{
lean_dec_ref(v_source_5017_);
lean_dec(v_i_5016_);
return v_target_5018_;
}
else
{
lean_object* v_es_5021_; lean_object* v___x_5022_; lean_object* v_source_5023_; lean_object* v_target_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v_es_5021_ = lean_array_fget(v_source_5017_, v_i_5016_);
v___x_5022_ = lean_box(0);
v_source_5023_ = lean_array_fset(v_source_5017_, v_i_5016_, v___x_5022_);
v_target_5024_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_target_5018_, v_es_5021_);
v___x_5025_ = lean_unsigned_to_nat(1u);
v___x_5026_ = lean_nat_add(v_i_5016_, v___x_5025_);
lean_dec(v_i_5016_);
v_i_5016_ = v___x_5026_;
v_source_5017_ = v_source_5023_;
v_target_5018_ = v_target_5024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object* v_data_5028_){
_start:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v_nbuckets_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5029_ = lean_array_get_size(v_data_5028_);
v___x_5030_ = lean_unsigned_to_nat(2u);
v_nbuckets_5031_ = lean_nat_mul(v___x_5029_, v___x_5030_);
v___x_5032_ = lean_unsigned_to_nat(0u);
v___x_5033_ = lean_box(0);
v___x_5034_ = lean_mk_array(v_nbuckets_5031_, v___x_5033_);
v___x_5035_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_5032_, v_data_5028_, v___x_5034_);
return v___x_5035_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_5036_, lean_object* v_x_5037_){
_start:
{
if (lean_obj_tag(v_x_5037_) == 0)
{
uint8_t v___x_5038_; 
v___x_5038_ = 0;
return v___x_5038_;
}
else
{
lean_object* v_key_5039_; lean_object* v_tail_5040_; uint8_t v___x_5041_; 
v_key_5039_ = lean_ctor_get(v_x_5037_, 0);
v_tail_5040_ = lean_ctor_get(v_x_5037_, 2);
v___x_5041_ = lean_name_eq(v_key_5039_, v_a_5036_);
if (v___x_5041_ == 0)
{
v_x_5037_ = v_tail_5040_;
goto _start;
}
else
{
return v___x_5041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_5043_, lean_object* v_x_5044_){
_start:
{
uint8_t v_res_5045_; lean_object* v_r_5046_; 
v_res_5045_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5043_, v_x_5044_);
lean_dec(v_x_5044_);
lean_dec(v_a_5043_);
v_r_5046_ = lean_box(v_res_5045_);
return v_r_5046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_5047_, lean_object* v_m_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v___y_5051_; lean_object* v___y_5052_; size_t v___y_5053_; lean_object* v___y_5054_; lean_object* v_size_5057_; lean_object* v_buckets_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5105_; 
v_size_5057_ = lean_ctor_get(v_m_5048_, 0);
v_buckets_5058_ = lean_ctor_get(v_m_5048_, 1);
v_isSharedCheck_5105_ = !lean_is_exclusive(v_m_5048_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5060_ = v_m_5048_;
v_isShared_5061_ = v_isSharedCheck_5105_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_buckets_5058_);
lean_inc(v_size_5057_);
lean_dec(v_m_5048_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5105_;
goto v_resetjp_5059_;
}
v___jp_5050_:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5055_ = lean_array_uset(v___y_5051_, v___y_5053_, v___y_5052_);
v___x_5056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5056_, 0, v___y_5054_);
lean_ctor_set(v___x_5056_, 1, v___x_5055_);
return v___x_5056_;
}
v_resetjp_5059_:
{
lean_object* v___x_5062_; uint64_t v___y_5064_; 
v___x_5062_ = lean_array_get_size(v_buckets_5058_);
if (lean_obj_tag(v_a_5049_) == 0)
{
uint64_t v___x_5103_; 
v___x_5103_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg___closed__0);
v___y_5064_ = v___x_5103_;
goto v___jp_5063_;
}
else
{
uint64_t v_hash_5104_; 
v_hash_5104_ = lean_ctor_get_uint64(v_a_5049_, sizeof(void*)*2);
v___y_5064_ = v_hash_5104_;
goto v___jp_5063_;
}
v___jp_5063_:
{
uint64_t v___x_5065_; uint64_t v___x_5066_; uint64_t v_fold_5067_; uint64_t v___x_5068_; uint64_t v___x_5069_; uint64_t v___x_5070_; size_t v___x_5071_; size_t v___x_5072_; size_t v___x_5073_; size_t v___x_5074_; size_t v___x_5075_; lean_object* v_bkt_5076_; uint8_t v___x_5077_; 
v___x_5065_ = 32ULL;
v___x_5066_ = lean_uint64_shift_right(v___y_5064_, v___x_5065_);
v_fold_5067_ = lean_uint64_xor(v___y_5064_, v___x_5066_);
v___x_5068_ = 16ULL;
v___x_5069_ = lean_uint64_shift_right(v_fold_5067_, v___x_5068_);
v___x_5070_ = lean_uint64_xor(v_fold_5067_, v___x_5069_);
v___x_5071_ = lean_uint64_to_usize(v___x_5070_);
v___x_5072_ = lean_usize_of_nat(v___x_5062_);
v___x_5073_ = ((size_t)1ULL);
v___x_5074_ = lean_usize_sub(v___x_5072_, v___x_5073_);
v___x_5075_ = lean_usize_land(v___x_5071_, v___x_5074_);
v_bkt_5076_ = lean_array_uget_borrowed(v_buckets_5058_, v___x_5075_);
v___x_5077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5049_, v_bkt_5076_);
if (v___x_5077_ == 0)
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v_size_x27_5081_; lean_object* v___x_5082_; lean_object* v_buckets_x27_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; uint8_t v___x_5089_; 
v___x_5078_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_5079_ = lean_array_push(v___x_5078_, v_a_5047_);
v___x_5080_ = lean_unsigned_to_nat(1u);
v_size_x27_5081_ = lean_nat_add(v_size_5057_, v___x_5080_);
lean_dec(v_size_5057_);
lean_inc(v_bkt_5076_);
v___x_5082_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5082_, 0, v_a_5049_);
lean_ctor_set(v___x_5082_, 1, v___x_5079_);
lean_ctor_set(v___x_5082_, 2, v_bkt_5076_);
v_buckets_x27_5083_ = lean_array_uset(v_buckets_5058_, v___x_5075_, v___x_5082_);
v___x_5084_ = lean_unsigned_to_nat(4u);
v___x_5085_ = lean_nat_mul(v_size_x27_5081_, v___x_5084_);
v___x_5086_ = lean_unsigned_to_nat(3u);
v___x_5087_ = lean_nat_div(v___x_5085_, v___x_5086_);
lean_dec(v___x_5085_);
v___x_5088_ = lean_array_get_size(v_buckets_x27_5083_);
v___x_5089_ = lean_nat_dec_le(v___x_5087_, v___x_5088_);
lean_dec(v___x_5087_);
if (v___x_5089_ == 0)
{
lean_object* v_val_5090_; lean_object* v___x_5092_; 
v_val_5090_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5083_);
if (v_isShared_5061_ == 0)
{
lean_ctor_set(v___x_5060_, 1, v_val_5090_);
lean_ctor_set(v___x_5060_, 0, v_size_x27_5081_);
v___x_5092_ = v___x_5060_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_size_x27_5081_);
lean_ctor_set(v_reuseFailAlloc_5093_, 1, v_val_5090_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
else
{
lean_object* v___x_5095_; 
if (v_isShared_5061_ == 0)
{
lean_ctor_set(v___x_5060_, 1, v_buckets_x27_5083_);
lean_ctor_set(v___x_5060_, 0, v_size_x27_5081_);
v___x_5095_ = v___x_5060_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_size_x27_5081_);
lean_ctor_set(v_reuseFailAlloc_5096_, 1, v_buckets_x27_5083_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
else
{
lean_object* v___x_5097_; lean_object* v_buckets_x27_5098_; lean_object* v_bkt_x27_5099_; uint8_t v___x_5100_; 
lean_inc(v_bkt_5076_);
lean_del_object(v___x_5060_);
v___x_5097_ = lean_box(0);
v_buckets_x27_5098_ = lean_array_uset(v_buckets_5058_, v___x_5075_, v___x_5097_);
lean_inc(v_a_5049_);
v_bkt_x27_5099_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5047_, v_a_5049_, v_bkt_5076_);
v___x_5100_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5049_, v_bkt_x27_5099_);
lean_dec(v_a_5049_);
if (v___x_5100_ == 0)
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5101_ = lean_unsigned_to_nat(1u);
v___x_5102_ = lean_nat_sub(v_size_5057_, v___x_5101_);
lean_dec(v_size_5057_);
v___y_5051_ = v_buckets_x27_5098_;
v___y_5052_ = v_bkt_x27_5099_;
v___y_5053_ = v___x_5075_;
v___y_5054_ = v___x_5102_;
goto v___jp_5050_;
}
else
{
v___y_5051_ = v_buckets_x27_5098_;
v___y_5052_ = v_bkt_x27_5099_;
v___y_5053_ = v___x_5075_;
v___y_5054_ = v_size_5057_;
goto v___jp_5050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5106_, lean_object* v_as_5107_, size_t v_sz_5108_, size_t v_i_5109_, lean_object* v_b_5110_){
_start:
{
uint8_t v___x_5111_; 
v___x_5111_ = lean_usize_dec_lt(v_i_5109_, v_sz_5108_);
if (v___x_5111_ == 0)
{
lean_dec_ref(v_key_5106_);
return v_b_5110_;
}
else
{
lean_object* v_a_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; size_t v___x_5115_; size_t v___x_5116_; 
v_a_5112_ = lean_array_uget_borrowed(v_as_5107_, v_i_5109_);
lean_inc_ref(v_key_5106_);
lean_inc_n(v_a_5112_, 2);
v___x_5113_ = lean_apply_1(v_key_5106_, v_a_5112_);
v___x_5114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5112_, v_b_5110_, v___x_5113_);
v___x_5115_ = ((size_t)1ULL);
v___x_5116_ = lean_usize_add(v_i_5109_, v___x_5115_);
v_i_5109_ = v___x_5116_;
v_b_5110_ = v___x_5114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5118_, lean_object* v_as_5119_, lean_object* v_sz_5120_, lean_object* v_i_5121_, lean_object* v_b_5122_){
_start:
{
size_t v_sz_boxed_5123_; size_t v_i_boxed_5124_; lean_object* v_res_5125_; 
v_sz_boxed_5123_ = lean_unbox_usize(v_sz_5120_);
lean_dec(v_sz_5120_);
v_i_boxed_5124_ = lean_unbox_usize(v_i_5121_);
lean_dec(v_i_5121_);
v_res_5125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5118_, v_as_5119_, v_sz_boxed_5123_, v_i_boxed_5124_, v_b_5122_);
lean_dec_ref(v_as_5119_);
return v_res_5125_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v___x_5126_ = lean_box(0);
v___x_5127_ = lean_unsigned_to_nat(16u);
v___x_5128_ = lean_mk_array(v___x_5127_, v___x_5126_);
return v___x_5128_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v_groups_5131_; 
v___x_5129_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5130_ = lean_unsigned_to_nat(0u);
v_groups_5131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5131_, 0, v___x_5130_);
lean_ctor_set(v_groups_5131_, 1, v___x_5129_);
return v_groups_5131_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5132_, lean_object* v_xs_5133_){
_start:
{
lean_object* v_groups_5134_; size_t v_sz_5135_; size_t v___x_5136_; lean_object* v___x_5137_; 
v_groups_5134_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5135_ = lean_array_size(v_xs_5133_);
v___x_5136_ = ((size_t)0ULL);
v___x_5137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5132_, v_xs_5133_, v_sz_5135_, v___x_5136_, v_groups_5134_);
return v___x_5137_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5138_, lean_object* v_xs_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5138_, v_xs_5139_);
lean_dec_ref(v_xs_5139_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5142_){
_start:
{
lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; 
v___x_5144_ = lean_unsigned_to_nat(0u);
v___x_5145_ = lean_array_get_size(v_infos_5142_);
v___x_5146_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5142_, v___x_5144_, v___x_5145_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5175_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5149_ = v___x_5146_;
v_isShared_5150_ = v_isSharedCheck_5175_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5146_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5175_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___y_5152_; lean_object* v___f_5161_; lean_object* v___x_5162_; lean_object* v_size_5163_; lean_object* v_buckets_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; uint8_t v___x_5167_; 
v___f_5161_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5162_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5161_, v_a_5147_);
v_size_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_size_5163_);
v_buckets_5164_ = lean_ctor_get(v___x_5162_, 1);
lean_inc_ref(v_buckets_5164_);
lean_dec_ref(v___x_5162_);
v___x_5165_ = lean_mk_empty_array_with_capacity(v_size_5163_);
lean_dec(v_size_5163_);
v___x_5166_ = lean_array_get_size(v_buckets_5164_);
v___x_5167_ = lean_nat_dec_lt(v___x_5144_, v___x_5166_);
if (v___x_5167_ == 0)
{
lean_dec_ref(v_buckets_5164_);
v___y_5152_ = v___x_5165_;
goto v___jp_5151_;
}
else
{
uint8_t v___x_5168_; 
v___x_5168_ = lean_nat_dec_le(v___x_5166_, v___x_5166_);
if (v___x_5168_ == 0)
{
if (v___x_5167_ == 0)
{
lean_dec_ref(v_buckets_5164_);
v___y_5152_ = v___x_5165_;
goto v___jp_5151_;
}
else
{
size_t v___x_5169_; size_t v___x_5170_; lean_object* v___x_5171_; 
v___x_5169_ = ((size_t)0ULL);
v___x_5170_ = lean_usize_of_nat(v___x_5166_);
v___x_5171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5164_, v___x_5169_, v___x_5170_, v___x_5165_);
lean_dec_ref(v_buckets_5164_);
v___y_5152_ = v___x_5171_;
goto v___jp_5151_;
}
}
else
{
size_t v___x_5172_; size_t v___x_5173_; lean_object* v___x_5174_; 
v___x_5172_ = ((size_t)0ULL);
v___x_5173_ = lean_usize_of_nat(v___x_5166_);
v___x_5174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5164_, v___x_5172_, v___x_5173_, v___x_5165_);
lean_dec_ref(v_buckets_5164_);
v___y_5152_ = v___x_5174_;
goto v___jp_5151_;
}
}
v___jp_5151_:
{
lean_object* v_r_5153_; size_t v_sz_5154_; size_t v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5159_; 
v_r_5153_ = lean_box(1);
v_sz_5154_ = lean_array_size(v___y_5152_);
v___x_5155_ = ((size_t)0ULL);
v___x_5156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5152_, v_sz_5154_, v___x_5155_, v_r_5153_);
lean_dec_ref(v___y_5152_);
v___x_5157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5157_, 0, v_a_5147_);
lean_ctor_set(v___x_5157_, 1, v___x_5156_);
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 0, v___x_5157_);
v___x_5159_ = v___x_5149_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5157_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
}
else
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5183_; 
v_a_5176_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5178_ = v___x_5146_;
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_5146_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v___x_5181_; 
if (v_isShared_5179_ == 0)
{
v___x_5181_ = v___x_5178_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
v___x_5181_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
return v___x_5181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5184_);
lean_dec_ref(v_infos_5184_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5187_, lean_object* v_k_5188_, lean_object* v_v_5189_, lean_object* v_t_5190_, lean_object* v_hl_5191_){
_start:
{
lean_object* v___x_5192_; 
v___x_5192_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5188_, v_v_5189_, v_t_5190_);
return v___x_5192_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5193_, lean_object* v_key_5194_, lean_object* v_xs_5195_){
_start:
{
lean_object* v___x_5196_; 
v___x_5196_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5194_, v_xs_5195_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5197_, lean_object* v_key_5198_, lean_object* v_xs_5199_){
_start:
{
lean_object* v_res_5200_; 
v_res_5200_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5197_, v_key_5198_, v_xs_5199_);
lean_dec_ref(v_xs_5199_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5201_, lean_object* v_a_5202_, lean_object* v_m_5203_, lean_object* v_a_5204_){
_start:
{
lean_object* v___x_5205_; 
v___x_5205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5202_, v_m_5203_, v_a_5204_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5206_, lean_object* v_key_5207_, lean_object* v_as_5208_, size_t v_sz_5209_, size_t v_i_5210_, lean_object* v_b_5211_){
_start:
{
lean_object* v___x_5212_; 
v___x_5212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5207_, v_as_5208_, v_sz_5209_, v_i_5210_, v_b_5211_);
return v___x_5212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5213_, lean_object* v_key_5214_, lean_object* v_as_5215_, lean_object* v_sz_5216_, lean_object* v_i_5217_, lean_object* v_b_5218_){
_start:
{
size_t v_sz_boxed_5219_; size_t v_i_boxed_5220_; lean_object* v_res_5221_; 
v_sz_boxed_5219_ = lean_unbox_usize(v_sz_5216_);
lean_dec(v_sz_5216_);
v_i_boxed_5220_ = lean_unbox_usize(v_i_5217_);
lean_dec(v_i_5217_);
v_res_5221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5213_, v_key_5214_, v_as_5215_, v_sz_boxed_5219_, v_i_boxed_5220_, v_b_5218_);
lean_dec_ref(v_as_5215_);
return v_res_5221_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5222_, lean_object* v_a_5223_, lean_object* v_x_5224_){
_start:
{
uint8_t v___x_5225_; 
v___x_5225_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5223_, v_x_5224_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5226_, lean_object* v_a_5227_, lean_object* v_x_5228_){
_start:
{
uint8_t v_res_5229_; lean_object* v_r_5230_; 
v_res_5229_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5226_, v_a_5227_, v_x_5228_);
lean_dec(v_x_5228_);
lean_dec(v_a_5227_);
v_r_5230_ = lean_box(v_res_5229_);
return v_r_5230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5231_, lean_object* v_data_5232_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5232_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_x_5237_){
_start:
{
lean_object* v___x_5238_; 
v___x_5238_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5235_, v_a_5236_, v_x_5237_);
return v___x_5238_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5239_, lean_object* v_i_5240_, lean_object* v_source_5241_, lean_object* v_target_5242_){
_start:
{
lean_object* v___x_5243_; 
v___x_5243_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5240_, v_source_5241_, v_target_5242_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5244_, lean_object* v_x_5245_, lean_object* v_x_5246_){
_start:
{
lean_object* v___x_5247_; 
v___x_5247_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5245_, v_x_5246_);
return v___x_5247_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5248_){
_start:
{
lean_object* v_isSetupFailure_x3f_5249_; 
v_isSetupFailure_x3f_5249_ = lean_ctor_get(v_i_5248_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5249_) == 0)
{
uint8_t v___x_5250_; 
v___x_5250_ = 0;
return v___x_5250_;
}
else
{
lean_object* v_val_5251_; uint8_t v___x_5252_; 
v_val_5251_ = lean_ctor_get(v_isSetupFailure_x3f_5249_, 0);
v___x_5252_ = lean_unbox(v_val_5251_);
if (v___x_5252_ == 0)
{
uint8_t v___x_5253_; 
v___x_5253_ = 1;
return v___x_5253_;
}
else
{
uint8_t v___x_5254_; 
v___x_5254_ = 0;
return v___x_5254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5255_){
_start:
{
uint8_t v_res_5256_; lean_object* v_r_5257_; 
v_res_5256_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5255_);
lean_dec_ref(v_i_5255_);
v_r_5257_ = lean_box(v_res_5256_);
return v_r_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5263_, lean_object* v_path_5264_, lean_object* v_ilean_5265_){
_start:
{
lean_object* v_module_5267_; lean_object* v_directImports_5268_; lean_object* v_references_5269_; lean_object* v_decls_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5322_; 
v_module_5267_ = lean_ctor_get(v_ilean_5265_, 1);
v_directImports_5268_ = lean_ctor_get(v_ilean_5265_, 2);
v_references_5269_ = lean_ctor_get(v_ilean_5265_, 3);
v_decls_5270_ = lean_ctor_get(v_ilean_5265_, 4);
v_isSharedCheck_5322_ = !lean_is_exclusive(v_ilean_5265_);
if (v_isSharedCheck_5322_ == 0)
{
lean_object* v_unused_5323_; 
v_unused_5323_ = lean_ctor_get(v_ilean_5265_, 0);
lean_dec(v_unused_5323_);
v___x_5272_ = v_ilean_5265_;
v_isShared_5273_ = v_isSharedCheck_5322_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_decls_5270_);
lean_inc(v_references_5269_);
lean_inc(v_directImports_5268_);
lean_inc(v_module_5267_);
lean_dec(v_ilean_5265_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5322_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5274_; 
lean_inc(v_module_5267_);
v___x_5274_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5267_);
if (lean_obj_tag(v___x_5274_) == 0)
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5313_; 
v_a_5275_ = lean_ctor_get(v___x_5274_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5274_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5277_ = v___x_5274_;
v_isShared_5278_ = v_isSharedCheck_5313_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5274_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5313_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
if (lean_obj_tag(v_a_5275_) == 1)
{
lean_object* v_val_5279_; lean_object* v___x_5280_; 
lean_del_object(v___x_5277_);
v_val_5279_ = lean_ctor_get(v_a_5275_, 0);
lean_inc(v_val_5279_);
lean_dec_ref(v_a_5275_);
v___x_5280_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5268_);
lean_dec_ref(v_directImports_5268_);
if (lean_obj_tag(v___x_5280_) == 0)
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5301_; 
v_a_5281_ = lean_ctor_get(v___x_5280_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5283_ = v___x_5280_;
v_isShared_5284_ = v_isSharedCheck_5301_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5280_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5301_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v_ileans_5285_; lean_object* v_workers_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5300_; 
v_ileans_5285_ = lean_ctor_get(v_self_5263_, 0);
v_workers_5286_ = lean_ctor_get(v_self_5263_, 1);
v_isSharedCheck_5300_ = !lean_is_exclusive(v_self_5263_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5288_ = v_self_5263_;
v_isShared_5289_ = v_isSharedCheck_5300_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_workers_5286_);
lean_inc(v_ileans_5285_);
lean_dec(v_self_5263_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5300_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 2, v_a_5281_);
lean_ctor_set(v___x_5272_, 1, v_path_5264_);
lean_ctor_set(v___x_5272_, 0, v_val_5279_);
v___x_5291_ = v___x_5272_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_val_5279_);
lean_ctor_set(v_reuseFailAlloc_5299_, 1, v_path_5264_);
lean_ctor_set(v_reuseFailAlloc_5299_, 2, v_a_5281_);
lean_ctor_set(v_reuseFailAlloc_5299_, 3, v_references_5269_);
lean_ctor_set(v_reuseFailAlloc_5299_, 4, v_decls_5270_);
v___x_5291_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
lean_object* v___x_5292_; lean_object* v___x_5294_; 
v___x_5292_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5267_, v___x_5291_, v_ileans_5285_);
if (v_isShared_5289_ == 0)
{
lean_ctor_set(v___x_5288_, 0, v___x_5292_);
v___x_5294_ = v___x_5288_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5292_);
lean_ctor_set(v_reuseFailAlloc_5298_, 1, v_workers_5286_);
v___x_5294_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
lean_object* v___x_5296_; 
if (v_isShared_5284_ == 0)
{
lean_ctor_set(v___x_5283_, 0, v___x_5294_);
v___x_5296_ = v___x_5283_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v___x_5294_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
}
}
}
}
else
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5309_; 
lean_dec(v_val_5279_);
lean_del_object(v___x_5272_);
lean_dec(v_decls_5270_);
lean_dec(v_references_5269_);
lean_dec(v_module_5267_);
lean_dec_ref(v_path_5264_);
lean_dec_ref(v_self_5263_);
v_a_5302_ = lean_ctor_get(v___x_5280_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5304_ = v___x_5280_;
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___x_5280_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5307_; 
if (v_isShared_5305_ == 0)
{
v___x_5307_ = v___x_5304_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
}
else
{
lean_object* v___x_5311_; 
lean_dec(v_a_5275_);
lean_del_object(v___x_5272_);
lean_dec(v_decls_5270_);
lean_dec(v_references_5269_);
lean_dec_ref(v_directImports_5268_);
lean_dec(v_module_5267_);
lean_dec_ref(v_path_5264_);
if (v_isShared_5278_ == 0)
{
lean_ctor_set(v___x_5277_, 0, v_self_5263_);
v___x_5311_ = v___x_5277_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_self_5263_);
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
else
{
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5321_; 
lean_del_object(v___x_5272_);
lean_dec(v_decls_5270_);
lean_dec(v_references_5269_);
lean_dec_ref(v_directImports_5268_);
lean_dec(v_module_5267_);
lean_dec_ref(v_path_5264_);
lean_dec_ref(v_self_5263_);
v_a_5314_ = lean_ctor_get(v___x_5274_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5274_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5316_ = v___x_5274_;
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v___x_5274_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5319_; 
if (v_isShared_5317_ == 0)
{
v___x_5319_ = v___x_5316_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_a_5314_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5324_, lean_object* v_path_5325_, lean_object* v_ilean_5326_, lean_object* v_a_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = l_Lean_Server_References_addIlean(v_self_5324_, v_path_5325_, v_ilean_5326_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5329_, lean_object* v_t_5330_){
_start:
{
if (lean_obj_tag(v_t_5330_) == 0)
{
lean_object* v_v_5331_; lean_object* v_k_5332_; lean_object* v_l_5333_; lean_object* v_r_5334_; lean_object* v_ileanPath_5335_; uint8_t v___x_5336_; 
v_v_5331_ = lean_ctor_get(v_t_5330_, 2);
lean_inc(v_v_5331_);
v_k_5332_ = lean_ctor_get(v_t_5330_, 1);
lean_inc(v_k_5332_);
v_l_5333_ = lean_ctor_get(v_t_5330_, 3);
lean_inc(v_l_5333_);
v_r_5334_ = lean_ctor_get(v_t_5330_, 4);
lean_inc(v_r_5334_);
lean_dec_ref(v_t_5330_);
v_ileanPath_5335_ = lean_ctor_get(v_v_5331_, 1);
v___x_5336_ = lean_string_dec_eq(v_ileanPath_5335_, v_path_5329_);
if (v___x_5336_ == 0)
{
lean_object* v_impl_5337_; lean_object* v_impl_5338_; lean_object* v___x_5339_; 
lean_dec(v_k_5332_);
lean_dec(v_v_5331_);
v_impl_5337_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5329_, v_l_5333_);
v_impl_5338_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5329_, v_r_5334_);
v___x_5339_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5337_, v_impl_5338_);
return v___x_5339_;
}
else
{
lean_object* v_impl_5340_; lean_object* v_impl_5341_; lean_object* v___x_5342_; 
v_impl_5340_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5329_, v_l_5333_);
v_impl_5341_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5329_, v_r_5334_);
v___x_5342_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5332_, v_v_5331_, v_impl_5340_, v_impl_5341_);
return v___x_5342_;
}
}
else
{
return v_t_5330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5343_, lean_object* v_t_5344_){
_start:
{
lean_object* v_res_5345_; 
v_res_5345_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5343_, v_t_5344_);
lean_dec_ref(v_path_5343_);
return v_res_5345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5346_, lean_object* v_t_5347_){
_start:
{
if (lean_obj_tag(v_t_5347_) == 0)
{
lean_object* v_k_5348_; lean_object* v_v_5349_; lean_object* v_l_5350_; lean_object* v_r_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_6005_; 
v_k_5348_ = lean_ctor_get(v_t_5347_, 1);
v_v_5349_ = lean_ctor_get(v_t_5347_, 2);
v_l_5350_ = lean_ctor_get(v_t_5347_, 3);
v_r_5351_ = lean_ctor_get(v_t_5347_, 4);
v_isSharedCheck_6005_ = !lean_is_exclusive(v_t_5347_);
if (v_isSharedCheck_6005_ == 0)
{
lean_object* v_unused_6006_; 
v_unused_6006_ = lean_ctor_get(v_t_5347_, 0);
lean_dec(v_unused_6006_);
v___x_5353_ = v_t_5347_;
v_isShared_5354_ = v_isSharedCheck_6005_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_r_5351_);
lean_inc(v_l_5350_);
lean_inc(v_v_5349_);
lean_inc(v_k_5348_);
lean_dec(v_t_5347_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_6005_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
uint8_t v___x_5355_; 
v___x_5355_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5346_, v_k_5348_);
switch(v___x_5355_)
{
case 0:
{
lean_object* v_impl_5356_; lean_object* v___x_5357_; 
v_impl_5356_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5346_, v_l_5350_);
v___x_5357_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5356_) == 0)
{
if (lean_obj_tag(v_r_5351_) == 0)
{
lean_object* v_size_5358_; lean_object* v_size_5359_; lean_object* v_k_5360_; lean_object* v_v_5361_; lean_object* v_l_5362_; lean_object* v_r_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; uint8_t v___x_5366_; 
v_size_5358_ = lean_ctor_get(v_impl_5356_, 0);
lean_inc(v_size_5358_);
v_size_5359_ = lean_ctor_get(v_r_5351_, 0);
v_k_5360_ = lean_ctor_get(v_r_5351_, 1);
v_v_5361_ = lean_ctor_get(v_r_5351_, 2);
v_l_5362_ = lean_ctor_get(v_r_5351_, 3);
lean_inc(v_l_5362_);
v_r_5363_ = lean_ctor_get(v_r_5351_, 4);
v___x_5364_ = lean_unsigned_to_nat(3u);
v___x_5365_ = lean_nat_mul(v___x_5364_, v_size_5358_);
v___x_5366_ = lean_nat_dec_lt(v___x_5365_, v_size_5359_);
lean_dec(v___x_5365_);
if (v___x_5366_ == 0)
{
lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5370_; 
lean_dec(v_l_5362_);
v___x_5367_ = lean_nat_add(v___x_5357_, v_size_5358_);
lean_dec(v_size_5358_);
v___x_5368_ = lean_nat_add(v___x_5367_, v_size_5359_);
lean_dec(v___x_5367_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 3, v_impl_5356_);
lean_ctor_set(v___x_5353_, 0, v___x_5368_);
v___x_5370_ = v___x_5353_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5368_);
lean_ctor_set(v_reuseFailAlloc_5371_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5371_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5371_, 3, v_impl_5356_);
lean_ctor_set(v_reuseFailAlloc_5371_, 4, v_r_5351_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
else
{
lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5435_; 
lean_inc(v_r_5363_);
lean_inc(v_v_5361_);
lean_inc(v_k_5360_);
lean_inc(v_size_5359_);
v_isSharedCheck_5435_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5435_ == 0)
{
lean_object* v_unused_5436_; lean_object* v_unused_5437_; lean_object* v_unused_5438_; lean_object* v_unused_5439_; lean_object* v_unused_5440_; 
v_unused_5436_ = lean_ctor_get(v_r_5351_, 4);
lean_dec(v_unused_5436_);
v_unused_5437_ = lean_ctor_get(v_r_5351_, 3);
lean_dec(v_unused_5437_);
v_unused_5438_ = lean_ctor_get(v_r_5351_, 2);
lean_dec(v_unused_5438_);
v_unused_5439_ = lean_ctor_get(v_r_5351_, 1);
lean_dec(v_unused_5439_);
v_unused_5440_ = lean_ctor_get(v_r_5351_, 0);
lean_dec(v_unused_5440_);
v___x_5373_ = v_r_5351_;
v_isShared_5374_ = v_isSharedCheck_5435_;
goto v_resetjp_5372_;
}
else
{
lean_dec(v_r_5351_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5435_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v_size_5375_; lean_object* v_k_5376_; lean_object* v_v_5377_; lean_object* v_l_5378_; lean_object* v_r_5379_; lean_object* v_size_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; uint8_t v___x_5383_; 
v_size_5375_ = lean_ctor_get(v_l_5362_, 0);
v_k_5376_ = lean_ctor_get(v_l_5362_, 1);
v_v_5377_ = lean_ctor_get(v_l_5362_, 2);
v_l_5378_ = lean_ctor_get(v_l_5362_, 3);
v_r_5379_ = lean_ctor_get(v_l_5362_, 4);
v_size_5380_ = lean_ctor_get(v_r_5363_, 0);
v___x_5381_ = lean_unsigned_to_nat(2u);
v___x_5382_ = lean_nat_mul(v___x_5381_, v_size_5380_);
v___x_5383_ = lean_nat_dec_lt(v_size_5375_, v___x_5382_);
lean_dec(v___x_5382_);
if (v___x_5383_ == 0)
{
lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5411_; 
lean_inc(v_r_5379_);
lean_inc(v_l_5378_);
lean_inc(v_v_5377_);
lean_inc(v_k_5376_);
v_isSharedCheck_5411_ = !lean_is_exclusive(v_l_5362_);
if (v_isSharedCheck_5411_ == 0)
{
lean_object* v_unused_5412_; lean_object* v_unused_5413_; lean_object* v_unused_5414_; lean_object* v_unused_5415_; lean_object* v_unused_5416_; 
v_unused_5412_ = lean_ctor_get(v_l_5362_, 4);
lean_dec(v_unused_5412_);
v_unused_5413_ = lean_ctor_get(v_l_5362_, 3);
lean_dec(v_unused_5413_);
v_unused_5414_ = lean_ctor_get(v_l_5362_, 2);
lean_dec(v_unused_5414_);
v_unused_5415_ = lean_ctor_get(v_l_5362_, 1);
lean_dec(v_unused_5415_);
v_unused_5416_ = lean_ctor_get(v_l_5362_, 0);
lean_dec(v_unused_5416_);
v___x_5385_ = v_l_5362_;
v_isShared_5386_ = v_isSharedCheck_5411_;
goto v_resetjp_5384_;
}
else
{
lean_dec(v_l_5362_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5411_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___y_5390_; lean_object* v___y_5391_; lean_object* v___y_5392_; lean_object* v___y_5401_; 
v___x_5387_ = lean_nat_add(v___x_5357_, v_size_5358_);
lean_dec(v_size_5358_);
v___x_5388_ = lean_nat_add(v___x_5387_, v_size_5359_);
lean_dec(v_size_5359_);
if (lean_obj_tag(v_l_5378_) == 0)
{
lean_object* v_size_5409_; 
v_size_5409_ = lean_ctor_get(v_l_5378_, 0);
lean_inc(v_size_5409_);
v___y_5401_ = v_size_5409_;
goto v___jp_5400_;
}
else
{
lean_object* v___x_5410_; 
v___x_5410_ = lean_unsigned_to_nat(0u);
v___y_5401_ = v___x_5410_;
goto v___jp_5400_;
}
v___jp_5389_:
{
lean_object* v___x_5393_; lean_object* v___x_5395_; 
v___x_5393_ = lean_nat_add(v___y_5390_, v___y_5392_);
lean_dec(v___y_5392_);
lean_dec(v___y_5390_);
if (v_isShared_5386_ == 0)
{
lean_ctor_set(v___x_5385_, 4, v_r_5363_);
lean_ctor_set(v___x_5385_, 3, v_r_5379_);
lean_ctor_set(v___x_5385_, 2, v_v_5361_);
lean_ctor_set(v___x_5385_, 1, v_k_5360_);
lean_ctor_set(v___x_5385_, 0, v___x_5393_);
v___x_5395_ = v___x_5385_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v___x_5393_);
lean_ctor_set(v_reuseFailAlloc_5399_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5399_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5399_, 3, v_r_5379_);
lean_ctor_set(v_reuseFailAlloc_5399_, 4, v_r_5363_);
v___x_5395_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
lean_object* v___x_5397_; 
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 4, v___x_5395_);
lean_ctor_set(v___x_5373_, 3, v___y_5391_);
lean_ctor_set(v___x_5373_, 2, v_v_5377_);
lean_ctor_set(v___x_5373_, 1, v_k_5376_);
lean_ctor_set(v___x_5373_, 0, v___x_5388_);
v___x_5397_ = v___x_5373_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v___x_5388_);
lean_ctor_set(v_reuseFailAlloc_5398_, 1, v_k_5376_);
lean_ctor_set(v_reuseFailAlloc_5398_, 2, v_v_5377_);
lean_ctor_set(v_reuseFailAlloc_5398_, 3, v___y_5391_);
lean_ctor_set(v_reuseFailAlloc_5398_, 4, v___x_5395_);
v___x_5397_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
return v___x_5397_;
}
}
}
v___jp_5400_:
{
lean_object* v___x_5402_; lean_object* v___x_5404_; 
v___x_5402_ = lean_nat_add(v___x_5387_, v___y_5401_);
lean_dec(v___y_5401_);
lean_dec(v___x_5387_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_l_5378_);
lean_ctor_set(v___x_5353_, 3, v_impl_5356_);
lean_ctor_set(v___x_5353_, 0, v___x_5402_);
v___x_5404_ = v___x_5353_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v___x_5402_);
lean_ctor_set(v_reuseFailAlloc_5408_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5408_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5408_, 3, v_impl_5356_);
lean_ctor_set(v_reuseFailAlloc_5408_, 4, v_l_5378_);
v___x_5404_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
lean_object* v___x_5405_; 
v___x_5405_ = lean_nat_add(v___x_5357_, v_size_5380_);
if (lean_obj_tag(v_r_5379_) == 0)
{
lean_object* v_size_5406_; 
v_size_5406_ = lean_ctor_get(v_r_5379_, 0);
lean_inc(v_size_5406_);
v___y_5390_ = v___x_5405_;
v___y_5391_ = v___x_5404_;
v___y_5392_ = v_size_5406_;
goto v___jp_5389_;
}
else
{
lean_object* v___x_5407_; 
v___x_5407_ = lean_unsigned_to_nat(0u);
v___y_5390_ = v___x_5405_;
v___y_5391_ = v___x_5404_;
v___y_5392_ = v___x_5407_;
goto v___jp_5389_;
}
}
}
}
}
else
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5421_; 
lean_del_object(v___x_5353_);
v___x_5417_ = lean_nat_add(v___x_5357_, v_size_5358_);
lean_dec(v_size_5358_);
v___x_5418_ = lean_nat_add(v___x_5417_, v_size_5359_);
lean_dec(v_size_5359_);
v___x_5419_ = lean_nat_add(v___x_5417_, v_size_5375_);
lean_dec(v___x_5417_);
lean_inc_ref(v_impl_5356_);
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 4, v_l_5362_);
lean_ctor_set(v___x_5373_, 3, v_impl_5356_);
lean_ctor_set(v___x_5373_, 2, v_v_5349_);
lean_ctor_set(v___x_5373_, 1, v_k_5348_);
lean_ctor_set(v___x_5373_, 0, v___x_5419_);
v___x_5421_ = v___x_5373_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v___x_5419_);
lean_ctor_set(v_reuseFailAlloc_5434_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5434_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5434_, 3, v_impl_5356_);
lean_ctor_set(v_reuseFailAlloc_5434_, 4, v_l_5362_);
v___x_5421_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
v_isSharedCheck_5428_ = !lean_is_exclusive(v_impl_5356_);
if (v_isSharedCheck_5428_ == 0)
{
lean_object* v_unused_5429_; lean_object* v_unused_5430_; lean_object* v_unused_5431_; lean_object* v_unused_5432_; lean_object* v_unused_5433_; 
v_unused_5429_ = lean_ctor_get(v_impl_5356_, 4);
lean_dec(v_unused_5429_);
v_unused_5430_ = lean_ctor_get(v_impl_5356_, 3);
lean_dec(v_unused_5430_);
v_unused_5431_ = lean_ctor_get(v_impl_5356_, 2);
lean_dec(v_unused_5431_);
v_unused_5432_ = lean_ctor_get(v_impl_5356_, 1);
lean_dec(v_unused_5432_);
v_unused_5433_ = lean_ctor_get(v_impl_5356_, 0);
lean_dec(v_unused_5433_);
v___x_5423_ = v_impl_5356_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_dec(v_impl_5356_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5426_; 
if (v_isShared_5424_ == 0)
{
lean_ctor_set(v___x_5423_, 4, v_r_5363_);
lean_ctor_set(v___x_5423_, 3, v___x_5421_);
lean_ctor_set(v___x_5423_, 2, v_v_5361_);
lean_ctor_set(v___x_5423_, 1, v_k_5360_);
lean_ctor_set(v___x_5423_, 0, v___x_5418_);
v___x_5426_ = v___x_5423_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v___x_5418_);
lean_ctor_set(v_reuseFailAlloc_5427_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5427_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5427_, 3, v___x_5421_);
lean_ctor_set(v_reuseFailAlloc_5427_, 4, v_r_5363_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5441_; lean_object* v___x_5442_; lean_object* v___x_5444_; 
v_size_5441_ = lean_ctor_get(v_impl_5356_, 0);
lean_inc(v_size_5441_);
v___x_5442_ = lean_nat_add(v___x_5357_, v_size_5441_);
lean_dec(v_size_5441_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 3, v_impl_5356_);
lean_ctor_set(v___x_5353_, 0, v___x_5442_);
v___x_5444_ = v___x_5353_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v___x_5442_);
lean_ctor_set(v_reuseFailAlloc_5445_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5445_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5445_, 3, v_impl_5356_);
lean_ctor_set(v_reuseFailAlloc_5445_, 4, v_r_5351_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
else
{
if (lean_obj_tag(v_r_5351_) == 0)
{
lean_object* v_l_5446_; 
v_l_5446_ = lean_ctor_get(v_r_5351_, 3);
lean_inc(v_l_5446_);
if (lean_obj_tag(v_l_5446_) == 0)
{
lean_object* v_r_5447_; 
v_r_5447_ = lean_ctor_get(v_r_5351_, 4);
lean_inc(v_r_5447_);
if (lean_obj_tag(v_r_5447_) == 0)
{
lean_object* v_size_5448_; lean_object* v_k_5449_; lean_object* v_v_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5463_; 
v_size_5448_ = lean_ctor_get(v_r_5351_, 0);
v_k_5449_ = lean_ctor_get(v_r_5351_, 1);
v_v_5450_ = lean_ctor_get(v_r_5351_, 2);
v_isSharedCheck_5463_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5463_ == 0)
{
lean_object* v_unused_5464_; lean_object* v_unused_5465_; 
v_unused_5464_ = lean_ctor_get(v_r_5351_, 4);
lean_dec(v_unused_5464_);
v_unused_5465_ = lean_ctor_get(v_r_5351_, 3);
lean_dec(v_unused_5465_);
v___x_5452_ = v_r_5351_;
v_isShared_5453_ = v_isSharedCheck_5463_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_v_5450_);
lean_inc(v_k_5449_);
lean_inc(v_size_5448_);
lean_dec(v_r_5351_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5463_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v_size_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5458_; 
v_size_5454_ = lean_ctor_get(v_l_5446_, 0);
v___x_5455_ = lean_nat_add(v___x_5357_, v_size_5448_);
lean_dec(v_size_5448_);
v___x_5456_ = lean_nat_add(v___x_5357_, v_size_5454_);
if (v_isShared_5453_ == 0)
{
lean_ctor_set(v___x_5452_, 4, v_l_5446_);
lean_ctor_set(v___x_5452_, 3, v_impl_5356_);
lean_ctor_set(v___x_5452_, 2, v_v_5349_);
lean_ctor_set(v___x_5452_, 1, v_k_5348_);
lean_ctor_set(v___x_5452_, 0, v___x_5456_);
v___x_5458_ = v___x_5452_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v___x_5456_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5462_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5462_, 3, v_impl_5356_);
lean_ctor_set(v_reuseFailAlloc_5462_, 4, v_l_5446_);
v___x_5458_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
lean_object* v___x_5460_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_r_5447_);
lean_ctor_set(v___x_5353_, 3, v___x_5458_);
lean_ctor_set(v___x_5353_, 2, v_v_5450_);
lean_ctor_set(v___x_5353_, 1, v_k_5449_);
lean_ctor_set(v___x_5353_, 0, v___x_5455_);
v___x_5460_ = v___x_5353_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5455_);
lean_ctor_set(v_reuseFailAlloc_5461_, 1, v_k_5449_);
lean_ctor_set(v_reuseFailAlloc_5461_, 2, v_v_5450_);
lean_ctor_set(v_reuseFailAlloc_5461_, 3, v___x_5458_);
lean_ctor_set(v_reuseFailAlloc_5461_, 4, v_r_5447_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
else
{
lean_object* v_k_5466_; lean_object* v_v_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5490_; 
v_k_5466_ = lean_ctor_get(v_r_5351_, 1);
v_v_5467_ = lean_ctor_get(v_r_5351_, 2);
v_isSharedCheck_5490_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5490_ == 0)
{
lean_object* v_unused_5491_; lean_object* v_unused_5492_; lean_object* v_unused_5493_; 
v_unused_5491_ = lean_ctor_get(v_r_5351_, 4);
lean_dec(v_unused_5491_);
v_unused_5492_ = lean_ctor_get(v_r_5351_, 3);
lean_dec(v_unused_5492_);
v_unused_5493_ = lean_ctor_get(v_r_5351_, 0);
lean_dec(v_unused_5493_);
v___x_5469_ = v_r_5351_;
v_isShared_5470_ = v_isSharedCheck_5490_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_v_5467_);
lean_inc(v_k_5466_);
lean_dec(v_r_5351_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5490_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
lean_object* v_k_5471_; lean_object* v_v_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5486_; 
v_k_5471_ = lean_ctor_get(v_l_5446_, 1);
v_v_5472_ = lean_ctor_get(v_l_5446_, 2);
v_isSharedCheck_5486_ = !lean_is_exclusive(v_l_5446_);
if (v_isSharedCheck_5486_ == 0)
{
lean_object* v_unused_5487_; lean_object* v_unused_5488_; lean_object* v_unused_5489_; 
v_unused_5487_ = lean_ctor_get(v_l_5446_, 4);
lean_dec(v_unused_5487_);
v_unused_5488_ = lean_ctor_get(v_l_5446_, 3);
lean_dec(v_unused_5488_);
v_unused_5489_ = lean_ctor_get(v_l_5446_, 0);
lean_dec(v_unused_5489_);
v___x_5474_ = v_l_5446_;
v_isShared_5475_ = v_isSharedCheck_5486_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_v_5472_);
lean_inc(v_k_5471_);
lean_dec(v_l_5446_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5486_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___x_5476_; lean_object* v___x_5478_; 
v___x_5476_ = lean_unsigned_to_nat(3u);
if (v_isShared_5475_ == 0)
{
lean_ctor_set(v___x_5474_, 4, v_r_5447_);
lean_ctor_set(v___x_5474_, 3, v_r_5447_);
lean_ctor_set(v___x_5474_, 2, v_v_5349_);
lean_ctor_set(v___x_5474_, 1, v_k_5348_);
lean_ctor_set(v___x_5474_, 0, v___x_5357_);
v___x_5478_ = v___x_5474_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v___x_5357_);
lean_ctor_set(v_reuseFailAlloc_5485_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5485_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5485_, 3, v_r_5447_);
lean_ctor_set(v_reuseFailAlloc_5485_, 4, v_r_5447_);
v___x_5478_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
lean_object* v___x_5480_; 
if (v_isShared_5470_ == 0)
{
lean_ctor_set(v___x_5469_, 3, v_r_5447_);
lean_ctor_set(v___x_5469_, 0, v___x_5357_);
v___x_5480_ = v___x_5469_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5357_);
lean_ctor_set(v_reuseFailAlloc_5484_, 1, v_k_5466_);
lean_ctor_set(v_reuseFailAlloc_5484_, 2, v_v_5467_);
lean_ctor_set(v_reuseFailAlloc_5484_, 3, v_r_5447_);
lean_ctor_set(v_reuseFailAlloc_5484_, 4, v_r_5447_);
v___x_5480_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
lean_object* v___x_5482_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v___x_5480_);
lean_ctor_set(v___x_5353_, 3, v___x_5478_);
lean_ctor_set(v___x_5353_, 2, v_v_5472_);
lean_ctor_set(v___x_5353_, 1, v_k_5471_);
lean_ctor_set(v___x_5353_, 0, v___x_5476_);
v___x_5482_ = v___x_5353_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5483_, 1, v_k_5471_);
lean_ctor_set(v_reuseFailAlloc_5483_, 2, v_v_5472_);
lean_ctor_set(v_reuseFailAlloc_5483_, 3, v___x_5478_);
lean_ctor_set(v_reuseFailAlloc_5483_, 4, v___x_5480_);
v___x_5482_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
return v___x_5482_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_5494_; 
v_r_5494_ = lean_ctor_get(v_r_5351_, 4);
lean_inc(v_r_5494_);
if (lean_obj_tag(v_r_5494_) == 0)
{
lean_object* v_k_5495_; lean_object* v_v_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5507_; 
v_k_5495_ = lean_ctor_get(v_r_5351_, 1);
v_v_5496_ = lean_ctor_get(v_r_5351_, 2);
v_isSharedCheck_5507_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5507_ == 0)
{
lean_object* v_unused_5508_; lean_object* v_unused_5509_; lean_object* v_unused_5510_; 
v_unused_5508_ = lean_ctor_get(v_r_5351_, 4);
lean_dec(v_unused_5508_);
v_unused_5509_ = lean_ctor_get(v_r_5351_, 3);
lean_dec(v_unused_5509_);
v_unused_5510_ = lean_ctor_get(v_r_5351_, 0);
lean_dec(v_unused_5510_);
v___x_5498_ = v_r_5351_;
v_isShared_5499_ = v_isSharedCheck_5507_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_v_5496_);
lean_inc(v_k_5495_);
lean_dec(v_r_5351_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5507_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v___x_5500_; lean_object* v___x_5502_; 
v___x_5500_ = lean_unsigned_to_nat(3u);
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 4, v_l_5446_);
lean_ctor_set(v___x_5498_, 2, v_v_5349_);
lean_ctor_set(v___x_5498_, 1, v_k_5348_);
lean_ctor_set(v___x_5498_, 0, v___x_5357_);
v___x_5502_ = v___x_5498_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5357_);
lean_ctor_set(v_reuseFailAlloc_5506_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5506_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5506_, 3, v_l_5446_);
lean_ctor_set(v_reuseFailAlloc_5506_, 4, v_l_5446_);
v___x_5502_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5504_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_r_5494_);
lean_ctor_set(v___x_5353_, 3, v___x_5502_);
lean_ctor_set(v___x_5353_, 2, v_v_5496_);
lean_ctor_set(v___x_5353_, 1, v_k_5495_);
lean_ctor_set(v___x_5353_, 0, v___x_5500_);
v___x_5504_ = v___x_5353_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5500_);
lean_ctor_set(v_reuseFailAlloc_5505_, 1, v_k_5495_);
lean_ctor_set(v_reuseFailAlloc_5505_, 2, v_v_5496_);
lean_ctor_set(v_reuseFailAlloc_5505_, 3, v___x_5502_);
lean_ctor_set(v_reuseFailAlloc_5505_, 4, v_r_5494_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
else
{
lean_object* v_size_5511_; lean_object* v_k_5512_; lean_object* v_v_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5524_; 
v_size_5511_ = lean_ctor_get(v_r_5351_, 0);
v_k_5512_ = lean_ctor_get(v_r_5351_, 1);
v_v_5513_ = lean_ctor_get(v_r_5351_, 2);
v_isSharedCheck_5524_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5524_ == 0)
{
lean_object* v_unused_5525_; lean_object* v_unused_5526_; 
v_unused_5525_ = lean_ctor_get(v_r_5351_, 4);
lean_dec(v_unused_5525_);
v_unused_5526_ = lean_ctor_get(v_r_5351_, 3);
lean_dec(v_unused_5526_);
v___x_5515_ = v_r_5351_;
v_isShared_5516_ = v_isSharedCheck_5524_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_v_5513_);
lean_inc(v_k_5512_);
lean_inc(v_size_5511_);
lean_dec(v_r_5351_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5524_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5518_; 
if (v_isShared_5516_ == 0)
{
lean_ctor_set(v___x_5515_, 3, v_r_5494_);
v___x_5518_ = v___x_5515_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_size_5511_);
lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_k_5512_);
lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_v_5513_);
lean_ctor_set(v_reuseFailAlloc_5523_, 3, v_r_5494_);
lean_ctor_set(v_reuseFailAlloc_5523_, 4, v_r_5494_);
v___x_5518_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
lean_object* v___x_5519_; lean_object* v___x_5521_; 
v___x_5519_ = lean_unsigned_to_nat(2u);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v___x_5518_);
lean_ctor_set(v___x_5353_, 3, v_r_5494_);
lean_ctor_set(v___x_5353_, 0, v___x_5519_);
v___x_5521_ = v___x_5353_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5519_);
lean_ctor_set(v_reuseFailAlloc_5522_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5522_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5522_, 3, v_r_5494_);
lean_ctor_set(v_reuseFailAlloc_5522_, 4, v___x_5518_);
v___x_5521_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
return v___x_5521_;
}
}
}
}
}
}
else
{
lean_object* v___x_5528_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 3, v_r_5351_);
lean_ctor_set(v___x_5353_, 0, v___x_5357_);
v___x_5528_ = v___x_5353_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5357_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5529_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5529_, 3, v_r_5351_);
lean_ctor_set(v_reuseFailAlloc_5529_, 4, v_r_5351_);
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
case 1:
{
lean_del_object(v___x_5353_);
lean_dec(v_v_5349_);
lean_dec(v_k_5348_);
if (lean_obj_tag(v_l_5350_) == 0)
{
if (lean_obj_tag(v_r_5351_) == 0)
{
lean_object* v_size_5530_; lean_object* v_k_5531_; lean_object* v_v_5532_; lean_object* v_l_5533_; lean_object* v_r_5534_; lean_object* v_size_5535_; lean_object* v_k_5536_; lean_object* v_v_5537_; lean_object* v_l_5538_; lean_object* v_r_5539_; lean_object* v___x_5540_; uint8_t v___x_5541_; 
v_size_5530_ = lean_ctor_get(v_l_5350_, 0);
v_k_5531_ = lean_ctor_get(v_l_5350_, 1);
v_v_5532_ = lean_ctor_get(v_l_5350_, 2);
v_l_5533_ = lean_ctor_get(v_l_5350_, 3);
v_r_5534_ = lean_ctor_get(v_l_5350_, 4);
lean_inc(v_r_5534_);
v_size_5535_ = lean_ctor_get(v_r_5351_, 0);
v_k_5536_ = lean_ctor_get(v_r_5351_, 1);
v_v_5537_ = lean_ctor_get(v_r_5351_, 2);
v_l_5538_ = lean_ctor_get(v_r_5351_, 3);
lean_inc(v_l_5538_);
v_r_5539_ = lean_ctor_get(v_r_5351_, 4);
v___x_5540_ = lean_unsigned_to_nat(1u);
v___x_5541_ = lean_nat_dec_lt(v_size_5530_, v_size_5535_);
if (v___x_5541_ == 0)
{
lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5677_; 
lean_inc(v_l_5533_);
lean_inc(v_v_5532_);
lean_inc(v_k_5531_);
v_isSharedCheck_5677_ = !lean_is_exclusive(v_l_5350_);
if (v_isSharedCheck_5677_ == 0)
{
lean_object* v_unused_5678_; lean_object* v_unused_5679_; lean_object* v_unused_5680_; lean_object* v_unused_5681_; lean_object* v_unused_5682_; 
v_unused_5678_ = lean_ctor_get(v_l_5350_, 4);
lean_dec(v_unused_5678_);
v_unused_5679_ = lean_ctor_get(v_l_5350_, 3);
lean_dec(v_unused_5679_);
v_unused_5680_ = lean_ctor_get(v_l_5350_, 2);
lean_dec(v_unused_5680_);
v_unused_5681_ = lean_ctor_get(v_l_5350_, 1);
lean_dec(v_unused_5681_);
v_unused_5682_ = lean_ctor_get(v_l_5350_, 0);
lean_dec(v_unused_5682_);
v___x_5543_ = v_l_5350_;
v_isShared_5544_ = v_isSharedCheck_5677_;
goto v_resetjp_5542_;
}
else
{
lean_dec(v_l_5350_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5677_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5545_; lean_object* v_tree_5546_; 
v___x_5545_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5531_, v_v_5532_, v_l_5533_, v_r_5534_);
v_tree_5546_ = lean_ctor_get(v___x_5545_, 2);
lean_inc(v_tree_5546_);
if (lean_obj_tag(v_tree_5546_) == 0)
{
lean_object* v_k_5547_; lean_object* v_v_5548_; lean_object* v_size_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; uint8_t v___x_5552_; 
v_k_5547_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_k_5547_);
v_v_5548_ = lean_ctor_get(v___x_5545_, 1);
lean_inc(v_v_5548_);
lean_dec_ref(v___x_5545_);
v_size_5549_ = lean_ctor_get(v_tree_5546_, 0);
v___x_5550_ = lean_unsigned_to_nat(3u);
v___x_5551_ = lean_nat_mul(v___x_5550_, v_size_5549_);
v___x_5552_ = lean_nat_dec_lt(v___x_5551_, v_size_5535_);
lean_dec(v___x_5551_);
if (v___x_5552_ == 0)
{
lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5556_; 
lean_dec(v_l_5538_);
v___x_5553_ = lean_nat_add(v___x_5540_, v_size_5549_);
v___x_5554_ = lean_nat_add(v___x_5553_, v_size_5535_);
lean_dec(v___x_5553_);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 4, v_r_5351_);
lean_ctor_set(v___x_5543_, 3, v_tree_5546_);
lean_ctor_set(v___x_5543_, 2, v_v_5548_);
lean_ctor_set(v___x_5543_, 1, v_k_5547_);
lean_ctor_set(v___x_5543_, 0, v___x_5554_);
v___x_5556_ = v___x_5543_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5554_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v_k_5547_);
lean_ctor_set(v_reuseFailAlloc_5557_, 2, v_v_5548_);
lean_ctor_set(v_reuseFailAlloc_5557_, 3, v_tree_5546_);
lean_ctor_set(v_reuseFailAlloc_5557_, 4, v_r_5351_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
else
{
lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5612_; 
lean_inc(v_r_5539_);
lean_inc(v_v_5537_);
lean_inc(v_k_5536_);
lean_inc(v_size_5535_);
v_isSharedCheck_5612_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5612_ == 0)
{
lean_object* v_unused_5613_; lean_object* v_unused_5614_; lean_object* v_unused_5615_; lean_object* v_unused_5616_; lean_object* v_unused_5617_; 
v_unused_5613_ = lean_ctor_get(v_r_5351_, 4);
lean_dec(v_unused_5613_);
v_unused_5614_ = lean_ctor_get(v_r_5351_, 3);
lean_dec(v_unused_5614_);
v_unused_5615_ = lean_ctor_get(v_r_5351_, 2);
lean_dec(v_unused_5615_);
v_unused_5616_ = lean_ctor_get(v_r_5351_, 1);
lean_dec(v_unused_5616_);
v_unused_5617_ = lean_ctor_get(v_r_5351_, 0);
lean_dec(v_unused_5617_);
v___x_5559_ = v_r_5351_;
v_isShared_5560_ = v_isSharedCheck_5612_;
goto v_resetjp_5558_;
}
else
{
lean_dec(v_r_5351_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5612_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v_size_5561_; lean_object* v_k_5562_; lean_object* v_v_5563_; lean_object* v_l_5564_; lean_object* v_r_5565_; lean_object* v_size_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; uint8_t v___x_5569_; 
v_size_5561_ = lean_ctor_get(v_l_5538_, 0);
v_k_5562_ = lean_ctor_get(v_l_5538_, 1);
v_v_5563_ = lean_ctor_get(v_l_5538_, 2);
v_l_5564_ = lean_ctor_get(v_l_5538_, 3);
v_r_5565_ = lean_ctor_get(v_l_5538_, 4);
v_size_5566_ = lean_ctor_get(v_r_5539_, 0);
v___x_5567_ = lean_unsigned_to_nat(2u);
v___x_5568_ = lean_nat_mul(v___x_5567_, v_size_5566_);
v___x_5569_ = lean_nat_dec_lt(v_size_5561_, v___x_5568_);
lean_dec(v___x_5568_);
if (v___x_5569_ == 0)
{
lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5597_; 
lean_inc(v_r_5565_);
lean_inc(v_l_5564_);
lean_inc(v_v_5563_);
lean_inc(v_k_5562_);
v_isSharedCheck_5597_ = !lean_is_exclusive(v_l_5538_);
if (v_isSharedCheck_5597_ == 0)
{
lean_object* v_unused_5598_; lean_object* v_unused_5599_; lean_object* v_unused_5600_; lean_object* v_unused_5601_; lean_object* v_unused_5602_; 
v_unused_5598_ = lean_ctor_get(v_l_5538_, 4);
lean_dec(v_unused_5598_);
v_unused_5599_ = lean_ctor_get(v_l_5538_, 3);
lean_dec(v_unused_5599_);
v_unused_5600_ = lean_ctor_get(v_l_5538_, 2);
lean_dec(v_unused_5600_);
v_unused_5601_ = lean_ctor_get(v_l_5538_, 1);
lean_dec(v_unused_5601_);
v_unused_5602_ = lean_ctor_get(v_l_5538_, 0);
lean_dec(v_unused_5602_);
v___x_5571_ = v_l_5538_;
v_isShared_5572_ = v_isSharedCheck_5597_;
goto v_resetjp_5570_;
}
else
{
lean_dec(v_l_5538_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5597_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___y_5576_; lean_object* v___y_5577_; lean_object* v___y_5578_; lean_object* v___y_5587_; 
v___x_5573_ = lean_nat_add(v___x_5540_, v_size_5549_);
v___x_5574_ = lean_nat_add(v___x_5573_, v_size_5535_);
lean_dec(v_size_5535_);
if (lean_obj_tag(v_l_5564_) == 0)
{
lean_object* v_size_5595_; 
v_size_5595_ = lean_ctor_get(v_l_5564_, 0);
lean_inc(v_size_5595_);
v___y_5587_ = v_size_5595_;
goto v___jp_5586_;
}
else
{
lean_object* v___x_5596_; 
v___x_5596_ = lean_unsigned_to_nat(0u);
v___y_5587_ = v___x_5596_;
goto v___jp_5586_;
}
v___jp_5575_:
{
lean_object* v___x_5579_; lean_object* v___x_5581_; 
v___x_5579_ = lean_nat_add(v___y_5576_, v___y_5578_);
lean_dec(v___y_5578_);
lean_dec(v___y_5576_);
if (v_isShared_5572_ == 0)
{
lean_ctor_set(v___x_5571_, 4, v_r_5539_);
lean_ctor_set(v___x_5571_, 3, v_r_5565_);
lean_ctor_set(v___x_5571_, 2, v_v_5537_);
lean_ctor_set(v___x_5571_, 1, v_k_5536_);
lean_ctor_set(v___x_5571_, 0, v___x_5579_);
v___x_5581_ = v___x_5571_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5579_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_k_5536_);
lean_ctor_set(v_reuseFailAlloc_5585_, 2, v_v_5537_);
lean_ctor_set(v_reuseFailAlloc_5585_, 3, v_r_5565_);
lean_ctor_set(v_reuseFailAlloc_5585_, 4, v_r_5539_);
v___x_5581_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
lean_object* v___x_5583_; 
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 4, v___x_5581_);
lean_ctor_set(v___x_5559_, 3, v___y_5577_);
lean_ctor_set(v___x_5559_, 2, v_v_5563_);
lean_ctor_set(v___x_5559_, 1, v_k_5562_);
lean_ctor_set(v___x_5559_, 0, v___x_5574_);
v___x_5583_ = v___x_5559_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5574_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v_k_5562_);
lean_ctor_set(v_reuseFailAlloc_5584_, 2, v_v_5563_);
lean_ctor_set(v_reuseFailAlloc_5584_, 3, v___y_5577_);
lean_ctor_set(v_reuseFailAlloc_5584_, 4, v___x_5581_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
return v___x_5583_;
}
}
}
v___jp_5586_:
{
lean_object* v___x_5588_; lean_object* v___x_5590_; 
v___x_5588_ = lean_nat_add(v___x_5573_, v___y_5587_);
lean_dec(v___y_5587_);
lean_dec(v___x_5573_);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 4, v_l_5564_);
lean_ctor_set(v___x_5543_, 3, v_tree_5546_);
lean_ctor_set(v___x_5543_, 2, v_v_5548_);
lean_ctor_set(v___x_5543_, 1, v_k_5547_);
lean_ctor_set(v___x_5543_, 0, v___x_5588_);
v___x_5590_ = v___x_5543_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5588_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v_k_5547_);
lean_ctor_set(v_reuseFailAlloc_5594_, 2, v_v_5548_);
lean_ctor_set(v_reuseFailAlloc_5594_, 3, v_tree_5546_);
lean_ctor_set(v_reuseFailAlloc_5594_, 4, v_l_5564_);
v___x_5590_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
lean_object* v___x_5591_; 
v___x_5591_ = lean_nat_add(v___x_5540_, v_size_5566_);
if (lean_obj_tag(v_r_5565_) == 0)
{
lean_object* v_size_5592_; 
v_size_5592_ = lean_ctor_get(v_r_5565_, 0);
lean_inc(v_size_5592_);
v___y_5576_ = v___x_5591_;
v___y_5577_ = v___x_5590_;
v___y_5578_ = v_size_5592_;
goto v___jp_5575_;
}
else
{
lean_object* v___x_5593_; 
v___x_5593_ = lean_unsigned_to_nat(0u);
v___y_5576_ = v___x_5591_;
v___y_5577_ = v___x_5590_;
v___y_5578_ = v___x_5593_;
goto v___jp_5575_;
}
}
}
}
}
else
{
lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5607_; 
v___x_5603_ = lean_nat_add(v___x_5540_, v_size_5549_);
v___x_5604_ = lean_nat_add(v___x_5603_, v_size_5535_);
lean_dec(v_size_5535_);
v___x_5605_ = lean_nat_add(v___x_5603_, v_size_5561_);
lean_dec(v___x_5603_);
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 4, v_l_5538_);
lean_ctor_set(v___x_5559_, 3, v_tree_5546_);
lean_ctor_set(v___x_5559_, 2, v_v_5548_);
lean_ctor_set(v___x_5559_, 1, v_k_5547_);
lean_ctor_set(v___x_5559_, 0, v___x_5605_);
v___x_5607_ = v___x_5559_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v___x_5605_);
lean_ctor_set(v_reuseFailAlloc_5611_, 1, v_k_5547_);
lean_ctor_set(v_reuseFailAlloc_5611_, 2, v_v_5548_);
lean_ctor_set(v_reuseFailAlloc_5611_, 3, v_tree_5546_);
lean_ctor_set(v_reuseFailAlloc_5611_, 4, v_l_5538_);
v___x_5607_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
lean_object* v___x_5609_; 
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 4, v_r_5539_);
lean_ctor_set(v___x_5543_, 3, v___x_5607_);
lean_ctor_set(v___x_5543_, 2, v_v_5537_);
lean_ctor_set(v___x_5543_, 1, v_k_5536_);
lean_ctor_set(v___x_5543_, 0, v___x_5604_);
v___x_5609_ = v___x_5543_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v___x_5604_);
lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_k_5536_);
lean_ctor_set(v_reuseFailAlloc_5610_, 2, v_v_5537_);
lean_ctor_set(v_reuseFailAlloc_5610_, 3, v___x_5607_);
lean_ctor_set(v_reuseFailAlloc_5610_, 4, v_r_5539_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
}
}
else
{
lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5671_; 
lean_inc(v_r_5539_);
lean_inc(v_v_5537_);
lean_inc(v_k_5536_);
lean_inc(v_size_5535_);
v_isSharedCheck_5671_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5671_ == 0)
{
lean_object* v_unused_5672_; lean_object* v_unused_5673_; lean_object* v_unused_5674_; lean_object* v_unused_5675_; lean_object* v_unused_5676_; 
v_unused_5672_ = lean_ctor_get(v_r_5351_, 4);
lean_dec(v_unused_5672_);
v_unused_5673_ = lean_ctor_get(v_r_5351_, 3);
lean_dec(v_unused_5673_);
v_unused_5674_ = lean_ctor_get(v_r_5351_, 2);
lean_dec(v_unused_5674_);
v_unused_5675_ = lean_ctor_get(v_r_5351_, 1);
lean_dec(v_unused_5675_);
v_unused_5676_ = lean_ctor_get(v_r_5351_, 0);
lean_dec(v_unused_5676_);
v___x_5619_ = v_r_5351_;
v_isShared_5620_ = v_isSharedCheck_5671_;
goto v_resetjp_5618_;
}
else
{
lean_dec(v_r_5351_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5671_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
if (lean_obj_tag(v_l_5538_) == 0)
{
if (lean_obj_tag(v_r_5539_) == 0)
{
lean_object* v_k_5621_; lean_object* v_v_5622_; lean_object* v_size_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5627_; 
v_k_5621_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_k_5621_);
v_v_5622_ = lean_ctor_get(v___x_5545_, 1);
lean_inc(v_v_5622_);
lean_dec_ref(v___x_5545_);
v_size_5623_ = lean_ctor_get(v_l_5538_, 0);
v___x_5624_ = lean_nat_add(v___x_5540_, v_size_5535_);
lean_dec(v_size_5535_);
v___x_5625_ = lean_nat_add(v___x_5540_, v_size_5623_);
if (v_isShared_5620_ == 0)
{
lean_ctor_set(v___x_5619_, 4, v_l_5538_);
lean_ctor_set(v___x_5619_, 3, v_tree_5546_);
lean_ctor_set(v___x_5619_, 2, v_v_5622_);
lean_ctor_set(v___x_5619_, 1, v_k_5621_);
lean_ctor_set(v___x_5619_, 0, v___x_5625_);
v___x_5627_ = v___x_5619_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v___x_5625_);
lean_ctor_set(v_reuseFailAlloc_5631_, 1, v_k_5621_);
lean_ctor_set(v_reuseFailAlloc_5631_, 2, v_v_5622_);
lean_ctor_set(v_reuseFailAlloc_5631_, 3, v_tree_5546_);
lean_ctor_set(v_reuseFailAlloc_5631_, 4, v_l_5538_);
v___x_5627_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
lean_object* v___x_5629_; 
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 4, v_r_5539_);
lean_ctor_set(v___x_5543_, 3, v___x_5627_);
lean_ctor_set(v___x_5543_, 2, v_v_5537_);
lean_ctor_set(v___x_5543_, 1, v_k_5536_);
lean_ctor_set(v___x_5543_, 0, v___x_5624_);
v___x_5629_ = v___x_5543_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5624_);
lean_ctor_set(v_reuseFailAlloc_5630_, 1, v_k_5536_);
lean_ctor_set(v_reuseFailAlloc_5630_, 2, v_v_5537_);
lean_ctor_set(v_reuseFailAlloc_5630_, 3, v___x_5627_);
lean_ctor_set(v_reuseFailAlloc_5630_, 4, v_r_5539_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
else
{
lean_object* v_k_5632_; lean_object* v_v_5633_; lean_object* v_k_5634_; lean_object* v_v_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5649_; 
lean_dec(v_size_5535_);
v_k_5632_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_k_5632_);
v_v_5633_ = lean_ctor_get(v___x_5545_, 1);
lean_inc(v_v_5633_);
lean_dec_ref(v___x_5545_);
v_k_5634_ = lean_ctor_get(v_l_5538_, 1);
v_v_5635_ = lean_ctor_get(v_l_5538_, 2);
v_isSharedCheck_5649_ = !lean_is_exclusive(v_l_5538_);
if (v_isSharedCheck_5649_ == 0)
{
lean_object* v_unused_5650_; lean_object* v_unused_5651_; lean_object* v_unused_5652_; 
v_unused_5650_ = lean_ctor_get(v_l_5538_, 4);
lean_dec(v_unused_5650_);
v_unused_5651_ = lean_ctor_get(v_l_5538_, 3);
lean_dec(v_unused_5651_);
v_unused_5652_ = lean_ctor_get(v_l_5538_, 0);
lean_dec(v_unused_5652_);
v___x_5637_ = v_l_5538_;
v_isShared_5638_ = v_isSharedCheck_5649_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_v_5635_);
lean_inc(v_k_5634_);
lean_dec(v_l_5538_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5649_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v___x_5639_; lean_object* v___x_5641_; 
v___x_5639_ = lean_unsigned_to_nat(3u);
if (v_isShared_5638_ == 0)
{
lean_ctor_set(v___x_5637_, 4, v_r_5539_);
lean_ctor_set(v___x_5637_, 3, v_r_5539_);
lean_ctor_set(v___x_5637_, 2, v_v_5633_);
lean_ctor_set(v___x_5637_, 1, v_k_5632_);
lean_ctor_set(v___x_5637_, 0, v___x_5540_);
v___x_5641_ = v___x_5637_;
goto v_reusejp_5640_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v___x_5540_);
lean_ctor_set(v_reuseFailAlloc_5648_, 1, v_k_5632_);
lean_ctor_set(v_reuseFailAlloc_5648_, 2, v_v_5633_);
lean_ctor_set(v_reuseFailAlloc_5648_, 3, v_r_5539_);
lean_ctor_set(v_reuseFailAlloc_5648_, 4, v_r_5539_);
v___x_5641_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5640_;
}
v_reusejp_5640_:
{
lean_object* v___x_5643_; 
if (v_isShared_5620_ == 0)
{
lean_ctor_set(v___x_5619_, 3, v_r_5539_);
lean_ctor_set(v___x_5619_, 0, v___x_5540_);
v___x_5643_ = v___x_5619_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v___x_5540_);
lean_ctor_set(v_reuseFailAlloc_5647_, 1, v_k_5536_);
lean_ctor_set(v_reuseFailAlloc_5647_, 2, v_v_5537_);
lean_ctor_set(v_reuseFailAlloc_5647_, 3, v_r_5539_);
lean_ctor_set(v_reuseFailAlloc_5647_, 4, v_r_5539_);
v___x_5643_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
lean_object* v___x_5645_; 
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 4, v___x_5643_);
lean_ctor_set(v___x_5543_, 3, v___x_5641_);
lean_ctor_set(v___x_5543_, 2, v_v_5635_);
lean_ctor_set(v___x_5543_, 1, v_k_5634_);
lean_ctor_set(v___x_5543_, 0, v___x_5639_);
v___x_5645_ = v___x_5543_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5639_);
lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_k_5634_);
lean_ctor_set(v_reuseFailAlloc_5646_, 2, v_v_5635_);
lean_ctor_set(v_reuseFailAlloc_5646_, 3, v___x_5641_);
lean_ctor_set(v_reuseFailAlloc_5646_, 4, v___x_5643_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5539_) == 0)
{
lean_object* v_k_5653_; lean_object* v_v_5654_; lean_object* v___x_5655_; lean_object* v___x_5657_; 
lean_dec(v_size_5535_);
v_k_5653_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_k_5653_);
v_v_5654_ = lean_ctor_get(v___x_5545_, 1);
lean_inc(v_v_5654_);
lean_dec_ref(v___x_5545_);
v___x_5655_ = lean_unsigned_to_nat(3u);
if (v_isShared_5620_ == 0)
{
lean_ctor_set(v___x_5619_, 4, v_l_5538_);
lean_ctor_set(v___x_5619_, 2, v_v_5654_);
lean_ctor_set(v___x_5619_, 1, v_k_5653_);
lean_ctor_set(v___x_5619_, 0, v___x_5540_);
v___x_5657_ = v___x_5619_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v___x_5540_);
lean_ctor_set(v_reuseFailAlloc_5661_, 1, v_k_5653_);
lean_ctor_set(v_reuseFailAlloc_5661_, 2, v_v_5654_);
lean_ctor_set(v_reuseFailAlloc_5661_, 3, v_l_5538_);
lean_ctor_set(v_reuseFailAlloc_5661_, 4, v_l_5538_);
v___x_5657_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
lean_object* v___x_5659_; 
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 4, v_r_5539_);
lean_ctor_set(v___x_5543_, 3, v___x_5657_);
lean_ctor_set(v___x_5543_, 2, v_v_5537_);
lean_ctor_set(v___x_5543_, 1, v_k_5536_);
lean_ctor_set(v___x_5543_, 0, v___x_5655_);
v___x_5659_ = v___x_5543_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v___x_5655_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v_k_5536_);
lean_ctor_set(v_reuseFailAlloc_5660_, 2, v_v_5537_);
lean_ctor_set(v_reuseFailAlloc_5660_, 3, v___x_5657_);
lean_ctor_set(v_reuseFailAlloc_5660_, 4, v_r_5539_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
return v___x_5659_;
}
}
}
else
{
lean_object* v_k_5662_; lean_object* v_v_5663_; lean_object* v___x_5665_; 
v_k_5662_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_k_5662_);
v_v_5663_ = lean_ctor_get(v___x_5545_, 1);
lean_inc(v_v_5663_);
lean_dec_ref(v___x_5545_);
if (v_isShared_5620_ == 0)
{
lean_ctor_set(v___x_5619_, 3, v_r_5539_);
v___x_5665_ = v___x_5619_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_size_5535_);
lean_ctor_set(v_reuseFailAlloc_5670_, 1, v_k_5536_);
lean_ctor_set(v_reuseFailAlloc_5670_, 2, v_v_5537_);
lean_ctor_set(v_reuseFailAlloc_5670_, 3, v_r_5539_);
lean_ctor_set(v_reuseFailAlloc_5670_, 4, v_r_5539_);
v___x_5665_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
lean_object* v___x_5666_; lean_object* v___x_5668_; 
v___x_5666_ = lean_unsigned_to_nat(2u);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 4, v___x_5665_);
lean_ctor_set(v___x_5543_, 3, v_r_5539_);
lean_ctor_set(v___x_5543_, 2, v_v_5663_);
lean_ctor_set(v___x_5543_, 1, v_k_5662_);
lean_ctor_set(v___x_5543_, 0, v___x_5666_);
v___x_5668_ = v___x_5543_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v___x_5666_);
lean_ctor_set(v_reuseFailAlloc_5669_, 1, v_k_5662_);
lean_ctor_set(v_reuseFailAlloc_5669_, 2, v_v_5663_);
lean_ctor_set(v_reuseFailAlloc_5669_, 3, v_r_5539_);
lean_ctor_set(v_reuseFailAlloc_5669_, 4, v___x_5665_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
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
lean_object* v___x_5684_; uint8_t v_isShared_5685_; uint8_t v_isSharedCheck_5835_; 
lean_inc(v_r_5539_);
lean_inc(v_v_5537_);
lean_inc(v_k_5536_);
v_isSharedCheck_5835_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5835_ == 0)
{
lean_object* v_unused_5836_; lean_object* v_unused_5837_; lean_object* v_unused_5838_; lean_object* v_unused_5839_; lean_object* v_unused_5840_; 
v_unused_5836_ = lean_ctor_get(v_r_5351_, 4);
lean_dec(v_unused_5836_);
v_unused_5837_ = lean_ctor_get(v_r_5351_, 3);
lean_dec(v_unused_5837_);
v_unused_5838_ = lean_ctor_get(v_r_5351_, 2);
lean_dec(v_unused_5838_);
v_unused_5839_ = lean_ctor_get(v_r_5351_, 1);
lean_dec(v_unused_5839_);
v_unused_5840_ = lean_ctor_get(v_r_5351_, 0);
lean_dec(v_unused_5840_);
v___x_5684_ = v_r_5351_;
v_isShared_5685_ = v_isSharedCheck_5835_;
goto v_resetjp_5683_;
}
else
{
lean_dec(v_r_5351_);
v___x_5684_ = lean_box(0);
v_isShared_5685_ = v_isSharedCheck_5835_;
goto v_resetjp_5683_;
}
v_resetjp_5683_:
{
lean_object* v___x_5686_; lean_object* v_tree_5687_; 
v___x_5686_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5536_, v_v_5537_, v_l_5538_, v_r_5539_);
v_tree_5687_ = lean_ctor_get(v___x_5686_, 2);
lean_inc(v_tree_5687_);
if (lean_obj_tag(v_tree_5687_) == 0)
{
lean_object* v_k_5688_; lean_object* v_v_5689_; lean_object* v_size_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; uint8_t v___x_5693_; 
v_k_5688_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_k_5688_);
v_v_5689_ = lean_ctor_get(v___x_5686_, 1);
lean_inc(v_v_5689_);
lean_dec_ref(v___x_5686_);
v_size_5690_ = lean_ctor_get(v_tree_5687_, 0);
v___x_5691_ = lean_unsigned_to_nat(3u);
v___x_5692_ = lean_nat_mul(v___x_5691_, v_size_5690_);
v___x_5693_ = lean_nat_dec_lt(v___x_5692_, v_size_5530_);
lean_dec(v___x_5692_);
if (v___x_5693_ == 0)
{
lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5697_; 
lean_dec(v_r_5534_);
v___x_5694_ = lean_nat_add(v___x_5540_, v_size_5530_);
v___x_5695_ = lean_nat_add(v___x_5694_, v_size_5690_);
lean_dec(v___x_5694_);
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 4, v_tree_5687_);
lean_ctor_set(v___x_5684_, 3, v_l_5350_);
lean_ctor_set(v___x_5684_, 2, v_v_5689_);
lean_ctor_set(v___x_5684_, 1, v_k_5688_);
lean_ctor_set(v___x_5684_, 0, v___x_5695_);
v___x_5697_ = v___x_5684_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5695_);
lean_ctor_set(v_reuseFailAlloc_5698_, 1, v_k_5688_);
lean_ctor_set(v_reuseFailAlloc_5698_, 2, v_v_5689_);
lean_ctor_set(v_reuseFailAlloc_5698_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_5698_, 4, v_tree_5687_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
else
{
lean_object* v___x_5700_; uint8_t v_isShared_5701_; uint8_t v_isSharedCheck_5764_; 
lean_inc(v_l_5533_);
lean_inc(v_v_5532_);
lean_inc(v_k_5531_);
lean_inc(v_size_5530_);
v_isSharedCheck_5764_ = !lean_is_exclusive(v_l_5350_);
if (v_isSharedCheck_5764_ == 0)
{
lean_object* v_unused_5765_; lean_object* v_unused_5766_; lean_object* v_unused_5767_; lean_object* v_unused_5768_; lean_object* v_unused_5769_; 
v_unused_5765_ = lean_ctor_get(v_l_5350_, 4);
lean_dec(v_unused_5765_);
v_unused_5766_ = lean_ctor_get(v_l_5350_, 3);
lean_dec(v_unused_5766_);
v_unused_5767_ = lean_ctor_get(v_l_5350_, 2);
lean_dec(v_unused_5767_);
v_unused_5768_ = lean_ctor_get(v_l_5350_, 1);
lean_dec(v_unused_5768_);
v_unused_5769_ = lean_ctor_get(v_l_5350_, 0);
lean_dec(v_unused_5769_);
v___x_5700_ = v_l_5350_;
v_isShared_5701_ = v_isSharedCheck_5764_;
goto v_resetjp_5699_;
}
else
{
lean_dec(v_l_5350_);
v___x_5700_ = lean_box(0);
v_isShared_5701_ = v_isSharedCheck_5764_;
goto v_resetjp_5699_;
}
v_resetjp_5699_:
{
lean_object* v_size_5702_; lean_object* v_size_5703_; lean_object* v_k_5704_; lean_object* v_v_5705_; lean_object* v_l_5706_; lean_object* v_r_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; uint8_t v___x_5710_; 
v_size_5702_ = lean_ctor_get(v_l_5533_, 0);
v_size_5703_ = lean_ctor_get(v_r_5534_, 0);
v_k_5704_ = lean_ctor_get(v_r_5534_, 1);
v_v_5705_ = lean_ctor_get(v_r_5534_, 2);
v_l_5706_ = lean_ctor_get(v_r_5534_, 3);
v_r_5707_ = lean_ctor_get(v_r_5534_, 4);
v___x_5708_ = lean_unsigned_to_nat(2u);
v___x_5709_ = lean_nat_mul(v___x_5708_, v_size_5702_);
v___x_5710_ = lean_nat_dec_lt(v_size_5703_, v___x_5709_);
lean_dec(v___x_5709_);
if (v___x_5710_ == 0)
{
lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5748_; 
lean_inc(v_r_5707_);
lean_inc(v_l_5706_);
lean_inc(v_v_5705_);
lean_inc(v_k_5704_);
lean_del_object(v___x_5700_);
v_isSharedCheck_5748_ = !lean_is_exclusive(v_r_5534_);
if (v_isSharedCheck_5748_ == 0)
{
lean_object* v_unused_5749_; lean_object* v_unused_5750_; lean_object* v_unused_5751_; lean_object* v_unused_5752_; lean_object* v_unused_5753_; 
v_unused_5749_ = lean_ctor_get(v_r_5534_, 4);
lean_dec(v_unused_5749_);
v_unused_5750_ = lean_ctor_get(v_r_5534_, 3);
lean_dec(v_unused_5750_);
v_unused_5751_ = lean_ctor_get(v_r_5534_, 2);
lean_dec(v_unused_5751_);
v_unused_5752_ = lean_ctor_get(v_r_5534_, 1);
lean_dec(v_unused_5752_);
v_unused_5753_ = lean_ctor_get(v_r_5534_, 0);
lean_dec(v_unused_5753_);
v___x_5712_ = v_r_5534_;
v_isShared_5713_ = v_isSharedCheck_5748_;
goto v_resetjp_5711_;
}
else
{
lean_dec(v_r_5534_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5748_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___y_5717_; lean_object* v___y_5718_; lean_object* v___y_5719_; lean_object* v___x_5736_; lean_object* v___y_5738_; 
v___x_5714_ = lean_nat_add(v___x_5540_, v_size_5530_);
lean_dec(v_size_5530_);
v___x_5715_ = lean_nat_add(v___x_5714_, v_size_5690_);
lean_dec(v___x_5714_);
v___x_5736_ = lean_nat_add(v___x_5540_, v_size_5702_);
if (lean_obj_tag(v_l_5706_) == 0)
{
lean_object* v_size_5746_; 
v_size_5746_ = lean_ctor_get(v_l_5706_, 0);
lean_inc(v_size_5746_);
v___y_5738_ = v_size_5746_;
goto v___jp_5737_;
}
else
{
lean_object* v___x_5747_; 
v___x_5747_ = lean_unsigned_to_nat(0u);
v___y_5738_ = v___x_5747_;
goto v___jp_5737_;
}
v___jp_5716_:
{
lean_object* v___x_5720_; lean_object* v___x_5722_; 
v___x_5720_ = lean_nat_add(v___y_5717_, v___y_5719_);
lean_dec(v___y_5719_);
lean_dec(v___y_5717_);
lean_inc_ref(v_tree_5687_);
if (v_isShared_5713_ == 0)
{
lean_ctor_set(v___x_5712_, 4, v_tree_5687_);
lean_ctor_set(v___x_5712_, 3, v_r_5707_);
lean_ctor_set(v___x_5712_, 2, v_v_5689_);
lean_ctor_set(v___x_5712_, 1, v_k_5688_);
lean_ctor_set(v___x_5712_, 0, v___x_5720_);
v___x_5722_ = v___x_5712_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v___x_5720_);
lean_ctor_set(v_reuseFailAlloc_5735_, 1, v_k_5688_);
lean_ctor_set(v_reuseFailAlloc_5735_, 2, v_v_5689_);
lean_ctor_set(v_reuseFailAlloc_5735_, 3, v_r_5707_);
lean_ctor_set(v_reuseFailAlloc_5735_, 4, v_tree_5687_);
v___x_5722_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5729_; 
v_isSharedCheck_5729_ = !lean_is_exclusive(v_tree_5687_);
if (v_isSharedCheck_5729_ == 0)
{
lean_object* v_unused_5730_; lean_object* v_unused_5731_; lean_object* v_unused_5732_; lean_object* v_unused_5733_; lean_object* v_unused_5734_; 
v_unused_5730_ = lean_ctor_get(v_tree_5687_, 4);
lean_dec(v_unused_5730_);
v_unused_5731_ = lean_ctor_get(v_tree_5687_, 3);
lean_dec(v_unused_5731_);
v_unused_5732_ = lean_ctor_get(v_tree_5687_, 2);
lean_dec(v_unused_5732_);
v_unused_5733_ = lean_ctor_get(v_tree_5687_, 1);
lean_dec(v_unused_5733_);
v_unused_5734_ = lean_ctor_get(v_tree_5687_, 0);
lean_dec(v_unused_5734_);
v___x_5724_ = v_tree_5687_;
v_isShared_5725_ = v_isSharedCheck_5729_;
goto v_resetjp_5723_;
}
else
{
lean_dec(v_tree_5687_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5729_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v___x_5727_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 4, v___x_5722_);
lean_ctor_set(v___x_5724_, 3, v___y_5718_);
lean_ctor_set(v___x_5724_, 2, v_v_5705_);
lean_ctor_set(v___x_5724_, 1, v_k_5704_);
lean_ctor_set(v___x_5724_, 0, v___x_5715_);
v___x_5727_ = v___x_5724_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v___x_5715_);
lean_ctor_set(v_reuseFailAlloc_5728_, 1, v_k_5704_);
lean_ctor_set(v_reuseFailAlloc_5728_, 2, v_v_5705_);
lean_ctor_set(v_reuseFailAlloc_5728_, 3, v___y_5718_);
lean_ctor_set(v_reuseFailAlloc_5728_, 4, v___x_5722_);
v___x_5727_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
return v___x_5727_;
}
}
}
}
v___jp_5737_:
{
lean_object* v___x_5739_; lean_object* v___x_5741_; 
v___x_5739_ = lean_nat_add(v___x_5736_, v___y_5738_);
lean_dec(v___y_5738_);
lean_dec(v___x_5736_);
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 4, v_l_5706_);
lean_ctor_set(v___x_5684_, 3, v_l_5533_);
lean_ctor_set(v___x_5684_, 2, v_v_5532_);
lean_ctor_set(v___x_5684_, 1, v_k_5531_);
lean_ctor_set(v___x_5684_, 0, v___x_5739_);
v___x_5741_ = v___x_5684_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v___x_5739_);
lean_ctor_set(v_reuseFailAlloc_5745_, 1, v_k_5531_);
lean_ctor_set(v_reuseFailAlloc_5745_, 2, v_v_5532_);
lean_ctor_set(v_reuseFailAlloc_5745_, 3, v_l_5533_);
lean_ctor_set(v_reuseFailAlloc_5745_, 4, v_l_5706_);
v___x_5741_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
lean_object* v___x_5742_; 
v___x_5742_ = lean_nat_add(v___x_5540_, v_size_5690_);
if (lean_obj_tag(v_r_5707_) == 0)
{
lean_object* v_size_5743_; 
v_size_5743_ = lean_ctor_get(v_r_5707_, 0);
lean_inc(v_size_5743_);
v___y_5717_ = v___x_5742_;
v___y_5718_ = v___x_5741_;
v___y_5719_ = v_size_5743_;
goto v___jp_5716_;
}
else
{
lean_object* v___x_5744_; 
v___x_5744_ = lean_unsigned_to_nat(0u);
v___y_5717_ = v___x_5742_;
v___y_5718_ = v___x_5741_;
v___y_5719_ = v___x_5744_;
goto v___jp_5716_;
}
}
}
}
}
else
{
lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5759_; 
v___x_5754_ = lean_nat_add(v___x_5540_, v_size_5530_);
lean_dec(v_size_5530_);
v___x_5755_ = lean_nat_add(v___x_5754_, v_size_5690_);
lean_dec(v___x_5754_);
v___x_5756_ = lean_nat_add(v___x_5540_, v_size_5690_);
v___x_5757_ = lean_nat_add(v___x_5756_, v_size_5703_);
lean_dec(v___x_5756_);
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 4, v_tree_5687_);
lean_ctor_set(v___x_5684_, 3, v_r_5534_);
lean_ctor_set(v___x_5684_, 2, v_v_5689_);
lean_ctor_set(v___x_5684_, 1, v_k_5688_);
lean_ctor_set(v___x_5684_, 0, v___x_5757_);
v___x_5759_ = v___x_5684_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v___x_5757_);
lean_ctor_set(v_reuseFailAlloc_5763_, 1, v_k_5688_);
lean_ctor_set(v_reuseFailAlloc_5763_, 2, v_v_5689_);
lean_ctor_set(v_reuseFailAlloc_5763_, 3, v_r_5534_);
lean_ctor_set(v_reuseFailAlloc_5763_, 4, v_tree_5687_);
v___x_5759_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
lean_object* v___x_5761_; 
if (v_isShared_5701_ == 0)
{
lean_ctor_set(v___x_5700_, 4, v___x_5759_);
lean_ctor_set(v___x_5700_, 0, v___x_5755_);
v___x_5761_ = v___x_5700_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v___x_5755_);
lean_ctor_set(v_reuseFailAlloc_5762_, 1, v_k_5531_);
lean_ctor_set(v_reuseFailAlloc_5762_, 2, v_v_5532_);
lean_ctor_set(v_reuseFailAlloc_5762_, 3, v_l_5533_);
lean_ctor_set(v_reuseFailAlloc_5762_, 4, v___x_5759_);
v___x_5761_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
return v___x_5761_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_5533_) == 0)
{
lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5793_; 
lean_inc_ref(v_l_5533_);
lean_inc(v_v_5532_);
lean_inc(v_k_5531_);
lean_inc(v_size_5530_);
v_isSharedCheck_5793_ = !lean_is_exclusive(v_l_5350_);
if (v_isSharedCheck_5793_ == 0)
{
lean_object* v_unused_5794_; lean_object* v_unused_5795_; lean_object* v_unused_5796_; lean_object* v_unused_5797_; lean_object* v_unused_5798_; 
v_unused_5794_ = lean_ctor_get(v_l_5350_, 4);
lean_dec(v_unused_5794_);
v_unused_5795_ = lean_ctor_get(v_l_5350_, 3);
lean_dec(v_unused_5795_);
v_unused_5796_ = lean_ctor_get(v_l_5350_, 2);
lean_dec(v_unused_5796_);
v_unused_5797_ = lean_ctor_get(v_l_5350_, 1);
lean_dec(v_unused_5797_);
v_unused_5798_ = lean_ctor_get(v_l_5350_, 0);
lean_dec(v_unused_5798_);
v___x_5771_ = v_l_5350_;
v_isShared_5772_ = v_isSharedCheck_5793_;
goto v_resetjp_5770_;
}
else
{
lean_dec(v_l_5350_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5793_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
if (lean_obj_tag(v_r_5534_) == 0)
{
lean_object* v_k_5773_; lean_object* v_v_5774_; lean_object* v_size_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5779_; 
v_k_5773_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_k_5773_);
v_v_5774_ = lean_ctor_get(v___x_5686_, 1);
lean_inc(v_v_5774_);
lean_dec_ref(v___x_5686_);
v_size_5775_ = lean_ctor_get(v_r_5534_, 0);
v___x_5776_ = lean_nat_add(v___x_5540_, v_size_5530_);
lean_dec(v_size_5530_);
v___x_5777_ = lean_nat_add(v___x_5540_, v_size_5775_);
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 4, v_tree_5687_);
lean_ctor_set(v___x_5684_, 3, v_r_5534_);
lean_ctor_set(v___x_5684_, 2, v_v_5774_);
lean_ctor_set(v___x_5684_, 1, v_k_5773_);
lean_ctor_set(v___x_5684_, 0, v___x_5777_);
v___x_5779_ = v___x_5684_;
goto v_reusejp_5778_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v___x_5777_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v_k_5773_);
lean_ctor_set(v_reuseFailAlloc_5783_, 2, v_v_5774_);
lean_ctor_set(v_reuseFailAlloc_5783_, 3, v_r_5534_);
lean_ctor_set(v_reuseFailAlloc_5783_, 4, v_tree_5687_);
v___x_5779_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5778_;
}
v_reusejp_5778_:
{
lean_object* v___x_5781_; 
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 4, v___x_5779_);
lean_ctor_set(v___x_5771_, 0, v___x_5776_);
v___x_5781_ = v___x_5771_;
goto v_reusejp_5780_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5776_);
lean_ctor_set(v_reuseFailAlloc_5782_, 1, v_k_5531_);
lean_ctor_set(v_reuseFailAlloc_5782_, 2, v_v_5532_);
lean_ctor_set(v_reuseFailAlloc_5782_, 3, v_l_5533_);
lean_ctor_set(v_reuseFailAlloc_5782_, 4, v___x_5779_);
v___x_5781_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5780_;
}
v_reusejp_5780_:
{
return v___x_5781_;
}
}
}
else
{
lean_object* v_k_5784_; lean_object* v_v_5785_; lean_object* v___x_5786_; lean_object* v___x_5788_; 
lean_dec(v_size_5530_);
v_k_5784_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_k_5784_);
v_v_5785_ = lean_ctor_get(v___x_5686_, 1);
lean_inc(v_v_5785_);
lean_dec_ref(v___x_5686_);
v___x_5786_ = lean_unsigned_to_nat(3u);
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 4, v_r_5534_);
lean_ctor_set(v___x_5684_, 3, v_r_5534_);
lean_ctor_set(v___x_5684_, 2, v_v_5785_);
lean_ctor_set(v___x_5684_, 1, v_k_5784_);
lean_ctor_set(v___x_5684_, 0, v___x_5540_);
v___x_5788_ = v___x_5684_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v___x_5540_);
lean_ctor_set(v_reuseFailAlloc_5792_, 1, v_k_5784_);
lean_ctor_set(v_reuseFailAlloc_5792_, 2, v_v_5785_);
lean_ctor_set(v_reuseFailAlloc_5792_, 3, v_r_5534_);
lean_ctor_set(v_reuseFailAlloc_5792_, 4, v_r_5534_);
v___x_5788_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
lean_object* v___x_5790_; 
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 4, v___x_5788_);
lean_ctor_set(v___x_5771_, 0, v___x_5786_);
v___x_5790_ = v___x_5771_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5791_; 
v_reuseFailAlloc_5791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5791_, 0, v___x_5786_);
lean_ctor_set(v_reuseFailAlloc_5791_, 1, v_k_5531_);
lean_ctor_set(v_reuseFailAlloc_5791_, 2, v_v_5532_);
lean_ctor_set(v_reuseFailAlloc_5791_, 3, v_l_5533_);
lean_ctor_set(v_reuseFailAlloc_5791_, 4, v___x_5788_);
v___x_5790_ = v_reuseFailAlloc_5791_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
return v___x_5790_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5534_) == 0)
{
lean_object* v___x_5800_; uint8_t v_isShared_5801_; uint8_t v_isSharedCheck_5823_; 
lean_inc(v_l_5533_);
lean_inc(v_v_5532_);
lean_inc(v_k_5531_);
v_isSharedCheck_5823_ = !lean_is_exclusive(v_l_5350_);
if (v_isSharedCheck_5823_ == 0)
{
lean_object* v_unused_5824_; lean_object* v_unused_5825_; lean_object* v_unused_5826_; lean_object* v_unused_5827_; lean_object* v_unused_5828_; 
v_unused_5824_ = lean_ctor_get(v_l_5350_, 4);
lean_dec(v_unused_5824_);
v_unused_5825_ = lean_ctor_get(v_l_5350_, 3);
lean_dec(v_unused_5825_);
v_unused_5826_ = lean_ctor_get(v_l_5350_, 2);
lean_dec(v_unused_5826_);
v_unused_5827_ = lean_ctor_get(v_l_5350_, 1);
lean_dec(v_unused_5827_);
v_unused_5828_ = lean_ctor_get(v_l_5350_, 0);
lean_dec(v_unused_5828_);
v___x_5800_ = v_l_5350_;
v_isShared_5801_ = v_isSharedCheck_5823_;
goto v_resetjp_5799_;
}
else
{
lean_dec(v_l_5350_);
v___x_5800_ = lean_box(0);
v_isShared_5801_ = v_isSharedCheck_5823_;
goto v_resetjp_5799_;
}
v_resetjp_5799_:
{
lean_object* v_k_5802_; lean_object* v_v_5803_; lean_object* v_k_5804_; lean_object* v_v_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5819_; 
v_k_5802_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_k_5802_);
v_v_5803_ = lean_ctor_get(v___x_5686_, 1);
lean_inc(v_v_5803_);
lean_dec_ref(v___x_5686_);
v_k_5804_ = lean_ctor_get(v_r_5534_, 1);
v_v_5805_ = lean_ctor_get(v_r_5534_, 2);
v_isSharedCheck_5819_ = !lean_is_exclusive(v_r_5534_);
if (v_isSharedCheck_5819_ == 0)
{
lean_object* v_unused_5820_; lean_object* v_unused_5821_; lean_object* v_unused_5822_; 
v_unused_5820_ = lean_ctor_get(v_r_5534_, 4);
lean_dec(v_unused_5820_);
v_unused_5821_ = lean_ctor_get(v_r_5534_, 3);
lean_dec(v_unused_5821_);
v_unused_5822_ = lean_ctor_get(v_r_5534_, 0);
lean_dec(v_unused_5822_);
v___x_5807_ = v_r_5534_;
v_isShared_5808_ = v_isSharedCheck_5819_;
goto v_resetjp_5806_;
}
else
{
lean_inc(v_v_5805_);
lean_inc(v_k_5804_);
lean_dec(v_r_5534_);
v___x_5807_ = lean_box(0);
v_isShared_5808_ = v_isSharedCheck_5819_;
goto v_resetjp_5806_;
}
v_resetjp_5806_:
{
lean_object* v___x_5809_; lean_object* v___x_5811_; 
v___x_5809_ = lean_unsigned_to_nat(3u);
if (v_isShared_5808_ == 0)
{
lean_ctor_set(v___x_5807_, 4, v_l_5533_);
lean_ctor_set(v___x_5807_, 3, v_l_5533_);
lean_ctor_set(v___x_5807_, 2, v_v_5532_);
lean_ctor_set(v___x_5807_, 1, v_k_5531_);
lean_ctor_set(v___x_5807_, 0, v___x_5540_);
v___x_5811_ = v___x_5807_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v___x_5540_);
lean_ctor_set(v_reuseFailAlloc_5818_, 1, v_k_5531_);
lean_ctor_set(v_reuseFailAlloc_5818_, 2, v_v_5532_);
lean_ctor_set(v_reuseFailAlloc_5818_, 3, v_l_5533_);
lean_ctor_set(v_reuseFailAlloc_5818_, 4, v_l_5533_);
v___x_5811_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
lean_object* v___x_5813_; 
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 4, v_l_5533_);
lean_ctor_set(v___x_5684_, 3, v_l_5533_);
lean_ctor_set(v___x_5684_, 2, v_v_5803_);
lean_ctor_set(v___x_5684_, 1, v_k_5802_);
lean_ctor_set(v___x_5684_, 0, v___x_5540_);
v___x_5813_ = v___x_5684_;
goto v_reusejp_5812_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v___x_5540_);
lean_ctor_set(v_reuseFailAlloc_5817_, 1, v_k_5802_);
lean_ctor_set(v_reuseFailAlloc_5817_, 2, v_v_5803_);
lean_ctor_set(v_reuseFailAlloc_5817_, 3, v_l_5533_);
lean_ctor_set(v_reuseFailAlloc_5817_, 4, v_l_5533_);
v___x_5813_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5812_;
}
v_reusejp_5812_:
{
lean_object* v___x_5815_; 
if (v_isShared_5801_ == 0)
{
lean_ctor_set(v___x_5800_, 4, v___x_5813_);
lean_ctor_set(v___x_5800_, 3, v___x_5811_);
lean_ctor_set(v___x_5800_, 2, v_v_5805_);
lean_ctor_set(v___x_5800_, 1, v_k_5804_);
lean_ctor_set(v___x_5800_, 0, v___x_5809_);
v___x_5815_ = v___x_5800_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v___x_5809_);
lean_ctor_set(v_reuseFailAlloc_5816_, 1, v_k_5804_);
lean_ctor_set(v_reuseFailAlloc_5816_, 2, v_v_5805_);
lean_ctor_set(v_reuseFailAlloc_5816_, 3, v___x_5811_);
lean_ctor_set(v_reuseFailAlloc_5816_, 4, v___x_5813_);
v___x_5815_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
return v___x_5815_;
}
}
}
}
}
}
else
{
lean_object* v_k_5829_; lean_object* v_v_5830_; lean_object* v___x_5831_; lean_object* v___x_5833_; 
v_k_5829_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_k_5829_);
v_v_5830_ = lean_ctor_get(v___x_5686_, 1);
lean_inc(v_v_5830_);
lean_dec_ref(v___x_5686_);
v___x_5831_ = lean_unsigned_to_nat(2u);
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 4, v_r_5534_);
lean_ctor_set(v___x_5684_, 3, v_l_5350_);
lean_ctor_set(v___x_5684_, 2, v_v_5830_);
lean_ctor_set(v___x_5684_, 1, v_k_5829_);
lean_ctor_set(v___x_5684_, 0, v___x_5831_);
v___x_5833_ = v___x_5684_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v___x_5831_);
lean_ctor_set(v_reuseFailAlloc_5834_, 1, v_k_5829_);
lean_ctor_set(v_reuseFailAlloc_5834_, 2, v_v_5830_);
lean_ctor_set(v_reuseFailAlloc_5834_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_5834_, 4, v_r_5534_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
return v___x_5833_;
}
}
}
}
}
}
}
else
{
return v_l_5350_;
}
}
else
{
return v_r_5351_;
}
}
default: 
{
lean_object* v_impl_5841_; lean_object* v___x_5842_; 
v_impl_5841_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5346_, v_r_5351_);
v___x_5842_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5841_) == 0)
{
if (lean_obj_tag(v_l_5350_) == 0)
{
lean_object* v_size_5843_; lean_object* v_size_5844_; lean_object* v_k_5845_; lean_object* v_v_5846_; lean_object* v_l_5847_; lean_object* v_r_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; uint8_t v___x_5851_; 
v_size_5843_ = lean_ctor_get(v_impl_5841_, 0);
lean_inc(v_size_5843_);
v_size_5844_ = lean_ctor_get(v_l_5350_, 0);
v_k_5845_ = lean_ctor_get(v_l_5350_, 1);
v_v_5846_ = lean_ctor_get(v_l_5350_, 2);
v_l_5847_ = lean_ctor_get(v_l_5350_, 3);
v_r_5848_ = lean_ctor_get(v_l_5350_, 4);
lean_inc(v_r_5848_);
v___x_5849_ = lean_unsigned_to_nat(3u);
v___x_5850_ = lean_nat_mul(v___x_5849_, v_size_5843_);
v___x_5851_ = lean_nat_dec_lt(v___x_5850_, v_size_5844_);
lean_dec(v___x_5850_);
if (v___x_5851_ == 0)
{
lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5855_; 
lean_dec(v_r_5848_);
v___x_5852_ = lean_nat_add(v___x_5842_, v_size_5844_);
v___x_5853_ = lean_nat_add(v___x_5852_, v_size_5843_);
lean_dec(v_size_5843_);
lean_dec(v___x_5852_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_impl_5841_);
lean_ctor_set(v___x_5353_, 0, v___x_5853_);
v___x_5855_ = v___x_5353_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5856_; 
v_reuseFailAlloc_5856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5856_, 0, v___x_5853_);
lean_ctor_set(v_reuseFailAlloc_5856_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5856_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5856_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_5856_, 4, v_impl_5841_);
v___x_5855_ = v_reuseFailAlloc_5856_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
return v___x_5855_;
}
}
else
{
lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5922_; 
lean_inc(v_l_5847_);
lean_inc(v_v_5846_);
lean_inc(v_k_5845_);
lean_inc(v_size_5844_);
v_isSharedCheck_5922_ = !lean_is_exclusive(v_l_5350_);
if (v_isSharedCheck_5922_ == 0)
{
lean_object* v_unused_5923_; lean_object* v_unused_5924_; lean_object* v_unused_5925_; lean_object* v_unused_5926_; lean_object* v_unused_5927_; 
v_unused_5923_ = lean_ctor_get(v_l_5350_, 4);
lean_dec(v_unused_5923_);
v_unused_5924_ = lean_ctor_get(v_l_5350_, 3);
lean_dec(v_unused_5924_);
v_unused_5925_ = lean_ctor_get(v_l_5350_, 2);
lean_dec(v_unused_5925_);
v_unused_5926_ = lean_ctor_get(v_l_5350_, 1);
lean_dec(v_unused_5926_);
v_unused_5927_ = lean_ctor_get(v_l_5350_, 0);
lean_dec(v_unused_5927_);
v___x_5858_ = v_l_5350_;
v_isShared_5859_ = v_isSharedCheck_5922_;
goto v_resetjp_5857_;
}
else
{
lean_dec(v_l_5350_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5922_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
lean_object* v_size_5860_; lean_object* v_size_5861_; lean_object* v_k_5862_; lean_object* v_v_5863_; lean_object* v_l_5864_; lean_object* v_r_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; uint8_t v___x_5868_; 
v_size_5860_ = lean_ctor_get(v_l_5847_, 0);
v_size_5861_ = lean_ctor_get(v_r_5848_, 0);
v_k_5862_ = lean_ctor_get(v_r_5848_, 1);
v_v_5863_ = lean_ctor_get(v_r_5848_, 2);
v_l_5864_ = lean_ctor_get(v_r_5848_, 3);
v_r_5865_ = lean_ctor_get(v_r_5848_, 4);
v___x_5866_ = lean_unsigned_to_nat(2u);
v___x_5867_ = lean_nat_mul(v___x_5866_, v_size_5860_);
v___x_5868_ = lean_nat_dec_lt(v_size_5861_, v___x_5867_);
lean_dec(v___x_5867_);
if (v___x_5868_ == 0)
{
lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5897_; 
lean_inc(v_r_5865_);
lean_inc(v_l_5864_);
lean_inc(v_v_5863_);
lean_inc(v_k_5862_);
v_isSharedCheck_5897_ = !lean_is_exclusive(v_r_5848_);
if (v_isSharedCheck_5897_ == 0)
{
lean_object* v_unused_5898_; lean_object* v_unused_5899_; lean_object* v_unused_5900_; lean_object* v_unused_5901_; lean_object* v_unused_5902_; 
v_unused_5898_ = lean_ctor_get(v_r_5848_, 4);
lean_dec(v_unused_5898_);
v_unused_5899_ = lean_ctor_get(v_r_5848_, 3);
lean_dec(v_unused_5899_);
v_unused_5900_ = lean_ctor_get(v_r_5848_, 2);
lean_dec(v_unused_5900_);
v_unused_5901_ = lean_ctor_get(v_r_5848_, 1);
lean_dec(v_unused_5901_);
v_unused_5902_ = lean_ctor_get(v_r_5848_, 0);
lean_dec(v_unused_5902_);
v___x_5870_ = v_r_5848_;
v_isShared_5871_ = v_isSharedCheck_5897_;
goto v_resetjp_5869_;
}
else
{
lean_dec(v_r_5848_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5897_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___y_5875_; lean_object* v___y_5876_; lean_object* v___y_5877_; lean_object* v___x_5885_; lean_object* v___y_5887_; 
v___x_5872_ = lean_nat_add(v___x_5842_, v_size_5844_);
lean_dec(v_size_5844_);
v___x_5873_ = lean_nat_add(v___x_5872_, v_size_5843_);
lean_dec(v___x_5872_);
v___x_5885_ = lean_nat_add(v___x_5842_, v_size_5860_);
if (lean_obj_tag(v_l_5864_) == 0)
{
lean_object* v_size_5895_; 
v_size_5895_ = lean_ctor_get(v_l_5864_, 0);
lean_inc(v_size_5895_);
v___y_5887_ = v_size_5895_;
goto v___jp_5886_;
}
else
{
lean_object* v___x_5896_; 
v___x_5896_ = lean_unsigned_to_nat(0u);
v___y_5887_ = v___x_5896_;
goto v___jp_5886_;
}
v___jp_5874_:
{
lean_object* v___x_5878_; lean_object* v___x_5880_; 
v___x_5878_ = lean_nat_add(v___y_5875_, v___y_5877_);
lean_dec(v___y_5877_);
lean_dec(v___y_5875_);
if (v_isShared_5871_ == 0)
{
lean_ctor_set(v___x_5870_, 4, v_impl_5841_);
lean_ctor_set(v___x_5870_, 3, v_r_5865_);
lean_ctor_set(v___x_5870_, 2, v_v_5349_);
lean_ctor_set(v___x_5870_, 1, v_k_5348_);
lean_ctor_set(v___x_5870_, 0, v___x_5878_);
v___x_5880_ = v___x_5870_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v___x_5878_);
lean_ctor_set(v_reuseFailAlloc_5884_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5884_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5884_, 3, v_r_5865_);
lean_ctor_set(v_reuseFailAlloc_5884_, 4, v_impl_5841_);
v___x_5880_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
lean_object* v___x_5882_; 
if (v_isShared_5859_ == 0)
{
lean_ctor_set(v___x_5858_, 4, v___x_5880_);
lean_ctor_set(v___x_5858_, 3, v___y_5876_);
lean_ctor_set(v___x_5858_, 2, v_v_5863_);
lean_ctor_set(v___x_5858_, 1, v_k_5862_);
lean_ctor_set(v___x_5858_, 0, v___x_5873_);
v___x_5882_ = v___x_5858_;
goto v_reusejp_5881_;
}
else
{
lean_object* v_reuseFailAlloc_5883_; 
v_reuseFailAlloc_5883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5883_, 0, v___x_5873_);
lean_ctor_set(v_reuseFailAlloc_5883_, 1, v_k_5862_);
lean_ctor_set(v_reuseFailAlloc_5883_, 2, v_v_5863_);
lean_ctor_set(v_reuseFailAlloc_5883_, 3, v___y_5876_);
lean_ctor_set(v_reuseFailAlloc_5883_, 4, v___x_5880_);
v___x_5882_ = v_reuseFailAlloc_5883_;
goto v_reusejp_5881_;
}
v_reusejp_5881_:
{
return v___x_5882_;
}
}
}
v___jp_5886_:
{
lean_object* v___x_5888_; lean_object* v___x_5890_; 
v___x_5888_ = lean_nat_add(v___x_5885_, v___y_5887_);
lean_dec(v___y_5887_);
lean_dec(v___x_5885_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_l_5864_);
lean_ctor_set(v___x_5353_, 3, v_l_5847_);
lean_ctor_set(v___x_5353_, 2, v_v_5846_);
lean_ctor_set(v___x_5353_, 1, v_k_5845_);
lean_ctor_set(v___x_5353_, 0, v___x_5888_);
v___x_5890_ = v___x_5353_;
goto v_reusejp_5889_;
}
else
{
lean_object* v_reuseFailAlloc_5894_; 
v_reuseFailAlloc_5894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5894_, 0, v___x_5888_);
lean_ctor_set(v_reuseFailAlloc_5894_, 1, v_k_5845_);
lean_ctor_set(v_reuseFailAlloc_5894_, 2, v_v_5846_);
lean_ctor_set(v_reuseFailAlloc_5894_, 3, v_l_5847_);
lean_ctor_set(v_reuseFailAlloc_5894_, 4, v_l_5864_);
v___x_5890_ = v_reuseFailAlloc_5894_;
goto v_reusejp_5889_;
}
v_reusejp_5889_:
{
lean_object* v___x_5891_; 
v___x_5891_ = lean_nat_add(v___x_5842_, v_size_5843_);
lean_dec(v_size_5843_);
if (lean_obj_tag(v_r_5865_) == 0)
{
lean_object* v_size_5892_; 
v_size_5892_ = lean_ctor_get(v_r_5865_, 0);
lean_inc(v_size_5892_);
v___y_5875_ = v___x_5891_;
v___y_5876_ = v___x_5890_;
v___y_5877_ = v_size_5892_;
goto v___jp_5874_;
}
else
{
lean_object* v___x_5893_; 
v___x_5893_ = lean_unsigned_to_nat(0u);
v___y_5875_ = v___x_5891_;
v___y_5876_ = v___x_5890_;
v___y_5877_ = v___x_5893_;
goto v___jp_5874_;
}
}
}
}
}
else
{
lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5908_; 
lean_del_object(v___x_5353_);
v___x_5903_ = lean_nat_add(v___x_5842_, v_size_5844_);
lean_dec(v_size_5844_);
v___x_5904_ = lean_nat_add(v___x_5903_, v_size_5843_);
lean_dec(v___x_5903_);
v___x_5905_ = lean_nat_add(v___x_5842_, v_size_5843_);
lean_dec(v_size_5843_);
v___x_5906_ = lean_nat_add(v___x_5905_, v_size_5861_);
lean_dec(v___x_5905_);
lean_inc_ref(v_impl_5841_);
if (v_isShared_5859_ == 0)
{
lean_ctor_set(v___x_5858_, 4, v_impl_5841_);
lean_ctor_set(v___x_5858_, 3, v_r_5848_);
lean_ctor_set(v___x_5858_, 2, v_v_5349_);
lean_ctor_set(v___x_5858_, 1, v_k_5348_);
lean_ctor_set(v___x_5858_, 0, v___x_5906_);
v___x_5908_ = v___x_5858_;
goto v_reusejp_5907_;
}
else
{
lean_object* v_reuseFailAlloc_5921_; 
v_reuseFailAlloc_5921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5921_, 0, v___x_5906_);
lean_ctor_set(v_reuseFailAlloc_5921_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5921_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5921_, 3, v_r_5848_);
lean_ctor_set(v_reuseFailAlloc_5921_, 4, v_impl_5841_);
v___x_5908_ = v_reuseFailAlloc_5921_;
goto v_reusejp_5907_;
}
v_reusejp_5907_:
{
lean_object* v___x_5910_; uint8_t v_isShared_5911_; uint8_t v_isSharedCheck_5915_; 
v_isSharedCheck_5915_ = !lean_is_exclusive(v_impl_5841_);
if (v_isSharedCheck_5915_ == 0)
{
lean_object* v_unused_5916_; lean_object* v_unused_5917_; lean_object* v_unused_5918_; lean_object* v_unused_5919_; lean_object* v_unused_5920_; 
v_unused_5916_ = lean_ctor_get(v_impl_5841_, 4);
lean_dec(v_unused_5916_);
v_unused_5917_ = lean_ctor_get(v_impl_5841_, 3);
lean_dec(v_unused_5917_);
v_unused_5918_ = lean_ctor_get(v_impl_5841_, 2);
lean_dec(v_unused_5918_);
v_unused_5919_ = lean_ctor_get(v_impl_5841_, 1);
lean_dec(v_unused_5919_);
v_unused_5920_ = lean_ctor_get(v_impl_5841_, 0);
lean_dec(v_unused_5920_);
v___x_5910_ = v_impl_5841_;
v_isShared_5911_ = v_isSharedCheck_5915_;
goto v_resetjp_5909_;
}
else
{
lean_dec(v_impl_5841_);
v___x_5910_ = lean_box(0);
v_isShared_5911_ = v_isSharedCheck_5915_;
goto v_resetjp_5909_;
}
v_resetjp_5909_:
{
lean_object* v___x_5913_; 
if (v_isShared_5911_ == 0)
{
lean_ctor_set(v___x_5910_, 4, v___x_5908_);
lean_ctor_set(v___x_5910_, 3, v_l_5847_);
lean_ctor_set(v___x_5910_, 2, v_v_5846_);
lean_ctor_set(v___x_5910_, 1, v_k_5845_);
lean_ctor_set(v___x_5910_, 0, v___x_5904_);
v___x_5913_ = v___x_5910_;
goto v_reusejp_5912_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v___x_5904_);
lean_ctor_set(v_reuseFailAlloc_5914_, 1, v_k_5845_);
lean_ctor_set(v_reuseFailAlloc_5914_, 2, v_v_5846_);
lean_ctor_set(v_reuseFailAlloc_5914_, 3, v_l_5847_);
lean_ctor_set(v_reuseFailAlloc_5914_, 4, v___x_5908_);
v___x_5913_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5912_;
}
v_reusejp_5912_:
{
return v___x_5913_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5928_; lean_object* v___x_5929_; lean_object* v___x_5931_; 
v_size_5928_ = lean_ctor_get(v_impl_5841_, 0);
lean_inc(v_size_5928_);
v___x_5929_ = lean_nat_add(v___x_5842_, v_size_5928_);
lean_dec(v_size_5928_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_impl_5841_);
lean_ctor_set(v___x_5353_, 0, v___x_5929_);
v___x_5931_ = v___x_5353_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v___x_5929_);
lean_ctor_set(v_reuseFailAlloc_5932_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5932_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5932_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_5932_, 4, v_impl_5841_);
v___x_5931_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
return v___x_5931_;
}
}
}
else
{
if (lean_obj_tag(v_l_5350_) == 0)
{
lean_object* v_l_5933_; 
v_l_5933_ = lean_ctor_get(v_l_5350_, 3);
if (lean_obj_tag(v_l_5933_) == 0)
{
lean_object* v_r_5934_; 
lean_inc_ref(v_l_5933_);
v_r_5934_ = lean_ctor_get(v_l_5350_, 4);
lean_inc(v_r_5934_);
if (lean_obj_tag(v_r_5934_) == 0)
{
lean_object* v_size_5935_; lean_object* v_k_5936_; lean_object* v_v_5937_; lean_object* v___x_5939_; uint8_t v_isShared_5940_; uint8_t v_isSharedCheck_5950_; 
v_size_5935_ = lean_ctor_get(v_l_5350_, 0);
v_k_5936_ = lean_ctor_get(v_l_5350_, 1);
v_v_5937_ = lean_ctor_get(v_l_5350_, 2);
v_isSharedCheck_5950_ = !lean_is_exclusive(v_l_5350_);
if (v_isSharedCheck_5950_ == 0)
{
lean_object* v_unused_5951_; lean_object* v_unused_5952_; 
v_unused_5951_ = lean_ctor_get(v_l_5350_, 4);
lean_dec(v_unused_5951_);
v_unused_5952_ = lean_ctor_get(v_l_5350_, 3);
lean_dec(v_unused_5952_);
v___x_5939_ = v_l_5350_;
v_isShared_5940_ = v_isSharedCheck_5950_;
goto v_resetjp_5938_;
}
else
{
lean_inc(v_v_5937_);
lean_inc(v_k_5936_);
lean_inc(v_size_5935_);
lean_dec(v_l_5350_);
v___x_5939_ = lean_box(0);
v_isShared_5940_ = v_isSharedCheck_5950_;
goto v_resetjp_5938_;
}
v_resetjp_5938_:
{
lean_object* v_size_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5945_; 
v_size_5941_ = lean_ctor_get(v_r_5934_, 0);
v___x_5942_ = lean_nat_add(v___x_5842_, v_size_5935_);
lean_dec(v_size_5935_);
v___x_5943_ = lean_nat_add(v___x_5842_, v_size_5941_);
if (v_isShared_5940_ == 0)
{
lean_ctor_set(v___x_5939_, 4, v_impl_5841_);
lean_ctor_set(v___x_5939_, 3, v_r_5934_);
lean_ctor_set(v___x_5939_, 2, v_v_5349_);
lean_ctor_set(v___x_5939_, 1, v_k_5348_);
lean_ctor_set(v___x_5939_, 0, v___x_5943_);
v___x_5945_ = v___x_5939_;
goto v_reusejp_5944_;
}
else
{
lean_object* v_reuseFailAlloc_5949_; 
v_reuseFailAlloc_5949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5949_, 0, v___x_5943_);
lean_ctor_set(v_reuseFailAlloc_5949_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5949_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5949_, 3, v_r_5934_);
lean_ctor_set(v_reuseFailAlloc_5949_, 4, v_impl_5841_);
v___x_5945_ = v_reuseFailAlloc_5949_;
goto v_reusejp_5944_;
}
v_reusejp_5944_:
{
lean_object* v___x_5947_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v___x_5945_);
lean_ctor_set(v___x_5353_, 3, v_l_5933_);
lean_ctor_set(v___x_5353_, 2, v_v_5937_);
lean_ctor_set(v___x_5353_, 1, v_k_5936_);
lean_ctor_set(v___x_5353_, 0, v___x_5942_);
v___x_5947_ = v___x_5353_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v___x_5942_);
lean_ctor_set(v_reuseFailAlloc_5948_, 1, v_k_5936_);
lean_ctor_set(v_reuseFailAlloc_5948_, 2, v_v_5937_);
lean_ctor_set(v_reuseFailAlloc_5948_, 3, v_l_5933_);
lean_ctor_set(v_reuseFailAlloc_5948_, 4, v___x_5945_);
v___x_5947_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
return v___x_5947_;
}
}
}
}
else
{
lean_object* v_k_5953_; lean_object* v_v_5954_; lean_object* v___x_5956_; uint8_t v_isShared_5957_; uint8_t v_isSharedCheck_5965_; 
v_k_5953_ = lean_ctor_get(v_l_5350_, 1);
v_v_5954_ = lean_ctor_get(v_l_5350_, 2);
v_isSharedCheck_5965_ = !lean_is_exclusive(v_l_5350_);
if (v_isSharedCheck_5965_ == 0)
{
lean_object* v_unused_5966_; lean_object* v_unused_5967_; lean_object* v_unused_5968_; 
v_unused_5966_ = lean_ctor_get(v_l_5350_, 4);
lean_dec(v_unused_5966_);
v_unused_5967_ = lean_ctor_get(v_l_5350_, 3);
lean_dec(v_unused_5967_);
v_unused_5968_ = lean_ctor_get(v_l_5350_, 0);
lean_dec(v_unused_5968_);
v___x_5956_ = v_l_5350_;
v_isShared_5957_ = v_isSharedCheck_5965_;
goto v_resetjp_5955_;
}
else
{
lean_inc(v_v_5954_);
lean_inc(v_k_5953_);
lean_dec(v_l_5350_);
v___x_5956_ = lean_box(0);
v_isShared_5957_ = v_isSharedCheck_5965_;
goto v_resetjp_5955_;
}
v_resetjp_5955_:
{
lean_object* v___x_5958_; lean_object* v___x_5960_; 
v___x_5958_ = lean_unsigned_to_nat(3u);
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 3, v_r_5934_);
lean_ctor_set(v___x_5956_, 2, v_v_5349_);
lean_ctor_set(v___x_5956_, 1, v_k_5348_);
lean_ctor_set(v___x_5956_, 0, v___x_5842_);
v___x_5960_ = v___x_5956_;
goto v_reusejp_5959_;
}
else
{
lean_object* v_reuseFailAlloc_5964_; 
v_reuseFailAlloc_5964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5964_, 0, v___x_5842_);
lean_ctor_set(v_reuseFailAlloc_5964_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5964_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5964_, 3, v_r_5934_);
lean_ctor_set(v_reuseFailAlloc_5964_, 4, v_r_5934_);
v___x_5960_ = v_reuseFailAlloc_5964_;
goto v_reusejp_5959_;
}
v_reusejp_5959_:
{
lean_object* v___x_5962_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v___x_5960_);
lean_ctor_set(v___x_5353_, 3, v_l_5933_);
lean_ctor_set(v___x_5353_, 2, v_v_5954_);
lean_ctor_set(v___x_5353_, 1, v_k_5953_);
lean_ctor_set(v___x_5353_, 0, v___x_5958_);
v___x_5962_ = v___x_5353_;
goto v_reusejp_5961_;
}
else
{
lean_object* v_reuseFailAlloc_5963_; 
v_reuseFailAlloc_5963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5963_, 0, v___x_5958_);
lean_ctor_set(v_reuseFailAlloc_5963_, 1, v_k_5953_);
lean_ctor_set(v_reuseFailAlloc_5963_, 2, v_v_5954_);
lean_ctor_set(v_reuseFailAlloc_5963_, 3, v_l_5933_);
lean_ctor_set(v_reuseFailAlloc_5963_, 4, v___x_5960_);
v___x_5962_ = v_reuseFailAlloc_5963_;
goto v_reusejp_5961_;
}
v_reusejp_5961_:
{
return v___x_5962_;
}
}
}
}
}
else
{
lean_object* v_r_5969_; 
v_r_5969_ = lean_ctor_get(v_l_5350_, 4);
lean_inc(v_r_5969_);
if (lean_obj_tag(v_r_5969_) == 0)
{
lean_object* v_k_5970_; lean_object* v_v_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5994_; 
lean_inc(v_l_5933_);
v_k_5970_ = lean_ctor_get(v_l_5350_, 1);
v_v_5971_ = lean_ctor_get(v_l_5350_, 2);
v_isSharedCheck_5994_ = !lean_is_exclusive(v_l_5350_);
if (v_isSharedCheck_5994_ == 0)
{
lean_object* v_unused_5995_; lean_object* v_unused_5996_; lean_object* v_unused_5997_; 
v_unused_5995_ = lean_ctor_get(v_l_5350_, 4);
lean_dec(v_unused_5995_);
v_unused_5996_ = lean_ctor_get(v_l_5350_, 3);
lean_dec(v_unused_5996_);
v_unused_5997_ = lean_ctor_get(v_l_5350_, 0);
lean_dec(v_unused_5997_);
v___x_5973_ = v_l_5350_;
v_isShared_5974_ = v_isSharedCheck_5994_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_v_5971_);
lean_inc(v_k_5970_);
lean_dec(v_l_5350_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5994_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v_k_5975_; lean_object* v_v_5976_; lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_5990_; 
v_k_5975_ = lean_ctor_get(v_r_5969_, 1);
v_v_5976_ = lean_ctor_get(v_r_5969_, 2);
v_isSharedCheck_5990_ = !lean_is_exclusive(v_r_5969_);
if (v_isSharedCheck_5990_ == 0)
{
lean_object* v_unused_5991_; lean_object* v_unused_5992_; lean_object* v_unused_5993_; 
v_unused_5991_ = lean_ctor_get(v_r_5969_, 4);
lean_dec(v_unused_5991_);
v_unused_5992_ = lean_ctor_get(v_r_5969_, 3);
lean_dec(v_unused_5992_);
v_unused_5993_ = lean_ctor_get(v_r_5969_, 0);
lean_dec(v_unused_5993_);
v___x_5978_ = v_r_5969_;
v_isShared_5979_ = v_isSharedCheck_5990_;
goto v_resetjp_5977_;
}
else
{
lean_inc(v_v_5976_);
lean_inc(v_k_5975_);
lean_dec(v_r_5969_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_5990_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v___x_5980_; lean_object* v___x_5982_; 
v___x_5980_ = lean_unsigned_to_nat(3u);
if (v_isShared_5979_ == 0)
{
lean_ctor_set(v___x_5978_, 4, v_l_5933_);
lean_ctor_set(v___x_5978_, 3, v_l_5933_);
lean_ctor_set(v___x_5978_, 2, v_v_5971_);
lean_ctor_set(v___x_5978_, 1, v_k_5970_);
lean_ctor_set(v___x_5978_, 0, v___x_5842_);
v___x_5982_ = v___x_5978_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5842_);
lean_ctor_set(v_reuseFailAlloc_5989_, 1, v_k_5970_);
lean_ctor_set(v_reuseFailAlloc_5989_, 2, v_v_5971_);
lean_ctor_set(v_reuseFailAlloc_5989_, 3, v_l_5933_);
lean_ctor_set(v_reuseFailAlloc_5989_, 4, v_l_5933_);
v___x_5982_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
lean_object* v___x_5984_; 
if (v_isShared_5974_ == 0)
{
lean_ctor_set(v___x_5973_, 4, v_l_5933_);
lean_ctor_set(v___x_5973_, 2, v_v_5349_);
lean_ctor_set(v___x_5973_, 1, v_k_5348_);
lean_ctor_set(v___x_5973_, 0, v___x_5842_);
v___x_5984_ = v___x_5973_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_5988_; 
v_reuseFailAlloc_5988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5988_, 0, v___x_5842_);
lean_ctor_set(v_reuseFailAlloc_5988_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5988_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5988_, 3, v_l_5933_);
lean_ctor_set(v_reuseFailAlloc_5988_, 4, v_l_5933_);
v___x_5984_ = v_reuseFailAlloc_5988_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
lean_object* v___x_5986_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v___x_5984_);
lean_ctor_set(v___x_5353_, 3, v___x_5982_);
lean_ctor_set(v___x_5353_, 2, v_v_5976_);
lean_ctor_set(v___x_5353_, 1, v_k_5975_);
lean_ctor_set(v___x_5353_, 0, v___x_5980_);
v___x_5986_ = v___x_5353_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5987_; 
v_reuseFailAlloc_5987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5987_, 0, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_5987_, 1, v_k_5975_);
lean_ctor_set(v_reuseFailAlloc_5987_, 2, v_v_5976_);
lean_ctor_set(v_reuseFailAlloc_5987_, 3, v___x_5982_);
lean_ctor_set(v_reuseFailAlloc_5987_, 4, v___x_5984_);
v___x_5986_ = v_reuseFailAlloc_5987_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
return v___x_5986_;
}
}
}
}
}
}
else
{
lean_object* v___x_5998_; lean_object* v___x_6000_; 
v___x_5998_ = lean_unsigned_to_nat(2u);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_r_5969_);
lean_ctor_set(v___x_5353_, 0, v___x_5998_);
v___x_6000_ = v___x_5353_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v___x_5998_);
lean_ctor_set(v_reuseFailAlloc_6001_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_6001_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_6001_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_6001_, 4, v_r_5969_);
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
else
{
lean_object* v___x_6003_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_l_5350_);
lean_ctor_set(v___x_5353_, 0, v___x_5842_);
v___x_6003_ = v___x_5353_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v___x_5842_);
lean_ctor_set(v_reuseFailAlloc_6004_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_6004_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_6004_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_6004_, 4, v_l_5350_);
v___x_6003_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
return v___x_6003_;
}
}
}
}
}
}
}
else
{
return v_t_5347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_6007_, lean_object* v_t_6008_){
_start:
{
lean_object* v_res_6009_; 
v_res_6009_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6007_, v_t_6008_);
lean_dec(v_k_6007_);
return v_res_6009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_6010_, lean_object* v_x_6011_){
_start:
{
if (lean_obj_tag(v_x_6011_) == 0)
{
lean_object* v_k_6012_; lean_object* v_l_6013_; lean_object* v_r_6014_; lean_object* v___x_6015_; lean_object* v_ileans_6016_; lean_object* v_workers_6017_; lean_object* v___x_6019_; uint8_t v_isShared_6020_; uint8_t v_isSharedCheck_6026_; 
v_k_6012_ = lean_ctor_get(v_x_6011_, 1);
v_l_6013_ = lean_ctor_get(v_x_6011_, 3);
v_r_6014_ = lean_ctor_get(v_x_6011_, 4);
v___x_6015_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6010_, v_l_6013_);
v_ileans_6016_ = lean_ctor_get(v___x_6015_, 0);
v_workers_6017_ = lean_ctor_get(v___x_6015_, 1);
v_isSharedCheck_6026_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6026_ == 0)
{
v___x_6019_ = v___x_6015_;
v_isShared_6020_ = v_isSharedCheck_6026_;
goto v_resetjp_6018_;
}
else
{
lean_inc(v_workers_6017_);
lean_inc(v_ileans_6016_);
lean_dec(v___x_6015_);
v___x_6019_ = lean_box(0);
v_isShared_6020_ = v_isSharedCheck_6026_;
goto v_resetjp_6018_;
}
v_resetjp_6018_:
{
lean_object* v___x_6021_; lean_object* v___x_6023_; 
v___x_6021_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6012_, v_ileans_6016_);
if (v_isShared_6020_ == 0)
{
lean_ctor_set(v___x_6019_, 0, v___x_6021_);
v___x_6023_ = v___x_6019_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6025_; 
v_reuseFailAlloc_6025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6025_, 0, v___x_6021_);
lean_ctor_set(v_reuseFailAlloc_6025_, 1, v_workers_6017_);
v___x_6023_ = v_reuseFailAlloc_6025_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
v_init_6010_ = v___x_6023_;
v_x_6011_ = v_r_6014_;
goto _start;
}
}
}
else
{
return v_init_6010_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_6027_, lean_object* v_x_6028_){
_start:
{
lean_object* v_res_6029_; 
v_res_6029_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6027_, v_x_6028_);
lean_dec(v_x_6028_);
return v_res_6029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_6030_, lean_object* v_path_6031_){
_start:
{
lean_object* v_ileans_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; 
v_ileans_6032_ = lean_ctor_get(v_self_6030_, 0);
lean_inc(v_ileans_6032_);
v___x_6033_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6031_, v_ileans_6032_);
v___x_6034_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_6030_, v___x_6033_);
lean_dec(v___x_6033_);
return v___x_6034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_6035_, lean_object* v_path_6036_){
_start:
{
lean_object* v_res_6037_; 
v_res_6037_ = l_Lean_Server_References_removeIlean(v_self_6035_, v_path_6036_);
lean_dec_ref(v_path_6036_);
return v_res_6037_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_6038_, lean_object* v_k_6039_, lean_object* v_t_6040_, lean_object* v_h_6041_){
_start:
{
lean_object* v___x_6042_; 
v___x_6042_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6039_, v_t_6040_);
return v___x_6042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_6043_, lean_object* v_k_6044_, lean_object* v_t_6045_, lean_object* v_h_6046_){
_start:
{
lean_object* v_res_6047_; 
v_res_6047_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_6043_, v_k_6044_, v_t_6045_, v_h_6046_);
lean_dec(v_k_6044_);
return v_res_6047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_6048_, lean_object* v_t_6049_, lean_object* v_hl_6050_){
_start:
{
lean_object* v___x_6051_; 
v___x_6051_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6048_, v_t_6049_);
return v___x_6051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_6052_, lean_object* v_t_6053_, lean_object* v_hl_6054_){
_start:
{
lean_object* v_res_6055_; 
v_res_6055_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_6052_, v_t_6053_, v_hl_6054_);
lean_dec_ref(v_path_6052_);
return v_res_6055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_6056_, lean_object* v_t_6057_){
_start:
{
lean_object* v___x_6058_; 
v___x_6058_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6056_, v_t_6057_);
return v___x_6058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_6059_, lean_object* v_t_6060_){
_start:
{
lean_object* v_res_6061_; 
v_res_6061_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_6059_, v_t_6060_);
lean_dec(v_t_6060_);
return v_res_6061_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_6062_, lean_object* v_k_6063_){
_start:
{
if (lean_obj_tag(v_t_6062_) == 0)
{
lean_object* v_k_6064_; lean_object* v_v_6065_; lean_object* v_l_6066_; lean_object* v_r_6067_; uint8_t v___x_6068_; 
v_k_6064_ = lean_ctor_get(v_t_6062_, 1);
v_v_6065_ = lean_ctor_get(v_t_6062_, 2);
v_l_6066_ = lean_ctor_get(v_t_6062_, 3);
v_r_6067_ = lean_ctor_get(v_t_6062_, 4);
v___x_6068_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6063_, v_k_6064_);
switch(v___x_6068_)
{
case 0:
{
v_t_6062_ = v_l_6066_;
goto _start;
}
case 1:
{
lean_object* v___x_6070_; 
lean_inc(v_v_6065_);
v___x_6070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6070_, 0, v_v_6065_);
return v___x_6070_;
}
default: 
{
v_t_6062_ = v_r_6067_;
goto _start;
}
}
}
else
{
lean_object* v___x_6072_; 
v___x_6072_ = lean_box(0);
return v___x_6072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_6073_, lean_object* v_k_6074_){
_start:
{
lean_object* v_res_6075_; 
v_res_6075_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6073_, v_k_6074_);
lean_dec(v_k_6074_);
lean_dec(v_t_6073_);
return v_res_6075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_6076_, lean_object* v_name_6077_, lean_object* v_moduleUri_6078_, lean_object* v_version_6079_, lean_object* v_directImports_6080_, uint8_t v_isSetupFailure_6081_){
_start:
{
lean_object* v___x_6083_; 
v___x_6083_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_6080_);
if (lean_obj_tag(v___x_6083_) == 0)
{
lean_object* v_a_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6150_; 
v_a_6084_ = lean_ctor_get(v___x_6083_, 0);
v_isSharedCheck_6150_ = !lean_is_exclusive(v___x_6083_);
if (v_isSharedCheck_6150_ == 0)
{
v___x_6086_ = v___x_6083_;
v_isShared_6087_ = v_isSharedCheck_6150_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_a_6084_);
lean_dec(v___x_6083_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6150_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
lean_object* v_ileans_6088_; lean_object* v_workers_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; 
v_ileans_6088_ = lean_ctor_get(v_self_6076_, 0);
v_workers_6089_ = lean_ctor_get(v_self_6076_, 1);
v___x_6090_ = lean_box(1);
v___x_6091_ = lean_box(v_isSetupFailure_6081_);
v___x_6092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6091_);
v___x_6093_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6089_, v_name_6077_);
if (lean_obj_tag(v___x_6093_) == 1)
{
lean_object* v_val_6094_; lean_object* v_version_6095_; lean_object* v_refs_6096_; lean_object* v_decls_6097_; lean_object* v___x_6099_; uint8_t v_isShared_6100_; uint8_t v_isSharedCheck_6132_; 
v_val_6094_ = lean_ctor_get(v___x_6093_, 0);
lean_inc(v_val_6094_);
lean_dec_ref(v___x_6093_);
v_version_6095_ = lean_ctor_get(v_val_6094_, 1);
v_refs_6096_ = lean_ctor_get(v_val_6094_, 4);
v_decls_6097_ = lean_ctor_get(v_val_6094_, 5);
v_isSharedCheck_6132_ = !lean_is_exclusive(v_val_6094_);
if (v_isSharedCheck_6132_ == 0)
{
lean_object* v_unused_6133_; lean_object* v_unused_6134_; lean_object* v_unused_6135_; 
v_unused_6133_ = lean_ctor_get(v_val_6094_, 3);
lean_dec(v_unused_6133_);
v_unused_6134_ = lean_ctor_get(v_val_6094_, 2);
lean_dec(v_unused_6134_);
v_unused_6135_ = lean_ctor_get(v_val_6094_, 0);
lean_dec(v_unused_6135_);
v___x_6099_ = v_val_6094_;
v_isShared_6100_ = v_isSharedCheck_6132_;
goto v_resetjp_6098_;
}
else
{
lean_inc(v_decls_6097_);
lean_inc(v_refs_6096_);
lean_inc(v_version_6095_);
lean_dec(v_val_6094_);
v___x_6099_ = lean_box(0);
v_isShared_6100_ = v_isSharedCheck_6132_;
goto v_resetjp_6098_;
}
v_resetjp_6098_:
{
uint8_t v___x_6101_; 
v___x_6101_ = lean_nat_dec_lt(v_version_6079_, v_version_6095_);
if (v___x_6101_ == 0)
{
lean_object* v___x_6103_; uint8_t v_isShared_6104_; uint8_t v_isSharedCheck_6126_; 
lean_inc(v_workers_6089_);
lean_inc(v_ileans_6088_);
v_isSharedCheck_6126_ = !lean_is_exclusive(v_self_6076_);
if (v_isSharedCheck_6126_ == 0)
{
lean_object* v_unused_6127_; lean_object* v_unused_6128_; 
v_unused_6127_ = lean_ctor_get(v_self_6076_, 1);
lean_dec(v_unused_6127_);
v_unused_6128_ = lean_ctor_get(v_self_6076_, 0);
lean_dec(v_unused_6128_);
v___x_6103_ = v_self_6076_;
v_isShared_6104_ = v_isSharedCheck_6126_;
goto v_resetjp_6102_;
}
else
{
lean_dec(v_self_6076_);
v___x_6103_ = lean_box(0);
v_isShared_6104_ = v_isSharedCheck_6126_;
goto v_resetjp_6102_;
}
v_resetjp_6102_:
{
uint8_t v___x_6105_; 
v___x_6105_ = lean_nat_dec_eq(v_version_6079_, v_version_6095_);
lean_dec(v_version_6095_);
if (v___x_6105_ == 0)
{
lean_object* v___x_6107_; 
lean_dec(v_decls_6097_);
lean_dec(v_refs_6096_);
if (v_isShared_6100_ == 0)
{
lean_ctor_set(v___x_6099_, 5, v___x_6090_);
lean_ctor_set(v___x_6099_, 4, v___x_6090_);
lean_ctor_set(v___x_6099_, 3, v___x_6092_);
lean_ctor_set(v___x_6099_, 2, v_a_6084_);
lean_ctor_set(v___x_6099_, 1, v_version_6079_);
lean_ctor_set(v___x_6099_, 0, v_moduleUri_6078_);
v___x_6107_ = v___x_6099_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6115_; 
v_reuseFailAlloc_6115_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6115_, 0, v_moduleUri_6078_);
lean_ctor_set(v_reuseFailAlloc_6115_, 1, v_version_6079_);
lean_ctor_set(v_reuseFailAlloc_6115_, 2, v_a_6084_);
lean_ctor_set(v_reuseFailAlloc_6115_, 3, v___x_6092_);
lean_ctor_set(v_reuseFailAlloc_6115_, 4, v___x_6090_);
lean_ctor_set(v_reuseFailAlloc_6115_, 5, v___x_6090_);
v___x_6107_ = v_reuseFailAlloc_6115_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
lean_object* v___x_6108_; lean_object* v___x_6110_; 
v___x_6108_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6077_, v___x_6107_, v_workers_6089_);
if (v_isShared_6104_ == 0)
{
lean_ctor_set(v___x_6103_, 1, v___x_6108_);
v___x_6110_ = v___x_6103_;
goto v_reusejp_6109_;
}
else
{
lean_object* v_reuseFailAlloc_6114_; 
v_reuseFailAlloc_6114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6114_, 0, v_ileans_6088_);
lean_ctor_set(v_reuseFailAlloc_6114_, 1, v___x_6108_);
v___x_6110_ = v_reuseFailAlloc_6114_;
goto v_reusejp_6109_;
}
v_reusejp_6109_:
{
lean_object* v___x_6112_; 
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 0, v___x_6110_);
v___x_6112_ = v___x_6086_;
goto v_reusejp_6111_;
}
else
{
lean_object* v_reuseFailAlloc_6113_; 
v_reuseFailAlloc_6113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6113_, 0, v___x_6110_);
v___x_6112_ = v_reuseFailAlloc_6113_;
goto v_reusejp_6111_;
}
v_reusejp_6111_:
{
return v___x_6112_;
}
}
}
}
else
{
lean_object* v___x_6117_; 
if (v_isShared_6100_ == 0)
{
lean_ctor_set(v___x_6099_, 3, v___x_6092_);
lean_ctor_set(v___x_6099_, 2, v_a_6084_);
lean_ctor_set(v___x_6099_, 1, v_version_6079_);
lean_ctor_set(v___x_6099_, 0, v_moduleUri_6078_);
v___x_6117_ = v___x_6099_;
goto v_reusejp_6116_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_moduleUri_6078_);
lean_ctor_set(v_reuseFailAlloc_6125_, 1, v_version_6079_);
lean_ctor_set(v_reuseFailAlloc_6125_, 2, v_a_6084_);
lean_ctor_set(v_reuseFailAlloc_6125_, 3, v___x_6092_);
lean_ctor_set(v_reuseFailAlloc_6125_, 4, v_refs_6096_);
lean_ctor_set(v_reuseFailAlloc_6125_, 5, v_decls_6097_);
v___x_6117_ = v_reuseFailAlloc_6125_;
goto v_reusejp_6116_;
}
v_reusejp_6116_:
{
lean_object* v___x_6118_; lean_object* v___x_6120_; 
v___x_6118_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6077_, v___x_6117_, v_workers_6089_);
if (v_isShared_6104_ == 0)
{
lean_ctor_set(v___x_6103_, 1, v___x_6118_);
v___x_6120_ = v___x_6103_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6124_; 
v_reuseFailAlloc_6124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_ileans_6088_);
lean_ctor_set(v_reuseFailAlloc_6124_, 1, v___x_6118_);
v___x_6120_ = v_reuseFailAlloc_6124_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
lean_object* v___x_6122_; 
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 0, v___x_6120_);
v___x_6122_ = v___x_6086_;
goto v_reusejp_6121_;
}
else
{
lean_object* v_reuseFailAlloc_6123_; 
v_reuseFailAlloc_6123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6123_, 0, v___x_6120_);
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
}
}
else
{
lean_object* v___x_6130_; 
lean_del_object(v___x_6099_);
lean_dec(v_decls_6097_);
lean_dec(v_refs_6096_);
lean_dec(v_version_6095_);
lean_dec_ref(v___x_6092_);
lean_dec(v_a_6084_);
lean_dec(v_version_6079_);
lean_dec_ref(v_moduleUri_6078_);
lean_dec(v_name_6077_);
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 0, v_self_6076_);
v___x_6130_ = v___x_6086_;
goto v_reusejp_6129_;
}
else
{
lean_object* v_reuseFailAlloc_6131_; 
v_reuseFailAlloc_6131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6131_, 0, v_self_6076_);
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
else
{
lean_object* v___x_6137_; uint8_t v_isShared_6138_; uint8_t v_isSharedCheck_6147_; 
lean_inc(v_workers_6089_);
lean_inc(v_ileans_6088_);
lean_dec(v___x_6093_);
v_isSharedCheck_6147_ = !lean_is_exclusive(v_self_6076_);
if (v_isSharedCheck_6147_ == 0)
{
lean_object* v_unused_6148_; lean_object* v_unused_6149_; 
v_unused_6148_ = lean_ctor_get(v_self_6076_, 1);
lean_dec(v_unused_6148_);
v_unused_6149_ = lean_ctor_get(v_self_6076_, 0);
lean_dec(v_unused_6149_);
v___x_6137_ = v_self_6076_;
v_isShared_6138_ = v_isSharedCheck_6147_;
goto v_resetjp_6136_;
}
else
{
lean_dec(v_self_6076_);
v___x_6137_ = lean_box(0);
v_isShared_6138_ = v_isSharedCheck_6147_;
goto v_resetjp_6136_;
}
v_resetjp_6136_:
{
lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6142_; 
v___x_6139_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6139_, 0, v_moduleUri_6078_);
lean_ctor_set(v___x_6139_, 1, v_version_6079_);
lean_ctor_set(v___x_6139_, 2, v_a_6084_);
lean_ctor_set(v___x_6139_, 3, v___x_6092_);
lean_ctor_set(v___x_6139_, 4, v___x_6090_);
lean_ctor_set(v___x_6139_, 5, v___x_6090_);
v___x_6140_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6077_, v___x_6139_, v_workers_6089_);
if (v_isShared_6138_ == 0)
{
lean_ctor_set(v___x_6137_, 1, v___x_6140_);
v___x_6142_ = v___x_6137_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6146_; 
v_reuseFailAlloc_6146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6146_, 0, v_ileans_6088_);
lean_ctor_set(v_reuseFailAlloc_6146_, 1, v___x_6140_);
v___x_6142_ = v_reuseFailAlloc_6146_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
lean_object* v___x_6144_; 
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 0, v___x_6142_);
v___x_6144_ = v___x_6086_;
goto v_reusejp_6143_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v___x_6142_);
v___x_6144_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6143_;
}
v_reusejp_6143_:
{
return v___x_6144_;
}
}
}
}
}
}
else
{
lean_object* v_a_6151_; lean_object* v___x_6153_; uint8_t v_isShared_6154_; uint8_t v_isSharedCheck_6158_; 
lean_dec(v_version_6079_);
lean_dec_ref(v_moduleUri_6078_);
lean_dec(v_name_6077_);
lean_dec_ref(v_self_6076_);
v_a_6151_ = lean_ctor_get(v___x_6083_, 0);
v_isSharedCheck_6158_ = !lean_is_exclusive(v___x_6083_);
if (v_isSharedCheck_6158_ == 0)
{
v___x_6153_ = v___x_6083_;
v_isShared_6154_ = v_isSharedCheck_6158_;
goto v_resetjp_6152_;
}
else
{
lean_inc(v_a_6151_);
lean_dec(v___x_6083_);
v___x_6153_ = lean_box(0);
v_isShared_6154_ = v_isSharedCheck_6158_;
goto v_resetjp_6152_;
}
v_resetjp_6152_:
{
lean_object* v___x_6156_; 
if (v_isShared_6154_ == 0)
{
v___x_6156_ = v___x_6153_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6157_; 
v_reuseFailAlloc_6157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6157_, 0, v_a_6151_);
v___x_6156_ = v_reuseFailAlloc_6157_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
return v___x_6156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6159_, lean_object* v_name_6160_, lean_object* v_moduleUri_6161_, lean_object* v_version_6162_, lean_object* v_directImports_6163_, lean_object* v_isSetupFailure_6164_, lean_object* v_a_6165_){
_start:
{
uint8_t v_isSetupFailure_boxed_6166_; lean_object* v_res_6167_; 
v_isSetupFailure_boxed_6166_ = lean_unbox(v_isSetupFailure_6164_);
v_res_6167_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6159_, v_name_6160_, v_moduleUri_6161_, v_version_6162_, v_directImports_6163_, v_isSetupFailure_boxed_6166_);
lean_dec_ref(v_directImports_6163_);
return v_res_6167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6168_, lean_object* v_t_6169_, lean_object* v_k_6170_){
_start:
{
lean_object* v___x_6171_; 
v___x_6171_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6169_, v_k_6170_);
return v___x_6171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6172_, lean_object* v_t_6173_, lean_object* v_k_6174_){
_start:
{
lean_object* v_res_6175_; 
v_res_6175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6172_, v_t_6173_, v_k_6174_);
lean_dec(v_k_6174_);
lean_dec(v_t_6173_);
return v_res_6175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6176_, lean_object* v_____s_6177_){
_start:
{
lean_object* v_fst_6178_; lean_object* v_snd_6179_; lean_object* v_r_6180_; lean_object* v___x_6181_; 
v_fst_6178_ = lean_ctor_get(v_x_6176_, 0);
lean_inc(v_fst_6178_);
v_snd_6179_ = lean_ctor_get(v_x_6176_, 1);
lean_inc(v_snd_6179_);
lean_dec_ref(v_x_6176_);
v_r_6180_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6178_, v_snd_6179_, v_____s_6177_);
v___x_6181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6181_, 0, v_r_6180_);
return v___x_6181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6182_, lean_object* v_k_6183_, lean_object* v_fallback_6184_){
_start:
{
if (lean_obj_tag(v_t_6182_) == 0)
{
lean_object* v_k_6185_; lean_object* v_v_6186_; lean_object* v_l_6187_; lean_object* v_r_6188_; uint8_t v___x_6189_; 
v_k_6185_ = lean_ctor_get(v_t_6182_, 1);
v_v_6186_ = lean_ctor_get(v_t_6182_, 2);
v_l_6187_ = lean_ctor_get(v_t_6182_, 3);
v_r_6188_ = lean_ctor_get(v_t_6182_, 4);
v___x_6189_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6183_, v_k_6185_);
switch(v___x_6189_)
{
case 0:
{
v_t_6182_ = v_l_6187_;
goto _start;
}
case 1:
{
lean_inc(v_v_6186_);
return v_v_6186_;
}
default: 
{
v_t_6182_ = v_r_6188_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6184_);
return v_fallback_6184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6192_, lean_object* v_k_6193_, lean_object* v_fallback_6194_){
_start:
{
lean_object* v_res_6195_; 
v_res_6195_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6192_, v_k_6193_, v_fallback_6194_);
lean_dec(v_fallback_6194_);
lean_dec_ref(v_k_6193_);
lean_dec(v_t_6192_);
return v_res_6195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6196_, lean_object* v_x_6197_){
_start:
{
if (lean_obj_tag(v_x_6197_) == 0)
{
lean_object* v_k_6198_; lean_object* v_v_6199_; lean_object* v_l_6200_; lean_object* v_r_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; 
v_k_6198_ = lean_ctor_get(v_x_6197_, 1);
lean_inc(v_k_6198_);
v_v_6199_ = lean_ctor_get(v_x_6197_, 2);
lean_inc(v_v_6199_);
v_l_6200_ = lean_ctor_get(v_x_6197_, 3);
lean_inc(v_l_6200_);
v_r_6201_ = lean_ctor_get(v_x_6197_, 4);
lean_inc(v_r_6201_);
lean_dec_ref(v_x_6197_);
v___x_6202_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6196_, v_l_6200_);
v___x_6203_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6204_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6202_, v_k_6198_, v___x_6203_);
v___x_6205_ = l_Lean_Lsp_RefInfo_merge(v___x_6204_, v_v_6199_);
v___x_6206_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6198_, v___x_6205_, v___x_6202_);
v_init_6196_ = v___x_6206_;
v_x_6197_ = v_r_6201_;
goto _start;
}
else
{
return v_init_6196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6209_, lean_object* v_name_6210_, lean_object* v_moduleUri_6211_, lean_object* v_version_6212_, lean_object* v_refs_6213_, lean_object* v_decls_6214_){
_start:
{
lean_object* v_ileans_6216_; lean_object* v_workers_6217_; lean_object* v___x_6218_; 
v_ileans_6216_ = lean_ctor_get(v_self_6209_, 0);
v_workers_6217_ = lean_ctor_get(v_self_6209_, 1);
v___x_6218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6217_, v_name_6210_);
if (lean_obj_tag(v___x_6218_) == 1)
{
lean_object* v_val_6219_; lean_object* v___x_6221_; uint8_t v_isShared_6222_; uint8_t v_isSharedCheck_6267_; 
v_val_6219_ = lean_ctor_get(v___x_6218_, 0);
v_isSharedCheck_6267_ = !lean_is_exclusive(v___x_6218_);
if (v_isSharedCheck_6267_ == 0)
{
v___x_6221_ = v___x_6218_;
v_isShared_6222_ = v_isSharedCheck_6267_;
goto v_resetjp_6220_;
}
else
{
lean_inc(v_val_6219_);
lean_dec(v___x_6218_);
v___x_6221_ = lean_box(0);
v_isShared_6222_ = v_isSharedCheck_6267_;
goto v_resetjp_6220_;
}
v_resetjp_6220_:
{
lean_object* v_version_6223_; lean_object* v_directImports_6224_; lean_object* v_isSetupFailure_x3f_6225_; lean_object* v_refs_6226_; lean_object* v_decls_6227_; lean_object* v___x_6229_; uint8_t v_isShared_6230_; uint8_t v_isSharedCheck_6265_; 
v_version_6223_ = lean_ctor_get(v_val_6219_, 1);
v_directImports_6224_ = lean_ctor_get(v_val_6219_, 2);
v_isSetupFailure_x3f_6225_ = lean_ctor_get(v_val_6219_, 3);
v_refs_6226_ = lean_ctor_get(v_val_6219_, 4);
v_decls_6227_ = lean_ctor_get(v_val_6219_, 5);
v_isSharedCheck_6265_ = !lean_is_exclusive(v_val_6219_);
if (v_isSharedCheck_6265_ == 0)
{
lean_object* v_unused_6266_; 
v_unused_6266_ = lean_ctor_get(v_val_6219_, 0);
lean_dec(v_unused_6266_);
v___x_6229_ = v_val_6219_;
v_isShared_6230_ = v_isSharedCheck_6265_;
goto v_resetjp_6228_;
}
else
{
lean_inc(v_decls_6227_);
lean_inc(v_refs_6226_);
lean_inc(v_isSetupFailure_x3f_6225_);
lean_inc(v_directImports_6224_);
lean_inc(v_version_6223_);
lean_dec(v_val_6219_);
v___x_6229_ = lean_box(0);
v_isShared_6230_ = v_isSharedCheck_6265_;
goto v_resetjp_6228_;
}
v_resetjp_6228_:
{
uint8_t v___x_6231_; 
v___x_6231_ = lean_nat_dec_lt(v_version_6212_, v_version_6223_);
if (v___x_6231_ == 0)
{
lean_object* v___x_6233_; uint8_t v_isShared_6234_; uint8_t v_isSharedCheck_6259_; 
lean_inc(v_workers_6217_);
lean_inc(v_ileans_6216_);
v_isSharedCheck_6259_ = !lean_is_exclusive(v_self_6209_);
if (v_isSharedCheck_6259_ == 0)
{
lean_object* v_unused_6260_; lean_object* v_unused_6261_; 
v_unused_6260_ = lean_ctor_get(v_self_6209_, 1);
lean_dec(v_unused_6260_);
v_unused_6261_ = lean_ctor_get(v_self_6209_, 0);
lean_dec(v_unused_6261_);
v___x_6233_ = v_self_6209_;
v_isShared_6234_ = v_isSharedCheck_6259_;
goto v_resetjp_6232_;
}
else
{
lean_dec(v_self_6209_);
v___x_6233_ = lean_box(0);
v_isShared_6234_ = v_isSharedCheck_6259_;
goto v_resetjp_6232_;
}
v_resetjp_6232_:
{
uint8_t v___x_6235_; 
v___x_6235_ = lean_nat_dec_eq(v_version_6212_, v_version_6223_);
lean_dec(v_version_6223_);
if (v___x_6235_ == 0)
{
lean_object* v___x_6237_; 
lean_dec(v_decls_6227_);
lean_dec(v_refs_6226_);
if (v_isShared_6230_ == 0)
{
lean_ctor_set(v___x_6229_, 5, v_decls_6214_);
lean_ctor_set(v___x_6229_, 4, v_refs_6213_);
lean_ctor_set(v___x_6229_, 1, v_version_6212_);
lean_ctor_set(v___x_6229_, 0, v_moduleUri_6211_);
v___x_6237_ = v___x_6229_;
goto v_reusejp_6236_;
}
else
{
lean_object* v_reuseFailAlloc_6245_; 
v_reuseFailAlloc_6245_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6245_, 0, v_moduleUri_6211_);
lean_ctor_set(v_reuseFailAlloc_6245_, 1, v_version_6212_);
lean_ctor_set(v_reuseFailAlloc_6245_, 2, v_directImports_6224_);
lean_ctor_set(v_reuseFailAlloc_6245_, 3, v_isSetupFailure_x3f_6225_);
lean_ctor_set(v_reuseFailAlloc_6245_, 4, v_refs_6213_);
lean_ctor_set(v_reuseFailAlloc_6245_, 5, v_decls_6214_);
v___x_6237_ = v_reuseFailAlloc_6245_;
goto v_reusejp_6236_;
}
v_reusejp_6236_:
{
lean_object* v___x_6238_; lean_object* v___x_6240_; 
v___x_6238_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6210_, v___x_6237_, v_workers_6217_);
if (v_isShared_6234_ == 0)
{
lean_ctor_set(v___x_6233_, 1, v___x_6238_);
v___x_6240_ = v___x_6233_;
goto v_reusejp_6239_;
}
else
{
lean_object* v_reuseFailAlloc_6244_; 
v_reuseFailAlloc_6244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6244_, 0, v_ileans_6216_);
lean_ctor_set(v_reuseFailAlloc_6244_, 1, v___x_6238_);
v___x_6240_ = v_reuseFailAlloc_6244_;
goto v_reusejp_6239_;
}
v_reusejp_6239_:
{
lean_object* v___x_6242_; 
if (v_isShared_6222_ == 0)
{
lean_ctor_set_tag(v___x_6221_, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6240_);
v___x_6242_ = v___x_6221_;
goto v_reusejp_6241_;
}
else
{
lean_object* v_reuseFailAlloc_6243_; 
v_reuseFailAlloc_6243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6243_, 0, v___x_6240_);
v___x_6242_ = v_reuseFailAlloc_6243_;
goto v_reusejp_6241_;
}
v_reusejp_6241_:
{
return v___x_6242_;
}
}
}
}
else
{
lean_object* v___f_6246_; lean_object* v_mergedRefs_6247_; lean_object* v_mergedDecls_6248_; lean_object* v___x_6250_; 
v___f_6246_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6247_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6226_, v_refs_6213_);
v_mergedDecls_6248_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6214_, v_decls_6227_, v___f_6246_);
lean_dec(v_decls_6214_);
if (v_isShared_6230_ == 0)
{
lean_ctor_set(v___x_6229_, 5, v_mergedDecls_6248_);
lean_ctor_set(v___x_6229_, 4, v_mergedRefs_6247_);
lean_ctor_set(v___x_6229_, 1, v_version_6212_);
lean_ctor_set(v___x_6229_, 0, v_moduleUri_6211_);
v___x_6250_ = v___x_6229_;
goto v_reusejp_6249_;
}
else
{
lean_object* v_reuseFailAlloc_6258_; 
v_reuseFailAlloc_6258_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6258_, 0, v_moduleUri_6211_);
lean_ctor_set(v_reuseFailAlloc_6258_, 1, v_version_6212_);
lean_ctor_set(v_reuseFailAlloc_6258_, 2, v_directImports_6224_);
lean_ctor_set(v_reuseFailAlloc_6258_, 3, v_isSetupFailure_x3f_6225_);
lean_ctor_set(v_reuseFailAlloc_6258_, 4, v_mergedRefs_6247_);
lean_ctor_set(v_reuseFailAlloc_6258_, 5, v_mergedDecls_6248_);
v___x_6250_ = v_reuseFailAlloc_6258_;
goto v_reusejp_6249_;
}
v_reusejp_6249_:
{
lean_object* v___x_6251_; lean_object* v___x_6253_; 
v___x_6251_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6210_, v___x_6250_, v_workers_6217_);
if (v_isShared_6234_ == 0)
{
lean_ctor_set(v___x_6233_, 1, v___x_6251_);
v___x_6253_ = v___x_6233_;
goto v_reusejp_6252_;
}
else
{
lean_object* v_reuseFailAlloc_6257_; 
v_reuseFailAlloc_6257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6257_, 0, v_ileans_6216_);
lean_ctor_set(v_reuseFailAlloc_6257_, 1, v___x_6251_);
v___x_6253_ = v_reuseFailAlloc_6257_;
goto v_reusejp_6252_;
}
v_reusejp_6252_:
{
lean_object* v___x_6255_; 
if (v_isShared_6222_ == 0)
{
lean_ctor_set_tag(v___x_6221_, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6253_);
v___x_6255_ = v___x_6221_;
goto v_reusejp_6254_;
}
else
{
lean_object* v_reuseFailAlloc_6256_; 
v_reuseFailAlloc_6256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6256_, 0, v___x_6253_);
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
}
else
{
lean_object* v___x_6263_; 
lean_del_object(v___x_6229_);
lean_dec(v_decls_6227_);
lean_dec(v_refs_6226_);
lean_dec(v_isSetupFailure_x3f_6225_);
lean_dec_ref(v_directImports_6224_);
lean_dec(v_version_6223_);
lean_dec(v_decls_6214_);
lean_dec(v_refs_6213_);
lean_dec(v_version_6212_);
lean_dec_ref(v_moduleUri_6211_);
lean_dec(v_name_6210_);
if (v_isShared_6222_ == 0)
{
lean_ctor_set_tag(v___x_6221_, 0);
lean_ctor_set(v___x_6221_, 0, v_self_6209_);
v___x_6263_ = v___x_6221_;
goto v_reusejp_6262_;
}
else
{
lean_object* v_reuseFailAlloc_6264_; 
v_reuseFailAlloc_6264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6264_, 0, v_self_6209_);
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
else
{
lean_object* v___x_6269_; uint8_t v_isShared_6270_; uint8_t v_isSharedCheck_6279_; 
lean_inc(v_workers_6217_);
lean_inc(v_ileans_6216_);
lean_dec(v___x_6218_);
v_isSharedCheck_6279_ = !lean_is_exclusive(v_self_6209_);
if (v_isSharedCheck_6279_ == 0)
{
lean_object* v_unused_6280_; lean_object* v_unused_6281_; 
v_unused_6280_ = lean_ctor_get(v_self_6209_, 1);
lean_dec(v_unused_6280_);
v_unused_6281_ = lean_ctor_get(v_self_6209_, 0);
lean_dec(v_unused_6281_);
v___x_6269_ = v_self_6209_;
v_isShared_6270_ = v_isSharedCheck_6279_;
goto v_resetjp_6268_;
}
else
{
lean_dec(v_self_6209_);
v___x_6269_ = lean_box(0);
v_isShared_6270_ = v_isSharedCheck_6279_;
goto v_resetjp_6268_;
}
v_resetjp_6268_:
{
lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6276_; 
v___x_6271_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6272_ = lean_box(0);
v___x_6273_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6273_, 0, v_moduleUri_6211_);
lean_ctor_set(v___x_6273_, 1, v_version_6212_);
lean_ctor_set(v___x_6273_, 2, v___x_6271_);
lean_ctor_set(v___x_6273_, 3, v___x_6272_);
lean_ctor_set(v___x_6273_, 4, v_refs_6213_);
lean_ctor_set(v___x_6273_, 5, v_decls_6214_);
v___x_6274_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6210_, v___x_6273_, v_workers_6217_);
if (v_isShared_6270_ == 0)
{
lean_ctor_set(v___x_6269_, 1, v___x_6274_);
v___x_6276_ = v___x_6269_;
goto v_reusejp_6275_;
}
else
{
lean_object* v_reuseFailAlloc_6278_; 
v_reuseFailAlloc_6278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6278_, 0, v_ileans_6216_);
lean_ctor_set(v_reuseFailAlloc_6278_, 1, v___x_6274_);
v___x_6276_ = v_reuseFailAlloc_6278_;
goto v_reusejp_6275_;
}
v_reusejp_6275_:
{
lean_object* v___x_6277_; 
v___x_6277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6277_, 0, v___x_6276_);
return v___x_6277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6282_, lean_object* v_name_6283_, lean_object* v_moduleUri_6284_, lean_object* v_version_6285_, lean_object* v_refs_6286_, lean_object* v_decls_6287_, lean_object* v_a_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_Lean_Server_References_updateWorkerRefs(v_self_6282_, v_name_6283_, v_moduleUri_6284_, v_version_6285_, v_refs_6286_, v_decls_6287_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6290_, lean_object* v_t_6291_, lean_object* v_k_6292_, lean_object* v_fallback_6293_){
_start:
{
lean_object* v___x_6294_; 
v___x_6294_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6291_, v_k_6292_, v_fallback_6293_);
return v___x_6294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6295_, lean_object* v_t_6296_, lean_object* v_k_6297_, lean_object* v_fallback_6298_){
_start:
{
lean_object* v_res_6299_; 
v_res_6299_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6295_, v_t_6296_, v_k_6297_, v_fallback_6298_);
lean_dec(v_fallback_6298_);
lean_dec_ref(v_k_6297_);
lean_dec(v_t_6296_);
return v_res_6299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6300_, lean_object* v_t_6301_){
_start:
{
lean_object* v___x_6302_; 
v___x_6302_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6300_, v_t_6301_);
return v___x_6302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6303_, lean_object* v_name_6304_, lean_object* v_moduleUri_6305_, lean_object* v_version_6306_, lean_object* v_refs_6307_, lean_object* v_decls_6308_){
_start:
{
lean_object* v_ileans_6310_; lean_object* v_workers_6311_; lean_object* v___x_6312_; 
v_ileans_6310_ = lean_ctor_get(v_self_6303_, 0);
v_workers_6311_ = lean_ctor_get(v_self_6303_, 1);
v___x_6312_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6311_, v_name_6304_);
if (lean_obj_tag(v___x_6312_) == 1)
{
lean_object* v_val_6313_; lean_object* v___x_6315_; uint8_t v_isShared_6316_; uint8_t v_isSharedCheck_6347_; 
v_val_6313_ = lean_ctor_get(v___x_6312_, 0);
v_isSharedCheck_6347_ = !lean_is_exclusive(v___x_6312_);
if (v_isSharedCheck_6347_ == 0)
{
v___x_6315_ = v___x_6312_;
v_isShared_6316_ = v_isSharedCheck_6347_;
goto v_resetjp_6314_;
}
else
{
lean_inc(v_val_6313_);
lean_dec(v___x_6312_);
v___x_6315_ = lean_box(0);
v_isShared_6316_ = v_isSharedCheck_6347_;
goto v_resetjp_6314_;
}
v_resetjp_6314_:
{
lean_object* v_version_6317_; lean_object* v_directImports_6318_; lean_object* v_isSetupFailure_x3f_6319_; lean_object* v___x_6321_; uint8_t v_isShared_6322_; uint8_t v_isSharedCheck_6343_; 
v_version_6317_ = lean_ctor_get(v_val_6313_, 1);
v_directImports_6318_ = lean_ctor_get(v_val_6313_, 2);
v_isSetupFailure_x3f_6319_ = lean_ctor_get(v_val_6313_, 3);
v_isSharedCheck_6343_ = !lean_is_exclusive(v_val_6313_);
if (v_isSharedCheck_6343_ == 0)
{
lean_object* v_unused_6344_; lean_object* v_unused_6345_; lean_object* v_unused_6346_; 
v_unused_6344_ = lean_ctor_get(v_val_6313_, 5);
lean_dec(v_unused_6344_);
v_unused_6345_ = lean_ctor_get(v_val_6313_, 4);
lean_dec(v_unused_6345_);
v_unused_6346_ = lean_ctor_get(v_val_6313_, 0);
lean_dec(v_unused_6346_);
v___x_6321_ = v_val_6313_;
v_isShared_6322_ = v_isSharedCheck_6343_;
goto v_resetjp_6320_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6319_);
lean_inc(v_directImports_6318_);
lean_inc(v_version_6317_);
lean_dec(v_val_6313_);
v___x_6321_ = lean_box(0);
v_isShared_6322_ = v_isSharedCheck_6343_;
goto v_resetjp_6320_;
}
v_resetjp_6320_:
{
uint8_t v___x_6323_; 
v___x_6323_ = lean_nat_dec_lt(v_version_6306_, v_version_6317_);
lean_dec(v_version_6317_);
if (v___x_6323_ == 0)
{
lean_object* v___x_6325_; uint8_t v_isShared_6326_; uint8_t v_isSharedCheck_6337_; 
lean_inc(v_workers_6311_);
lean_inc(v_ileans_6310_);
v_isSharedCheck_6337_ = !lean_is_exclusive(v_self_6303_);
if (v_isSharedCheck_6337_ == 0)
{
lean_object* v_unused_6338_; lean_object* v_unused_6339_; 
v_unused_6338_ = lean_ctor_get(v_self_6303_, 1);
lean_dec(v_unused_6338_);
v_unused_6339_ = lean_ctor_get(v_self_6303_, 0);
lean_dec(v_unused_6339_);
v___x_6325_ = v_self_6303_;
v_isShared_6326_ = v_isSharedCheck_6337_;
goto v_resetjp_6324_;
}
else
{
lean_dec(v_self_6303_);
v___x_6325_ = lean_box(0);
v_isShared_6326_ = v_isSharedCheck_6337_;
goto v_resetjp_6324_;
}
v_resetjp_6324_:
{
lean_object* v___x_6328_; 
if (v_isShared_6322_ == 0)
{
lean_ctor_set(v___x_6321_, 5, v_decls_6308_);
lean_ctor_set(v___x_6321_, 4, v_refs_6307_);
lean_ctor_set(v___x_6321_, 1, v_version_6306_);
lean_ctor_set(v___x_6321_, 0, v_moduleUri_6305_);
v___x_6328_ = v___x_6321_;
goto v_reusejp_6327_;
}
else
{
lean_object* v_reuseFailAlloc_6336_; 
v_reuseFailAlloc_6336_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6336_, 0, v_moduleUri_6305_);
lean_ctor_set(v_reuseFailAlloc_6336_, 1, v_version_6306_);
lean_ctor_set(v_reuseFailAlloc_6336_, 2, v_directImports_6318_);
lean_ctor_set(v_reuseFailAlloc_6336_, 3, v_isSetupFailure_x3f_6319_);
lean_ctor_set(v_reuseFailAlloc_6336_, 4, v_refs_6307_);
lean_ctor_set(v_reuseFailAlloc_6336_, 5, v_decls_6308_);
v___x_6328_ = v_reuseFailAlloc_6336_;
goto v_reusejp_6327_;
}
v_reusejp_6327_:
{
lean_object* v___x_6329_; lean_object* v___x_6331_; 
v___x_6329_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6304_, v___x_6328_, v_workers_6311_);
if (v_isShared_6326_ == 0)
{
lean_ctor_set(v___x_6325_, 1, v___x_6329_);
v___x_6331_ = v___x_6325_;
goto v_reusejp_6330_;
}
else
{
lean_object* v_reuseFailAlloc_6335_; 
v_reuseFailAlloc_6335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6335_, 0, v_ileans_6310_);
lean_ctor_set(v_reuseFailAlloc_6335_, 1, v___x_6329_);
v___x_6331_ = v_reuseFailAlloc_6335_;
goto v_reusejp_6330_;
}
v_reusejp_6330_:
{
lean_object* v___x_6333_; 
if (v_isShared_6316_ == 0)
{
lean_ctor_set_tag(v___x_6315_, 0);
lean_ctor_set(v___x_6315_, 0, v___x_6331_);
v___x_6333_ = v___x_6315_;
goto v_reusejp_6332_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v___x_6331_);
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
lean_object* v___x_6341_; 
lean_del_object(v___x_6321_);
lean_dec(v_isSetupFailure_x3f_6319_);
lean_dec_ref(v_directImports_6318_);
lean_dec(v_decls_6308_);
lean_dec(v_refs_6307_);
lean_dec(v_version_6306_);
lean_dec_ref(v_moduleUri_6305_);
lean_dec(v_name_6304_);
if (v_isShared_6316_ == 0)
{
lean_ctor_set_tag(v___x_6315_, 0);
lean_ctor_set(v___x_6315_, 0, v_self_6303_);
v___x_6341_ = v___x_6315_;
goto v_reusejp_6340_;
}
else
{
lean_object* v_reuseFailAlloc_6342_; 
v_reuseFailAlloc_6342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6342_, 0, v_self_6303_);
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
lean_object* v___x_6349_; uint8_t v_isShared_6350_; uint8_t v_isSharedCheck_6359_; 
lean_inc(v_workers_6311_);
lean_inc(v_ileans_6310_);
lean_dec(v___x_6312_);
v_isSharedCheck_6359_ = !lean_is_exclusive(v_self_6303_);
if (v_isSharedCheck_6359_ == 0)
{
lean_object* v_unused_6360_; lean_object* v_unused_6361_; 
v_unused_6360_ = lean_ctor_get(v_self_6303_, 1);
lean_dec(v_unused_6360_);
v_unused_6361_ = lean_ctor_get(v_self_6303_, 0);
lean_dec(v_unused_6361_);
v___x_6349_ = v_self_6303_;
v_isShared_6350_ = v_isSharedCheck_6359_;
goto v_resetjp_6348_;
}
else
{
lean_dec(v_self_6303_);
v___x_6349_ = lean_box(0);
v_isShared_6350_ = v_isSharedCheck_6359_;
goto v_resetjp_6348_;
}
v_resetjp_6348_:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6356_; 
v___x_6351_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6352_ = lean_box(0);
v___x_6353_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6353_, 0, v_moduleUri_6305_);
lean_ctor_set(v___x_6353_, 1, v_version_6306_);
lean_ctor_set(v___x_6353_, 2, v___x_6351_);
lean_ctor_set(v___x_6353_, 3, v___x_6352_);
lean_ctor_set(v___x_6353_, 4, v_refs_6307_);
lean_ctor_set(v___x_6353_, 5, v_decls_6308_);
v___x_6354_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6304_, v___x_6353_, v_workers_6311_);
if (v_isShared_6350_ == 0)
{
lean_ctor_set(v___x_6349_, 1, v___x_6354_);
v___x_6356_ = v___x_6349_;
goto v_reusejp_6355_;
}
else
{
lean_object* v_reuseFailAlloc_6358_; 
v_reuseFailAlloc_6358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6358_, 0, v_ileans_6310_);
lean_ctor_set(v_reuseFailAlloc_6358_, 1, v___x_6354_);
v___x_6356_ = v_reuseFailAlloc_6358_;
goto v_reusejp_6355_;
}
v_reusejp_6355_:
{
lean_object* v___x_6357_; 
v___x_6357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6357_, 0, v___x_6356_);
return v___x_6357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6362_, lean_object* v_name_6363_, lean_object* v_moduleUri_6364_, lean_object* v_version_6365_, lean_object* v_refs_6366_, lean_object* v_decls_6367_, lean_object* v_a_6368_){
_start:
{
lean_object* v_res_6369_; 
v_res_6369_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6362_, v_name_6363_, v_moduleUri_6364_, v_version_6365_, v_refs_6366_, v_decls_6367_);
return v_res_6369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6370_, lean_object* v_name_6371_){
_start:
{
lean_object* v_ileans_6372_; lean_object* v_workers_6373_; lean_object* v___x_6375_; uint8_t v_isShared_6376_; uint8_t v_isSharedCheck_6381_; 
v_ileans_6372_ = lean_ctor_get(v_self_6370_, 0);
v_workers_6373_ = lean_ctor_get(v_self_6370_, 1);
v_isSharedCheck_6381_ = !lean_is_exclusive(v_self_6370_);
if (v_isSharedCheck_6381_ == 0)
{
v___x_6375_ = v_self_6370_;
v_isShared_6376_ = v_isSharedCheck_6381_;
goto v_resetjp_6374_;
}
else
{
lean_inc(v_workers_6373_);
lean_inc(v_ileans_6372_);
lean_dec(v_self_6370_);
v___x_6375_ = lean_box(0);
v_isShared_6376_ = v_isSharedCheck_6381_;
goto v_resetjp_6374_;
}
v_resetjp_6374_:
{
lean_object* v___x_6377_; lean_object* v___x_6379_; 
v___x_6377_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6371_, v_workers_6373_);
if (v_isShared_6376_ == 0)
{
lean_ctor_set(v___x_6375_, 1, v___x_6377_);
v___x_6379_ = v___x_6375_;
goto v_reusejp_6378_;
}
else
{
lean_object* v_reuseFailAlloc_6380_; 
v_reuseFailAlloc_6380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6380_, 0, v_ileans_6372_);
lean_ctor_set(v_reuseFailAlloc_6380_, 1, v___x_6377_);
v___x_6379_ = v_reuseFailAlloc_6380_;
goto v_reusejp_6378_;
}
v_reusejp_6378_:
{
return v___x_6379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6382_, lean_object* v_name_6383_){
_start:
{
lean_object* v_res_6384_; 
v_res_6384_ = l_Lean_Server_References_removeWorkerRefs(v_self_6382_, v_name_6383_);
lean_dec(v_name_6383_);
return v_res_6384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6385_, lean_object* v_x_6386_){
_start:
{
if (lean_obj_tag(v_x_6386_) == 0)
{
lean_object* v_v_6387_; lean_object* v_k_6388_; lean_object* v_l_6389_; lean_object* v_r_6390_; lean_object* v_moduleUri_6391_; lean_object* v_refs_6392_; lean_object* v_decls_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; 
v_v_6387_ = lean_ctor_get(v_x_6386_, 2);
lean_inc(v_v_6387_);
v_k_6388_ = lean_ctor_get(v_x_6386_, 1);
lean_inc(v_k_6388_);
v_l_6389_ = lean_ctor_get(v_x_6386_, 3);
lean_inc(v_l_6389_);
v_r_6390_ = lean_ctor_get(v_x_6386_, 4);
lean_inc(v_r_6390_);
lean_dec_ref(v_x_6386_);
v_moduleUri_6391_ = lean_ctor_get(v_v_6387_, 0);
lean_inc_ref(v_moduleUri_6391_);
v_refs_6392_ = lean_ctor_get(v_v_6387_, 3);
lean_inc(v_refs_6392_);
v_decls_6393_ = lean_ctor_get(v_v_6387_, 4);
lean_inc(v_decls_6393_);
lean_dec(v_v_6387_);
v___x_6394_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6385_, v_l_6389_);
v___x_6395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6395_, 0, v_refs_6392_);
lean_ctor_set(v___x_6395_, 1, v_decls_6393_);
v___x_6396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6396_, 0, v_moduleUri_6391_);
lean_ctor_set(v___x_6396_, 1, v___x_6395_);
v___x_6397_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6388_, v___x_6396_, v___x_6394_);
v_init_6385_ = v___x_6397_;
v_x_6386_ = v_r_6390_;
goto _start;
}
else
{
return v_init_6385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6399_, lean_object* v_x_6400_){
_start:
{
if (lean_obj_tag(v_x_6400_) == 0)
{
lean_object* v_v_6401_; lean_object* v_k_6402_; lean_object* v_l_6403_; lean_object* v_r_6404_; lean_object* v_moduleUri_6405_; lean_object* v_refs_6406_; lean_object* v_decls_6407_; lean_object* v___x_6408_; uint8_t v___x_6409_; 
v_v_6401_ = lean_ctor_get(v_x_6400_, 2);
lean_inc(v_v_6401_);
v_k_6402_ = lean_ctor_get(v_x_6400_, 1);
lean_inc(v_k_6402_);
v_l_6403_ = lean_ctor_get(v_x_6400_, 3);
lean_inc(v_l_6403_);
v_r_6404_ = lean_ctor_get(v_x_6400_, 4);
lean_inc(v_r_6404_);
lean_dec_ref(v_x_6400_);
v_moduleUri_6405_ = lean_ctor_get(v_v_6401_, 0);
lean_inc_ref(v_moduleUri_6405_);
v_refs_6406_ = lean_ctor_get(v_v_6401_, 4);
lean_inc(v_refs_6406_);
v_decls_6407_ = lean_ctor_get(v_v_6401_, 5);
lean_inc(v_decls_6407_);
v___x_6408_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6399_, v_l_6403_);
v___x_6409_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6401_);
lean_dec(v_v_6401_);
if (v___x_6409_ == 0)
{
lean_dec(v_decls_6407_);
lean_dec(v_refs_6406_);
lean_dec_ref(v_moduleUri_6405_);
lean_dec(v_k_6402_);
v_init_6399_ = v___x_6408_;
v_x_6400_ = v_r_6404_;
goto _start;
}
else
{
lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; 
v___x_6411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6411_, 0, v_refs_6406_);
lean_ctor_set(v___x_6411_, 1, v_decls_6407_);
v___x_6412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6412_, 0, v_moduleUri_6405_);
lean_ctor_set(v___x_6412_, 1, v___x_6411_);
v___x_6413_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6402_, v___x_6412_, v___x_6408_);
v_init_6399_ = v___x_6413_;
v_x_6400_ = v_r_6404_;
goto _start;
}
}
else
{
return v_init_6399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6415_){
_start:
{
lean_object* v_ileans_6416_; lean_object* v_workers_6417_; lean_object* v___x_6418_; lean_object* v_ileanRefs_6419_; lean_object* v___x_6420_; 
v_ileans_6416_ = lean_ctor_get(v_self_6415_, 0);
lean_inc(v_ileans_6416_);
v_workers_6417_ = lean_ctor_get(v_self_6415_, 1);
lean_inc(v_workers_6417_);
lean_dec_ref(v_self_6415_);
v___x_6418_ = lean_box(1);
v_ileanRefs_6419_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6418_, v_ileans_6416_);
v___x_6420_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6419_, v_workers_6417_);
return v___x_6420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6421_, lean_object* v_t_6422_){
_start:
{
lean_object* v___x_6423_; 
v___x_6423_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6421_, v_t_6422_);
return v___x_6423_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6424_, lean_object* v_t_6425_){
_start:
{
lean_object* v___x_6426_; 
v___x_6426_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6424_, v_t_6425_);
return v___x_6426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6427_, lean_object* v_x_6428_){
_start:
{
if (lean_obj_tag(v_x_6428_) == 0)
{
lean_object* v_k_6429_; lean_object* v_v_6430_; lean_object* v_l_6431_; lean_object* v_r_6432_; lean_object* v___x_6433_; lean_object* v_a_6434_; uint8_t v___x_6435_; 
v_k_6429_ = lean_ctor_get(v_x_6428_, 1);
lean_inc(v_k_6429_);
v_v_6430_ = lean_ctor_get(v_x_6428_, 2);
lean_inc(v_v_6430_);
v_l_6431_ = lean_ctor_get(v_x_6428_, 3);
lean_inc(v_l_6431_);
v_r_6432_ = lean_ctor_get(v_x_6428_, 4);
lean_inc(v_r_6432_);
lean_dec_ref(v_x_6428_);
v___x_6433_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6427_, v_l_6431_);
v_a_6434_ = lean_ctor_get(v___x_6433_, 0);
lean_inc(v_a_6434_);
v___x_6435_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6430_);
if (v___x_6435_ == 0)
{
lean_object* v_a_6436_; 
lean_dec(v_a_6434_);
lean_dec(v_v_6430_);
lean_dec(v_k_6429_);
v_a_6436_ = lean_ctor_get(v___x_6433_, 0);
lean_inc(v_a_6436_);
lean_dec_ref(v___x_6433_);
v_init_6427_ = v_a_6436_;
v_x_6428_ = v_r_6432_;
goto _start;
}
else
{
lean_object* v_moduleUri_6438_; lean_object* v_directImports_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; 
lean_dec_ref(v___x_6433_);
v_moduleUri_6438_ = lean_ctor_get(v_v_6430_, 0);
lean_inc_ref(v_moduleUri_6438_);
v_directImports_6439_ = lean_ctor_get(v_v_6430_, 2);
lean_inc_ref(v_directImports_6439_);
lean_dec(v_v_6430_);
v___x_6440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6440_, 0, v_moduleUri_6438_);
lean_ctor_set(v___x_6440_, 1, v_directImports_6439_);
v___x_6441_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6429_, v___x_6440_, v_a_6434_);
v_init_6427_ = v___x_6441_;
v_x_6428_ = v_r_6432_;
goto _start;
}
}
else
{
lean_object* v___x_6443_; 
v___x_6443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6443_, 0, v_init_6427_);
return v___x_6443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6444_, lean_object* v_x_6445_){
_start:
{
if (lean_obj_tag(v_x_6445_) == 0)
{
lean_object* v_k_6446_; lean_object* v_v_6447_; lean_object* v_l_6448_; lean_object* v_r_6449_; lean_object* v___x_6450_; lean_object* v_a_6451_; lean_object* v_moduleUri_6452_; lean_object* v_directImports_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; 
v_k_6446_ = lean_ctor_get(v_x_6445_, 1);
lean_inc(v_k_6446_);
v_v_6447_ = lean_ctor_get(v_x_6445_, 2);
lean_inc(v_v_6447_);
v_l_6448_ = lean_ctor_get(v_x_6445_, 3);
lean_inc(v_l_6448_);
v_r_6449_ = lean_ctor_get(v_x_6445_, 4);
lean_inc(v_r_6449_);
lean_dec_ref(v_x_6445_);
v___x_6450_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6444_, v_l_6448_);
v_a_6451_ = lean_ctor_get(v___x_6450_, 0);
lean_inc(v_a_6451_);
lean_dec_ref(v___x_6450_);
v_moduleUri_6452_ = lean_ctor_get(v_v_6447_, 0);
lean_inc_ref(v_moduleUri_6452_);
v_directImports_6453_ = lean_ctor_get(v_v_6447_, 2);
lean_inc_ref(v_directImports_6453_);
lean_dec(v_v_6447_);
v___x_6454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6454_, 0, v_moduleUri_6452_);
lean_ctor_set(v___x_6454_, 1, v_directImports_6453_);
v___x_6455_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6446_, v___x_6454_, v_a_6451_);
v_init_6444_ = v___x_6455_;
v_x_6445_ = v_r_6449_;
goto _start;
}
else
{
lean_object* v___x_6457_; 
v___x_6457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6457_, 0, v_init_6444_);
return v___x_6457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6458_){
_start:
{
lean_object* v_ileans_6459_; lean_object* v_workers_6460_; lean_object* v___y_6462_; lean_object* v_allDirectImports_6465_; lean_object* v___x_6466_; lean_object* v_a_6467_; 
v_ileans_6459_ = lean_ctor_get(v_self_6458_, 0);
lean_inc(v_ileans_6459_);
v_workers_6460_ = lean_ctor_get(v_self_6458_, 1);
lean_inc(v_workers_6460_);
lean_dec_ref(v_self_6458_);
v_allDirectImports_6465_ = lean_box(1);
v___x_6466_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6465_, v_ileans_6459_);
v_a_6467_ = lean_ctor_get(v___x_6466_, 0);
lean_inc(v_a_6467_);
lean_dec_ref(v___x_6466_);
v___y_6462_ = v_a_6467_;
goto v___jp_6461_;
v___jp_6461_:
{
lean_object* v___x_6463_; lean_object* v_a_6464_; 
v___x_6463_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6462_, v_workers_6460_);
v_a_6464_ = lean_ctor_get(v___x_6463_, 0);
lean_inc(v_a_6464_);
lean_dec_ref(v___x_6463_);
return v_a_6464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6468_, lean_object* v_mod_6469_){
_start:
{
lean_object* v_ileans_6470_; lean_object* v_workers_6471_; lean_object* v___x_6473_; uint8_t v_isShared_6474_; uint8_t v_isSharedCheck_6508_; 
v_ileans_6470_ = lean_ctor_get(v_self_6468_, 0);
v_workers_6471_ = lean_ctor_get(v_self_6468_, 1);
v_isSharedCheck_6508_ = !lean_is_exclusive(v_self_6468_);
if (v_isSharedCheck_6508_ == 0)
{
v___x_6473_ = v_self_6468_;
v_isShared_6474_ = v_isSharedCheck_6508_;
goto v_resetjp_6472_;
}
else
{
lean_inc(v_workers_6471_);
lean_inc(v_ileans_6470_);
lean_dec(v_self_6468_);
v___x_6473_ = lean_box(0);
v_isShared_6474_ = v_isSharedCheck_6508_;
goto v_resetjp_6472_;
}
v_resetjp_6472_:
{
lean_object* v___x_6493_; 
v___x_6493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6471_, v_mod_6469_);
lean_dec(v_workers_6471_);
if (lean_obj_tag(v___x_6493_) == 1)
{
lean_object* v_val_6494_; lean_object* v___x_6496_; uint8_t v_isShared_6497_; uint8_t v_isSharedCheck_6507_; 
v_val_6494_ = lean_ctor_get(v___x_6493_, 0);
v_isSharedCheck_6507_ = !lean_is_exclusive(v___x_6493_);
if (v_isSharedCheck_6507_ == 0)
{
v___x_6496_ = v___x_6493_;
v_isShared_6497_ = v_isSharedCheck_6507_;
goto v_resetjp_6495_;
}
else
{
lean_inc(v_val_6494_);
lean_dec(v___x_6493_);
v___x_6496_ = lean_box(0);
v_isShared_6497_ = v_isSharedCheck_6507_;
goto v_resetjp_6495_;
}
v_resetjp_6495_:
{
uint8_t v___x_6498_; 
v___x_6498_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6494_);
if (v___x_6498_ == 0)
{
lean_del_object(v___x_6496_);
lean_dec(v_val_6494_);
goto v___jp_6475_;
}
else
{
lean_object* v_moduleUri_6499_; lean_object* v_refs_6500_; lean_object* v_decls_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; lean_object* v___x_6505_; 
lean_del_object(v___x_6473_);
lean_dec(v_ileans_6470_);
v_moduleUri_6499_ = lean_ctor_get(v_val_6494_, 0);
lean_inc_ref(v_moduleUri_6499_);
v_refs_6500_ = lean_ctor_get(v_val_6494_, 4);
lean_inc(v_refs_6500_);
v_decls_6501_ = lean_ctor_get(v_val_6494_, 5);
lean_inc(v_decls_6501_);
lean_dec(v_val_6494_);
v___x_6502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6502_, 0, v_refs_6500_);
lean_ctor_set(v___x_6502_, 1, v_decls_6501_);
v___x_6503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6503_, 0, v_moduleUri_6499_);
lean_ctor_set(v___x_6503_, 1, v___x_6502_);
if (v_isShared_6497_ == 0)
{
lean_ctor_set(v___x_6496_, 0, v___x_6503_);
v___x_6505_ = v___x_6496_;
goto v_reusejp_6504_;
}
else
{
lean_object* v_reuseFailAlloc_6506_; 
v_reuseFailAlloc_6506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6506_, 0, v___x_6503_);
v___x_6505_ = v_reuseFailAlloc_6506_;
goto v_reusejp_6504_;
}
v_reusejp_6504_:
{
return v___x_6505_;
}
}
}
}
else
{
lean_dec(v___x_6493_);
goto v___jp_6475_;
}
v___jp_6475_:
{
lean_object* v___x_6476_; 
v___x_6476_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6470_, v_mod_6469_);
lean_dec(v_ileans_6470_);
if (lean_obj_tag(v___x_6476_) == 1)
{
lean_object* v_val_6477_; lean_object* v___x_6479_; uint8_t v_isShared_6480_; uint8_t v_isSharedCheck_6491_; 
v_val_6477_ = lean_ctor_get(v___x_6476_, 0);
v_isSharedCheck_6491_ = !lean_is_exclusive(v___x_6476_);
if (v_isSharedCheck_6491_ == 0)
{
v___x_6479_ = v___x_6476_;
v_isShared_6480_ = v_isSharedCheck_6491_;
goto v_resetjp_6478_;
}
else
{
lean_inc(v_val_6477_);
lean_dec(v___x_6476_);
v___x_6479_ = lean_box(0);
v_isShared_6480_ = v_isSharedCheck_6491_;
goto v_resetjp_6478_;
}
v_resetjp_6478_:
{
lean_object* v_moduleUri_6481_; lean_object* v_refs_6482_; lean_object* v_decls_6483_; lean_object* v___x_6485_; 
v_moduleUri_6481_ = lean_ctor_get(v_val_6477_, 0);
lean_inc_ref(v_moduleUri_6481_);
v_refs_6482_ = lean_ctor_get(v_val_6477_, 3);
lean_inc(v_refs_6482_);
v_decls_6483_ = lean_ctor_get(v_val_6477_, 4);
lean_inc(v_decls_6483_);
lean_dec(v_val_6477_);
if (v_isShared_6474_ == 0)
{
lean_ctor_set(v___x_6473_, 1, v_decls_6483_);
lean_ctor_set(v___x_6473_, 0, v_refs_6482_);
v___x_6485_ = v___x_6473_;
goto v_reusejp_6484_;
}
else
{
lean_object* v_reuseFailAlloc_6490_; 
v_reuseFailAlloc_6490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6490_, 0, v_refs_6482_);
lean_ctor_set(v_reuseFailAlloc_6490_, 1, v_decls_6483_);
v___x_6485_ = v_reuseFailAlloc_6490_;
goto v_reusejp_6484_;
}
v_reusejp_6484_:
{
lean_object* v___x_6486_; lean_object* v___x_6488_; 
v___x_6486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6486_, 0, v_moduleUri_6481_);
lean_ctor_set(v___x_6486_, 1, v___x_6485_);
if (v_isShared_6480_ == 0)
{
lean_ctor_set(v___x_6479_, 0, v___x_6486_);
v___x_6488_ = v___x_6479_;
goto v_reusejp_6487_;
}
else
{
lean_object* v_reuseFailAlloc_6489_; 
v_reuseFailAlloc_6489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6489_, 0, v___x_6486_);
v___x_6488_ = v_reuseFailAlloc_6489_;
goto v_reusejp_6487_;
}
v_reusejp_6487_:
{
return v___x_6488_;
}
}
}
}
else
{
lean_object* v___x_6492_; 
lean_dec(v___x_6476_);
lean_del_object(v___x_6473_);
v___x_6492_ = lean_box(0);
return v___x_6492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6509_, lean_object* v_mod_6510_){
_start:
{
lean_object* v_res_6511_; 
v_res_6511_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6509_, v_mod_6510_);
lean_dec(v_mod_6510_);
return v_res_6511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6512_, lean_object* v_mod_6513_){
_start:
{
lean_object* v_ileans_6514_; lean_object* v_workers_6515_; lean_object* v___x_6528_; 
v_ileans_6514_ = lean_ctor_get(v_self_6512_, 0);
v_workers_6515_ = lean_ctor_get(v_self_6512_, 1);
v___x_6528_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6515_, v_mod_6513_);
if (lean_obj_tag(v___x_6528_) == 1)
{
lean_object* v_val_6529_; lean_object* v___x_6531_; uint8_t v_isShared_6532_; uint8_t v_isSharedCheck_6538_; 
v_val_6529_ = lean_ctor_get(v___x_6528_, 0);
v_isSharedCheck_6538_ = !lean_is_exclusive(v___x_6528_);
if (v_isSharedCheck_6538_ == 0)
{
v___x_6531_ = v___x_6528_;
v_isShared_6532_ = v_isSharedCheck_6538_;
goto v_resetjp_6530_;
}
else
{
lean_inc(v_val_6529_);
lean_dec(v___x_6528_);
v___x_6531_ = lean_box(0);
v_isShared_6532_ = v_isSharedCheck_6538_;
goto v_resetjp_6530_;
}
v_resetjp_6530_:
{
uint8_t v___x_6533_; 
v___x_6533_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6529_);
if (v___x_6533_ == 0)
{
lean_del_object(v___x_6531_);
lean_dec(v_val_6529_);
goto v___jp_6516_;
}
else
{
lean_object* v_directImports_6534_; lean_object* v___x_6536_; 
v_directImports_6534_ = lean_ctor_get(v_val_6529_, 2);
lean_inc_ref(v_directImports_6534_);
lean_dec(v_val_6529_);
if (v_isShared_6532_ == 0)
{
lean_ctor_set(v___x_6531_, 0, v_directImports_6534_);
v___x_6536_ = v___x_6531_;
goto v_reusejp_6535_;
}
else
{
lean_object* v_reuseFailAlloc_6537_; 
v_reuseFailAlloc_6537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6537_, 0, v_directImports_6534_);
v___x_6536_ = v_reuseFailAlloc_6537_;
goto v_reusejp_6535_;
}
v_reusejp_6535_:
{
return v___x_6536_;
}
}
}
}
else
{
lean_dec(v___x_6528_);
goto v___jp_6516_;
}
v___jp_6516_:
{
lean_object* v___x_6517_; 
v___x_6517_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6514_, v_mod_6513_);
if (lean_obj_tag(v___x_6517_) == 1)
{
lean_object* v_val_6518_; lean_object* v___x_6520_; uint8_t v_isShared_6521_; uint8_t v_isSharedCheck_6526_; 
v_val_6518_ = lean_ctor_get(v___x_6517_, 0);
v_isSharedCheck_6526_ = !lean_is_exclusive(v___x_6517_);
if (v_isSharedCheck_6526_ == 0)
{
v___x_6520_ = v___x_6517_;
v_isShared_6521_ = v_isSharedCheck_6526_;
goto v_resetjp_6519_;
}
else
{
lean_inc(v_val_6518_);
lean_dec(v___x_6517_);
v___x_6520_ = lean_box(0);
v_isShared_6521_ = v_isSharedCheck_6526_;
goto v_resetjp_6519_;
}
v_resetjp_6519_:
{
lean_object* v_directImports_6522_; lean_object* v___x_6524_; 
v_directImports_6522_ = lean_ctor_get(v_val_6518_, 2);
lean_inc_ref(v_directImports_6522_);
lean_dec(v_val_6518_);
if (v_isShared_6521_ == 0)
{
lean_ctor_set(v___x_6520_, 0, v_directImports_6522_);
v___x_6524_ = v___x_6520_;
goto v_reusejp_6523_;
}
else
{
lean_object* v_reuseFailAlloc_6525_; 
v_reuseFailAlloc_6525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6525_, 0, v_directImports_6522_);
v___x_6524_ = v_reuseFailAlloc_6525_;
goto v_reusejp_6523_;
}
v_reusejp_6523_:
{
return v___x_6524_;
}
}
}
else
{
lean_object* v___x_6527_; 
lean_dec(v___x_6517_);
v___x_6527_ = lean_box(0);
return v___x_6527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6539_, lean_object* v_mod_6540_){
_start:
{
lean_object* v_res_6541_; 
v_res_6541_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6539_, v_mod_6540_);
lean_dec(v_mod_6540_);
lean_dec_ref(v_self_6539_);
return v_res_6541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6542_, lean_object* v_mod_6543_){
_start:
{
lean_object* v_ileans_6544_; lean_object* v_workers_6545_; lean_object* v___x_6558_; 
v_ileans_6544_ = lean_ctor_get(v_self_6542_, 0);
v_workers_6545_ = lean_ctor_get(v_self_6542_, 1);
v___x_6558_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6545_, v_mod_6543_);
if (lean_obj_tag(v___x_6558_) == 1)
{
lean_object* v_val_6559_; lean_object* v___x_6561_; uint8_t v_isShared_6562_; uint8_t v_isSharedCheck_6568_; 
v_val_6559_ = lean_ctor_get(v___x_6558_, 0);
v_isSharedCheck_6568_ = !lean_is_exclusive(v___x_6558_);
if (v_isSharedCheck_6568_ == 0)
{
v___x_6561_ = v___x_6558_;
v_isShared_6562_ = v_isSharedCheck_6568_;
goto v_resetjp_6560_;
}
else
{
lean_inc(v_val_6559_);
lean_dec(v___x_6558_);
v___x_6561_ = lean_box(0);
v_isShared_6562_ = v_isSharedCheck_6568_;
goto v_resetjp_6560_;
}
v_resetjp_6560_:
{
uint8_t v___x_6563_; 
v___x_6563_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6559_);
if (v___x_6563_ == 0)
{
lean_del_object(v___x_6561_);
lean_dec(v_val_6559_);
goto v___jp_6546_;
}
else
{
lean_object* v_decls_6564_; lean_object* v___x_6566_; 
v_decls_6564_ = lean_ctor_get(v_val_6559_, 5);
lean_inc(v_decls_6564_);
lean_dec(v_val_6559_);
if (v_isShared_6562_ == 0)
{
lean_ctor_set(v___x_6561_, 0, v_decls_6564_);
v___x_6566_ = v___x_6561_;
goto v_reusejp_6565_;
}
else
{
lean_object* v_reuseFailAlloc_6567_; 
v_reuseFailAlloc_6567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6567_, 0, v_decls_6564_);
v___x_6566_ = v_reuseFailAlloc_6567_;
goto v_reusejp_6565_;
}
v_reusejp_6565_:
{
return v___x_6566_;
}
}
}
}
else
{
lean_dec(v___x_6558_);
goto v___jp_6546_;
}
v___jp_6546_:
{
lean_object* v___x_6547_; 
v___x_6547_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6544_, v_mod_6543_);
if (lean_obj_tag(v___x_6547_) == 1)
{
lean_object* v_val_6548_; lean_object* v___x_6550_; uint8_t v_isShared_6551_; uint8_t v_isSharedCheck_6556_; 
v_val_6548_ = lean_ctor_get(v___x_6547_, 0);
v_isSharedCheck_6556_ = !lean_is_exclusive(v___x_6547_);
if (v_isSharedCheck_6556_ == 0)
{
v___x_6550_ = v___x_6547_;
v_isShared_6551_ = v_isSharedCheck_6556_;
goto v_resetjp_6549_;
}
else
{
lean_inc(v_val_6548_);
lean_dec(v___x_6547_);
v___x_6550_ = lean_box(0);
v_isShared_6551_ = v_isSharedCheck_6556_;
goto v_resetjp_6549_;
}
v_resetjp_6549_:
{
lean_object* v_decls_6552_; lean_object* v___x_6554_; 
v_decls_6552_ = lean_ctor_get(v_val_6548_, 4);
lean_inc(v_decls_6552_);
lean_dec(v_val_6548_);
if (v_isShared_6551_ == 0)
{
lean_ctor_set(v___x_6550_, 0, v_decls_6552_);
v___x_6554_ = v___x_6550_;
goto v_reusejp_6553_;
}
else
{
lean_object* v_reuseFailAlloc_6555_; 
v_reuseFailAlloc_6555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6555_, 0, v_decls_6552_);
v___x_6554_ = v_reuseFailAlloc_6555_;
goto v_reusejp_6553_;
}
v_reusejp_6553_:
{
return v___x_6554_;
}
}
}
else
{
lean_object* v___x_6557_; 
lean_dec(v___x_6547_);
v___x_6557_ = lean_box(0);
return v___x_6557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6569_, lean_object* v_mod_6570_){
_start:
{
lean_object* v_res_6571_; 
v_res_6571_ = l_Lean_Server_References_getDecls_x3f(v_self_6569_, v_mod_6570_);
lean_dec(v_mod_6570_);
lean_dec_ref(v_self_6569_);
return v_res_6571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6572_, lean_object* v_x_6573_){
_start:
{
if (lean_obj_tag(v_x_6573_) == 0)
{
lean_object* v_k_6574_; lean_object* v_v_6575_; lean_object* v_l_6576_; lean_object* v_r_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; 
v_k_6574_ = lean_ctor_get(v_x_6573_, 1);
v_v_6575_ = lean_ctor_get(v_x_6573_, 2);
v_l_6576_ = lean_ctor_get(v_x_6573_, 3);
v_r_6577_ = lean_ctor_get(v_x_6573_, 4);
v___x_6578_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6572_, v_l_6576_);
lean_inc(v_v_6575_);
lean_inc(v_k_6574_);
v___x_6579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6579_, 0, v_k_6574_);
lean_ctor_set(v___x_6579_, 1, v_v_6575_);
v___x_6580_ = lean_array_push(v___x_6578_, v___x_6579_);
v_init_6572_ = v___x_6580_;
v_x_6573_ = v_r_6577_;
goto _start;
}
else
{
return v_init_6572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6582_, lean_object* v_x_6583_){
_start:
{
lean_object* v_res_6584_; 
v_res_6584_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6582_, v_x_6583_);
lean_dec(v_x_6583_);
return v_res_6584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6585_, lean_object* v_k_6586_){
_start:
{
if (lean_obj_tag(v_t_6585_) == 0)
{
lean_object* v_k_6587_; lean_object* v_v_6588_; lean_object* v_l_6589_; lean_object* v_r_6590_; uint8_t v___x_6591_; 
v_k_6587_ = lean_ctor_get(v_t_6585_, 1);
v_v_6588_ = lean_ctor_get(v_t_6585_, 2);
v_l_6589_ = lean_ctor_get(v_t_6585_, 3);
v_r_6590_ = lean_ctor_get(v_t_6585_, 4);
v___x_6591_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6586_, v_k_6587_);
switch(v___x_6591_)
{
case 0:
{
v_t_6585_ = v_l_6589_;
goto _start;
}
case 1:
{
lean_object* v___x_6593_; 
lean_inc(v_v_6588_);
v___x_6593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6593_, 0, v_v_6588_);
return v___x_6593_;
}
default: 
{
v_t_6585_ = v_r_6590_;
goto _start;
}
}
}
else
{
lean_object* v___x_6595_; 
v___x_6595_ = lean_box(0);
return v___x_6595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6596_, lean_object* v_k_6597_){
_start:
{
lean_object* v_res_6598_; 
v_res_6598_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6596_, v_k_6597_);
lean_dec_ref(v_k_6597_);
lean_dec(v_t_6596_);
return v_res_6598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6599_, lean_object* v_as_6600_, size_t v_sz_6601_, size_t v_i_6602_, lean_object* v_b_6603_){
_start:
{
lean_object* v_a_6605_; uint8_t v___x_6609_; 
v___x_6609_ = lean_usize_dec_lt(v_i_6602_, v_sz_6601_);
if (v___x_6609_ == 0)
{
return v_b_6603_;
}
else
{
lean_object* v_a_6610_; lean_object* v_snd_6611_; lean_object* v_snd_6612_; lean_object* v_fst_6613_; lean_object* v___x_6615_; uint8_t v_isShared_6616_; uint8_t v_isSharedCheck_6641_; 
v_a_6610_ = lean_array_uget(v_as_6600_, v_i_6602_);
v_snd_6611_ = lean_ctor_get(v_a_6610_, 1);
lean_inc(v_snd_6611_);
v_snd_6612_ = lean_ctor_get(v_snd_6611_, 1);
lean_inc(v_snd_6612_);
v_fst_6613_ = lean_ctor_get(v_a_6610_, 0);
v_isSharedCheck_6641_ = !lean_is_exclusive(v_a_6610_);
if (v_isSharedCheck_6641_ == 0)
{
lean_object* v_unused_6642_; 
v_unused_6642_ = lean_ctor_get(v_a_6610_, 1);
lean_dec(v_unused_6642_);
v___x_6615_ = v_a_6610_;
v_isShared_6616_ = v_isSharedCheck_6641_;
goto v_resetjp_6614_;
}
else
{
lean_inc(v_fst_6613_);
lean_dec(v_a_6610_);
v___x_6615_ = lean_box(0);
v_isShared_6616_ = v_isSharedCheck_6641_;
goto v_resetjp_6614_;
}
v_resetjp_6614_:
{
lean_object* v_fst_6617_; lean_object* v___x_6619_; uint8_t v_isShared_6620_; uint8_t v_isSharedCheck_6639_; 
v_fst_6617_ = lean_ctor_get(v_snd_6611_, 0);
v_isSharedCheck_6639_ = !lean_is_exclusive(v_snd_6611_);
if (v_isSharedCheck_6639_ == 0)
{
lean_object* v_unused_6640_; 
v_unused_6640_ = lean_ctor_get(v_snd_6611_, 1);
lean_dec(v_unused_6640_);
v___x_6619_ = v_snd_6611_;
v_isShared_6620_ = v_isSharedCheck_6639_;
goto v_resetjp_6618_;
}
else
{
lean_inc(v_fst_6617_);
lean_dec(v_snd_6611_);
v___x_6619_ = lean_box(0);
v_isShared_6620_ = v_isSharedCheck_6639_;
goto v_resetjp_6618_;
}
v_resetjp_6618_:
{
lean_object* v_fst_6621_; lean_object* v_snd_6622_; lean_object* v___x_6624_; uint8_t v_isShared_6625_; uint8_t v_isSharedCheck_6638_; 
v_fst_6621_ = lean_ctor_get(v_snd_6612_, 0);
v_snd_6622_ = lean_ctor_get(v_snd_6612_, 1);
v_isSharedCheck_6638_ = !lean_is_exclusive(v_snd_6612_);
if (v_isSharedCheck_6638_ == 0)
{
v___x_6624_ = v_snd_6612_;
v_isShared_6625_ = v_isSharedCheck_6638_;
goto v_resetjp_6623_;
}
else
{
lean_inc(v_snd_6622_);
lean_inc(v_fst_6621_);
lean_dec(v_snd_6612_);
v___x_6624_ = lean_box(0);
v_isShared_6625_ = v_isSharedCheck_6638_;
goto v_resetjp_6623_;
}
v_resetjp_6623_:
{
lean_object* v___x_6626_; 
v___x_6626_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6621_, v_ident_6599_);
lean_dec(v_fst_6621_);
if (lean_obj_tag(v___x_6626_) == 1)
{
lean_object* v_val_6627_; lean_object* v___x_6629_; 
v_val_6627_ = lean_ctor_get(v___x_6626_, 0);
lean_inc(v_val_6627_);
lean_dec_ref(v___x_6626_);
if (v_isShared_6625_ == 0)
{
lean_ctor_set(v___x_6624_, 0, v_val_6627_);
v___x_6629_ = v___x_6624_;
goto v_reusejp_6628_;
}
else
{
lean_object* v_reuseFailAlloc_6637_; 
v_reuseFailAlloc_6637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6637_, 0, v_val_6627_);
lean_ctor_set(v_reuseFailAlloc_6637_, 1, v_snd_6622_);
v___x_6629_ = v_reuseFailAlloc_6637_;
goto v_reusejp_6628_;
}
v_reusejp_6628_:
{
lean_object* v___x_6631_; 
if (v_isShared_6620_ == 0)
{
lean_ctor_set(v___x_6619_, 1, v___x_6629_);
lean_ctor_set(v___x_6619_, 0, v_fst_6613_);
v___x_6631_ = v___x_6619_;
goto v_reusejp_6630_;
}
else
{
lean_object* v_reuseFailAlloc_6636_; 
v_reuseFailAlloc_6636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6636_, 0, v_fst_6613_);
lean_ctor_set(v_reuseFailAlloc_6636_, 1, v___x_6629_);
v___x_6631_ = v_reuseFailAlloc_6636_;
goto v_reusejp_6630_;
}
v_reusejp_6630_:
{
lean_object* v___x_6633_; 
if (v_isShared_6616_ == 0)
{
lean_ctor_set(v___x_6615_, 1, v___x_6631_);
lean_ctor_set(v___x_6615_, 0, v_fst_6617_);
v___x_6633_ = v___x_6615_;
goto v_reusejp_6632_;
}
else
{
lean_object* v_reuseFailAlloc_6635_; 
v_reuseFailAlloc_6635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6635_, 0, v_fst_6617_);
lean_ctor_set(v_reuseFailAlloc_6635_, 1, v___x_6631_);
v___x_6633_ = v_reuseFailAlloc_6635_;
goto v_reusejp_6632_;
}
v_reusejp_6632_:
{
lean_object* v___x_6634_; 
v___x_6634_ = lean_array_push(v_b_6603_, v___x_6633_);
v_a_6605_ = v___x_6634_;
goto v___jp_6604_;
}
}
}
}
else
{
lean_dec(v___x_6626_);
lean_del_object(v___x_6624_);
lean_dec(v_snd_6622_);
lean_del_object(v___x_6619_);
lean_dec(v_fst_6617_);
lean_del_object(v___x_6615_);
lean_dec(v_fst_6613_);
v_a_6605_ = v_b_6603_;
goto v___jp_6604_;
}
}
}
}
}
v___jp_6604_:
{
size_t v___x_6606_; size_t v___x_6607_; 
v___x_6606_ = ((size_t)1ULL);
v___x_6607_ = lean_usize_add(v_i_6602_, v___x_6606_);
v_i_6602_ = v___x_6607_;
v_b_6603_ = v_a_6605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6643_, lean_object* v_as_6644_, lean_object* v_sz_6645_, lean_object* v_i_6646_, lean_object* v_b_6647_){
_start:
{
size_t v_sz_boxed_6648_; size_t v_i_boxed_6649_; lean_object* v_res_6650_; 
v_sz_boxed_6648_ = lean_unbox_usize(v_sz_6645_);
lean_dec(v_sz_6645_);
v_i_boxed_6649_ = lean_unbox_usize(v_i_6646_);
lean_dec(v_i_6646_);
v_res_6650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6643_, v_as_6644_, v_sz_boxed_6648_, v_i_boxed_6649_, v_b_6647_);
lean_dec_ref(v_as_6644_);
lean_dec_ref(v_ident_6643_);
return v_res_6650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6657_, lean_object* v_ident_6658_){
_start:
{
lean_object* v___y_6660_; 
if (lean_obj_tag(v_ident_6658_) == 0)
{
lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; 
v___x_6665_ = l_Lean_Server_References_allRefs(v_self_6657_);
v___x_6666_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6667_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6666_, v___x_6665_);
lean_dec(v___x_6665_);
v___y_6660_ = v___x_6667_;
goto v___jp_6659_;
}
else
{
lean_object* v_moduleName_6668_; lean_object* v_identModuleName_6669_; lean_object* v___x_6670_; 
v_moduleName_6668_ = lean_ctor_get(v_ident_6658_, 0);
lean_inc_ref(v_moduleName_6668_);
v_identModuleName_6669_ = l_String_toName(v_moduleName_6668_);
v___x_6670_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6657_, v_identModuleName_6669_);
if (lean_obj_tag(v___x_6670_) == 0)
{
lean_object* v___x_6671_; 
lean_dec(v_identModuleName_6669_);
v___x_6671_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6660_ = v___x_6671_;
goto v___jp_6659_;
}
else
{
lean_object* v_val_6672_; lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; 
v_val_6672_ = lean_ctor_get(v___x_6670_, 0);
lean_inc(v_val_6672_);
lean_dec_ref(v___x_6670_);
v___x_6673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6673_, 0, v_identModuleName_6669_);
lean_ctor_set(v___x_6673_, 1, v_val_6672_);
v___x_6674_ = lean_unsigned_to_nat(1u);
v___x_6675_ = lean_mk_empty_array_with_capacity(v___x_6674_);
v___x_6676_ = lean_array_push(v___x_6675_, v___x_6673_);
v___y_6660_ = v___x_6676_;
goto v___jp_6659_;
}
}
v___jp_6659_:
{
lean_object* v_result_6661_; size_t v_sz_6662_; size_t v___x_6663_; lean_object* v___x_6664_; 
v_result_6661_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6662_ = lean_array_size(v___y_6660_);
v___x_6663_ = ((size_t)0ULL);
v___x_6664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6658_, v___y_6660_, v_sz_6662_, v___x_6663_, v_result_6661_);
lean_dec_ref(v___y_6660_);
lean_dec_ref(v_ident_6658_);
return v___x_6664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6677_, lean_object* v_t_6678_, lean_object* v_k_6679_){
_start:
{
lean_object* v___x_6680_; 
v___x_6680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6678_, v_k_6679_);
return v___x_6680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6681_, lean_object* v_t_6682_, lean_object* v_k_6683_){
_start:
{
lean_object* v_res_6684_; 
v_res_6684_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6681_, v_t_6682_, v_k_6683_);
lean_dec_ref(v_k_6683_);
lean_dec(v_t_6682_);
return v_res_6684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6685_, lean_object* v_t_6686_){
_start:
{
lean_object* v___x_6687_; 
v___x_6687_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6685_, v_t_6686_);
return v___x_6687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6688_, lean_object* v_t_6689_){
_start:
{
lean_object* v_res_6690_; 
v_res_6690_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6688_, v_t_6689_);
lean_dec(v_t_6689_);
return v_res_6690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6691_, lean_object* v_module_6692_, lean_object* v_pos_6693_, uint8_t v_includeStop_6694_){
_start:
{
lean_object* v___x_6695_; 
v___x_6695_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6691_, v_module_6692_);
if (lean_obj_tag(v___x_6695_) == 1)
{
lean_object* v_val_6696_; lean_object* v_snd_6697_; lean_object* v_fst_6698_; lean_object* v___x_6699_; 
v_val_6696_ = lean_ctor_get(v___x_6695_, 0);
lean_inc(v_val_6696_);
lean_dec_ref(v___x_6695_);
v_snd_6697_ = lean_ctor_get(v_val_6696_, 1);
lean_inc(v_snd_6697_);
lean_dec(v_val_6696_);
v_fst_6698_ = lean_ctor_get(v_snd_6697_, 0);
lean_inc(v_fst_6698_);
lean_dec(v_snd_6697_);
v___x_6699_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6698_, v_pos_6693_, v_includeStop_6694_);
return v___x_6699_;
}
else
{
lean_object* v___x_6700_; 
lean_dec(v___x_6695_);
v___x_6700_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6701_, lean_object* v_module_6702_, lean_object* v_pos_6703_, lean_object* v_includeStop_6704_){
_start:
{
uint8_t v_includeStop_boxed_6705_; lean_object* v_res_6706_; 
v_includeStop_boxed_6705_ = lean_unbox(v_includeStop_6704_);
v_res_6706_ = l_Lean_Server_References_findAt(v_self_6701_, v_module_6702_, v_pos_6703_, v_includeStop_boxed_6705_);
lean_dec_ref(v_pos_6703_);
lean_dec(v_module_6702_);
return v_res_6706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6707_, lean_object* v_module_6708_, lean_object* v_pos_6709_, uint8_t v_includeStop_6710_){
_start:
{
lean_object* v___x_6711_; 
v___x_6711_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6707_, v_module_6708_);
if (lean_obj_tag(v___x_6711_) == 0)
{
lean_object* v___x_6712_; 
v___x_6712_ = lean_box(0);
return v___x_6712_;
}
else
{
lean_object* v_val_6713_; lean_object* v_snd_6714_; lean_object* v_fst_6715_; lean_object* v___x_6716_; 
v_val_6713_ = lean_ctor_get(v___x_6711_, 0);
lean_inc(v_val_6713_);
lean_dec_ref(v___x_6711_);
v_snd_6714_ = lean_ctor_get(v_val_6713_, 1);
lean_inc(v_snd_6714_);
lean_dec(v_val_6713_);
v_fst_6715_ = lean_ctor_get(v_snd_6714_, 0);
lean_inc(v_fst_6715_);
lean_dec(v_snd_6714_);
v___x_6716_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6715_, v_pos_6709_, v_includeStop_6710_);
lean_dec(v_fst_6715_);
return v___x_6716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6717_, lean_object* v_module_6718_, lean_object* v_pos_6719_, lean_object* v_includeStop_6720_){
_start:
{
uint8_t v_includeStop_boxed_6721_; lean_object* v_res_6722_; 
v_includeStop_boxed_6721_ = lean_unbox(v_includeStop_6720_);
v_res_6722_ = l_Lean_Server_References_findRange_x3f(v_self_6717_, v_module_6718_, v_pos_6719_, v_includeStop_boxed_6721_);
lean_dec_ref(v_pos_6719_);
lean_dec(v_module_6718_);
return v_res_6722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6723_, lean_object* v_k_6724_){
_start:
{
if (lean_obj_tag(v_t_6723_) == 0)
{
lean_object* v_k_6725_; lean_object* v_v_6726_; lean_object* v_l_6727_; lean_object* v_r_6728_; uint8_t v___x_6729_; 
v_k_6725_ = lean_ctor_get(v_t_6723_, 1);
v_v_6726_ = lean_ctor_get(v_t_6723_, 2);
v_l_6727_ = lean_ctor_get(v_t_6723_, 3);
v_r_6728_ = lean_ctor_get(v_t_6723_, 4);
v___x_6729_ = lean_string_dec_lt(v_k_6724_, v_k_6725_);
if (v___x_6729_ == 0)
{
uint8_t v___x_6730_; 
v___x_6730_ = lean_string_dec_eq(v_k_6724_, v_k_6725_);
if (v___x_6730_ == 0)
{
v_t_6723_ = v_r_6728_;
goto _start;
}
else
{
lean_object* v___x_6732_; 
lean_inc(v_v_6726_);
v___x_6732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6732_, 0, v_v_6726_);
return v___x_6732_;
}
}
else
{
v_t_6723_ = v_l_6727_;
goto _start;
}
}
else
{
lean_object* v___x_6734_; 
v___x_6734_ = lean_box(0);
return v___x_6734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6735_, lean_object* v_k_6736_){
_start:
{
lean_object* v_res_6737_; 
v_res_6737_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6735_, v_k_6736_);
lean_dec_ref(v_k_6736_);
lean_dec(v_t_6735_);
return v_res_6737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6738_, lean_object* v_name_6739_){
_start:
{
lean_object* v___x_6740_; 
v___x_6740_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6738_, v_name_6739_);
if (lean_obj_tag(v___x_6740_) == 0)
{
lean_object* v___x_6741_; 
lean_dec_ref(v_name_6739_);
v___x_6741_ = lean_box(0);
return v___x_6741_;
}
else
{
lean_object* v_val_6742_; lean_object* v___x_6744_; uint8_t v_isShared_6745_; uint8_t v_isSharedCheck_6752_; 
v_val_6742_ = lean_ctor_get(v___x_6740_, 0);
v_isSharedCheck_6752_ = !lean_is_exclusive(v___x_6740_);
if (v_isSharedCheck_6752_ == 0)
{
v___x_6744_ = v___x_6740_;
v_isShared_6745_ = v_isSharedCheck_6752_;
goto v_resetjp_6743_;
}
else
{
lean_inc(v_val_6742_);
lean_dec(v___x_6740_);
v___x_6744_ = lean_box(0);
v_isShared_6745_ = v_isSharedCheck_6752_;
goto v_resetjp_6743_;
}
v_resetjp_6743_:
{
lean_object* v___x_6746_; lean_object* v___x_6747_; lean_object* v___x_6748_; lean_object* v___x_6750_; 
v___x_6746_ = l_Lean_Lsp_DeclInfo_range(v_val_6742_);
v___x_6747_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6742_);
lean_dec(v_val_6742_);
v___x_6748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6748_, 0, v_name_6739_);
lean_ctor_set(v___x_6748_, 1, v___x_6746_);
lean_ctor_set(v___x_6748_, 2, v___x_6747_);
if (v_isShared_6745_ == 0)
{
lean_ctor_set(v___x_6744_, 0, v___x_6748_);
v___x_6750_ = v___x_6744_;
goto v_reusejp_6749_;
}
else
{
lean_object* v_reuseFailAlloc_6751_; 
v_reuseFailAlloc_6751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6751_, 0, v___x_6748_);
v___x_6750_ = v_reuseFailAlloc_6751_;
goto v_reusejp_6749_;
}
v_reusejp_6749_:
{
return v___x_6750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6753_, lean_object* v_name_6754_){
_start:
{
lean_object* v_res_6755_; 
v_res_6755_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6753_, v_name_6754_);
lean_dec(v_ds_6753_);
return v_res_6755_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6756_, lean_object* v_t_6757_, lean_object* v_k_6758_){
_start:
{
lean_object* v___x_6759_; 
v___x_6759_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6757_, v_k_6758_);
return v___x_6759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6760_, lean_object* v_t_6761_, lean_object* v_k_6762_){
_start:
{
lean_object* v_res_6763_; 
v_res_6763_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6760_, v_t_6761_, v_k_6762_);
lean_dec_ref(v_k_6762_);
lean_dec(v_t_6761_);
return v_res_6763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6764_, lean_object* v_fst_6765_, lean_object* v_snd_6766_, lean_object* v_as_6767_, size_t v_sz_6768_, size_t v_i_6769_, lean_object* v_b_6770_){
_start:
{
uint8_t v___x_6771_; 
v___x_6771_ = lean_usize_dec_lt(v_i_6769_, v_sz_6768_);
if (v___x_6771_ == 0)
{
lean_dec(v_fst_6765_);
lean_dec_ref(v_fst_6764_);
return v_b_6770_;
}
else
{
lean_object* v_a_6772_; lean_object* v___y_6774_; lean_object* v___x_6782_; 
v_a_6772_ = lean_array_uget_borrowed(v_as_6767_, v_i_6769_);
v___x_6782_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6772_);
if (lean_obj_tag(v___x_6782_) == 0)
{
lean_object* v___x_6783_; 
v___x_6783_ = lean_box(0);
v___y_6774_ = v___x_6783_;
goto v___jp_6773_;
}
else
{
lean_object* v_val_6784_; lean_object* v___x_6785_; 
v_val_6784_ = lean_ctor_get(v___x_6782_, 0);
lean_inc(v_val_6784_);
lean_dec_ref(v___x_6782_);
v___x_6785_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6766_, v_val_6784_);
v___y_6774_ = v___x_6785_;
goto v___jp_6773_;
}
v___jp_6773_:
{
lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; size_t v___x_6779_; size_t v___x_6780_; 
v___x_6775_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6772_);
lean_inc_ref(v_fst_6764_);
v___x_6776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6776_, 0, v_fst_6764_);
lean_ctor_set(v___x_6776_, 1, v___x_6775_);
lean_inc(v_fst_6765_);
v___x_6777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6777_, 0, v___x_6776_);
lean_ctor_set(v___x_6777_, 1, v_fst_6765_);
lean_ctor_set(v___x_6777_, 2, v___y_6774_);
v___x_6778_ = lean_array_push(v_b_6770_, v___x_6777_);
v___x_6779_ = ((size_t)1ULL);
v___x_6780_ = lean_usize_add(v_i_6769_, v___x_6779_);
v_i_6769_ = v___x_6780_;
v_b_6770_ = v___x_6778_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6786_, lean_object* v_fst_6787_, lean_object* v_snd_6788_, lean_object* v_as_6789_, lean_object* v_sz_6790_, lean_object* v_i_6791_, lean_object* v_b_6792_){
_start:
{
size_t v_sz_boxed_6793_; size_t v_i_boxed_6794_; lean_object* v_res_6795_; 
v_sz_boxed_6793_ = lean_unbox_usize(v_sz_6790_);
lean_dec(v_sz_6790_);
v_i_boxed_6794_ = lean_unbox_usize(v_i_6791_);
lean_dec(v_i_6791_);
v_res_6795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6786_, v_fst_6787_, v_snd_6788_, v_as_6789_, v_sz_boxed_6793_, v_i_boxed_6794_, v_b_6792_);
lean_dec_ref(v_as_6789_);
lean_dec(v_snd_6788_);
return v_res_6795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6796_, lean_object* v_as_6797_, size_t v_sz_6798_, size_t v_i_6799_, lean_object* v_b_6800_){
_start:
{
uint8_t v___x_6801_; 
v___x_6801_ = lean_usize_dec_lt(v_i_6799_, v_sz_6798_);
if (v___x_6801_ == 0)
{
return v_b_6800_;
}
else
{
lean_object* v_a_6802_; lean_object* v_snd_6803_; lean_object* v_snd_6804_; lean_object* v_fst_6805_; lean_object* v_fst_6806_; lean_object* v_fst_6807_; lean_object* v_snd_6808_; lean_object* v___x_6810_; uint8_t v_isShared_6811_; uint8_t v_isSharedCheck_6835_; 
v_a_6802_ = lean_array_uget_borrowed(v_as_6797_, v_i_6799_);
v_snd_6803_ = lean_ctor_get(v_a_6802_, 1);
v_snd_6804_ = lean_ctor_get(v_snd_6803_, 1);
lean_inc(v_snd_6804_);
v_fst_6805_ = lean_ctor_get(v_a_6802_, 0);
v_fst_6806_ = lean_ctor_get(v_snd_6803_, 0);
v_fst_6807_ = lean_ctor_get(v_snd_6804_, 0);
v_snd_6808_ = lean_ctor_get(v_snd_6804_, 1);
v_isSharedCheck_6835_ = !lean_is_exclusive(v_snd_6804_);
if (v_isSharedCheck_6835_ == 0)
{
v___x_6810_ = v_snd_6804_;
v_isShared_6811_ = v_isSharedCheck_6835_;
goto v_resetjp_6809_;
}
else
{
lean_inc(v_snd_6808_);
lean_inc(v_fst_6807_);
lean_dec(v_snd_6804_);
v___x_6810_ = lean_box(0);
v_isShared_6811_ = v_isSharedCheck_6835_;
goto v_resetjp_6809_;
}
v_resetjp_6809_:
{
lean_object* v_result_6813_; 
if (v_includeDefinition_6796_ == 0)
{
lean_del_object(v___x_6810_);
v_result_6813_ = v_b_6800_;
goto v___jp_6812_;
}
else
{
lean_object* v_definition_x3f_6821_; 
v_definition_x3f_6821_ = lean_ctor_get(v_fst_6807_, 0);
if (lean_obj_tag(v_definition_x3f_6821_) == 1)
{
lean_object* v_val_6822_; lean_object* v___y_6824_; lean_object* v___x_6831_; 
v_val_6822_ = lean_ctor_get(v_definition_x3f_6821_, 0);
v___x_6831_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6822_);
if (lean_obj_tag(v___x_6831_) == 0)
{
lean_object* v___x_6832_; 
v___x_6832_ = lean_box(0);
v___y_6824_ = v___x_6832_;
goto v___jp_6823_;
}
else
{
lean_object* v_val_6833_; lean_object* v___x_6834_; 
v_val_6833_ = lean_ctor_get(v___x_6831_, 0);
lean_inc(v_val_6833_);
lean_dec_ref(v___x_6831_);
v___x_6834_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6808_, v_val_6833_);
v___y_6824_ = v___x_6834_;
goto v___jp_6823_;
}
v___jp_6823_:
{
lean_object* v___x_6825_; lean_object* v___x_6827_; 
v___x_6825_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6822_);
lean_inc(v_fst_6805_);
if (v_isShared_6811_ == 0)
{
lean_ctor_set(v___x_6810_, 1, v___x_6825_);
lean_ctor_set(v___x_6810_, 0, v_fst_6805_);
v___x_6827_ = v___x_6810_;
goto v_reusejp_6826_;
}
else
{
lean_object* v_reuseFailAlloc_6830_; 
v_reuseFailAlloc_6830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6830_, 0, v_fst_6805_);
lean_ctor_set(v_reuseFailAlloc_6830_, 1, v___x_6825_);
v___x_6827_ = v_reuseFailAlloc_6830_;
goto v_reusejp_6826_;
}
v_reusejp_6826_:
{
lean_object* v___x_6828_; lean_object* v___x_6829_; 
lean_inc(v_fst_6806_);
v___x_6828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6828_, 0, v___x_6827_);
lean_ctor_set(v___x_6828_, 1, v_fst_6806_);
lean_ctor_set(v___x_6828_, 2, v___y_6824_);
v___x_6829_ = lean_array_push(v_b_6800_, v___x_6828_);
v_result_6813_ = v___x_6829_;
goto v___jp_6812_;
}
}
}
else
{
lean_del_object(v___x_6810_);
v_result_6813_ = v_b_6800_;
goto v___jp_6812_;
}
}
v___jp_6812_:
{
lean_object* v_usages_6814_; size_t v_sz_6815_; size_t v___x_6816_; lean_object* v___x_6817_; size_t v___x_6818_; size_t v___x_6819_; 
v_usages_6814_ = lean_ctor_get(v_fst_6807_, 1);
lean_inc_ref(v_usages_6814_);
lean_dec(v_fst_6807_);
v_sz_6815_ = lean_array_size(v_usages_6814_);
v___x_6816_ = ((size_t)0ULL);
lean_inc(v_fst_6806_);
lean_inc(v_fst_6805_);
v___x_6817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6805_, v_fst_6806_, v_snd_6808_, v_usages_6814_, v_sz_6815_, v___x_6816_, v_result_6813_);
lean_dec_ref(v_usages_6814_);
lean_dec(v_snd_6808_);
v___x_6818_ = ((size_t)1ULL);
v___x_6819_ = lean_usize_add(v_i_6799_, v___x_6818_);
v_i_6799_ = v___x_6819_;
v_b_6800_ = v___x_6817_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6836_, lean_object* v_as_6837_, lean_object* v_sz_6838_, lean_object* v_i_6839_, lean_object* v_b_6840_){
_start:
{
uint8_t v_includeDefinition_boxed_6841_; size_t v_sz_boxed_6842_; size_t v_i_boxed_6843_; lean_object* v_res_6844_; 
v_includeDefinition_boxed_6841_ = lean_unbox(v_includeDefinition_6836_);
v_sz_boxed_6842_ = lean_unbox_usize(v_sz_6838_);
lean_dec(v_sz_6838_);
v_i_boxed_6843_ = lean_unbox_usize(v_i_6839_);
lean_dec(v_i_6839_);
v_res_6844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6841_, v_as_6837_, v_sz_boxed_6842_, v_i_boxed_6843_, v_b_6840_);
lean_dec_ref(v_as_6837_);
return v_res_6844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6847_, lean_object* v_ident_6848_, uint8_t v_includeDefinition_6849_){
_start:
{
lean_object* v_result_6850_; lean_object* v___x_6851_; size_t v_sz_6852_; size_t v___x_6853_; lean_object* v___x_6854_; 
v_result_6850_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6851_ = l_Lean_Server_References_allRefsFor(v_self_6847_, v_ident_6848_);
v_sz_6852_ = lean_array_size(v___x_6851_);
v___x_6853_ = ((size_t)0ULL);
v___x_6854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6849_, v___x_6851_, v_sz_6852_, v___x_6853_, v_result_6850_);
lean_dec_ref(v___x_6851_);
return v___x_6854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6855_, lean_object* v_ident_6856_, lean_object* v_includeDefinition_6857_){
_start:
{
uint8_t v_includeDefinition_boxed_6858_; lean_object* v_res_6859_; 
v_includeDefinition_boxed_6858_ = lean_unbox(v_includeDefinition_6857_);
v_res_6859_ = l_Lean_Server_References_referringTo(v_self_6855_, v_ident_6856_, v_includeDefinition_boxed_6858_);
return v_res_6859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6863_, size_t v_sz_6864_, size_t v_i_6865_, lean_object* v_b_6866_){
_start:
{
uint8_t v___x_6867_; 
v___x_6867_ = lean_usize_dec_lt(v_i_6865_, v_sz_6864_);
if (v___x_6867_ == 0)
{
lean_inc_ref(v_b_6866_);
return v_b_6866_;
}
else
{
lean_object* v_a_6868_; lean_object* v_snd_6869_; lean_object* v_snd_6870_; lean_object* v_fst_6871_; lean_object* v_fst_6872_; lean_object* v_fst_6873_; lean_object* v_snd_6874_; lean_object* v___x_6876_; uint8_t v_isShared_6877_; uint8_t v_isSharedCheck_6912_; 
v_a_6868_ = lean_array_uget_borrowed(v_as_6863_, v_i_6865_);
v_snd_6869_ = lean_ctor_get(v_a_6868_, 1);
v_snd_6870_ = lean_ctor_get(v_snd_6869_, 1);
lean_inc(v_snd_6870_);
v_fst_6871_ = lean_ctor_get(v_snd_6870_, 0);
lean_inc(v_fst_6871_);
v_fst_6872_ = lean_ctor_get(v_a_6868_, 0);
v_fst_6873_ = lean_ctor_get(v_snd_6869_, 0);
v_snd_6874_ = lean_ctor_get(v_snd_6870_, 1);
v_isSharedCheck_6912_ = !lean_is_exclusive(v_snd_6870_);
if (v_isSharedCheck_6912_ == 0)
{
lean_object* v_unused_6913_; 
v_unused_6913_ = lean_ctor_get(v_snd_6870_, 0);
lean_dec(v_unused_6913_);
v___x_6876_ = v_snd_6870_;
v_isShared_6877_ = v_isSharedCheck_6912_;
goto v_resetjp_6875_;
}
else
{
lean_inc(v_snd_6874_);
lean_dec(v_snd_6870_);
v___x_6876_ = lean_box(0);
v_isShared_6877_ = v_isSharedCheck_6912_;
goto v_resetjp_6875_;
}
v_resetjp_6875_:
{
lean_object* v_definition_x3f_6878_; lean_object* v___x_6880_; uint8_t v_isShared_6881_; uint8_t v_isSharedCheck_6910_; 
v_definition_x3f_6878_ = lean_ctor_get(v_fst_6871_, 0);
v_isSharedCheck_6910_ = !lean_is_exclusive(v_fst_6871_);
if (v_isSharedCheck_6910_ == 0)
{
lean_object* v_unused_6911_; 
v_unused_6911_ = lean_ctor_get(v_fst_6871_, 1);
lean_dec(v_unused_6911_);
v___x_6880_ = v_fst_6871_;
v_isShared_6881_ = v_isSharedCheck_6910_;
goto v_resetjp_6879_;
}
else
{
lean_inc(v_definition_x3f_6878_);
lean_dec(v_fst_6871_);
v___x_6880_ = lean_box(0);
v_isShared_6881_ = v_isSharedCheck_6910_;
goto v_resetjp_6879_;
}
v_resetjp_6879_:
{
lean_object* v___x_6882_; 
v___x_6882_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6878_) == 1)
{
lean_object* v_val_6883_; lean_object* v___x_6885_; uint8_t v_isShared_6886_; uint8_t v_isSharedCheck_6905_; 
v_val_6883_ = lean_ctor_get(v_definition_x3f_6878_, 0);
v_isSharedCheck_6905_ = !lean_is_exclusive(v_definition_x3f_6878_);
if (v_isSharedCheck_6905_ == 0)
{
v___x_6885_ = v_definition_x3f_6878_;
v_isShared_6886_ = v_isSharedCheck_6905_;
goto v_resetjp_6884_;
}
else
{
lean_inc(v_val_6883_);
lean_dec(v_definition_x3f_6878_);
v___x_6885_ = lean_box(0);
v_isShared_6886_ = v_isSharedCheck_6905_;
goto v_resetjp_6884_;
}
v_resetjp_6884_:
{
lean_object* v___y_6888_; lean_object* v___x_6901_; 
v___x_6901_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6883_);
if (lean_obj_tag(v___x_6901_) == 0)
{
lean_object* v___x_6902_; 
lean_dec(v_snd_6874_);
v___x_6902_ = lean_box(0);
v___y_6888_ = v___x_6902_;
goto v___jp_6887_;
}
else
{
lean_object* v_val_6903_; lean_object* v___x_6904_; 
v_val_6903_ = lean_ctor_get(v___x_6901_, 0);
lean_inc(v_val_6903_);
lean_dec_ref(v___x_6901_);
v___x_6904_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6874_, v_val_6903_);
lean_dec(v_snd_6874_);
v___y_6888_ = v___x_6904_;
goto v___jp_6887_;
}
v___jp_6887_:
{
lean_object* v___x_6889_; lean_object* v___x_6891_; 
v___x_6889_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6883_);
lean_dec(v_val_6883_);
lean_inc(v_fst_6872_);
if (v_isShared_6881_ == 0)
{
lean_ctor_set(v___x_6880_, 1, v___x_6889_);
lean_ctor_set(v___x_6880_, 0, v_fst_6872_);
v___x_6891_ = v___x_6880_;
goto v_reusejp_6890_;
}
else
{
lean_object* v_reuseFailAlloc_6900_; 
v_reuseFailAlloc_6900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6900_, 0, v_fst_6872_);
lean_ctor_set(v_reuseFailAlloc_6900_, 1, v___x_6889_);
v___x_6891_ = v_reuseFailAlloc_6900_;
goto v_reusejp_6890_;
}
v_reusejp_6890_:
{
lean_object* v___x_6892_; lean_object* v___x_6894_; 
lean_inc(v_fst_6873_);
v___x_6892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6892_, 0, v___x_6891_);
lean_ctor_set(v___x_6892_, 1, v_fst_6873_);
lean_ctor_set(v___x_6892_, 2, v___y_6888_);
if (v_isShared_6886_ == 0)
{
lean_ctor_set(v___x_6885_, 0, v___x_6892_);
v___x_6894_ = v___x_6885_;
goto v_reusejp_6893_;
}
else
{
lean_object* v_reuseFailAlloc_6899_; 
v_reuseFailAlloc_6899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6899_, 0, v___x_6892_);
v___x_6894_ = v_reuseFailAlloc_6899_;
goto v_reusejp_6893_;
}
v_reusejp_6893_:
{
lean_object* v___x_6895_; lean_object* v___x_6897_; 
v___x_6895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6895_, 0, v___x_6894_);
if (v_isShared_6877_ == 0)
{
lean_ctor_set(v___x_6876_, 1, v___x_6882_);
lean_ctor_set(v___x_6876_, 0, v___x_6895_);
v___x_6897_ = v___x_6876_;
goto v_reusejp_6896_;
}
else
{
lean_object* v_reuseFailAlloc_6898_; 
v_reuseFailAlloc_6898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6898_, 0, v___x_6895_);
lean_ctor_set(v_reuseFailAlloc_6898_, 1, v___x_6882_);
v___x_6897_ = v_reuseFailAlloc_6898_;
goto v_reusejp_6896_;
}
v_reusejp_6896_:
{
return v___x_6897_;
}
}
}
}
}
}
else
{
lean_object* v___x_6906_; size_t v___x_6907_; size_t v___x_6908_; 
lean_del_object(v___x_6880_);
lean_dec(v_definition_x3f_6878_);
lean_del_object(v___x_6876_);
lean_dec(v_snd_6874_);
v___x_6906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6907_ = ((size_t)1ULL);
v___x_6908_ = lean_usize_add(v_i_6865_, v___x_6907_);
v_i_6865_ = v___x_6908_;
v_b_6866_ = v___x_6906_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6914_, lean_object* v_sz_6915_, lean_object* v_i_6916_, lean_object* v_b_6917_){
_start:
{
size_t v_sz_boxed_6918_; size_t v_i_boxed_6919_; lean_object* v_res_6920_; 
v_sz_boxed_6918_ = lean_unbox_usize(v_sz_6915_);
lean_dec(v_sz_6915_);
v_i_boxed_6919_ = lean_unbox_usize(v_i_6916_);
lean_dec(v_i_6916_);
v_res_6920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6914_, v_sz_boxed_6918_, v_i_boxed_6919_, v_b_6917_);
lean_dec_ref(v_b_6917_);
lean_dec_ref(v_as_6914_);
return v_res_6920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6921_, lean_object* v_ident_6922_){
_start:
{
lean_object* v___x_6923_; lean_object* v___x_6924_; lean_object* v___x_6925_; size_t v_sz_6926_; size_t v___x_6927_; lean_object* v___x_6928_; lean_object* v_fst_6929_; 
v___x_6923_ = l_Lean_Server_References_allRefsFor(v_self_6921_, v_ident_6922_);
v___x_6924_ = lean_box(0);
v___x_6925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6926_ = lean_array_size(v___x_6923_);
v___x_6927_ = ((size_t)0ULL);
v___x_6928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6923_, v_sz_6926_, v___x_6927_, v___x_6925_);
lean_dec_ref(v___x_6923_);
v_fst_6929_ = lean_ctor_get(v___x_6928_, 0);
lean_inc(v_fst_6929_);
lean_dec_ref(v___x_6928_);
if (lean_obj_tag(v_fst_6929_) == 0)
{
return v___x_6924_;
}
else
{
lean_object* v_val_6930_; 
v_val_6930_ = lean_ctor_get(v_fst_6929_, 0);
lean_inc(v_val_6930_);
lean_dec_ref(v_fst_6929_);
return v_val_6930_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6931_, lean_object* v_a_6932_, lean_object* v_fst_6933_, lean_object* v_init_6934_, lean_object* v_x_6935_){
_start:
{
lean_object* v_d_6938_; 
if (lean_obj_tag(v_x_6935_) == 0)
{
lean_object* v_k_6940_; lean_object* v_v_6941_; lean_object* v_l_6942_; lean_object* v_r_6943_; lean_object* v___y_6945_; lean_object* v___x_6949_; 
v_k_6940_ = lean_ctor_get(v_x_6935_, 1);
lean_inc(v_k_6940_);
v_v_6941_ = lean_ctor_get(v_x_6935_, 2);
lean_inc(v_v_6941_);
v_l_6942_ = lean_ctor_get(v_x_6935_, 3);
lean_inc(v_l_6942_);
v_r_6943_ = lean_ctor_get(v_x_6935_, 4);
lean_inc(v_r_6943_);
lean_dec_ref(v_x_6935_);
lean_inc_ref(v_fst_6933_);
lean_inc(v_a_6932_);
lean_inc_ref(v_filterMapIdent_6931_);
v___x_6949_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6931_, v_a_6932_, v_fst_6933_, v_init_6934_, v_l_6942_);
if (lean_obj_tag(v___x_6949_) == 0)
{
lean_object* v_a_6950_; 
lean_dec(v_r_6943_);
lean_dec(v_v_6941_);
lean_dec(v_k_6940_);
lean_dec_ref(v_fst_6933_);
lean_dec(v_a_6932_);
lean_dec_ref(v_filterMapIdent_6931_);
v_a_6950_ = lean_ctor_get(v___x_6949_, 0);
lean_inc(v_a_6950_);
lean_dec_ref(v___x_6949_);
v_d_6938_ = v_a_6950_;
goto v___jp_6937_;
}
else
{
if (lean_obj_tag(v_k_6940_) == 0)
{
lean_object* v_definition_x3f_6951_; 
v_definition_x3f_6951_ = lean_ctor_get(v_v_6941_, 0);
lean_inc(v_definition_x3f_6951_);
lean_dec(v_v_6941_);
if (lean_obj_tag(v_definition_x3f_6951_) == 1)
{
lean_object* v_a_6952_; lean_object* v_identName_6953_; lean_object* v_val_6954_; lean_object* v___x_6955_; lean_object* v___x_6956_; 
v_a_6952_ = lean_ctor_get(v___x_6949_, 0);
lean_inc(v_a_6952_);
v_identName_6953_ = lean_ctor_get(v_k_6940_, 1);
lean_inc_ref(v_identName_6953_);
lean_dec_ref(v_k_6940_);
v_val_6954_ = lean_ctor_get(v_definition_x3f_6951_, 0);
lean_inc(v_val_6954_);
lean_dec_ref(v_definition_x3f_6951_);
v___x_6955_ = l_String_toName(v_identName_6953_);
lean_inc_ref(v_filterMapIdent_6931_);
v___x_6956_ = lean_apply_1(v_filterMapIdent_6931_, v___x_6955_);
if (lean_obj_tag(v___x_6956_) == 1)
{
lean_object* v_val_6957_; lean_object* v___x_6958_; lean_object* v___x_6959_; lean_object* v___x_6960_; 
lean_dec_ref(v___x_6949_);
v_val_6957_ = lean_ctor_get(v___x_6956_, 0);
lean_inc(v_val_6957_);
lean_dec_ref(v___x_6956_);
v___x_6958_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6954_);
lean_dec(v_val_6954_);
lean_inc_ref(v_fst_6933_);
lean_inc(v_a_6932_);
v___x_6959_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6959_, 0, v_a_6932_);
lean_ctor_set(v___x_6959_, 1, v_fst_6933_);
lean_ctor_set(v___x_6959_, 2, v_val_6957_);
lean_ctor_set(v___x_6959_, 3, v___x_6958_);
v___x_6960_ = lean_array_push(v_a_6952_, v___x_6959_);
v_init_6934_ = v___x_6960_;
v_x_6935_ = v_r_6943_;
goto _start;
}
else
{
lean_dec(v___x_6956_);
lean_dec(v_val_6954_);
lean_dec(v_a_6952_);
v___y_6945_ = v___x_6949_;
goto v___jp_6944_;
}
}
else
{
lean_dec(v_definition_x3f_6951_);
lean_dec_ref(v_k_6940_);
v___y_6945_ = v___x_6949_;
goto v___jp_6944_;
}
}
else
{
lean_dec(v_v_6941_);
lean_dec(v_k_6940_);
v___y_6945_ = v___x_6949_;
goto v___jp_6944_;
}
}
v___jp_6944_:
{
if (lean_obj_tag(v___y_6945_) == 0)
{
lean_object* v_a_6946_; 
lean_dec(v_r_6943_);
lean_dec_ref(v_fst_6933_);
lean_dec(v_a_6932_);
lean_dec_ref(v_filterMapIdent_6931_);
v_a_6946_ = lean_ctor_get(v___y_6945_, 0);
lean_inc(v_a_6946_);
lean_dec_ref(v___y_6945_);
v_d_6938_ = v_a_6946_;
goto v___jp_6937_;
}
else
{
lean_object* v_a_6947_; 
v_a_6947_ = lean_ctor_get(v___y_6945_, 0);
lean_inc(v_a_6947_);
lean_dec_ref(v___y_6945_);
v_init_6934_ = v_a_6947_;
v_x_6935_ = v_r_6943_;
goto _start;
}
}
}
else
{
lean_object* v___x_6962_; 
lean_dec_ref(v_fst_6933_);
lean_dec(v_a_6932_);
lean_dec_ref(v_filterMapIdent_6931_);
v___x_6962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6962_, 0, v_init_6934_);
return v___x_6962_;
}
v___jp_6937_:
{
lean_object* v___x_6939_; 
v___x_6939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6939_, 0, v_d_6938_);
return v___x_6939_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6963_, lean_object* v_a_6964_, lean_object* v_fst_6965_, lean_object* v_init_6966_, lean_object* v_x_6967_, lean_object* v___y_6968_){
_start:
{
lean_object* v_res_6969_; 
v_res_6969_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6963_, v_a_6964_, v_fst_6965_, v_init_6966_, v_x_6967_);
return v_res_6969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6970_, lean_object* v_cancelTk_x3f_6971_, lean_object* v_init_6972_, lean_object* v_x_6973_){
_start:
{
lean_object* v_d_6976_; 
if (lean_obj_tag(v_x_6973_) == 0)
{
lean_object* v_k_6978_; lean_object* v_v_6979_; lean_object* v_l_6980_; lean_object* v_r_6981_; lean_object* v___x_6982_; 
v_k_6978_ = lean_ctor_get(v_x_6973_, 1);
lean_inc(v_k_6978_);
v_v_6979_ = lean_ctor_get(v_x_6973_, 2);
lean_inc(v_v_6979_);
v_l_6980_ = lean_ctor_get(v_x_6973_, 3);
lean_inc(v_l_6980_);
v_r_6981_ = lean_ctor_get(v_x_6973_, 4);
lean_inc(v_r_6981_);
lean_dec_ref(v_x_6973_);
lean_inc(v_cancelTk_x3f_6971_);
lean_inc_ref(v_filterMapIdent_6970_);
v___x_6982_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6970_, v_cancelTk_x3f_6971_, v_init_6972_, v_l_6980_);
if (lean_obj_tag(v___x_6982_) == 0)
{
lean_object* v_a_6983_; 
lean_dec(v_r_6981_);
lean_dec(v_v_6979_);
lean_dec(v_k_6978_);
lean_dec(v_cancelTk_x3f_6971_);
lean_dec_ref(v_filterMapIdent_6970_);
v_a_6983_ = lean_ctor_get(v___x_6982_, 0);
lean_inc(v_a_6983_);
lean_dec_ref(v___x_6982_);
v_d_6976_ = v_a_6983_;
goto v___jp_6975_;
}
else
{
lean_object* v_snd_6984_; lean_object* v_a_6985_; lean_object* v_fst_6986_; lean_object* v_fst_6987_; lean_object* v___x_6989_; uint8_t v_isShared_6990_; uint8_t v_isSharedCheck_7020_; 
v_snd_6984_ = lean_ctor_get(v_v_6979_, 1);
lean_inc(v_snd_6984_);
v_a_6985_ = lean_ctor_get(v___x_6982_, 0);
lean_inc(v_a_6985_);
lean_dec_ref(v___x_6982_);
v_fst_6986_ = lean_ctor_get(v_v_6979_, 0);
lean_inc(v_fst_6986_);
lean_dec(v_v_6979_);
v_fst_6987_ = lean_ctor_get(v_snd_6984_, 0);
v_isSharedCheck_7020_ = !lean_is_exclusive(v_snd_6984_);
if (v_isSharedCheck_7020_ == 0)
{
lean_object* v_unused_7021_; 
v_unused_7021_ = lean_ctor_get(v_snd_6984_, 1);
lean_dec(v_unused_7021_);
v___x_6989_ = v_snd_6984_;
v_isShared_6990_ = v_isSharedCheck_7020_;
goto v_resetjp_6988_;
}
else
{
lean_inc(v_fst_6987_);
lean_dec(v_snd_6984_);
v___x_6989_ = lean_box(0);
v_isShared_6990_ = v_isSharedCheck_7020_;
goto v_resetjp_6988_;
}
v_resetjp_6988_:
{
lean_object* v_snd_6991_; lean_object* v___x_6993_; uint8_t v_isShared_6994_; uint8_t v_isSharedCheck_7018_; 
v_snd_6991_ = lean_ctor_get(v_a_6985_, 1);
v_isSharedCheck_7018_ = !lean_is_exclusive(v_a_6985_);
if (v_isSharedCheck_7018_ == 0)
{
lean_object* v_unused_7019_; 
v_unused_7019_ = lean_ctor_get(v_a_6985_, 0);
lean_dec(v_unused_7019_);
v___x_6993_ = v_a_6985_;
v_isShared_6994_ = v_isSharedCheck_7018_;
goto v_resetjp_6992_;
}
else
{
lean_inc(v_snd_6991_);
lean_dec(v_a_6985_);
v___x_6993_ = lean_box(0);
v_isShared_6994_ = v_isSharedCheck_7018_;
goto v_resetjp_6992_;
}
v_resetjp_6992_:
{
lean_object* v___x_6995_; lean_object* v_val_6997_; 
v___x_6995_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_6971_) == 1)
{
lean_object* v_val_7005_; uint8_t v___x_7006_; 
v_val_7005_ = lean_ctor_get(v_cancelTk_x3f_6971_, 0);
v___x_7006_ = l_IO_CancelToken_isSet(v_val_7005_);
if (v___x_7006_ == 0)
{
lean_del_object(v___x_6989_);
goto v___jp_7002_;
}
else
{
lean_object* v___x_7008_; uint8_t v_isShared_7009_; uint8_t v_isSharedCheck_7016_; 
lean_del_object(v___x_6993_);
lean_dec(v_fst_6987_);
lean_dec(v_fst_6986_);
lean_dec(v_r_6981_);
lean_dec(v_k_6978_);
lean_dec_ref(v_filterMapIdent_6970_);
v_isSharedCheck_7016_ = !lean_is_exclusive(v_cancelTk_x3f_6971_);
if (v_isSharedCheck_7016_ == 0)
{
lean_object* v_unused_7017_; 
v_unused_7017_ = lean_ctor_get(v_cancelTk_x3f_6971_, 0);
lean_dec(v_unused_7017_);
v___x_7008_ = v_cancelTk_x3f_6971_;
v_isShared_7009_ = v_isSharedCheck_7016_;
goto v_resetjp_7007_;
}
else
{
lean_dec(v_cancelTk_x3f_6971_);
v___x_7008_ = lean_box(0);
v_isShared_7009_ = v_isSharedCheck_7016_;
goto v_resetjp_7007_;
}
v_resetjp_7007_:
{
lean_object* v___x_7011_; 
lean_inc(v_snd_6991_);
if (v_isShared_7009_ == 0)
{
lean_ctor_set(v___x_7008_, 0, v_snd_6991_);
v___x_7011_ = v___x_7008_;
goto v_reusejp_7010_;
}
else
{
lean_object* v_reuseFailAlloc_7015_; 
v_reuseFailAlloc_7015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7015_, 0, v_snd_6991_);
v___x_7011_ = v_reuseFailAlloc_7015_;
goto v_reusejp_7010_;
}
v_reusejp_7010_:
{
lean_object* v___x_7013_; 
if (v_isShared_6990_ == 0)
{
lean_ctor_set(v___x_6989_, 1, v_snd_6991_);
lean_ctor_set(v___x_6989_, 0, v___x_7011_);
v___x_7013_ = v___x_6989_;
goto v_reusejp_7012_;
}
else
{
lean_object* v_reuseFailAlloc_7014_; 
v_reuseFailAlloc_7014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7014_, 0, v___x_7011_);
lean_ctor_set(v_reuseFailAlloc_7014_, 1, v_snd_6991_);
v___x_7013_ = v_reuseFailAlloc_7014_;
goto v_reusejp_7012_;
}
v_reusejp_7012_:
{
v_d_6976_ = v___x_7013_;
goto v___jp_6975_;
}
}
}
}
}
else
{
lean_del_object(v___x_6989_);
goto v___jp_7002_;
}
v___jp_6996_:
{
lean_object* v___x_6999_; 
if (v_isShared_6994_ == 0)
{
lean_ctor_set(v___x_6993_, 1, v_val_6997_);
lean_ctor_set(v___x_6993_, 0, v___x_6995_);
v___x_6999_ = v___x_6993_;
goto v_reusejp_6998_;
}
else
{
lean_object* v_reuseFailAlloc_7001_; 
v_reuseFailAlloc_7001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7001_, 0, v___x_6995_);
lean_ctor_set(v_reuseFailAlloc_7001_, 1, v_val_6997_);
v___x_6999_ = v_reuseFailAlloc_7001_;
goto v_reusejp_6998_;
}
v_reusejp_6998_:
{
v_init_6972_ = v___x_6999_;
v_x_6973_ = v_r_6981_;
goto _start;
}
}
v___jp_7002_:
{
lean_object* v___x_7003_; lean_object* v_a_7004_; 
lean_inc_ref(v_filterMapIdent_6970_);
v___x_7003_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6970_, v_k_6978_, v_fst_6986_, v_snd_6991_, v_fst_6987_);
v_a_7004_ = lean_ctor_get(v___x_7003_, 0);
lean_inc(v_a_7004_);
lean_dec_ref(v___x_7003_);
v_val_6997_ = v_a_7004_;
goto v___jp_6996_;
}
}
}
}
}
else
{
lean_object* v___x_7022_; 
lean_dec(v_cancelTk_x3f_6971_);
lean_dec_ref(v_filterMapIdent_6970_);
v___x_7022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7022_, 0, v_init_6972_);
return v___x_7022_;
}
v___jp_6975_:
{
lean_object* v___x_6977_; 
v___x_6977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6977_, 0, v_d_6976_);
return v___x_6977_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_7023_, lean_object* v_cancelTk_x3f_7024_, lean_object* v_init_7025_, lean_object* v_x_7026_, lean_object* v___y_7027_){
_start:
{
lean_object* v_res_7028_; 
v_res_7028_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7023_, v_cancelTk_x3f_7024_, v_init_7025_, v_x_7026_);
return v_res_7028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_7034_, lean_object* v_filterMapIdent_7035_, lean_object* v_cancelTk_x3f_7036_){
_start:
{
lean_object* v___x_7038_; lean_object* v___x_7039_; lean_object* v___x_7040_; lean_object* v_val_7042_; lean_object* v_a_7046_; 
v___x_7038_ = l_Lean_Server_References_allRefs(v_self_7034_);
v___x_7039_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_7040_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7035_, v_cancelTk_x3f_7036_, v___x_7039_, v___x_7038_);
v_a_7046_ = lean_ctor_get(v___x_7040_, 0);
lean_inc(v_a_7046_);
lean_dec_ref(v___x_7040_);
v_val_7042_ = v_a_7046_;
goto v___jp_7041_;
v___jp_7041_:
{
lean_object* v_fst_7043_; 
v_fst_7043_ = lean_ctor_get(v_val_7042_, 0);
if (lean_obj_tag(v_fst_7043_) == 0)
{
lean_object* v_snd_7044_; 
v_snd_7044_ = lean_ctor_get(v_val_7042_, 1);
lean_inc(v_snd_7044_);
lean_dec_ref(v_val_7042_);
return v_snd_7044_;
}
else
{
lean_object* v_val_7045_; 
lean_inc_ref(v_fst_7043_);
lean_dec_ref(v_val_7042_);
v_val_7045_ = lean_ctor_get(v_fst_7043_, 0);
lean_inc(v_val_7045_);
lean_dec_ref(v_fst_7043_);
return v_val_7045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_7047_, lean_object* v_filterMapIdent_7048_, lean_object* v_cancelTk_x3f_7049_, lean_object* v_a_7050_){
_start:
{
lean_object* v_res_7051_; 
v_res_7051_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7047_, v_filterMapIdent_7048_, v_cancelTk_x3f_7049_);
return v_res_7051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_7052_, lean_object* v_self_7053_, lean_object* v_filterMapIdent_7054_, lean_object* v_cancelTk_x3f_7055_){
_start:
{
lean_object* v___x_7057_; 
v___x_7057_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7053_, v_filterMapIdent_7054_, v_cancelTk_x3f_7055_);
return v___x_7057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_7058_, lean_object* v_self_7059_, lean_object* v_filterMapIdent_7060_, lean_object* v_cancelTk_x3f_7061_, lean_object* v_a_7062_){
_start:
{
lean_object* v_res_7063_; 
v_res_7063_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_7058_, v_self_7059_, v_filterMapIdent_7060_, v_cancelTk_x3f_7061_);
return v_res_7063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_7064_, lean_object* v_filterMapIdent_7065_, lean_object* v_a_7066_, lean_object* v_fst_7067_, lean_object* v_init_7068_, lean_object* v_x_7069_){
_start:
{
lean_object* v___x_7071_; 
v___x_7071_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_7065_, v_a_7066_, v_fst_7067_, v_init_7068_, v_x_7069_);
return v___x_7071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_7072_, lean_object* v_filterMapIdent_7073_, lean_object* v_a_7074_, lean_object* v_fst_7075_, lean_object* v_init_7076_, lean_object* v_x_7077_, lean_object* v___y_7078_){
_start:
{
lean_object* v_res_7079_; 
v_res_7079_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_7072_, v_filterMapIdent_7073_, v_a_7074_, v_fst_7075_, v_init_7076_, v_x_7077_);
return v_res_7079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_7080_, lean_object* v_filterMapIdent_7081_, lean_object* v_cancelTk_x3f_7082_, lean_object* v_init_7083_, lean_object* v_x_7084_){
_start:
{
lean_object* v___x_7086_; 
v___x_7086_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7081_, v_cancelTk_x3f_7082_, v_init_7083_, v_x_7084_);
return v___x_7086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7087_, lean_object* v_filterMapIdent_7088_, lean_object* v_cancelTk_x3f_7089_, lean_object* v_init_7090_, lean_object* v_x_7091_, lean_object* v___y_7092_){
_start:
{
lean_object* v_res_7093_; 
v_res_7093_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7087_, v_filterMapIdent_7088_, v_cancelTk_x3f_7089_, v_init_7090_, v_x_7091_);
return v_res_7093_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7094_){
_start:
{
lean_object* v___x_7095_; lean_object* v___x_7096_; 
v___x_7095_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7096_ = lean_panic_fn_borrowed(v___x_7095_, v_msg_7094_);
return v___x_7096_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7100_; lean_object* v___x_7101_; lean_object* v___x_7102_; lean_object* v___x_7103_; lean_object* v___x_7104_; lean_object* v___x_7105_; 
v___x_7100_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7101_ = lean_unsigned_to_nat(14u);
v___x_7102_ = lean_unsigned_to_nat(22u);
v___x_7103_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7104_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7105_ = l_mkPanicMessageWithDecl(v___x_7104_, v___x_7103_, v___x_7102_, v___x_7101_, v___x_7100_);
return v___x_7105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7106_, lean_object* v_init_7107_, lean_object* v_x_7108_){
_start:
{
if (lean_obj_tag(v_x_7108_) == 0)
{
lean_object* v_k_7109_; lean_object* v_v_7110_; lean_object* v_l_7111_; lean_object* v_r_7112_; lean_object* v___x_7113_; lean_object* v_a_7114_; lean_object* v_fst_7115_; lean_object* v_snd_7116_; lean_object* v___y_7118_; lean_object* v_index_7133_; lean_object* v___x_7134_; 
v_k_7109_ = lean_ctor_get(v_x_7108_, 1);
v_v_7110_ = lean_ctor_get(v_x_7108_, 2);
v_l_7111_ = lean_ctor_get(v_x_7108_, 3);
v_r_7112_ = lean_ctor_get(v_x_7108_, 4);
v___x_7113_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7106_, v_init_7107_, v_l_7111_);
v_a_7114_ = lean_ctor_get(v___x_7113_, 0);
lean_inc(v_a_7114_);
v_fst_7115_ = lean_ctor_get(v_v_7110_, 0);
v_snd_7116_ = lean_ctor_get(v_v_7110_, 1);
v_index_7133_ = lean_ctor_get(v_snd_7116_, 1);
v___x_7134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7133_, v_requestedMod_7106_);
if (lean_obj_tag(v___x_7134_) == 1)
{
lean_object* v_val_7135_; lean_object* v___x_7136_; 
lean_dec_ref(v___x_7113_);
v_val_7135_ = lean_ctor_get(v___x_7134_, 0);
lean_inc(v_val_7135_);
lean_dec_ref(v___x_7134_);
v___x_7136_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7135_);
lean_dec(v_val_7135_);
if (lean_obj_tag(v___x_7136_) == 0)
{
lean_object* v___x_7137_; lean_object* v___x_7138_; 
v___x_7137_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7138_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7137_);
v___y_7118_ = v___x_7138_;
goto v___jp_7117_;
}
else
{
lean_object* v_val_7139_; 
v_val_7139_ = lean_ctor_get(v___x_7136_, 0);
lean_inc(v_val_7139_);
lean_dec_ref(v___x_7136_);
v___y_7118_ = v_val_7139_;
goto v___jp_7117_;
}
}
else
{
lean_object* v_a_7140_; 
lean_dec(v___x_7134_);
lean_dec(v_a_7114_);
v_a_7140_ = lean_ctor_get(v___x_7113_, 0);
lean_inc(v_a_7140_);
lean_dec_ref(v___x_7113_);
v_init_7107_ = v_a_7140_;
v_x_7108_ = v_r_7112_;
goto _start;
}
v___jp_7117_:
{
uint8_t v_isAll_7119_; uint8_t v_isPrivate_7120_; uint8_t v_metaKind_7121_; lean_object* v___x_7123_; uint8_t v_isShared_7124_; uint8_t v_isSharedCheck_7130_; 
v_isAll_7119_ = lean_ctor_get_uint8(v___y_7118_, sizeof(void*)*2);
v_isPrivate_7120_ = lean_ctor_get_uint8(v___y_7118_, sizeof(void*)*2 + 1);
v_metaKind_7121_ = lean_ctor_get_uint8(v___y_7118_, sizeof(void*)*2 + 2);
v_isSharedCheck_7130_ = !lean_is_exclusive(v___y_7118_);
if (v_isSharedCheck_7130_ == 0)
{
lean_object* v_unused_7131_; lean_object* v_unused_7132_; 
v_unused_7131_ = lean_ctor_get(v___y_7118_, 1);
lean_dec(v_unused_7131_);
v_unused_7132_ = lean_ctor_get(v___y_7118_, 0);
lean_dec(v_unused_7132_);
v___x_7123_ = v___y_7118_;
v_isShared_7124_ = v_isSharedCheck_7130_;
goto v_resetjp_7122_;
}
else
{
lean_dec(v___y_7118_);
v___x_7123_ = lean_box(0);
v_isShared_7124_ = v_isSharedCheck_7130_;
goto v_resetjp_7122_;
}
v_resetjp_7122_:
{
lean_object* v___x_7126_; 
lean_inc(v_fst_7115_);
lean_inc(v_k_7109_);
if (v_isShared_7124_ == 0)
{
lean_ctor_set(v___x_7123_, 1, v_fst_7115_);
lean_ctor_set(v___x_7123_, 0, v_k_7109_);
v___x_7126_ = v___x_7123_;
goto v_reusejp_7125_;
}
else
{
lean_object* v_reuseFailAlloc_7129_; 
v_reuseFailAlloc_7129_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7129_, 0, v_k_7109_);
lean_ctor_set(v_reuseFailAlloc_7129_, 1, v_fst_7115_);
lean_ctor_set_uint8(v_reuseFailAlloc_7129_, sizeof(void*)*2, v_isAll_7119_);
lean_ctor_set_uint8(v_reuseFailAlloc_7129_, sizeof(void*)*2 + 1, v_isPrivate_7120_);
lean_ctor_set_uint8(v_reuseFailAlloc_7129_, sizeof(void*)*2 + 2, v_metaKind_7121_);
v___x_7126_ = v_reuseFailAlloc_7129_;
goto v_reusejp_7125_;
}
v_reusejp_7125_:
{
lean_object* v___x_7127_; 
v___x_7127_ = lean_array_push(v_a_7114_, v___x_7126_);
v_init_7107_ = v___x_7127_;
v_x_7108_ = v_r_7112_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7142_; 
v___x_7142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7142_, 0, v_init_7107_);
return v___x_7142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object* v_requestedMod_7143_, lean_object* v_init_7144_, lean_object* v_x_7145_){
_start:
{
lean_object* v_res_7146_; 
v_res_7146_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7143_, v_init_7144_, v_x_7145_);
lean_dec(v_x_7145_);
lean_dec(v_requestedMod_7143_);
return v_res_7146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object* v_self_7147_, lean_object* v_requestedMod_7148_){
_start:
{
lean_object* v_result_7149_; lean_object* v___x_7150_; lean_object* v___x_7151_; lean_object* v_a_7152_; 
v_result_7149_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_7150_ = l_Lean_Server_References_allDirectImports(v_self_7147_);
v___x_7151_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7148_, v_result_7149_, v___x_7150_);
lean_dec(v___x_7150_);
v_a_7152_ = lean_ctor_get(v___x_7151_, 0);
lean_inc(v_a_7152_);
lean_dec_ref(v___x_7151_);
return v_a_7152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object* v_self_7153_, lean_object* v_requestedMod_7154_){
_start:
{
lean_object* v_res_7155_; 
v_res_7155_ = l_Lean_Server_References_importedBy(v_self_7153_, v_requestedMod_7154_);
lean_dec(v_requestedMod_7154_);
return v_res_7155_;
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

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
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load(lean_object* v_path_2250_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_IO_FS_readFile(v_path_2250_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2274_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2274_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2274_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_a_2258_; lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Json_parse(v_a_2253_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; 
lean_del_object(v___x_2255_);
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v_a_2258_ = v_a_2266_;
goto v___jp_2257_;
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2268_; 
v_a_2267_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2268_ = l_Lean_Server_instFromJsonIlean_fromJson(v_a_2267_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; 
lean_del_object(v___x_2255_);
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v_a_2258_ = v_a_2269_;
goto v___jp_2257_;
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; 
v_a_2270_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2268_, 1);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v_a_2270_);
v___x_2272_ = v___x_2255_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
v___jp_2257_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2259_ = ((lean_object*)(l_Lean_Server_Ilean_load___closed__0));
v___x_2260_ = lean_string_append(v___x_2259_, v_path_2250_);
v___x_2261_ = ((lean_object*)(l_Lean_Server_instFromJsonIlean_fromJson___closed__11));
v___x_2262_ = lean_string_append(v___x_2260_, v___x_2261_);
v___x_2263_ = lean_string_append(v___x_2262_, v_a_2258_);
lean_dec_ref(v_a_2258_);
v___x_2264_ = l_Lean_IO_throwServerError___redArg(v___x_2263_);
return v___x_2264_;
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_a_2275_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2252_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2252_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Ilean_load___boxed(lean_object* v_path_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Server_Ilean_load(v_path_2283_);
lean_dec_ref(v_path_2283_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f(lean_object* v_env_2286_, lean_object* v_declName_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2286_, v_declName_2287_);
if (lean_obj_tag(v___x_2288_) == 1)
{
lean_object* v_val_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2301_; 
v_val_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2301_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_val_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2301_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = l_Lean_Environment_allImportedModuleNames(v_env_2286_);
v___x_2294_ = lean_array_get_size(v___x_2293_);
v___x_2295_ = lean_nat_dec_lt(v_val_2289_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
lean_dec_ref(v___x_2293_);
lean_del_object(v___x_2291_);
lean_dec(v_val_2289_);
v___x_2296_ = lean_box(0);
return v___x_2296_;
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = lean_array_fget(v___x_2293_, v_val_2289_);
lean_dec(v_val_2289_);
lean_dec_ref(v___x_2293_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2297_);
v___x_2299_ = v___x_2291_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v___x_2302_; lean_object* v_mainModule_2303_; lean_object* v___x_2304_; 
lean_dec(v___x_2288_);
v___x_2302_ = l_Lean_Environment_header(v_env_2286_);
v_mainModule_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_mainModule_2303_);
lean_dec_ref(v___x_2302_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_mainModule_2303_);
return v___x_2304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_getModuleContainingDecl_x3f___boxed(lean_object* v_env_2305_, lean_object* v_declName_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2305_, v_declName_2306_);
lean_dec(v_declName_2306_);
lean_dec_ref(v_env_2305_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf(lean_object* v_ci_2308_, lean_object* v_i_2309_){
_start:
{
switch(lean_obj_tag(v_i_2309_))
{
case 1:
{
lean_object* v_i_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2351_; 
v_i_2310_ = lean_ctor_get(v_i_2309_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_i_2309_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2312_ = v_i_2309_;
v_isShared_2313_ = v_isSharedCheck_2351_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_i_2310_);
lean_dec(v_i_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2351_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v_expr_2314_; 
v_expr_2314_ = lean_ctor_get(v_i_2310_, 3);
lean_inc_ref(v_expr_2314_);
switch(lean_obj_tag(v_expr_2314_))
{
case 4:
{
lean_object* v_toCommandContextInfo_2315_; uint8_t v_isBinder_2316_; lean_object* v_declName_2317_; lean_object* v_env_2318_; lean_object* v___x_2319_; 
lean_del_object(v___x_2312_);
v_toCommandContextInfo_2315_ = lean_ctor_get(v_ci_2308_, 0);
v_isBinder_2316_ = lean_ctor_get_uint8(v_i_2310_, sizeof(void*)*4);
lean_dec_ref(v_i_2310_);
v_declName_2317_ = lean_ctor_get(v_expr_2314_, 0);
lean_inc(v_declName_2317_);
lean_dec_ref_known(v_expr_2314_, 2);
v_env_2318_ = lean_ctor_get(v_toCommandContextInfo_2315_, 0);
v___x_2319_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2318_, v_declName_2317_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v___x_2320_; 
lean_dec(v_declName_2317_);
v___x_2320_ = lean_box(0);
return v___x_2320_;
}
else
{
lean_object* v_val_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2334_; 
v_val_2321_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2323_ = v___x_2319_;
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_val_2321_);
lean_dec(v___x_2319_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2325_ = 1;
v___x_2326_ = l_Lean_Name_toString(v_val_2321_, v___x_2325_);
v___x_2327_ = l_Lean_Name_toString(v_declName_2317_, v___x_2325_);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_box(v_isBinder_2316_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2330_);
v___x_2332_ = v___x_2323_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
case 1:
{
lean_object* v_toCommandContextInfo_2335_; uint8_t v_isBinder_2336_; lean_object* v_fvarId_2337_; lean_object* v_env_2338_; lean_object* v___x_2339_; lean_object* v_mainModule_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v_toCommandContextInfo_2335_ = lean_ctor_get(v_ci_2308_, 0);
v_isBinder_2336_ = lean_ctor_get_uint8(v_i_2310_, sizeof(void*)*4);
lean_dec_ref(v_i_2310_);
v_fvarId_2337_ = lean_ctor_get(v_expr_2314_, 0);
lean_inc(v_fvarId_2337_);
lean_dec_ref_known(v_expr_2314_, 1);
v_env_2338_ = lean_ctor_get(v_toCommandContextInfo_2335_, 0);
v___x_2339_ = l_Lean_Environment_header(v_env_2338_);
v_mainModule_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_mainModule_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = 1;
v___x_2342_ = l_Lean_Name_toString(v_mainModule_2340_, v___x_2341_);
v___x_2343_ = l_Lean_Name_toString(v_fvarId_2337_, v___x_2341_);
v___x_2344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = lean_box(v_isBinder_2336_);
v___x_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2346_);
v___x_2348_ = v___x_2312_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
default: 
{
lean_object* v___x_2350_; 
lean_dec_ref(v_expr_2314_);
lean_del_object(v___x_2312_);
lean_dec_ref(v_i_2310_);
v___x_2350_ = lean_box(0);
return v___x_2350_;
}
}
}
}
case 7:
{
lean_object* v_toCommandContextInfo_2352_; lean_object* v_i_2353_; lean_object* v_env_2354_; lean_object* v_projName_2355_; lean_object* v___x_2356_; 
v_toCommandContextInfo_2352_ = lean_ctor_get(v_ci_2308_, 0);
v_i_2353_ = lean_ctor_get(v_i_2309_, 0);
lean_inc_ref(v_i_2353_);
lean_dec_ref_known(v_i_2309_, 1);
v_env_2354_ = lean_ctor_get(v_toCommandContextInfo_2352_, 0);
v_projName_2355_ = lean_ctor_get(v_i_2353_, 0);
lean_inc(v_projName_2355_);
lean_dec_ref(v_i_2353_);
v___x_2356_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2354_, v_projName_2355_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v___x_2357_; 
lean_dec(v_projName_2355_);
v___x_2357_ = lean_box(0);
return v___x_2357_;
}
else
{
lean_object* v_val_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2372_; 
v_val_2358_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2360_ = v___x_2356_;
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_val_2358_);
lean_dec(v___x_2356_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2372_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
uint8_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2362_ = 1;
v___x_2363_ = l_Lean_Name_toString(v_val_2358_, v___x_2362_);
v___x_2364_ = l_Lean_Name_toString(v_projName_2355_, v___x_2362_);
v___x_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = 0;
v___x_2367_ = lean_box(v___x_2366_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2365_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2368_);
v___x_2370_ = v___x_2360_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
case 5:
{
lean_object* v_toCommandContextInfo_2373_; lean_object* v_i_2374_; lean_object* v_env_2375_; lean_object* v_declName_2376_; lean_object* v___x_2377_; 
v_toCommandContextInfo_2373_ = lean_ctor_get(v_ci_2308_, 0);
v_i_2374_ = lean_ctor_get(v_i_2309_, 0);
lean_inc_ref(v_i_2374_);
lean_dec_ref_known(v_i_2309_, 1);
v_env_2375_ = lean_ctor_get(v_toCommandContextInfo_2373_, 0);
v_declName_2376_ = lean_ctor_get(v_i_2374_, 2);
lean_inc(v_declName_2376_);
lean_dec_ref(v_i_2374_);
v___x_2377_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2375_, v_declName_2376_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v___x_2378_; 
lean_dec(v_declName_2376_);
v___x_2378_ = lean_box(0);
return v___x_2378_;
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2393_; 
v_val_2379_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2381_ = v___x_2377_;
v_isShared_2382_ = v_isSharedCheck_2393_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_val_2379_);
lean_dec(v___x_2377_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2393_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2383_ = 1;
v___x_2384_ = l_Lean_Name_toString(v_val_2379_, v___x_2383_);
v___x_2385_ = l_Lean_Name_toString(v_declName_2376_, v___x_2383_);
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = 0;
v___x_2388_ = lean_box(v___x_2387_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2389_);
v___x_2391_ = v___x_2381_;
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
case 17:
{
lean_object* v_toCommandContextInfo_2394_; lean_object* v_i_2395_; lean_object* v_env_2396_; lean_object* v_name_2397_; lean_object* v___x_2398_; 
v_toCommandContextInfo_2394_ = lean_ctor_get(v_ci_2308_, 0);
v_i_2395_ = lean_ctor_get(v_i_2309_, 0);
lean_inc_ref(v_i_2395_);
lean_dec_ref_known(v_i_2309_, 1);
v_env_2396_ = lean_ctor_get(v_toCommandContextInfo_2394_, 0);
v_name_2397_ = lean_ctor_get(v_i_2395_, 1);
lean_inc(v_name_2397_);
lean_dec_ref(v_i_2395_);
v___x_2398_ = l_Lean_Server_getModuleContainingDecl_x3f(v_env_2396_, v_name_2397_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v___x_2399_; 
lean_dec(v_name_2397_);
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
v___x_2406_ = l_Lean_Name_toString(v_name_2397_, v___x_2404_);
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
default: 
{
lean_object* v___x_2415_; 
lean_dec_ref(v_i_2309_);
v___x_2415_ = lean_box(0);
return v___x_2415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_identOf___boxed(lean_object* v_ci_2416_, lean_object* v_i_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Server_identOf(v_ci_2416_, v_i_2417_);
lean_dec_ref(v_ci_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(uint8_t v___x_2419_, lean_object* v_x_2420_, lean_object* v_x_2421_, lean_object* v_x_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_box(v___x_2419_);
v___x_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v___y_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed(lean_object* v___x_2426_, lean_object* v_x_2427_, lean_object* v_x_2428_, lean_object* v_x_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v___x_3525__boxed_2431_; lean_object* v_res_2432_; 
v___x_3525__boxed_2431_ = lean_unbox(v___x_2426_);
v_res_2432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(v___x_3525__boxed_2431_, v_x_2427_, v_x_2428_, v_x_2429_, v___y_2430_);
lean_dec_ref(v_x_2429_);
lean_dec_ref(v_x_2428_);
lean_dec_ref(v_x_2427_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(lean_object* v_text_2433_, lean_object* v_ci_2434_, lean_object* v_info_2435_, lean_object* v_x_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___x_2438_; 
lean_inc_ref(v_info_2435_);
v___x_2438_ = l_Lean_Server_identOf(v_ci_2434_, v_info_2435_);
if (lean_obj_tag(v___x_2438_) == 1)
{
lean_object* v_val_2439_; lean_object* v_fst_2440_; lean_object* v_snd_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2466_; 
v_val_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_val_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v_fst_2440_ = lean_ctor_get(v_val_2439_, 0);
v_snd_2441_ = lean_ctor_get(v_val_2439_, 1);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_val_2439_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2443_ = v_val_2439_;
v_isShared_2444_ = v_isSharedCheck_2466_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_snd_2441_);
lean_inc(v_fst_2440_);
lean_dec(v_val_2439_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2466_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_Elab_Info_range_x3f(v_info_2435_);
if (lean_obj_tag(v___x_2445_) == 1)
{
lean_object* v_val_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_val_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_val_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2447_ = l_Lean_Elab_Info_stx(v_info_2435_);
v___x_2448_ = l_Lean_Syntax_getHeadInfo(v___x_2447_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_dec_ref_known(v___x_2448_, 4);
v___x_2449_ = lean_box(0);
v___x_2450_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
v___x_2451_ = l_Lean_Syntax_Range_toLspRange(v_text_2433_, v_val_2446_);
v___x_2452_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2452_, 0, v_fst_2440_);
lean_ctor_set(v___x_2452_, 1, v___x_2450_);
lean_ctor_set(v___x_2452_, 2, v___x_2451_);
lean_ctor_set(v___x_2452_, 3, v___x_2447_);
lean_ctor_set(v___x_2452_, 4, v_ci_2434_);
lean_ctor_set(v___x_2452_, 5, v_info_2435_);
v___x_2453_ = lean_unbox(v_snd_2441_);
lean_dec(v_snd_2441_);
lean_ctor_set_uint8(v___x_2452_, sizeof(void*)*6, v___x_2453_);
v___x_2454_ = lean_array_push(v___y_2437_, v___x_2452_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 1, v___x_2454_);
lean_ctor_set(v___x_2443_, 0, v___x_2449_);
v___x_2456_ = v___x_2443_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2460_; 
lean_dec(v___x_2448_);
lean_dec(v___x_2447_);
lean_dec(v_val_2446_);
lean_dec(v_snd_2441_);
lean_dec(v_fst_2440_);
lean_dec_ref(v_info_2435_);
lean_dec_ref(v_ci_2434_);
lean_dec_ref(v_text_2433_);
v___x_2458_ = lean_box(0);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 1, v___y_2437_);
lean_ctor_set(v___x_2443_, 0, v___x_2458_);
v___x_2460_ = v___x_2443_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___y_2437_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
lean_dec(v___x_2445_);
lean_dec(v_snd_2441_);
lean_dec(v_fst_2440_);
lean_dec_ref(v_info_2435_);
lean_dec_ref(v_ci_2434_);
lean_dec_ref(v_text_2433_);
v___x_2462_ = lean_box(0);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 1, v___y_2437_);
lean_ctor_set(v___x_2443_, 0, v___x_2462_);
v___x_2464_ = v___x_2443_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___y_2437_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_dec(v___x_2438_);
lean_dec_ref(v_info_2435_);
lean_dec_ref(v_ci_2434_);
lean_dec_ref(v_text_2433_);
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
lean_ctor_set(v___x_2468_, 1, v___y_2437_);
return v___x_2468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed(lean_object* v_text_2469_, lean_object* v_ci_2470_, lean_object* v_info_2471_, lean_object* v_x_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1(v_text_2469_, v_ci_2470_, v_info_2471_, v_x_2472_, v___y_2473_);
lean_dec_ref(v_x_2472_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v___f_2484_; lean_object* v___f_2485_; lean_object* v___f_2486_; lean_object* v___f_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___f_2494_; lean_object* v___f_2495_; lean_object* v___f_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_3116__overap_2506_; lean_object* v___x_2507_; 
v___f_2484_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_2485_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_2486_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_2487_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_2488_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_2489_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_2490_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___f_2484_);
lean_ctor_set(v___x_2491_, 1, v___f_2485_);
v___x_2492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v___f_2486_);
lean_ctor_set(v___x_2492_, 2, v___f_2487_);
lean_ctor_set(v___x_2492_, 3, v___f_2488_);
lean_ctor_set(v___x_2492_, 4, v___f_2489_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v___f_2490_);
lean_inc_ref_n(v___x_2493_, 6);
v___f_2494_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2494_, 0, v___x_2493_);
v___f_2495_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2495_, 0, v___x_2493_);
v___f_2496_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2496_, 0, v___x_2493_);
v___f_2497_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2497_, 0, v___x_2493_);
v___x_2498_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2498_, 0, lean_box(0));
lean_closure_set(v___x_2498_, 1, lean_box(0));
lean_closure_set(v___x_2498_, 2, v___x_2493_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___f_2494_);
v___x_2500_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2500_, 0, lean_box(0));
lean_closure_set(v___x_2500_, 1, lean_box(0));
lean_closure_set(v___x_2500_, 2, v___x_2493_);
v___x_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
lean_ctor_set(v___x_2501_, 2, v___f_2495_);
lean_ctor_set(v___x_2501_, 3, v___f_2496_);
lean_ctor_set(v___x_2501_, 4, v___f_2497_);
v___x_2502_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2502_, 0, lean_box(0));
lean_closure_set(v___x_2502_, 1, lean_box(0));
lean_closure_set(v___x_2502_, 2, v___x_2493_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_box(0);
v___x_2505_ = l_instInhabitedOfMonad___redArg(v___x_2503_, v___x_2504_);
v___x_3116__overap_2506_ = lean_panic_fn_borrowed(v___x_2505_, v_msg_2482_);
lean_dec(v___x_2505_);
v___x_2507_ = lean_apply_1(v___x_3116__overap_2506_, v___y_2483_);
return v___x_2507_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2));
v___x_2512_ = lean_unsigned_to_nat(21u);
v___x_2513_ = lean_unsigned_to_nat(65u);
v___x_2514_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1));
v___x_2515_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0));
v___x_2516_ = l_mkPanicMessageWithDecl(v___x_2515_, v___x_2514_, v___x_2513_, v___x_2512_, v___x_2511_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object* v_preNode_2517_, lean_object* v_postNode_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_, lean_object* v___y_2521_){
_start:
{
switch(lean_obj_tag(v_x_2520_))
{
case 0:
{
lean_object* v_i_2522_; lean_object* v_t_2523_; lean_object* v___x_2524_; 
v_i_2522_ = lean_ctor_get(v_x_2520_, 0);
lean_inc_ref(v_i_2522_);
v_t_2523_ = lean_ctor_get(v_x_2520_, 1);
lean_inc_ref(v_t_2523_);
lean_dec_ref_known(v_x_2520_, 2);
v___x_2524_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2522_, v_x_2519_);
v_x_2519_ = v___x_2524_;
v_x_2520_ = v_t_2523_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_2519_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec_ref_known(v_x_2520_, 2);
lean_dec_ref(v_postNode_2518_);
lean_dec_ref(v_preNode_2517_);
v___x_2526_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_2527_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v___x_2526_, v___y_2521_);
return v___x_2527_;
}
else
{
lean_object* v_i_2528_; lean_object* v_children_2529_; lean_object* v_val_2530_; lean_object* v___x_2531_; lean_object* v_fst_2532_; uint8_t v___x_2533_; 
v_i_2528_ = lean_ctor_get(v_x_2520_, 0);
lean_inc_ref_n(v_i_2528_, 2);
v_children_2529_ = lean_ctor_get(v_x_2520_, 1);
lean_inc_ref_n(v_children_2529_, 2);
lean_dec_ref_known(v_x_2520_, 2);
v_val_2530_ = lean_ctor_get(v_x_2519_, 0);
lean_inc_n(v_val_2530_, 2);
lean_inc_ref(v_preNode_2517_);
v___x_2531_ = lean_apply_4(v_preNode_2517_, v_val_2530_, v_i_2528_, v_children_2529_, v___y_2521_);
v_fst_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_fst_2532_);
v___x_2533_ = lean_unbox(v_fst_2532_);
lean_dec(v_fst_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v_preNode_2517_);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_x_2519_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; 
v_unused_2553_ = lean_ctor_get(v_x_2519_, 0);
lean_dec(v_unused_2553_);
v___x_2535_ = v_x_2519_;
v_isShared_2536_ = v_isSharedCheck_2552_;
goto v_resetjp_2534_;
}
else
{
lean_dec(v_x_2519_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2552_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v_snd_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v_fst_2540_; lean_object* v_snd_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2551_; 
v_snd_2537_ = lean_ctor_get(v___x_2531_, 1);
lean_inc(v_snd_2537_);
lean_dec_ref(v___x_2531_);
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_apply_5(v_postNode_2518_, v_val_2530_, v_i_2528_, v_children_2529_, v___x_2538_, v_snd_2537_);
v_fst_2540_ = lean_ctor_get(v___x_2539_, 0);
v_snd_2541_ = lean_ctor_get(v___x_2539_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2543_ = v___x_2539_;
v_isShared_2544_ = v_isSharedCheck_2551_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_snd_2541_);
lean_inc(v_fst_2540_);
lean_dec(v___x_2539_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2551_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v_fst_2540_);
v___x_2546_ = v___x_2535_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_fst_2540_);
v___x_2546_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2548_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2546_);
v___x_2548_ = v___x_2543_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_snd_2541_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
else
{
lean_object* v_snd_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v___x_2561_; lean_object* v_fst_2562_; lean_object* v_snd_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2571_; 
v_snd_2554_ = lean_ctor_get(v___x_2531_, 1);
lean_inc(v_snd_2554_);
lean_dec_ref(v___x_2531_);
v___x_2555_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2519_, v_i_2528_);
v___x_2556_ = l_Lean_PersistentArray_toList___redArg(v_children_2529_);
v___x_2557_ = lean_box(0);
lean_inc_ref(v_postNode_2518_);
v___x_2558_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2517_, v_postNode_2518_, v___x_2555_, v___x_2556_, v___x_2557_, v_snd_2554_);
v_fst_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_fst_2559_);
v_snd_2560_ = lean_ctor_get(v___x_2558_, 1);
lean_inc(v_snd_2560_);
lean_dec_ref(v___x_2558_);
v___x_2561_ = lean_apply_5(v_postNode_2518_, v_val_2530_, v_i_2528_, v_children_2529_, v_fst_2559_, v_snd_2560_);
v_fst_2562_ = lean_ctor_get(v___x_2561_, 0);
v_snd_2563_ = lean_ctor_get(v___x_2561_, 1);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2565_ = v___x_2561_;
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_snd_2563_);
lean_inc(v_fst_2562_);
lean_dec(v___x_2561_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_fst_2562_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2567_);
v___x_2569_ = v___x_2565_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_snd_2563_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
default: 
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_dec_ref_known(v_x_2520_, 1);
lean_dec(v_x_2519_);
lean_dec_ref(v_postNode_2518_);
lean_dec_ref(v_preNode_2517_);
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
lean_ctor_set(v___x_2573_, 1, v___y_2521_);
return v___x_2573_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_2574_, lean_object* v_postNode_2575_, lean_object* v___x_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_, lean_object* v___y_2579_){
_start:
{
if (lean_obj_tag(v_x_2577_) == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec(v___x_2576_);
lean_dec_ref(v_postNode_2575_);
lean_dec_ref(v_preNode_2574_);
v___x_2580_ = l_List_reverse___redArg(v_x_2578_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v___y_2579_);
return v___x_2581_;
}
else
{
lean_object* v_head_2582_; lean_object* v_tail_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2594_; 
v_head_2582_ = lean_ctor_get(v_x_2577_, 0);
v_tail_2583_ = lean_ctor_get(v_x_2577_, 1);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_x_2577_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2585_ = v_x_2577_;
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_tail_2583_);
lean_inc(v_head_2582_);
lean_dec(v_x_2577_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v_fst_2588_; lean_object* v_snd_2589_; lean_object* v___x_2591_; 
lean_inc(v___x_2576_);
lean_inc_ref(v_postNode_2575_);
lean_inc_ref(v_preNode_2574_);
v___x_2587_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2574_, v_postNode_2575_, v___x_2576_, v_head_2582_, v___y_2579_);
v_fst_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_fst_2588_);
v_snd_2589_ = lean_ctor_get(v___x_2587_, 1);
lean_inc(v_snd_2589_);
lean_dec_ref(v___x_2587_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 1, v_x_2578_);
lean_ctor_set(v___x_2585_, 0, v_fst_2588_);
v___x_2591_ = v___x_2585_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_fst_2588_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_x_2578_);
v___x_2591_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
v_x_2577_ = v_tail_2583_;
v_x_2578_ = v___x_2591_;
v___y_2579_ = v_snd_2589_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object* v_postNode_2595_, lean_object* v_ci_2596_, lean_object* v_i_2597_, lean_object* v_cs_2598_, lean_object* v_x_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_apply_4(v_postNode_2595_, v_ci_2596_, v_i_2597_, v_cs_2598_, v___y_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object* v_postNode_2602_, lean_object* v_ci_2603_, lean_object* v_i_2604_, lean_object* v_cs_2605_, lean_object* v_x_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(v_postNode_2602_, v_ci_2603_, v_i_2604_, v_cs_2605_, v_x_2606_, v___y_2607_);
lean_dec(v_x_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object* v_preNode_2609_, lean_object* v_postNode_2610_, lean_object* v_ctx_x3f_2611_, lean_object* v_t_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___f_2614_; lean_object* v___x_2615_; lean_object* v_snd_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2624_; 
v___f_2614_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2614_, 0, v_postNode_2610_);
v___x_2615_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2609_, v___f_2614_, v_ctx_x3f_2611_, v_t_2612_, v___y_2613_);
v_snd_2616_ = lean_ctor_get(v___x_2615_, 1);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2624_ == 0)
{
lean_object* v_unused_2625_; 
v_unused_2625_ = lean_ctor_get(v___x_2615_, 0);
lean_dec(v_unused_2625_);
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2624_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_snd_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2624_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2620_ = lean_box(0);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2620_);
v___x_2622_ = v___x_2618_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_snd_2616_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(lean_object* v_text_2626_, lean_object* v_as_2627_, size_t v_sz_2628_, size_t v_i_2629_, lean_object* v_b_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v___x_2632_; 
v___x_2632_ = lean_usize_dec_lt(v_i_2629_, v_sz_2628_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec_ref(v_text_2626_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v_b_2630_);
lean_ctor_set(v___x_2633_, 1, v___y_2631_);
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; lean_object* v___f_2635_; lean_object* v___f_2636_; lean_object* v_a_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v_snd_2640_; lean_object* v___x_2641_; size_t v___x_2642_; size_t v___x_2643_; 
v___x_2634_ = lean_box(v___x_2632_);
v___f_2635_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2635_, 0, v___x_2634_);
lean_inc_ref(v_text_2626_);
v___f_2636_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2636_, 0, v_text_2626_);
v_a_2637_ = lean_array_uget_borrowed(v_as_2627_, v_i_2629_);
v___x_2638_ = lean_box(0);
lean_inc(v_a_2637_);
v___x_2639_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(v___f_2635_, v___f_2636_, v___x_2638_, v_a_2637_, v___y_2631_);
v_snd_2640_ = lean_ctor_get(v___x_2639_, 1);
lean_inc(v_snd_2640_);
lean_dec_ref(v___x_2639_);
v___x_2641_ = lean_box(0);
v___x_2642_ = ((size_t)1ULL);
v___x_2643_ = lean_usize_add(v_i_2629_, v___x_2642_);
v_i_2629_ = v___x_2643_;
v_b_2630_ = v___x_2641_;
v___y_2631_ = v_snd_2640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___boxed(lean_object* v_text_2645_, lean_object* v_as_2646_, lean_object* v_sz_2647_, lean_object* v_i_2648_, lean_object* v_b_2649_, lean_object* v___y_2650_){
_start:
{
size_t v_sz_boxed_2651_; size_t v_i_boxed_2652_; lean_object* v_res_2653_; 
v_sz_boxed_2651_ = lean_unbox_usize(v_sz_2647_);
lean_dec(v_sz_2647_);
v_i_boxed_2652_ = lean_unbox_usize(v_i_2648_);
lean_dec(v_i_2648_);
v_res_2653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2645_, v_as_2646_, v_sz_boxed_2651_, v_i_boxed_2652_, v_b_2649_, v___y_2650_);
lean_dec_ref(v_as_2646_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences(lean_object* v_text_2654_, lean_object* v_trees_2655_){
_start:
{
lean_object* v___x_2656_; size_t v_sz_2657_; size_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v_snd_2661_; 
v___x_2656_ = lean_box(0);
v_sz_2657_ = lean_array_size(v_trees_2655_);
v___x_2658_ = ((size_t)0ULL);
v___x_2659_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1(v_text_2654_, v_trees_2655_, v_sz_2657_, v___x_2658_, v___x_2656_, v___x_2659_);
v_snd_2661_ = lean_ctor_get(v___x_2660_, 1);
lean_inc(v_snd_2661_);
lean_dec_ref(v___x_2660_);
return v_snd_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findReferences___boxed(lean_object* v_text_2662_, lean_object* v_trees_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Server_findReferences(v_text_2662_, v_trees_2663_);
lean_dec_ref(v_trees_2663_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2665_, lean_object* v_msg_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v_msg_2666_, v___y_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object* v_00_u03b1_2669_, lean_object* v_preNode_2670_, lean_object* v_postNode_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2670_, v_postNode_2671_, v_x_2672_, v_x_2673_, v___y_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2676_, lean_object* v_preNode_2677_, lean_object* v_postNode_2678_, lean_object* v___x_2679_, lean_object* v_x_2680_, lean_object* v_x_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2677_, v_postNode_2678_, v___x_2679_, v_x_2680_, v_x_2681_, v___y_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(lean_object* v_a_2684_, lean_object* v_x_2685_){
_start:
{
lean_object* v_key_2686_; lean_object* v_value_2687_; lean_object* v_tail_2688_; uint8_t v___x_2689_; 
v_key_2686_ = lean_ctor_get(v_x_2685_, 0);
v_value_2687_ = lean_ctor_get(v_x_2685_, 1);
v_tail_2688_ = lean_ctor_get(v_x_2685_, 2);
v___x_2689_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2686_, v_a_2684_);
if (v___x_2689_ == 0)
{
v_x_2685_ = v_tail_2688_;
goto _start;
}
else
{
lean_inc(v_value_2687_);
return v_value_2687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg___boxed(lean_object* v_a_2691_, lean_object* v_x_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2691_, v_x_2692_);
lean_dec(v_x_2692_);
lean_dec_ref(v_a_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(lean_object* v_m_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_buckets_2696_; lean_object* v___x_2697_; uint64_t v___x_2698_; uint64_t v___x_2699_; uint64_t v___x_2700_; uint64_t v_fold_2701_; uint64_t v___x_2702_; uint64_t v___x_2703_; uint64_t v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; size_t v___x_2708_; size_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_buckets_2696_ = lean_ctor_get(v_m_2694_, 1);
v___x_2697_ = lean_array_get_size(v_buckets_2696_);
v___x_2698_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2695_);
v___x_2699_ = 32ULL;
v___x_2700_ = lean_uint64_shift_right(v___x_2698_, v___x_2699_);
v_fold_2701_ = lean_uint64_xor(v___x_2698_, v___x_2700_);
v___x_2702_ = 16ULL;
v___x_2703_ = lean_uint64_shift_right(v_fold_2701_, v___x_2702_);
v___x_2704_ = lean_uint64_xor(v_fold_2701_, v___x_2703_);
v___x_2705_ = lean_uint64_to_usize(v___x_2704_);
v___x_2706_ = lean_usize_of_nat(v___x_2697_);
v___x_2707_ = ((size_t)1ULL);
v___x_2708_ = lean_usize_sub(v___x_2706_, v___x_2707_);
v___x_2709_ = lean_usize_land(v___x_2705_, v___x_2708_);
v___x_2710_ = lean_array_uget_borrowed(v_buckets_2696_, v___x_2709_);
v___x_2711_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2695_, v___x_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg___boxed(lean_object* v_m_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2712_, v_a_2713_);
lean_dec_ref(v_a_2713_);
lean_dec_ref(v_m_2712_);
return v_res_2714_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(lean_object* v_a_2715_, lean_object* v_x_2716_){
_start:
{
if (lean_obj_tag(v_x_2716_) == 0)
{
uint8_t v___x_2717_; 
v___x_2717_ = 0;
return v___x_2717_;
}
else
{
lean_object* v_key_2718_; lean_object* v_tail_2719_; uint8_t v___x_2720_; 
v_key_2718_ = lean_ctor_get(v_x_2716_, 0);
v_tail_2719_ = lean_ctor_get(v_x_2716_, 2);
v___x_2720_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2718_, v_a_2715_);
if (v___x_2720_ == 0)
{
v_x_2716_ = v_tail_2719_;
goto _start;
}
else
{
return v___x_2720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg___boxed(lean_object* v_a_2722_, lean_object* v_x_2723_){
_start:
{
uint8_t v_res_2724_; lean_object* v_r_2725_; 
v_res_2724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2722_, v_x_2723_);
lean_dec(v_x_2723_);
lean_dec_ref(v_a_2722_);
v_r_2725_ = lean_box(v_res_2724_);
return v_r_2725_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(lean_object* v_m_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v_buckets_2728_; lean_object* v___x_2729_; uint64_t v___x_2730_; uint64_t v___x_2731_; uint64_t v___x_2732_; uint64_t v_fold_2733_; uint64_t v___x_2734_; uint64_t v___x_2735_; uint64_t v___x_2736_; size_t v___x_2737_; size_t v___x_2738_; size_t v___x_2739_; size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_buckets_2728_ = lean_ctor_get(v_m_2726_, 1);
v___x_2729_ = lean_array_get_size(v_buckets_2728_);
v___x_2730_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2727_);
v___x_2731_ = 32ULL;
v___x_2732_ = lean_uint64_shift_right(v___x_2730_, v___x_2731_);
v_fold_2733_ = lean_uint64_xor(v___x_2730_, v___x_2732_);
v___x_2734_ = 16ULL;
v___x_2735_ = lean_uint64_shift_right(v_fold_2733_, v___x_2734_);
v___x_2736_ = lean_uint64_xor(v_fold_2733_, v___x_2735_);
v___x_2737_ = lean_uint64_to_usize(v___x_2736_);
v___x_2738_ = lean_usize_of_nat(v___x_2729_);
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_sub(v___x_2738_, v___x_2739_);
v___x_2741_ = lean_usize_land(v___x_2737_, v___x_2740_);
v___x_2742_ = lean_array_uget_borrowed(v_buckets_2728_, v___x_2741_);
v___x_2743_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2727_, v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg___boxed(lean_object* v_m_2744_, lean_object* v_a_2745_){
_start:
{
uint8_t v_res_2746_; lean_object* v_r_2747_; 
v_res_2746_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2744_, v_a_2745_);
lean_dec_ref(v_a_2745_);
lean_dec_ref(v_m_2744_);
v_r_2747_ = lean_box(v_res_2746_);
return v_r_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(lean_object* v_idMap_2748_, lean_object* v_a_2749_){
_start:
{
uint8_t v___x_2750_; 
v___x_2750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_idMap_2748_, v_a_2749_);
if (v___x_2750_ == 0)
{
return v_a_2749_;
}
else
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_idMap_2748_, v_a_2749_);
lean_dec_ref(v_a_2749_);
v_a_2749_ = v___x_2751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg___boxed(lean_object* v_idMap_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2753_, v_a_2754_);
lean_dec_ref(v_idMap_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(lean_object* v_idMap_2756_, lean_object* v_id_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2756_, v_id_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative___boxed(lean_object* v_idMap_2759_, lean_object* v_id_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative(v_idMap_2759_, v_id_2760_);
lean_dec_ref(v_idMap_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(lean_object* v_00_u03b2_2762_, lean_object* v_m_2763_, lean_object* v_a_2764_){
_start:
{
uint8_t v___x_2765_; 
v___x_2765_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v_m_2763_, v_a_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___boxed(lean_object* v_00_u03b2_2766_, lean_object* v_m_2767_, lean_object* v_a_2768_){
_start:
{
uint8_t v_res_2769_; lean_object* v_r_2770_; 
v_res_2769_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0(v_00_u03b2_2766_, v_m_2767_, v_a_2768_);
lean_dec_ref(v_a_2768_);
lean_dec_ref(v_m_2767_);
v_r_2770_ = lean_box(v_res_2769_);
return v_r_2770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(lean_object* v_00_u03b2_2771_, lean_object* v_m_2772_, lean_object* v_a_2773_, lean_object* v_hma_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___redArg(v_m_2772_, v_a_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1___boxed(lean_object* v_00_u03b2_2776_, lean_object* v_m_2777_, lean_object* v_a_2778_, lean_object* v_hma_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1(v_00_u03b2_2776_, v_m_2777_, v_a_2778_, v_hma_2779_);
lean_dec_ref(v_a_2778_);
lean_dec_ref(v_m_2777_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(lean_object* v_idMap_2781_, lean_object* v_inst_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_2781_, v_a_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___boxed(lean_object* v_idMap_2785_, lean_object* v_inst_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2(v_idMap_2785_, v_inst_2786_, v_a_2787_);
lean_dec_ref(v_idMap_2785_);
return v_res_2788_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(lean_object* v_00_u03b2_2789_, lean_object* v_a_2790_, lean_object* v_x_2791_){
_start:
{
uint8_t v___x_2792_; 
v___x_2792_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2790_, v_x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2793_, lean_object* v_a_2794_, lean_object* v_x_2795_){
_start:
{
uint8_t v_res_2796_; lean_object* v_r_2797_; 
v_res_2796_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0(v_00_u03b2_2793_, v_a_2794_, v_x_2795_);
lean_dec(v_x_2795_);
lean_dec_ref(v_a_2794_);
v_r_2797_ = lean_box(v_res_2796_);
return v_r_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(lean_object* v_00_u03b2_2798_, lean_object* v_a_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___redArg(v_a_2799_, v_x_2800_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2803_, lean_object* v_a_2804_, lean_object* v_x_2805_, lean_object* v_x_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__1_spec__2(v_00_u03b2_2803_, v_a_2804_, v_x_2805_, v_x_2806_);
lean_dec(v_x_2805_);
lean_dec_ref(v_a_2804_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
if (lean_obj_tag(v_a_2808_) == 0)
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_a_2809_);
return v___x_2810_;
}
else
{
if (lean_obj_tag(v_a_2809_) == 0)
{
lean_object* v_tail_2811_; 
v_tail_2811_ = lean_ctor_get(v_a_2808_, 2);
lean_inc(v_tail_2811_);
lean_dec_ref_known(v_a_2808_, 3);
v_a_2808_ = v_tail_2811_;
goto _start;
}
else
{
lean_object* v_key_2813_; 
v_key_2813_ = lean_ctor_get(v_a_2808_, 0);
if (lean_obj_tag(v_key_2813_) == 0)
{
lean_object* v_tail_2814_; 
lean_inc_ref(v_key_2813_);
lean_dec_ref_known(v_a_2809_, 2);
v_tail_2814_ = lean_ctor_get(v_a_2808_, 2);
lean_inc(v_tail_2814_);
lean_dec_ref_known(v_a_2808_, 3);
v_a_2808_ = v_tail_2814_;
v_a_2809_ = v_key_2813_;
goto _start;
}
else
{
lean_object* v_tail_2816_; 
v_tail_2816_ = lean_ctor_get(v_a_2808_, 2);
lean_inc(v_tail_2816_);
lean_dec_ref_known(v_a_2808_, 3);
v_a_2808_ = v_tail_2816_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(lean_object* v_as_2818_, size_t v_sz_2819_, size_t v_i_2820_, lean_object* v_b_2821_){
_start:
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_usize_dec_lt(v_i_2820_, v_sz_2819_);
if (v___x_2822_ == 0)
{
return v_b_2821_;
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2824_; 
v_a_2823_ = lean_array_uget_borrowed(v_as_2818_, v_i_2820_);
lean_inc(v_a_2823_);
v___x_2824_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__4(v_a_2823_, v_b_2821_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
return v_a_2825_;
}
else
{
lean_object* v_a_2826_; size_t v___x_2827_; size_t v___x_2828_; 
v_a_2826_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2824_, 1);
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_add(v_i_2820_, v___x_2827_);
v_i_2820_ = v___x_2828_;
v_b_2821_ = v_a_2826_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5___boxed(lean_object* v_as_2830_, lean_object* v_sz_2831_, lean_object* v_i_2832_, lean_object* v_b_2833_){
_start:
{
size_t v_sz_boxed_2834_; size_t v_i_boxed_2835_; lean_object* v_res_2836_; 
v_sz_boxed_2834_ = lean_unbox_usize(v_sz_2831_);
lean_dec(v_sz_2831_);
v_i_boxed_2835_ = lean_unbox_usize(v_i_2832_);
lean_dec(v_i_2832_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_as_2830_, v_sz_boxed_2834_, v_i_boxed_2835_, v_b_2833_);
lean_dec_ref(v_as_2830_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(lean_object* v_a_2837_, lean_object* v_b_2838_, lean_object* v_x_2839_){
_start:
{
if (lean_obj_tag(v_x_2839_) == 0)
{
lean_dec(v_b_2838_);
lean_dec_ref(v_a_2837_);
return v_x_2839_;
}
else
{
lean_object* v_key_2840_; lean_object* v_value_2841_; lean_object* v_tail_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2854_; 
v_key_2840_ = lean_ctor_get(v_x_2839_, 0);
v_value_2841_ = lean_ctor_get(v_x_2839_, 1);
v_tail_2842_ = lean_ctor_get(v_x_2839_, 2);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_x_2839_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2844_ = v_x_2839_;
v_isShared_2845_ = v_isSharedCheck_2854_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_tail_2842_);
lean_inc(v_value_2841_);
lean_inc(v_key_2840_);
lean_dec(v_x_2839_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2854_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
uint8_t v___x_2846_; 
v___x_2846_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2840_, v_a_2837_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2847_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2837_, v_b_2838_, v_tail_2842_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 2, v___x_2847_);
v___x_2849_ = v___x_2844_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_key_2840_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_value_2841_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
else
{
lean_object* v___x_2852_; 
lean_dec(v_value_2841_);
lean_dec(v_key_2840_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v_b_2838_);
lean_ctor_set(v___x_2844_, 0, v_a_2837_);
v___x_2852_ = v___x_2844_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2837_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_b_2838_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_tail_2842_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(lean_object* v_x_2855_, lean_object* v_x_2856_){
_start:
{
if (lean_obj_tag(v_x_2856_) == 0)
{
return v_x_2855_;
}
else
{
lean_object* v_key_2857_; lean_object* v_value_2858_; lean_object* v_tail_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2882_; 
v_key_2857_ = lean_ctor_get(v_x_2856_, 0);
v_value_2858_ = lean_ctor_get(v_x_2856_, 1);
v_tail_2859_ = lean_ctor_get(v_x_2856_, 2);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_x_2856_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2861_ = v_x_2856_;
v_isShared_2862_ = v_isSharedCheck_2882_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_tail_2859_);
lean_inc(v_value_2858_);
lean_inc(v_key_2857_);
lean_dec(v_x_2856_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2882_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; uint64_t v___x_2864_; uint64_t v___x_2865_; uint64_t v___x_2866_; uint64_t v_fold_2867_; uint64_t v___x_2868_; uint64_t v___x_2869_; uint64_t v___x_2870_; size_t v___x_2871_; size_t v___x_2872_; size_t v___x_2873_; size_t v___x_2874_; size_t v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2863_ = lean_array_get_size(v_x_2855_);
v___x_2864_ = l_Lean_Lsp_instHashableRefIdent_hash(v_key_2857_);
v___x_2865_ = 32ULL;
v___x_2866_ = lean_uint64_shift_right(v___x_2864_, v___x_2865_);
v_fold_2867_ = lean_uint64_xor(v___x_2864_, v___x_2866_);
v___x_2868_ = 16ULL;
v___x_2869_ = lean_uint64_shift_right(v_fold_2867_, v___x_2868_);
v___x_2870_ = lean_uint64_xor(v_fold_2867_, v___x_2869_);
v___x_2871_ = lean_uint64_to_usize(v___x_2870_);
v___x_2872_ = lean_usize_of_nat(v___x_2863_);
v___x_2873_ = ((size_t)1ULL);
v___x_2874_ = lean_usize_sub(v___x_2872_, v___x_2873_);
v___x_2875_ = lean_usize_land(v___x_2871_, v___x_2874_);
v___x_2876_ = lean_array_uget_borrowed(v_x_2855_, v___x_2875_);
lean_inc(v___x_2876_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 2, v___x_2876_);
v___x_2878_ = v___x_2861_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_key_2857_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_value_2858_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2879_; 
v___x_2879_ = lean_array_uset(v_x_2855_, v___x_2875_, v___x_2878_);
v_x_2855_ = v___x_2879_;
v_x_2856_ = v_tail_2859_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(lean_object* v_i_2883_, lean_object* v_source_2884_, lean_object* v_target_2885_){
_start:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = lean_array_get_size(v_source_2884_);
v___x_2887_ = lean_nat_dec_lt(v_i_2883_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_dec_ref(v_source_2884_);
lean_dec(v_i_2883_);
return v_target_2885_;
}
else
{
lean_object* v_es_2888_; lean_object* v___x_2889_; lean_object* v_source_2890_; lean_object* v_target_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_es_2888_ = lean_array_fget(v_source_2884_, v_i_2883_);
v___x_2889_ = lean_box(0);
v_source_2890_ = lean_array_fset(v_source_2884_, v_i_2883_, v___x_2889_);
v_target_2891_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_target_2885_, v_es_2888_);
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_nat_add(v_i_2883_, v___x_2892_);
lean_dec(v_i_2883_);
v_i_2883_ = v___x_2893_;
v_source_2884_ = v_source_2890_;
v_target_2885_ = v_target_2891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(lean_object* v_data_2895_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v_nbuckets_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2896_ = lean_array_get_size(v_data_2895_);
v___x_2897_ = lean_unsigned_to_nat(2u);
v_nbuckets_2898_ = lean_nat_mul(v___x_2896_, v___x_2897_);
v___x_2899_ = lean_unsigned_to_nat(0u);
v___x_2900_ = lean_box(0);
v___x_2901_ = lean_mk_array(v_nbuckets_2898_, v___x_2900_);
v___x_2902_ = lean_array_propagate_mark(v_data_2895_, v___x_2901_);
v___x_2903_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2899_, v_data_2895_, v___x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object* v_m_2904_, lean_object* v_a_2905_, lean_object* v_b_2906_){
_start:
{
lean_object* v_size_2907_; lean_object* v_buckets_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2951_; 
v_size_2907_ = lean_ctor_get(v_m_2904_, 0);
v_buckets_2908_ = lean_ctor_get(v_m_2904_, 1);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_m_2904_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2910_ = v_m_2904_;
v_isShared_2911_ = v_isSharedCheck_2951_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_buckets_2908_);
lean_inc(v_size_2907_);
lean_dec(v_m_2904_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2951_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; uint64_t v___x_2913_; uint64_t v___x_2914_; uint64_t v___x_2915_; uint64_t v_fold_2916_; uint64_t v___x_2917_; uint64_t v___x_2918_; uint64_t v___x_2919_; size_t v___x_2920_; size_t v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; lean_object* v_bkt_2925_; uint8_t v___x_2926_; 
v___x_2912_ = lean_array_get_size(v_buckets_2908_);
v___x_2913_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2905_);
v___x_2914_ = 32ULL;
v___x_2915_ = lean_uint64_shift_right(v___x_2913_, v___x_2914_);
v_fold_2916_ = lean_uint64_xor(v___x_2913_, v___x_2915_);
v___x_2917_ = 16ULL;
v___x_2918_ = lean_uint64_shift_right(v_fold_2916_, v___x_2917_);
v___x_2919_ = lean_uint64_xor(v_fold_2916_, v___x_2918_);
v___x_2920_ = lean_uint64_to_usize(v___x_2919_);
v___x_2921_ = lean_usize_of_nat(v___x_2912_);
v___x_2922_ = ((size_t)1ULL);
v___x_2923_ = lean_usize_sub(v___x_2921_, v___x_2922_);
v___x_2924_ = lean_usize_land(v___x_2920_, v___x_2923_);
v_bkt_2925_ = lean_array_uget_borrowed(v_buckets_2908_, v___x_2924_);
v___x_2926_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2905_, v_bkt_2925_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v_size_x27_2928_; lean_object* v___x_2929_; lean_object* v_buckets_x27_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2927_ = lean_unsigned_to_nat(1u);
v_size_x27_2928_ = lean_nat_add(v_size_2907_, v___x_2927_);
lean_dec(v_size_2907_);
lean_inc(v_bkt_2925_);
v___x_2929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2929_, 0, v_a_2905_);
lean_ctor_set(v___x_2929_, 1, v_b_2906_);
lean_ctor_set(v___x_2929_, 2, v_bkt_2925_);
v_buckets_x27_2930_ = lean_array_uset(v_buckets_2908_, v___x_2924_, v___x_2929_);
v___x_2931_ = lean_unsigned_to_nat(4u);
v___x_2932_ = lean_nat_mul(v_size_x27_2928_, v___x_2931_);
v___x_2933_ = lean_unsigned_to_nat(3u);
v___x_2934_ = lean_nat_div(v___x_2932_, v___x_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_array_get_size(v_buckets_x27_2930_);
v___x_2936_ = lean_nat_dec_le(v___x_2934_, v___x_2935_);
lean_dec(v___x_2934_);
if (v___x_2936_ == 0)
{
lean_object* v_val_2937_; lean_object* v___x_2939_; 
v_val_2937_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_2930_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v_val_2937_);
lean_ctor_set(v___x_2910_, 0, v_size_x27_2928_);
v___x_2939_ = v___x_2910_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_size_x27_2928_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_val_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
else
{
lean_object* v___x_2942_; 
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v_buckets_x27_2930_);
lean_ctor_set(v___x_2910_, 0, v_size_x27_2928_);
v___x_2942_ = v___x_2910_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_size_x27_2928_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_buckets_x27_2930_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v___x_2944_; lean_object* v_buckets_x27_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
lean_inc(v_bkt_2925_);
v___x_2944_ = lean_box(0);
v_buckets_x27_2945_ = lean_array_uset(v_buckets_2908_, v___x_2924_, v___x_2944_);
v___x_2946_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2905_, v_b_2906_, v_bkt_2925_);
v___x_2947_ = lean_array_uset(v_buckets_x27_2945_, v___x_2924_, v___x_2946_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v___x_2947_);
v___x_2949_ = v___x_2910_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_size_2907_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object* v___x_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
if (lean_obj_tag(v_a_2953_) == 0)
{
lean_object* v___x_2955_; 
lean_dec_ref(v___x_2952_);
v___x_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2955_, 0, v_a_2954_);
return v___x_2955_;
}
else
{
lean_object* v_key_2956_; lean_object* v_tail_2957_; uint8_t v___x_2958_; 
v_key_2956_ = lean_ctor_get(v_a_2953_, 0);
lean_inc(v_key_2956_);
v_tail_2957_ = lean_ctor_get(v_a_2953_, 2);
lean_inc(v_tail_2957_);
lean_dec_ref_known(v_a_2953_, 3);
v___x_2958_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_2956_, v___x_2952_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; 
lean_inc_ref(v___x_2952_);
v___x_2959_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_2954_, v_key_2956_, v___x_2952_);
v_a_2953_ = v_tail_2957_;
v_a_2954_ = v___x_2959_;
goto _start;
}
else
{
lean_dec(v_key_2956_);
v_a_2953_ = v_tail_2957_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object* v___x_2962_, lean_object* v_as_2963_, size_t v_sz_2964_, size_t v_i_2965_, lean_object* v_b_2966_){
_start:
{
uint8_t v___x_2967_; 
v___x_2967_ = lean_usize_dec_lt(v_i_2965_, v_sz_2964_);
if (v___x_2967_ == 0)
{
lean_dec_ref(v___x_2962_);
return v_b_2966_;
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2969_; 
v_a_2968_ = lean_array_uget_borrowed(v_as_2963_, v_i_2965_);
lean_inc(v_a_2968_);
lean_inc_ref(v___x_2962_);
v___x_2969_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(v___x_2962_, v_a_2968_, v_b_2966_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; 
lean_dec_ref(v___x_2962_);
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
return v_a_2970_;
}
else
{
lean_object* v_a_2971_; size_t v___x_2972_; size_t v___x_2973_; 
v_a_2971_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2972_ = ((size_t)1ULL);
v___x_2973_ = lean_usize_add(v_i_2965_, v___x_2972_);
v_i_2965_ = v___x_2973_;
v_b_2966_ = v_a_2971_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object* v___x_2975_, lean_object* v_as_2976_, lean_object* v_sz_2977_, lean_object* v_i_2978_, lean_object* v_b_2979_){
_start:
{
size_t v_sz_boxed_2980_; size_t v_i_boxed_2981_; lean_object* v_res_2982_; 
v_sz_boxed_2980_ = lean_unbox_usize(v_sz_2977_);
lean_dec(v_sz_2977_);
v_i_boxed_2981_ = lean_unbox_usize(v_i_2978_);
lean_dec(v_i_2978_);
v_res_2982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_2975_, v_as_2976_, v_sz_boxed_2980_, v_i_boxed_2981_, v_b_2979_);
lean_dec_ref(v_as_2976_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
if (lean_obj_tag(v_a_2983_) == 0)
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_a_2984_);
return v___x_2985_;
}
else
{
lean_object* v_value_2986_; lean_object* v_key_2987_; lean_object* v_tail_2988_; lean_object* v_buckets_2989_; size_t v_sz_2990_; size_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_value_2986_ = lean_ctor_get(v_a_2983_, 1);
lean_inc(v_value_2986_);
v_key_2987_ = lean_ctor_get(v_a_2983_, 0);
lean_inc(v_key_2987_);
v_tail_2988_ = lean_ctor_get(v_a_2983_, 2);
lean_inc(v_tail_2988_);
lean_dec_ref_known(v_a_2983_, 3);
v_buckets_2989_ = lean_ctor_get(v_value_2986_, 1);
lean_inc_ref(v_buckets_2989_);
lean_dec(v_value_2986_);
v_sz_2990_ = lean_array_size(v_buckets_2989_);
v___x_2991_ = ((size_t)0ULL);
v___x_2992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_buckets_2989_, v_sz_2990_, v___x_2991_, v_key_2987_);
v___x_2993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_2992_, v_buckets_2989_, v_sz_2990_, v___x_2991_, v_a_2984_);
lean_dec_ref(v_buckets_2989_);
v_a_2983_ = v_tail_2988_;
v_a_2984_ = v___x_2993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object* v_as_2995_, size_t v_sz_2996_, size_t v_i_2997_, lean_object* v_b_2998_){
_start:
{
uint8_t v___x_2999_; 
v___x_2999_ = lean_usize_dec_lt(v_i_2997_, v_sz_2996_);
if (v___x_2999_ == 0)
{
return v_b_2998_;
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3001_; 
v_a_3000_ = lean_array_uget_borrowed(v_as_2995_, v_i_2997_);
lean_inc(v_a_3000_);
v___x_3001_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(v_a_3000_, v_b_2998_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
return v_a_3002_;
}
else
{
lean_object* v_a_3003_; size_t v___x_3004_; size_t v___x_3005_; 
v_a_3003_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3004_ = ((size_t)1ULL);
v___x_3005_ = lean_usize_add(v_i_2997_, v___x_3004_);
v_i_2997_ = v___x_3005_;
v_b_2998_ = v_a_3003_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object* v_as_3007_, lean_object* v_sz_3008_, lean_object* v_i_3009_, lean_object* v_b_3010_){
_start:
{
size_t v_sz_boxed_3011_; size_t v_i_boxed_3012_; lean_object* v_res_3013_; 
v_sz_boxed_3011_ = lean_unbox_usize(v_sz_3008_);
lean_dec(v_sz_3008_);
v_i_boxed_3012_ = lean_unbox_usize(v_i_3009_);
lean_dec(v_i_3009_);
v_res_3013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_as_3007_, v_sz_boxed_3011_, v_i_boxed_3012_, v_b_3010_);
lean_dec_ref(v_as_3007_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object* v_a_3014_, lean_object* v_x_3015_){
_start:
{
if (lean_obj_tag(v_x_3015_) == 0)
{
return v_x_3015_;
}
else
{
lean_object* v_key_3016_; lean_object* v_value_3017_; lean_object* v_tail_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3027_; 
v_key_3016_ = lean_ctor_get(v_x_3015_, 0);
v_value_3017_ = lean_ctor_get(v_x_3015_, 1);
v_tail_3018_ = lean_ctor_get(v_x_3015_, 2);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_x_3015_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3020_ = v_x_3015_;
v_isShared_3021_ = v_isSharedCheck_3027_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_tail_3018_);
lean_inc(v_value_3017_);
lean_inc(v_key_3016_);
lean_dec(v_x_3015_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3027_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
uint8_t v___x_3022_; 
v___x_3022_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3016_, v_a_3014_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3014_, v_tail_3018_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 2, v___x_3023_);
v___x_3025_ = v___x_3020_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_key_3016_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_value_3017_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
else
{
lean_del_object(v___x_3020_);
lean_dec(v_value_3017_);
lean_dec(v_key_3016_);
return v_tail_3018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object* v_a_3028_, lean_object* v_x_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3028_, v_x_3029_);
lean_dec_ref(v_a_3028_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object* v_m_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_size_3033_; lean_object* v_buckets_3034_; lean_object* v___x_3035_; uint64_t v___x_3036_; uint64_t v___x_3037_; uint64_t v___x_3038_; uint64_t v_fold_3039_; uint64_t v___x_3040_; uint64_t v___x_3041_; uint64_t v___x_3042_; size_t v___x_3043_; size_t v___x_3044_; size_t v___x_3045_; size_t v___x_3046_; size_t v___x_3047_; lean_object* v_bkt_3048_; uint8_t v___x_3049_; 
v_size_3033_ = lean_ctor_get(v_m_3031_, 0);
v_buckets_3034_ = lean_ctor_get(v_m_3031_, 1);
v___x_3035_ = lean_array_get_size(v_buckets_3034_);
v___x_3036_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3032_);
v___x_3037_ = 32ULL;
v___x_3038_ = lean_uint64_shift_right(v___x_3036_, v___x_3037_);
v_fold_3039_ = lean_uint64_xor(v___x_3036_, v___x_3038_);
v___x_3040_ = 16ULL;
v___x_3041_ = lean_uint64_shift_right(v_fold_3039_, v___x_3040_);
v___x_3042_ = lean_uint64_xor(v_fold_3039_, v___x_3041_);
v___x_3043_ = lean_uint64_to_usize(v___x_3042_);
v___x_3044_ = lean_usize_of_nat(v___x_3035_);
v___x_3045_ = ((size_t)1ULL);
v___x_3046_ = lean_usize_sub(v___x_3044_, v___x_3045_);
v___x_3047_ = lean_usize_land(v___x_3043_, v___x_3046_);
v_bkt_3048_ = lean_array_uget_borrowed(v_buckets_3034_, v___x_3047_);
v___x_3049_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3032_, v_bkt_3048_);
if (v___x_3049_ == 0)
{
return v_m_3031_;
}
else
{
lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3062_; 
lean_inc(v_bkt_3048_);
lean_inc_ref(v_buckets_3034_);
lean_inc(v_size_3033_);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_m_3031_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; lean_object* v_unused_3064_; 
v_unused_3063_ = lean_ctor_get(v_m_3031_, 1);
lean_dec(v_unused_3063_);
v_unused_3064_ = lean_ctor_get(v_m_3031_, 0);
lean_dec(v_unused_3064_);
v___x_3051_ = v_m_3031_;
v_isShared_3052_ = v_isSharedCheck_3062_;
goto v_resetjp_3050_;
}
else
{
lean_dec(v_m_3031_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3062_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v_buckets_x27_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3053_ = lean_box(0);
v_buckets_x27_3054_ = lean_array_uset(v_buckets_3034_, v___x_3047_, v___x_3053_);
v___x_3055_ = lean_unsigned_to_nat(1u);
v___x_3056_ = lean_nat_sub(v_size_3033_, v___x_3055_);
lean_dec(v_size_3033_);
v___x_3057_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3032_, v_bkt_3048_);
v___x_3058_ = lean_array_uset(v_buckets_x27_3054_, v___x_3047_, v___x_3057_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 1, v___x_3058_);
lean_ctor_set(v___x_3051_, 0, v___x_3056_);
v___x_3060_ = v___x_3051_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object* v_m_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3065_, v_a_3066_);
lean_dec_ref(v_a_3066_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object* v_m_3068_, lean_object* v_a_3069_, lean_object* v_b_3070_){
_start:
{
lean_object* v_size_3071_; lean_object* v_buckets_3072_; lean_object* v___x_3073_; uint64_t v___x_3074_; uint64_t v___x_3075_; uint64_t v___x_3076_; uint64_t v_fold_3077_; uint64_t v___x_3078_; uint64_t v___x_3079_; uint64_t v___x_3080_; size_t v___x_3081_; size_t v___x_3082_; size_t v___x_3083_; size_t v___x_3084_; size_t v___x_3085_; lean_object* v_bkt_3086_; uint8_t v___x_3087_; 
v_size_3071_ = lean_ctor_get(v_m_3068_, 0);
v_buckets_3072_ = lean_ctor_get(v_m_3068_, 1);
v___x_3073_ = lean_array_get_size(v_buckets_3072_);
v___x_3074_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3069_);
v___x_3075_ = 32ULL;
v___x_3076_ = lean_uint64_shift_right(v___x_3074_, v___x_3075_);
v_fold_3077_ = lean_uint64_xor(v___x_3074_, v___x_3076_);
v___x_3078_ = 16ULL;
v___x_3079_ = lean_uint64_shift_right(v_fold_3077_, v___x_3078_);
v___x_3080_ = lean_uint64_xor(v_fold_3077_, v___x_3079_);
v___x_3081_ = lean_uint64_to_usize(v___x_3080_);
v___x_3082_ = lean_usize_of_nat(v___x_3073_);
v___x_3083_ = ((size_t)1ULL);
v___x_3084_ = lean_usize_sub(v___x_3082_, v___x_3083_);
v___x_3085_ = lean_usize_land(v___x_3081_, v___x_3084_);
v_bkt_3086_ = lean_array_uget_borrowed(v_buckets_3072_, v___x_3085_);
v___x_3087_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3069_, v_bkt_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3108_; 
lean_inc_ref(v_buckets_3072_);
lean_inc(v_size_3071_);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_m_3068_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; lean_object* v_unused_3110_; 
v_unused_3109_ = lean_ctor_get(v_m_3068_, 1);
lean_dec(v_unused_3109_);
v_unused_3110_ = lean_ctor_get(v_m_3068_, 0);
lean_dec(v_unused_3110_);
v___x_3089_ = v_m_3068_;
v_isShared_3090_ = v_isSharedCheck_3108_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v_m_3068_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3108_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v_size_x27_3092_; lean_object* v___x_3093_; lean_object* v_buckets_x27_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3091_ = lean_unsigned_to_nat(1u);
v_size_x27_3092_ = lean_nat_add(v_size_3071_, v___x_3091_);
lean_dec(v_size_3071_);
lean_inc(v_bkt_3086_);
v___x_3093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3093_, 0, v_a_3069_);
lean_ctor_set(v___x_3093_, 1, v_b_3070_);
lean_ctor_set(v___x_3093_, 2, v_bkt_3086_);
v_buckets_x27_3094_ = lean_array_uset(v_buckets_3072_, v___x_3085_, v___x_3093_);
v___x_3095_ = lean_unsigned_to_nat(4u);
v___x_3096_ = lean_nat_mul(v_size_x27_3092_, v___x_3095_);
v___x_3097_ = lean_unsigned_to_nat(3u);
v___x_3098_ = lean_nat_div(v___x_3096_, v___x_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_array_get_size(v_buckets_x27_3094_);
v___x_3100_ = lean_nat_dec_le(v___x_3098_, v___x_3099_);
lean_dec(v___x_3098_);
if (v___x_3100_ == 0)
{
lean_object* v_val_3101_; lean_object* v___x_3103_; 
v_val_3101_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3094_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 1, v_val_3101_);
lean_ctor_set(v___x_3089_, 0, v_size_x27_3092_);
v___x_3103_ = v___x_3089_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_size_x27_3092_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_val_3101_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
else
{
lean_object* v___x_3106_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 1, v_buckets_x27_3094_);
lean_ctor_set(v___x_3089_, 0, v_size_x27_3092_);
v___x_3106_ = v___x_3089_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_size_x27_3092_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_buckets_x27_3094_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_dec(v_b_3070_);
lean_dec_ref(v_a_3069_);
return v_m_3068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object* v_a_3111_, lean_object* v_fallback_3112_, lean_object* v_x_3113_){
_start:
{
if (lean_obj_tag(v_x_3113_) == 0)
{
lean_inc(v_fallback_3112_);
return v_fallback_3112_;
}
else
{
lean_object* v_key_3114_; lean_object* v_value_3115_; lean_object* v_tail_3116_; uint8_t v___x_3117_; 
v_key_3114_ = lean_ctor_get(v_x_3113_, 0);
v_value_3115_ = lean_ctor_get(v_x_3113_, 1);
v_tail_3116_ = lean_ctor_get(v_x_3113_, 2);
v___x_3117_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3114_, v_a_3111_);
if (v___x_3117_ == 0)
{
v_x_3113_ = v_tail_3116_;
goto _start;
}
else
{
lean_inc(v_value_3115_);
return v_value_3115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object* v_a_3119_, lean_object* v_fallback_3120_, lean_object* v_x_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3119_, v_fallback_3120_, v_x_3121_);
lean_dec(v_x_3121_);
lean_dec(v_fallback_3120_);
lean_dec_ref(v_a_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object* v_m_3123_, lean_object* v_a_3124_, lean_object* v_fallback_3125_){
_start:
{
lean_object* v_buckets_3126_; lean_object* v___x_3127_; uint64_t v___x_3128_; uint64_t v___x_3129_; uint64_t v___x_3130_; uint64_t v_fold_3131_; uint64_t v___x_3132_; uint64_t v___x_3133_; uint64_t v___x_3134_; size_t v___x_3135_; size_t v___x_3136_; size_t v___x_3137_; size_t v___x_3138_; size_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_buckets_3126_ = lean_ctor_get(v_m_3123_, 1);
v___x_3127_ = lean_array_get_size(v_buckets_3126_);
v___x_3128_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3124_);
v___x_3129_ = 32ULL;
v___x_3130_ = lean_uint64_shift_right(v___x_3128_, v___x_3129_);
v_fold_3131_ = lean_uint64_xor(v___x_3128_, v___x_3130_);
v___x_3132_ = 16ULL;
v___x_3133_ = lean_uint64_shift_right(v_fold_3131_, v___x_3132_);
v___x_3134_ = lean_uint64_xor(v_fold_3131_, v___x_3133_);
v___x_3135_ = lean_uint64_to_usize(v___x_3134_);
v___x_3136_ = lean_usize_of_nat(v___x_3127_);
v___x_3137_ = ((size_t)1ULL);
v___x_3138_ = lean_usize_sub(v___x_3136_, v___x_3137_);
v___x_3139_ = lean_usize_land(v___x_3135_, v___x_3138_);
v___x_3140_ = lean_array_uget_borrowed(v_buckets_3126_, v___x_3139_);
v___x_3141_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3124_, v_fallback_3125_, v___x_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object* v_m_3142_, lean_object* v_a_3143_, lean_object* v_fallback_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3142_, v_a_3143_, v_fallback_3144_);
lean_dec(v_fallback_3144_);
lean_dec_ref(v_a_3143_);
lean_dec_ref(v_m_3142_);
return v_res_3145_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_unsigned_to_nat(16u);
v___x_3148_ = lean_mk_array(v___x_3147_, v___x_3146_);
return v___x_3148_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3149_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0);
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___x_3149_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object* v_idMap_3152_, lean_object* v_classesById_3153_, lean_object* v_id_3154_){
_start:
{
lean_object* v_representative_3155_; lean_object* v___x_3156_; lean_object* v_class_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v_class_3160_; lean_object* v___x_3161_; 
lean_inc_ref(v_id_3154_);
v_representative_3155_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_3152_, v_id_3154_);
v___x_3156_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_class_3157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_classesById_3153_, v_representative_3155_, v___x_3156_);
v___x_3158_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_classesById_3153_, v_representative_3155_);
v___x_3159_ = lean_box(0);
v_class_3160_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_class_3157_, v_id_3154_, v___x_3159_);
v___x_3161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v___x_3158_, v_representative_3155_, v_class_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object* v_idMap_3162_, lean_object* v_classesById_3163_, lean_object* v_id_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3162_, v_classesById_3163_, v_id_3164_);
lean_dec_ref(v_idMap_3162_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object* v_idMap_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
if (lean_obj_tag(v_a_3167_) == 0)
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_a_3168_);
return v___x_3169_;
}
else
{
lean_object* v_key_3170_; lean_object* v_value_3171_; lean_object* v_tail_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_key_3170_ = lean_ctor_get(v_a_3167_, 0);
lean_inc(v_key_3170_);
v_value_3171_ = lean_ctor_get(v_a_3167_, 1);
lean_inc(v_value_3171_);
v_tail_3172_ = lean_ctor_get(v_a_3167_, 2);
lean_inc(v_tail_3172_);
lean_dec_ref_known(v_a_3167_, 3);
v___x_3173_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3166_, v_a_3168_, v_key_3170_);
v___x_3174_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3166_, v___x_3173_, v_value_3171_);
v_a_3167_ = v_tail_3172_;
v_a_3168_ = v___x_3174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object* v_idMap_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3176_, v_a_3177_, v_a_3178_);
lean_dec_ref(v_idMap_3176_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object* v_idMap_3180_, lean_object* v_as_3181_, size_t v_sz_3182_, size_t v_i_3183_, lean_object* v_b_3184_){
_start:
{
uint8_t v___x_3185_; 
v___x_3185_ = lean_usize_dec_lt(v_i_3183_, v_sz_3182_);
if (v___x_3185_ == 0)
{
return v_b_3184_;
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3187_; 
v_a_3186_ = lean_array_uget_borrowed(v_as_3181_, v_i_3183_);
lean_inc(v_a_3186_);
v___x_3187_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3180_, v_a_3186_, v_b_3184_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
return v_a_3188_;
}
else
{
lean_object* v_a_3189_; size_t v___x_3190_; size_t v___x_3191_; 
v_a_3189_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3187_, 1);
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_add(v_i_3183_, v___x_3190_);
v_i_3183_ = v___x_3191_;
v_b_3184_ = v_a_3189_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object* v_idMap_3193_, lean_object* v_as_3194_, lean_object* v_sz_3195_, lean_object* v_i_3196_, lean_object* v_b_3197_){
_start:
{
size_t v_sz_boxed_3198_; size_t v_i_boxed_3199_; lean_object* v_res_3200_; 
v_sz_boxed_3198_ = lean_unbox_usize(v_sz_3195_);
lean_dec(v_sz_3195_);
v_i_boxed_3199_ = lean_unbox_usize(v_i_3196_);
lean_dec(v_i_3196_);
v_res_3200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3193_, v_as_3194_, v_sz_boxed_3198_, v_i_boxed_3199_, v_b_3197_);
lean_dec_ref(v_as_3194_);
lean_dec_ref(v_idMap_3193_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object* v_idMap_3201_){
_start:
{
lean_object* v_buckets_3202_; lean_object* v_classesById_3203_; size_t v_sz_3204_; size_t v___x_3205_; lean_object* v___x_3206_; lean_object* v_buckets_3207_; size_t v_sz_3208_; lean_object* v___x_3209_; 
v_buckets_3202_ = lean_ctor_get(v_idMap_3201_, 1);
v_classesById_3203_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_sz_3204_ = lean_array_size(v_buckets_3202_);
v___x_3205_ = ((size_t)0ULL);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3201_, v_buckets_3202_, v_sz_3204_, v___x_3205_, v_classesById_3203_);
v_buckets_3207_ = lean_ctor_get(v___x_3206_, 1);
lean_inc_ref(v_buckets_3207_);
lean_dec_ref(v___x_3206_);
v_sz_3208_ = lean_array_size(v_buckets_3207_);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_buckets_3207_, v_sz_3208_, v___x_3205_, v_classesById_3203_);
lean_dec_ref(v_buckets_3207_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object* v_idMap_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v_idMap_3210_);
lean_dec_ref(v_idMap_3210_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object* v_00_u03b2_3212_, lean_object* v_m_3213_, lean_object* v_a_3214_, lean_object* v_fallback_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3213_, v_a_3214_, v_fallback_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object* v_00_u03b2_3217_, lean_object* v_m_3218_, lean_object* v_a_3219_, lean_object* v_fallback_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(v_00_u03b2_3217_, v_m_3218_, v_a_3219_, v_fallback_3220_);
lean_dec(v_fallback_3220_);
lean_dec_ref(v_a_3219_);
lean_dec_ref(v_m_3218_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object* v_00_u03b2_3222_, lean_object* v_m_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3223_, v_a_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object* v_00_u03b2_3226_, lean_object* v_m_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(v_00_u03b2_3226_, v_m_3227_, v_a_3228_);
lean_dec_ref(v_a_3228_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object* v_00_u03b2_3230_, lean_object* v_m_3231_, lean_object* v_a_3232_, lean_object* v_b_3233_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_m_3231_, v_a_3232_, v_b_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object* v_00_u03b2_3235_, lean_object* v_m_3236_, lean_object* v_a_3237_, lean_object* v_b_3238_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_m_3236_, v_a_3237_, v_b_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object* v_00_u03b2_3240_, lean_object* v_a_3241_, lean_object* v_fallback_3242_, lean_object* v_x_3243_){
_start:
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3241_, v_fallback_3242_, v_x_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3245_, lean_object* v_a_3246_, lean_object* v_fallback_3247_, lean_object* v_x_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(v_00_u03b2_3245_, v_a_3246_, v_fallback_3247_, v_x_3248_);
lean_dec(v_x_3248_);
lean_dec(v_fallback_3247_);
lean_dec_ref(v_a_3246_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object* v_00_u03b2_3250_, lean_object* v_a_3251_, lean_object* v_x_3252_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3251_, v_x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3254_, lean_object* v_a_3255_, lean_object* v_x_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(v_00_u03b2_3254_, v_a_3255_, v_x_3256_);
lean_dec_ref(v_a_3255_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object* v_00_u03b2_3258_, lean_object* v_data_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_data_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object* v_00_u03b2_3261_, lean_object* v_a_3262_, lean_object* v_b_3263_, lean_object* v_x_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_3262_, v_b_3263_, v_x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3266_, lean_object* v_i_3267_, lean_object* v_source_3268_, lean_object* v_target_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v_i_3267_, v_source_3268_, v_target_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object* v_00_u03b2_3271_, lean_object* v_x_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_x_3272_, v_x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object* v_id_3275_, lean_object* v_baseId_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v___x_3278_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3277_, v_id_3275_);
v___x_3279_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3277_, v_baseId_3276_);
v___x_3280_ = l_Lean_Lsp_instBEqRefIdent_beq(v___x_3279_, v___x_3278_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_box(0);
v___x_3282_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3277_, v___x_3278_, v___x_3279_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
return v___x_3283_;
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec_ref(v___x_3279_);
lean_dec_ref(v___x_3278_);
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v_a_3277_);
return v___x_3285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object* v_ci_3286_, lean_object* v_info_3287_, lean_object* v_x_3288_, lean_object* v___y_3289_){
_start:
{
if (lean_obj_tag(v_info_3287_) == 11)
{
lean_object* v_toCommandContextInfo_3290_; lean_object* v_i_3291_; lean_object* v_env_3292_; lean_object* v___x_3293_; lean_object* v_mainModule_3294_; lean_object* v_id_3295_; lean_object* v_baseId_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_toCommandContextInfo_3290_ = lean_ctor_get(v_ci_3286_, 0);
v_i_3291_ = lean_ctor_get(v_info_3287_, 0);
lean_inc_ref(v_i_3291_);
lean_dec_ref_known(v_info_3287_, 1);
v_env_3292_ = lean_ctor_get(v_toCommandContextInfo_3290_, 0);
v___x_3293_ = l_Lean_Environment_header(v_env_3292_);
v_mainModule_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_mainModule_3294_);
lean_dec_ref(v___x_3293_);
v_id_3295_ = lean_ctor_get(v_i_3291_, 1);
lean_inc(v_id_3295_);
v_baseId_3296_ = lean_ctor_get(v_i_3291_, 2);
lean_inc(v_baseId_3296_);
lean_dec_ref(v_i_3291_);
v___x_3297_ = 1;
v___x_3298_ = l_Lean_Name_toString(v_mainModule_3294_, v___x_3297_);
v___x_3299_ = l_Lean_Name_toString(v_id_3295_, v___x_3297_);
lean_inc_ref(v___x_3298_);
v___x_3300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Lean_Name_toString(v_baseId_3296_, v___x_3297_);
v___x_3302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3298_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v___x_3300_, v___x_3302_, v___y_3289_);
return v___x_3303_;
}
else
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec_ref(v_info_3287_);
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v___y_3289_);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object* v_ci_3306_, lean_object* v_info_3307_, lean_object* v_x_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(v_ci_3306_, v_info_3307_, v_x_3308_, v___y_3309_);
lean_dec_ref(v_x_3308_);
lean_dec_ref(v_ci_3306_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object* v_x_3311_, lean_object* v_x_3312_, lean_object* v_x_3313_, lean_object* v___y_3314_){
_start:
{
uint8_t v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3315_ = 1;
v___x_3316_ = lean_box(v___x_3315_);
v___x_3317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v___y_3314_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object* v_x_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(v_x_3318_, v_x_3319_, v_x_3320_, v___y_3321_);
lean_dec_ref(v_x_3320_);
lean_dec_ref(v_x_3319_);
lean_dec_ref(v_x_3318_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___f_3325_; lean_object* v___f_3326_; lean_object* v___f_3327_; lean_object* v___f_3328_; lean_object* v___f_3329_; lean_object* v___f_3330_; lean_object* v___f_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___f_3335_; lean_object* v___f_3336_; lean_object* v___f_3337_; lean_object* v___f_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3750__overap_3347_; lean_object* v___x_3348_; 
v___f_3325_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3326_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3327_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3328_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3329_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3330_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3331_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___f_3325_);
lean_ctor_set(v___x_3332_, 1, v___f_3326_);
v___x_3333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
lean_ctor_set(v___x_3333_, 1, v___f_3327_);
lean_ctor_set(v___x_3333_, 2, v___f_3328_);
lean_ctor_set(v___x_3333_, 3, v___f_3329_);
lean_ctor_set(v___x_3333_, 4, v___f_3330_);
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_ctor_set(v___x_3334_, 1, v___f_3331_);
lean_inc_ref_n(v___x_3334_, 6);
v___f_3335_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3335_, 0, v___x_3334_);
v___f_3336_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3336_, 0, v___x_3334_);
v___f_3337_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3337_, 0, v___x_3334_);
v___f_3338_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3338_, 0, v___x_3334_);
v___x_3339_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3339_, 0, lean_box(0));
lean_closure_set(v___x_3339_, 1, lean_box(0));
lean_closure_set(v___x_3339_, 2, v___x_3334_);
v___x_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
lean_ctor_set(v___x_3340_, 1, v___f_3335_);
v___x_3341_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3341_, 0, lean_box(0));
lean_closure_set(v___x_3341_, 1, lean_box(0));
lean_closure_set(v___x_3341_, 2, v___x_3334_);
v___x_3342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
lean_ctor_set(v___x_3342_, 2, v___f_3336_);
lean_ctor_set(v___x_3342_, 3, v___f_3337_);
lean_ctor_set(v___x_3342_, 4, v___f_3338_);
v___x_3343_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3343_, 0, lean_box(0));
lean_closure_set(v___x_3343_, 1, lean_box(0));
lean_closure_set(v___x_3343_, 2, v___x_3334_);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = lean_box(0);
v___x_3346_ = l_instInhabitedOfMonad___redArg(v___x_3344_, v___x_3345_);
v___x_3750__overap_3347_ = lean_panic_fn_borrowed(v___x_3346_, v_msg_3323_);
lean_dec(v___x_3346_);
v___x_3348_ = lean_apply_1(v___x_3750__overap_3347_, v___y_3324_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3349_, lean_object* v_postNode_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v___y_3353_){
_start:
{
switch(lean_obj_tag(v_x_3352_))
{
case 0:
{
lean_object* v_i_3354_; lean_object* v_t_3355_; lean_object* v___x_3356_; 
v_i_3354_ = lean_ctor_get(v_x_3352_, 0);
lean_inc_ref(v_i_3354_);
v_t_3355_ = lean_ctor_get(v_x_3352_, 1);
lean_inc_ref(v_t_3355_);
lean_dec_ref_known(v_x_3352_, 2);
v___x_3356_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3354_, v_x_3351_);
v_x_3351_ = v___x_3356_;
v_x_3352_ = v_t_3355_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3351_) == 0)
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
lean_dec_ref_known(v_x_3352_, 2);
lean_dec_ref(v_postNode_3350_);
lean_dec_ref(v_preNode_3349_);
v___x_3358_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3359_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3358_, v___y_3353_);
return v___x_3359_;
}
else
{
lean_object* v_i_3360_; lean_object* v_children_3361_; lean_object* v_val_3362_; lean_object* v___x_3363_; lean_object* v_fst_3364_; uint8_t v___x_3365_; 
v_i_3360_ = lean_ctor_get(v_x_3352_, 0);
lean_inc_ref_n(v_i_3360_, 2);
v_children_3361_ = lean_ctor_get(v_x_3352_, 1);
lean_inc_ref_n(v_children_3361_, 2);
lean_dec_ref_known(v_x_3352_, 2);
v_val_3362_ = lean_ctor_get(v_x_3351_, 0);
lean_inc_n(v_val_3362_, 2);
lean_inc_ref(v_preNode_3349_);
v___x_3363_ = lean_apply_4(v_preNode_3349_, v_val_3362_, v_i_3360_, v_children_3361_, v___y_3353_);
v_fst_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_fst_3364_);
v___x_3365_ = lean_unbox(v_fst_3364_);
lean_dec(v_fst_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v_preNode_3349_);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_x_3351_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; 
v_unused_3385_ = lean_ctor_get(v_x_3351_, 0);
lean_dec(v_unused_3385_);
v___x_3367_ = v_x_3351_;
v_isShared_3368_ = v_isSharedCheck_3384_;
goto v_resetjp_3366_;
}
else
{
lean_dec(v_x_3351_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3384_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v_snd_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3383_; 
v_snd_3369_ = lean_ctor_get(v___x_3363_, 1);
lean_inc(v_snd_3369_);
lean_dec_ref(v___x_3363_);
v___x_3370_ = lean_box(0);
v___x_3371_ = lean_apply_5(v_postNode_3350_, v_val_3362_, v_i_3360_, v_children_3361_, v___x_3370_, v_snd_3369_);
v_fst_3372_ = lean_ctor_get(v___x_3371_, 0);
v_snd_3373_ = lean_ctor_get(v___x_3371_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3375_ = v___x_3371_;
v_isShared_3376_ = v_isSharedCheck_3383_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snd_3373_);
lean_inc(v_fst_3372_);
lean_dec(v___x_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3383_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v_fst_3372_);
v___x_3378_ = v___x_3367_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_fst_3372_);
v___x_3378_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3378_);
v___x_3380_ = v___x_3375_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_snd_3373_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
else
{
lean_object* v_snd_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v_fst_3391_; lean_object* v_snd_3392_; lean_object* v___x_3393_; lean_object* v_fst_3394_; lean_object* v_snd_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3403_; 
v_snd_3386_ = lean_ctor_get(v___x_3363_, 1);
lean_inc(v_snd_3386_);
lean_dec_ref(v___x_3363_);
v___x_3387_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3351_, v_i_3360_);
v___x_3388_ = l_Lean_PersistentArray_toList___redArg(v_children_3361_);
v___x_3389_ = lean_box(0);
lean_inc_ref(v_postNode_3350_);
v___x_3390_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3349_, v_postNode_3350_, v___x_3387_, v___x_3388_, v___x_3389_, v_snd_3386_);
v_fst_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_fst_3391_);
v_snd_3392_ = lean_ctor_get(v___x_3390_, 1);
lean_inc(v_snd_3392_);
lean_dec_ref(v___x_3390_);
v___x_3393_ = lean_apply_5(v_postNode_3350_, v_val_3362_, v_i_3360_, v_children_3361_, v_fst_3391_, v_snd_3392_);
v_fst_3394_ = lean_ctor_get(v___x_3393_, 0);
v_snd_3395_ = lean_ctor_get(v___x_3393_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3397_ = v___x_3393_;
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_snd_3395_);
lean_inc(v_fst_3394_);
lean_dec(v___x_3393_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3399_, 0, v_fst_3394_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3399_);
v___x_3401_ = v___x_3397_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_snd_3395_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
default: 
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec_ref_known(v_x_3352_, 1);
lean_dec(v_x_3351_);
lean_dec_ref(v_postNode_3350_);
lean_dec_ref(v_preNode_3349_);
v___x_3404_ = lean_box(0);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v___y_3353_);
return v___x_3405_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3406_, lean_object* v_postNode_3407_, lean_object* v___x_3408_, lean_object* v_x_3409_, lean_object* v_x_3410_, lean_object* v___y_3411_){
_start:
{
if (lean_obj_tag(v_x_3409_) == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec(v___x_3408_);
lean_dec_ref(v_postNode_3407_);
lean_dec_ref(v_preNode_3406_);
v___x_3412_ = l_List_reverse___redArg(v_x_3410_);
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v___y_3411_);
return v___x_3413_;
}
else
{
lean_object* v_head_3414_; lean_object* v_tail_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3426_; 
v_head_3414_ = lean_ctor_get(v_x_3409_, 0);
v_tail_3415_ = lean_ctor_get(v_x_3409_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_x_3409_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3417_ = v_x_3409_;
v_isShared_3418_ = v_isSharedCheck_3426_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_tail_3415_);
lean_inc(v_head_3414_);
lean_dec(v_x_3409_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3426_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v_fst_3420_; lean_object* v_snd_3421_; lean_object* v___x_3423_; 
lean_inc(v___x_3408_);
lean_inc_ref(v_postNode_3407_);
lean_inc_ref(v_preNode_3406_);
v___x_3419_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3406_, v_postNode_3407_, v___x_3408_, v_head_3414_, v___y_3411_);
v_fst_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_fst_3420_);
v_snd_3421_ = lean_ctor_get(v___x_3419_, 1);
lean_inc(v_snd_3421_);
lean_dec_ref(v___x_3419_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 1, v_x_3410_);
lean_ctor_set(v___x_3417_, 0, v_fst_3420_);
v___x_3423_ = v___x_3417_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_fst_3420_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_x_3410_);
v___x_3423_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
v_x_3409_ = v_tail_3415_;
v_x_3410_ = v___x_3423_;
v___y_3411_ = v_snd_3421_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3427_, lean_object* v_ci_3428_, lean_object* v_i_3429_, lean_object* v_cs_3430_, lean_object* v_x_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_apply_4(v_postNode_3427_, v_ci_3428_, v_i_3429_, v_cs_3430_, v___y_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3434_, lean_object* v_ci_3435_, lean_object* v_i_3436_, lean_object* v_cs_3437_, lean_object* v_x_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3434_, v_ci_3435_, v_i_3436_, v_cs_3437_, v_x_3438_, v___y_3439_);
lean_dec(v_x_3438_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3441_, lean_object* v_postNode_3442_, lean_object* v_ctx_x3f_3443_, lean_object* v_t_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v___f_3446_; lean_object* v___x_3447_; lean_object* v_snd_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3456_; 
v___f_3446_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3446_, 0, v_postNode_3442_);
v___x_3447_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3441_, v___f_3446_, v_ctx_x3f_3443_, v_t_3444_, v___y_3445_);
v_snd_3448_ = lean_ctor_get(v___x_3447_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; 
v_unused_3457_ = lean_ctor_get(v___x_3447_, 0);
lean_dec(v_unused_3457_);
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3456_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_snd_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3456_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3452_ = lean_box(0);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3452_);
v___x_3454_ = v___x_3450_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_snd_3448_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(lean_object* v_as_3460_, size_t v_i_3461_, size_t v_stop_3462_, lean_object* v_b_3463_, lean_object* v___y_3464_){
_start:
{
uint8_t v___x_3465_; 
v___x_3465_ = lean_usize_dec_eq(v_i_3461_, v_stop_3462_);
if (v___x_3465_ == 0)
{
lean_object* v___f_3466_; lean_object* v___f_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v_fst_3471_; lean_object* v_snd_3472_; size_t v___x_3473_; size_t v___x_3474_; 
v___f_3466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0));
v___f_3467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1));
v___x_3468_ = lean_array_uget_borrowed(v_as_3460_, v_i_3461_);
v___x_3469_ = lean_box(0);
lean_inc(v___x_3468_);
v___x_3470_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(v___f_3466_, v___f_3467_, v___x_3469_, v___x_3468_, v___y_3464_);
v_fst_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_fst_3471_);
v_snd_3472_ = lean_ctor_get(v___x_3470_, 1);
lean_inc(v_snd_3472_);
lean_dec_ref(v___x_3470_);
v___x_3473_ = ((size_t)1ULL);
v___x_3474_ = lean_usize_add(v_i_3461_, v___x_3473_);
v_i_3461_ = v___x_3474_;
v_b_3463_ = v_fst_3471_;
v___y_3464_ = v_snd_3472_;
goto _start;
}
else
{
lean_object* v___x_3476_; 
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_b_3463_);
lean_ctor_set(v___x_3476_, 1, v___y_3464_);
return v___x_3476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___boxed(lean_object* v_as_3477_, lean_object* v_i_3478_, lean_object* v_stop_3479_, lean_object* v_b_3480_, lean_object* v___y_3481_){
_start:
{
size_t v_i_boxed_3482_; size_t v_stop_boxed_3483_; lean_object* v_res_3484_; 
v_i_boxed_3482_ = lean_unbox_usize(v_i_3478_);
lean_dec(v_i_3478_);
v_stop_boxed_3483_ = lean_unbox_usize(v_stop_3479_);
lean_dec(v_stop_3479_);
v_res_3484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_as_3477_, v_i_boxed_3482_, v_stop_boxed_3483_, v_b_3480_, v___y_3481_);
lean_dec_ref(v_as_3477_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(lean_object* v_a_3485_, lean_object* v_x_3486_){
_start:
{
if (lean_obj_tag(v_x_3486_) == 0)
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_box(0);
return v___x_3487_;
}
else
{
lean_object* v_key_3488_; lean_object* v_value_3489_; lean_object* v_tail_3490_; uint8_t v___x_3491_; 
v_key_3488_ = lean_ctor_get(v_x_3486_, 0);
v_value_3489_ = lean_ctor_get(v_x_3486_, 1);
v_tail_3490_ = lean_ctor_get(v_x_3486_, 2);
v___x_3491_ = l_Lean_Lsp_instBEqRange_beq(v_key_3488_, v_a_3485_);
if (v___x_3491_ == 0)
{
v_x_3486_ = v_tail_3490_;
goto _start;
}
else
{
lean_object* v___x_3493_; 
lean_inc(v_value_3489_);
v___x_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3493_, 0, v_value_3489_);
return v___x_3493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_3494_, lean_object* v_x_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3494_, v_x_3495_);
lean_dec(v_x_3495_);
lean_dec_ref(v_a_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(lean_object* v_m_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v_buckets_3499_; lean_object* v___x_3500_; uint64_t v___x_3501_; uint64_t v___x_3502_; uint64_t v___x_3503_; uint64_t v_fold_3504_; uint64_t v___x_3505_; uint64_t v___x_3506_; uint64_t v___x_3507_; size_t v___x_3508_; size_t v___x_3509_; size_t v___x_3510_; size_t v___x_3511_; size_t v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_buckets_3499_ = lean_ctor_get(v_m_3497_, 1);
v___x_3500_ = lean_array_get_size(v_buckets_3499_);
v___x_3501_ = l_Lean_Lsp_instHashableRange_hash(v_a_3498_);
v___x_3502_ = 32ULL;
v___x_3503_ = lean_uint64_shift_right(v___x_3501_, v___x_3502_);
v_fold_3504_ = lean_uint64_xor(v___x_3501_, v___x_3503_);
v___x_3505_ = 16ULL;
v___x_3506_ = lean_uint64_shift_right(v_fold_3504_, v___x_3505_);
v___x_3507_ = lean_uint64_xor(v_fold_3504_, v___x_3506_);
v___x_3508_ = lean_uint64_to_usize(v___x_3507_);
v___x_3509_ = lean_usize_of_nat(v___x_3500_);
v___x_3510_ = ((size_t)1ULL);
v___x_3511_ = lean_usize_sub(v___x_3509_, v___x_3510_);
v___x_3512_ = lean_usize_land(v___x_3508_, v___x_3511_);
v___x_3513_ = lean_array_uget_borrowed(v_buckets_3499_, v___x_3512_);
v___x_3514_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3498_, v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg___boxed(lean_object* v_m_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3515_, v_a_3516_);
lean_dec_ref(v_a_3516_);
lean_dec_ref(v_m_3515_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(lean_object* v_posMap_3518_, lean_object* v_as_3519_, size_t v_sz_3520_, size_t v_i_3521_, lean_object* v_b_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_a_3525_; lean_object* v_snd_3526_; uint8_t v___x_3530_; 
v___x_3530_ = lean_usize_dec_lt(v_i_3521_, v_sz_3520_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; 
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v_b_3522_);
lean_ctor_set(v___x_3531_, 1, v___y_3523_);
return v___x_3531_;
}
else
{
lean_object* v_a_3532_; lean_object* v_ident_3533_; lean_object* v_range_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_a_3532_ = lean_array_uget_borrowed(v_as_3519_, v_i_3521_);
v_ident_3533_ = lean_ctor_get(v_a_3532_, 0);
v_range_3534_ = lean_ctor_get(v_a_3532_, 2);
v___x_3535_ = lean_box(0);
v___x_3536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_posMap_3518_, v_range_3534_);
if (lean_obj_tag(v___x_3536_) == 1)
{
lean_object* v_val_3537_; lean_object* v___x_3538_; lean_object* v_snd_3539_; 
v_val_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_val_3537_);
lean_dec_ref_known(v___x_3536_, 1);
lean_inc_ref(v_ident_3533_);
v___x_3538_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v_val_3537_, v_ident_3533_, v___y_3523_);
v_snd_3539_ = lean_ctor_get(v___x_3538_, 1);
lean_inc(v_snd_3539_);
lean_dec_ref(v___x_3538_);
v_a_3525_ = v___x_3535_;
v_snd_3526_ = v_snd_3539_;
goto v___jp_3524_;
}
else
{
lean_dec(v___x_3536_);
v_a_3525_ = v___x_3535_;
v_snd_3526_ = v___y_3523_;
goto v___jp_3524_;
}
}
v___jp_3524_:
{
size_t v___x_3527_; size_t v___x_3528_; 
v___x_3527_ = ((size_t)1ULL);
v___x_3528_ = lean_usize_add(v_i_3521_, v___x_3527_);
v_i_3521_ = v___x_3528_;
v_b_3522_ = v_a_3525_;
v___y_3523_ = v_snd_3526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2___boxed(lean_object* v_posMap_3540_, lean_object* v_as_3541_, lean_object* v_sz_3542_, lean_object* v_i_3543_, lean_object* v_b_3544_, lean_object* v___y_3545_){
_start:
{
size_t v_sz_boxed_3546_; size_t v_i_boxed_3547_; lean_object* v_res_3548_; 
v_sz_boxed_3546_ = lean_unbox_usize(v_sz_3542_);
lean_dec(v_sz_3542_);
v_i_boxed_3547_ = lean_unbox_usize(v_i_3543_);
lean_dec(v_i_3543_);
v_res_3548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3540_, v_as_3541_, v_sz_boxed_3546_, v_i_boxed_3547_, v_b_3544_, v___y_3545_);
lean_dec_ref(v_as_3541_);
lean_dec_ref(v_posMap_3540_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(lean_object* v_trees_3549_, lean_object* v_refs_3550_, lean_object* v_posMap_3551_){
_start:
{
lean_object* v___x_3552_; size_t v_sz_3553_; size_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v_snd_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3552_ = lean_box(0);
v_sz_3553_ = lean_array_size(v_refs_3550_);
v___x_3554_ = ((size_t)0ULL);
v___x_3555_ = lean_unsigned_to_nat(0u);
v___x_3556_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v___x_3557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3551_, v_refs_3550_, v_sz_3553_, v___x_3554_, v___x_3552_, v___x_3556_);
v_snd_3558_ = lean_ctor_get(v___x_3557_, 1);
lean_inc(v_snd_3558_);
lean_dec_ref(v___x_3557_);
v___x_3559_ = lean_array_get_size(v_trees_3549_);
v___x_3560_ = lean_nat_dec_lt(v___x_3555_, v___x_3559_);
if (v___x_3560_ == 0)
{
return v_snd_3558_;
}
else
{
size_t v___x_3561_; lean_object* v___x_3562_; lean_object* v_snd_3563_; 
v___x_3561_ = lean_usize_of_nat(v___x_3559_);
v___x_3562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3549_, v___x_3554_, v___x_3561_, v___x_3552_, v_snd_3558_);
v_snd_3563_ = lean_ctor_get(v___x_3562_, 1);
lean_inc(v_snd_3563_);
lean_dec_ref(v___x_3562_);
return v_snd_3563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap___boxed(lean_object* v_trees_3564_, lean_object* v_refs_3565_, lean_object* v_posMap_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3564_, v_refs_3565_, v_posMap_3566_);
lean_dec_ref(v_posMap_3566_);
lean_dec_ref(v_refs_3565_);
lean_dec_ref(v_trees_3564_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(lean_object* v_00_u03b2_3568_, lean_object* v_m_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3569_, v_a_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___boxed(lean_object* v_00_u03b2_3572_, lean_object* v_m_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(v_00_u03b2_3572_, v_m_3573_, v_a_3574_);
lean_dec_ref(v_a_3574_);
lean_dec_ref(v_m_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3576_, lean_object* v_msg_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v_msg_3577_, v___y_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object* v_00_u03b1_3580_, lean_object* v_preNode_3581_, lean_object* v_postNode_3582_, lean_object* v_x_3583_, lean_object* v_x_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3581_, v_postNode_3582_, v_x_3583_, v_x_3584_, v___y_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object* v_00_u03b2_3587_, lean_object* v_a_3588_, lean_object* v_x_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3588_, v_x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3591_, lean_object* v_a_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(v_00_u03b2_3591_, v_a_3592_, v_x_3593_);
lean_dec(v_x_3593_);
lean_dec_ref(v_a_3592_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3595_, lean_object* v_preNode_3596_, lean_object* v_postNode_3597_, lean_object* v___x_3598_, lean_object* v_x_3599_, lean_object* v_x_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3596_, v_postNode_3597_, v___x_3598_, v_x_3599_, v_x_3600_, v___y_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(lean_object* v_a_3603_, lean_object* v_b_3604_, lean_object* v_x_3605_){
_start:
{
if (lean_obj_tag(v_x_3605_) == 0)
{
lean_dec(v_b_3604_);
lean_dec_ref(v_a_3603_);
return v_x_3605_;
}
else
{
lean_object* v_key_3606_; lean_object* v_value_3607_; lean_object* v_tail_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3620_; 
v_key_3606_ = lean_ctor_get(v_x_3605_, 0);
v_value_3607_ = lean_ctor_get(v_x_3605_, 1);
v_tail_3608_ = lean_ctor_get(v_x_3605_, 2);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_x_3605_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3610_ = v_x_3605_;
v_isShared_3611_ = v_isSharedCheck_3620_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_tail_3608_);
lean_inc(v_value_3607_);
lean_inc(v_key_3606_);
lean_dec(v_x_3605_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3620_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
uint8_t v___x_3612_; 
v___x_3612_ = l_Lean_Lsp_instBEqRange_beq(v_key_3606_, v_a_3603_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3613_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3603_, v_b_3604_, v_tail_3608_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 2, v___x_3613_);
v___x_3615_ = v___x_3610_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_key_3606_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_value_3607_);
lean_ctor_set(v_reuseFailAlloc_3616_, 2, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
else
{
lean_object* v___x_3618_; 
lean_dec(v_value_3607_);
lean_dec(v_key_3606_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 1, v_b_3604_);
lean_ctor_set(v___x_3610_, 0, v_a_3603_);
v___x_3618_ = v___x_3610_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3603_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_b_3604_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_tail_3608_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
if (lean_obj_tag(v_x_3622_) == 0)
{
return v_x_3621_;
}
else
{
lean_object* v_key_3623_; lean_object* v_value_3624_; lean_object* v_tail_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3648_; 
v_key_3623_ = lean_ctor_get(v_x_3622_, 0);
v_value_3624_ = lean_ctor_get(v_x_3622_, 1);
v_tail_3625_ = lean_ctor_get(v_x_3622_, 2);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_x_3622_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3627_ = v_x_3622_;
v_isShared_3628_ = v_isSharedCheck_3648_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_tail_3625_);
lean_inc(v_value_3624_);
lean_inc(v_key_3623_);
lean_dec(v_x_3622_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3648_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; uint64_t v___x_3630_; uint64_t v___x_3631_; uint64_t v___x_3632_; uint64_t v_fold_3633_; uint64_t v___x_3634_; uint64_t v___x_3635_; uint64_t v___x_3636_; size_t v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; size_t v___x_3640_; size_t v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3644_; 
v___x_3629_ = lean_array_get_size(v_x_3621_);
v___x_3630_ = l_Lean_Lsp_instHashableRange_hash(v_key_3623_);
v___x_3631_ = 32ULL;
v___x_3632_ = lean_uint64_shift_right(v___x_3630_, v___x_3631_);
v_fold_3633_ = lean_uint64_xor(v___x_3630_, v___x_3632_);
v___x_3634_ = 16ULL;
v___x_3635_ = lean_uint64_shift_right(v_fold_3633_, v___x_3634_);
v___x_3636_ = lean_uint64_xor(v_fold_3633_, v___x_3635_);
v___x_3637_ = lean_uint64_to_usize(v___x_3636_);
v___x_3638_ = lean_usize_of_nat(v___x_3629_);
v___x_3639_ = ((size_t)1ULL);
v___x_3640_ = lean_usize_sub(v___x_3638_, v___x_3639_);
v___x_3641_ = lean_usize_land(v___x_3637_, v___x_3640_);
v___x_3642_ = lean_array_uget_borrowed(v_x_3621_, v___x_3641_);
lean_inc(v___x_3642_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 2, v___x_3642_);
v___x_3644_ = v___x_3627_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_key_3623_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_value_3624_);
lean_ctor_set(v_reuseFailAlloc_3647_, 2, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_array_uset(v_x_3621_, v___x_3641_, v___x_3644_);
v_x_3621_ = v___x_3645_;
v_x_3622_ = v_tail_3625_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3649_, lean_object* v_source_3650_, lean_object* v_target_3651_){
_start:
{
lean_object* v___x_3652_; uint8_t v___x_3653_; 
v___x_3652_ = lean_array_get_size(v_source_3650_);
v___x_3653_ = lean_nat_dec_lt(v_i_3649_, v___x_3652_);
if (v___x_3653_ == 0)
{
lean_dec_ref(v_source_3650_);
lean_dec(v_i_3649_);
return v_target_3651_;
}
else
{
lean_object* v_es_3654_; lean_object* v___x_3655_; lean_object* v_source_3656_; lean_object* v_target_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v_es_3654_ = lean_array_fget(v_source_3650_, v_i_3649_);
v___x_3655_ = lean_box(0);
v_source_3656_ = lean_array_fset(v_source_3650_, v_i_3649_, v___x_3655_);
v_target_3657_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3651_, v_es_3654_);
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = lean_nat_add(v_i_3649_, v___x_3658_);
lean_dec(v_i_3649_);
v_i_3649_ = v___x_3659_;
v_source_3650_ = v_source_3656_;
v_target_3651_ = v_target_3657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(lean_object* v_data_3661_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v_nbuckets_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3662_ = lean_array_get_size(v_data_3661_);
v___x_3663_ = lean_unsigned_to_nat(2u);
v_nbuckets_3664_ = lean_nat_mul(v___x_3662_, v___x_3663_);
v___x_3665_ = lean_unsigned_to_nat(0u);
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_mk_array(v_nbuckets_3664_, v___x_3666_);
v___x_3668_ = lean_array_propagate_mark(v_data_3661_, v___x_3667_);
v___x_3669_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v___x_3665_, v_data_3661_, v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object* v_a_3670_, lean_object* v_x_3671_){
_start:
{
if (lean_obj_tag(v_x_3671_) == 0)
{
uint8_t v___x_3672_; 
v___x_3672_ = 0;
return v___x_3672_;
}
else
{
lean_object* v_key_3673_; lean_object* v_tail_3674_; uint8_t v___x_3675_; 
v_key_3673_ = lean_ctor_get(v_x_3671_, 0);
v_tail_3674_ = lean_ctor_get(v_x_3671_, 2);
v___x_3675_ = l_Lean_Lsp_instBEqRange_beq(v_key_3673_, v_a_3670_);
if (v___x_3675_ == 0)
{
v_x_3671_ = v_tail_3674_;
goto _start;
}
else
{
return v___x_3675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object* v_a_3677_, lean_object* v_x_3678_){
_start:
{
uint8_t v_res_3679_; lean_object* v_r_3680_; 
v_res_3679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3677_, v_x_3678_);
lean_dec(v_x_3678_);
lean_dec_ref(v_a_3677_);
v_r_3680_ = lean_box(v_res_3679_);
return v_r_3680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object* v_m_3681_, lean_object* v_a_3682_, lean_object* v_b_3683_){
_start:
{
lean_object* v_size_3684_; lean_object* v_buckets_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3728_; 
v_size_3684_ = lean_ctor_get(v_m_3681_, 0);
v_buckets_3685_ = lean_ctor_get(v_m_3681_, 1);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_m_3681_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3687_ = v_m_3681_;
v_isShared_3688_ = v_isSharedCheck_3728_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_buckets_3685_);
lean_inc(v_size_3684_);
lean_dec(v_m_3681_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3728_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; uint64_t v___x_3690_; uint64_t v___x_3691_; uint64_t v___x_3692_; uint64_t v_fold_3693_; uint64_t v___x_3694_; uint64_t v___x_3695_; uint64_t v___x_3696_; size_t v___x_3697_; size_t v___x_3698_; size_t v___x_3699_; size_t v___x_3700_; size_t v___x_3701_; lean_object* v_bkt_3702_; uint8_t v___x_3703_; 
v___x_3689_ = lean_array_get_size(v_buckets_3685_);
v___x_3690_ = l_Lean_Lsp_instHashableRange_hash(v_a_3682_);
v___x_3691_ = 32ULL;
v___x_3692_ = lean_uint64_shift_right(v___x_3690_, v___x_3691_);
v_fold_3693_ = lean_uint64_xor(v___x_3690_, v___x_3692_);
v___x_3694_ = 16ULL;
v___x_3695_ = lean_uint64_shift_right(v_fold_3693_, v___x_3694_);
v___x_3696_ = lean_uint64_xor(v_fold_3693_, v___x_3695_);
v___x_3697_ = lean_uint64_to_usize(v___x_3696_);
v___x_3698_ = lean_usize_of_nat(v___x_3689_);
v___x_3699_ = ((size_t)1ULL);
v___x_3700_ = lean_usize_sub(v___x_3698_, v___x_3699_);
v___x_3701_ = lean_usize_land(v___x_3697_, v___x_3700_);
v_bkt_3702_ = lean_array_uget_borrowed(v_buckets_3685_, v___x_3701_);
v___x_3703_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3682_, v_bkt_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; lean_object* v_size_x27_3705_; lean_object* v___x_3706_; lean_object* v_buckets_x27_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3704_ = lean_unsigned_to_nat(1u);
v_size_x27_3705_ = lean_nat_add(v_size_3684_, v___x_3704_);
lean_dec(v_size_3684_);
lean_inc(v_bkt_3702_);
v___x_3706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3706_, 0, v_a_3682_);
lean_ctor_set(v___x_3706_, 1, v_b_3683_);
lean_ctor_set(v___x_3706_, 2, v_bkt_3702_);
v_buckets_x27_3707_ = lean_array_uset(v_buckets_3685_, v___x_3701_, v___x_3706_);
v___x_3708_ = lean_unsigned_to_nat(4u);
v___x_3709_ = lean_nat_mul(v_size_x27_3705_, v___x_3708_);
v___x_3710_ = lean_unsigned_to_nat(3u);
v___x_3711_ = lean_nat_div(v___x_3709_, v___x_3710_);
lean_dec(v___x_3709_);
v___x_3712_ = lean_array_get_size(v_buckets_x27_3707_);
v___x_3713_ = lean_nat_dec_le(v___x_3711_, v___x_3712_);
lean_dec(v___x_3711_);
if (v___x_3713_ == 0)
{
lean_object* v_val_3714_; lean_object* v___x_3716_; 
v_val_3714_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_buckets_x27_3707_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 1, v_val_3714_);
lean_ctor_set(v___x_3687_, 0, v_size_x27_3705_);
v___x_3716_ = v___x_3687_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_size_x27_3705_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_val_3714_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
else
{
lean_object* v___x_3719_; 
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 1, v_buckets_x27_3707_);
lean_ctor_set(v___x_3687_, 0, v_size_x27_3705_);
v___x_3719_ = v___x_3687_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_size_x27_3705_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v_buckets_x27_3707_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
else
{
lean_object* v___x_3721_; lean_object* v_buckets_x27_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
lean_inc(v_bkt_3702_);
v___x_3721_ = lean_box(0);
v_buckets_x27_3722_ = lean_array_uset(v_buckets_3685_, v___x_3701_, v___x_3721_);
v___x_3723_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3682_, v_b_3683_, v_bkt_3702_);
v___x_3724_ = lean_array_uset(v_buckets_x27_3722_, v___x_3701_, v___x_3723_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 1, v___x_3724_);
v___x_3726_ = v___x_3687_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_size_3684_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object* v_as_3729_, size_t v_sz_3730_, size_t v_i_3731_, lean_object* v_b_3732_){
_start:
{
lean_object* v_a_3734_; uint8_t v___x_3738_; 
v___x_3738_ = lean_usize_dec_lt(v_i_3731_, v_sz_3730_);
if (v___x_3738_ == 0)
{
return v_b_3732_;
}
else
{
lean_object* v_a_3739_; uint8_t v_isBinder_3740_; 
v_a_3739_ = lean_array_uget_borrowed(v_as_3729_, v_i_3731_);
v_isBinder_3740_ = lean_ctor_get_uint8(v_a_3739_, sizeof(void*)*6);
if (v_isBinder_3740_ == 1)
{
lean_object* v_ident_3741_; lean_object* v_range_3742_; lean_object* v___x_3743_; 
v_ident_3741_ = lean_ctor_get(v_a_3739_, 0);
v_range_3742_ = lean_ctor_get(v_a_3739_, 2);
lean_inc_ref(v_ident_3741_);
lean_inc_ref(v_range_3742_);
v___x_3743_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_b_3732_, v_range_3742_, v_ident_3741_);
v_a_3734_ = v___x_3743_;
goto v___jp_3733_;
}
else
{
v_a_3734_ = v_b_3732_;
goto v___jp_3733_;
}
}
v___jp_3733_:
{
size_t v___x_3735_; size_t v___x_3736_; 
v___x_3735_ = ((size_t)1ULL);
v___x_3736_ = lean_usize_add(v_i_3731_, v___x_3735_);
v_i_3731_ = v___x_3736_;
v_b_3732_ = v_a_3734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object* v_as_3744_, lean_object* v_sz_3745_, lean_object* v_i_3746_, lean_object* v_b_3747_){
_start:
{
size_t v_sz_boxed_3748_; size_t v_i_boxed_3749_; lean_object* v_res_3750_; 
v_sz_boxed_3748_ = lean_unbox_usize(v_sz_3745_);
lean_dec(v_sz_3745_);
v_i_boxed_3749_ = lean_unbox_usize(v_i_3746_);
lean_dec(v_i_3746_);
v_res_3750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_as_3744_, v_sz_boxed_3748_, v_i_boxed_3749_, v_b_3747_);
lean_dec_ref(v_as_3744_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object* v___x_3751_, lean_object* v_as_3752_, size_t v_sz_3753_, size_t v_i_3754_, lean_object* v_b_3755_){
_start:
{
lean_object* v_a_3757_; uint8_t v___x_3761_; 
v___x_3761_ = lean_usize_dec_lt(v_i_3754_, v_sz_3753_);
if (v___x_3761_ == 0)
{
return v_b_3755_;
}
else
{
lean_object* v_a_3762_; lean_object* v_ident_3763_; lean_object* v_range_3764_; lean_object* v_stx_3765_; lean_object* v_ci_3766_; lean_object* v_info_3767_; uint8_t v_isBinder_3768_; uint8_t v___x_3769_; 
v_a_3762_ = lean_array_uget(v_as_3752_, v_i_3754_);
v_ident_3763_ = lean_ctor_get(v_a_3762_, 0);
v_range_3764_ = lean_ctor_get(v_a_3762_, 2);
v_stx_3765_ = lean_ctor_get(v_a_3762_, 3);
v_ci_3766_ = lean_ctor_get(v_a_3762_, 4);
v_info_3767_ = lean_ctor_get(v_a_3762_, 5);
v_isBinder_3768_ = lean_ctor_get_uint8(v_a_3762_, sizeof(void*)*6);
v___x_3769_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v___x_3751_, v_ident_3763_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_array_push(v_b_3755_, v_a_3762_);
v_a_3757_ = v___x_3770_;
goto v___jp_3756_;
}
else
{
lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3782_; 
lean_inc_ref(v_info_3767_);
lean_inc_ref(v_ci_3766_);
lean_inc(v_stx_3765_);
lean_inc_ref(v_range_3764_);
lean_inc_ref(v_ident_3763_);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_a_3762_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; lean_object* v_unused_3784_; lean_object* v_unused_3785_; lean_object* v_unused_3786_; lean_object* v_unused_3787_; lean_object* v_unused_3788_; 
v_unused_3783_ = lean_ctor_get(v_a_3762_, 5);
lean_dec(v_unused_3783_);
v_unused_3784_ = lean_ctor_get(v_a_3762_, 4);
lean_dec(v_unused_3784_);
v_unused_3785_ = lean_ctor_get(v_a_3762_, 3);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_a_3762_, 2);
lean_dec(v_unused_3786_);
v_unused_3787_ = lean_ctor_get(v_a_3762_, 1);
lean_dec(v_unused_3787_);
v_unused_3788_ = lean_ctor_get(v_a_3762_, 0);
lean_dec(v_unused_3788_);
v___x_3772_ = v_a_3762_;
v_isShared_3773_ = v_isSharedCheck_3782_;
goto v_resetjp_3771_;
}
else
{
lean_dec(v_a_3762_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3782_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
lean_inc_ref(v_ident_3763_);
v___x_3774_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v___x_3751_, v_ident_3763_);
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_mk_empty_array_with_capacity(v___x_3775_);
v___x_3777_ = lean_array_push(v___x_3776_, v_ident_3763_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v___x_3777_);
lean_ctor_set(v___x_3772_, 0, v___x_3774_);
v___x_3779_ = v___x_3772_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_range_3764_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_stx_3765_);
lean_ctor_set(v_reuseFailAlloc_3781_, 4, v_ci_3766_);
lean_ctor_set(v_reuseFailAlloc_3781_, 5, v_info_3767_);
lean_ctor_set_uint8(v_reuseFailAlloc_3781_, sizeof(void*)*6, v_isBinder_3768_);
v___x_3779_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3780_; 
v___x_3780_ = lean_array_push(v_b_3755_, v___x_3779_);
v_a_3757_ = v___x_3780_;
goto v___jp_3756_;
}
}
}
}
v___jp_3756_:
{
size_t v___x_3758_; size_t v___x_3759_; 
v___x_3758_ = ((size_t)1ULL);
v___x_3759_ = lean_usize_add(v_i_3754_, v___x_3758_);
v_i_3754_ = v___x_3759_;
v_b_3755_ = v_a_3757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object* v___x_3789_, lean_object* v_as_3790_, lean_object* v_sz_3791_, lean_object* v_i_3792_, lean_object* v_b_3793_){
_start:
{
size_t v_sz_boxed_3794_; size_t v_i_boxed_3795_; lean_object* v_res_3796_; 
v_sz_boxed_3794_ = lean_unbox_usize(v_sz_3791_);
lean_dec(v_sz_3791_);
v_i_boxed_3795_ = lean_unbox_usize(v_i_3792_);
lean_dec(v_i_3792_);
v_res_3796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3789_, v_as_3790_, v_sz_boxed_3794_, v_i_boxed_3795_, v_b_3793_);
lean_dec_ref(v_as_3790_);
lean_dec_ref(v___x_3789_);
return v_res_3796_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__0(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3797_ = lean_box(0);
v___x_3798_ = lean_unsigned_to_nat(16u);
v___x_3799_ = lean_mk_array(v___x_3798_, v___x_3797_);
return v___x_3799_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__1(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v_posMap_3802_; 
v___x_3800_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__0, &l_Lean_Server_combineIdents___closed__0_once, _init_l_Lean_Server_combineIdents___closed__0);
v___x_3801_ = lean_unsigned_to_nat(0u);
v_posMap_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_posMap_3802_, 0, v___x_3801_);
lean_ctor_set(v_posMap_3802_, 1, v___x_3800_);
return v_posMap_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object* v_trees_3803_, lean_object* v_refs_3804_){
_start:
{
lean_object* v_posMap_3805_; size_t v_sz_3806_; size_t v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_posMap_3805_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__1, &l_Lean_Server_combineIdents___closed__1_once, _init_l_Lean_Server_combineIdents___closed__1);
v_sz_3806_ = lean_array_size(v_refs_3804_);
v___x_3807_ = ((size_t)0ULL);
v___x_3808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_refs_3804_, v_sz_3806_, v___x_3807_, v_posMap_3805_);
v___x_3809_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3803_, v_refs_3804_, v___x_3808_);
lean_dec_ref(v___x_3808_);
v___x_3810_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v___x_3809_);
lean_dec_ref(v___x_3809_);
v___x_3811_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3810_, v_refs_3804_, v_sz_3806_, v___x_3807_, v___x_3811_);
lean_dec_ref(v___x_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object* v_trees_3813_, lean_object* v_refs_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lean_Server_combineIdents(v_trees_3813_, v_refs_3814_);
lean_dec_ref(v_refs_3814_);
lean_dec_ref(v_trees_3813_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object* v_00_u03b2_3816_, lean_object* v_m_3817_, lean_object* v_a_3818_, lean_object* v_b_3819_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_m_3817_, v_a_3818_, v_b_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object* v_00_u03b2_3821_, lean_object* v_a_3822_, lean_object* v_x_3823_){
_start:
{
uint8_t v___x_3824_; 
v___x_3824_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3822_, v_x_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3825_, lean_object* v_a_3826_, lean_object* v_x_3827_){
_start:
{
uint8_t v_res_3828_; lean_object* v_r_3829_; 
v_res_3828_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(v_00_u03b2_3825_, v_a_3826_, v_x_3827_);
lean_dec(v_x_3827_);
lean_dec_ref(v_a_3826_);
v_r_3829_ = lean_box(v_res_3828_);
return v_r_3829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object* v_00_u03b2_3830_, lean_object* v_data_3831_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_data_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object* v_00_u03b2_3833_, lean_object* v_a_3834_, lean_object* v_b_3835_, lean_object* v_x_3836_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3834_, v_b_3835_, v_x_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3838_, lean_object* v_i_3839_, lean_object* v_source_3840_, lean_object* v_target_3841_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v_i_3839_, v_source_3840_, v_target_3841_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3843_, lean_object* v_x_3844_, lean_object* v_x_3845_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3844_, v_x_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object* v_hi_3847_, lean_object* v_pivot_3848_, lean_object* v_as_3849_, lean_object* v_i_3850_, lean_object* v_k_3851_){
_start:
{
uint8_t v___x_3852_; 
v___x_3852_ = lean_nat_dec_lt(v_k_3851_, v_hi_3847_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_dec(v_k_3851_);
v___x_3853_ = lean_array_fswap(v_as_3849_, v_i_3850_, v_hi_3847_);
v___x_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3854_, 0, v_i_3850_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
return v___x_3854_;
}
else
{
lean_object* v___x_3855_; lean_object* v_range_3856_; lean_object* v_range_3857_; uint8_t v___x_3858_; 
v___x_3855_ = lean_array_fget_borrowed(v_as_3849_, v_k_3851_);
v_range_3856_ = lean_ctor_get(v___x_3855_, 2);
v_range_3857_ = lean_ctor_get(v_pivot_3848_, 2);
v___x_3858_ = l_Lean_Lsp_instOrdRange_ord(v_range_3856_, v_range_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3859_ = lean_array_fswap(v_as_3849_, v_i_3850_, v_k_3851_);
v___x_3860_ = lean_unsigned_to_nat(1u);
v___x_3861_ = lean_nat_add(v_i_3850_, v___x_3860_);
lean_dec(v_i_3850_);
v___x_3862_ = lean_nat_add(v_k_3851_, v___x_3860_);
lean_dec(v_k_3851_);
v_as_3849_ = v___x_3859_;
v_i_3850_ = v___x_3861_;
v_k_3851_ = v___x_3862_;
goto _start;
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_unsigned_to_nat(1u);
v___x_3865_ = lean_nat_add(v_k_3851_, v___x_3864_);
lean_dec(v_k_3851_);
v_k_3851_ = v___x_3865_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object* v_hi_3867_, lean_object* v_pivot_3868_, lean_object* v_as_3869_, lean_object* v_i_3870_, lean_object* v_k_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3867_, v_pivot_3868_, v_as_3869_, v_i_3870_, v_k_3871_);
lean_dec_ref(v_pivot_3868_);
lean_dec(v_hi_3867_);
return v_res_3872_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3873_, lean_object* v_x1_3874_, lean_object* v_x2_3875_){
_start:
{
lean_object* v_range_3876_; lean_object* v_range_3877_; uint8_t v___x_3878_; 
v_range_3876_ = lean_ctor_get(v_x1_3874_, 2);
v_range_3877_ = lean_ctor_get(v_x2_3875_, 2);
v___x_3878_ = l_Lean_Lsp_instOrdRange_ord(v_range_3876_, v_range_3877_);
if (v___x_3878_ == 0)
{
return v___x_3873_;
}
else
{
uint8_t v___x_3879_; 
v___x_3879_ = 0;
return v___x_3879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3880_, lean_object* v_x1_3881_, lean_object* v_x2_3882_){
_start:
{
uint8_t v___x_2138__boxed_3883_; uint8_t v_res_3884_; lean_object* v_r_3885_; 
v___x_2138__boxed_3883_ = lean_unbox(v___x_3880_);
v_res_3884_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_2138__boxed_3883_, v_x1_3881_, v_x2_3882_);
lean_dec_ref(v_x2_3882_);
lean_dec_ref(v_x1_3881_);
v_r_3885_ = lean_box(v_res_3884_);
return v_r_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_n_3886_, lean_object* v_as_3887_, lean_object* v_lo_3888_, lean_object* v_hi_3889_){
_start:
{
lean_object* v___y_3891_; uint8_t v___x_3901_; 
v___x_3901_ = lean_nat_dec_lt(v_lo_3888_, v_hi_3889_);
if (v___x_3901_ == 0)
{
lean_dec(v_lo_3888_);
return v_as_3887_;
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v_mid_3904_; lean_object* v___y_3906_; lean_object* v___y_3912_; lean_object* v___x_3917_; lean_object* v___x_3918_; uint8_t v___x_3919_; 
v___x_3902_ = lean_nat_add(v_lo_3888_, v_hi_3889_);
v___x_3903_ = lean_unsigned_to_nat(1u);
v_mid_3904_ = lean_nat_shiftr(v___x_3902_, v___x_3903_);
lean_dec(v___x_3902_);
v___x_3917_ = lean_array_fget_borrowed(v_as_3887_, v_mid_3904_);
v___x_3918_ = lean_array_fget_borrowed(v_as_3887_, v_lo_3888_);
v___x_3919_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3901_, v___x_3917_, v___x_3918_);
if (v___x_3919_ == 0)
{
v___y_3912_ = v_as_3887_;
goto v___jp_3911_;
}
else
{
lean_object* v___x_3920_; 
v___x_3920_ = lean_array_fswap(v_as_3887_, v_lo_3888_, v_mid_3904_);
v___y_3912_ = v___x_3920_;
goto v___jp_3911_;
}
v___jp_3905_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v___x_3907_ = lean_array_fget_borrowed(v___y_3906_, v_mid_3904_);
v___x_3908_ = lean_array_fget_borrowed(v___y_3906_, v_hi_3889_);
v___x_3909_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3901_, v___x_3907_, v___x_3908_);
if (v___x_3909_ == 0)
{
lean_dec(v_mid_3904_);
v___y_3891_ = v___y_3906_;
goto v___jp_3890_;
}
else
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_array_fswap(v___y_3906_, v_mid_3904_, v_hi_3889_);
lean_dec(v_mid_3904_);
v___y_3891_ = v___x_3910_;
goto v___jp_3890_;
}
}
v___jp_3911_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v___x_3913_ = lean_array_fget_borrowed(v___y_3912_, v_hi_3889_);
v___x_3914_ = lean_array_fget_borrowed(v___y_3912_, v_lo_3888_);
v___x_3915_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3901_, v___x_3913_, v___x_3914_);
if (v___x_3915_ == 0)
{
v___y_3906_ = v___y_3912_;
goto v___jp_3905_;
}
else
{
lean_object* v___x_3916_; 
v___x_3916_ = lean_array_fswap(v___y_3912_, v_lo_3888_, v_hi_3889_);
v___y_3906_ = v___x_3916_;
goto v___jp_3905_;
}
}
}
v___jp_3890_:
{
lean_object* v_pivot_3892_; lean_object* v___x_3893_; lean_object* v_fst_3894_; lean_object* v_snd_3895_; uint8_t v___x_3896_; 
v_pivot_3892_ = lean_array_fget(v___y_3891_, v_hi_3889_);
lean_inc_n(v_lo_3888_, 2);
v___x_3893_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3889_, v_pivot_3892_, v___y_3891_, v_lo_3888_, v_lo_3888_);
lean_dec(v_pivot_3892_);
v_fst_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_fst_3894_);
v_snd_3895_ = lean_ctor_get(v___x_3893_, 1);
lean_inc(v_snd_3895_);
lean_dec_ref(v___x_3893_);
v___x_3896_ = lean_nat_dec_le(v_hi_3889_, v_fst_3894_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3897_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3886_, v_snd_3895_, v_lo_3888_, v_fst_3894_);
v___x_3898_ = lean_unsigned_to_nat(1u);
v___x_3899_ = lean_nat_add(v_fst_3894_, v___x_3898_);
lean_dec(v_fst_3894_);
v_as_3887_ = v___x_3897_;
v_lo_3888_ = v___x_3899_;
goto _start;
}
else
{
lean_dec(v_fst_3894_);
lean_dec(v_lo_3888_);
return v_snd_3895_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_n_3921_, lean_object* v_as_3922_, lean_object* v_lo_3923_, lean_object* v_hi_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3921_, v_as_3922_, v_lo_3923_, v_hi_3924_);
lean_dec(v_hi_3924_);
lean_dec(v_n_3921_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object* v_x_3926_, lean_object* v_x_3927_){
_start:
{
if (lean_obj_tag(v_x_3927_) == 0)
{
return v_x_3926_;
}
else
{
lean_object* v_key_3928_; lean_object* v_snd_3929_; lean_object* v_value_3930_; lean_object* v_tail_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3971_; 
v_key_3928_ = lean_ctor_get(v_x_3927_, 0);
lean_inc(v_key_3928_);
v_snd_3929_ = lean_ctor_get(v_key_3928_, 1);
v_value_3930_ = lean_ctor_get(v_x_3927_, 1);
v_tail_3931_ = lean_ctor_get(v_x_3927_, 2);
v_isSharedCheck_3971_ = !lean_is_exclusive(v_x_3927_);
if (v_isSharedCheck_3971_ == 0)
{
lean_object* v_unused_3972_; 
v_unused_3972_ = lean_ctor_get(v_x_3927_, 0);
lean_dec(v_unused_3972_);
v___x_3933_ = v_x_3927_;
v_isShared_3934_ = v_isSharedCheck_3971_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_tail_3931_);
lean_inc(v_value_3930_);
lean_dec(v_x_3927_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3971_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v_fst_3935_; lean_object* v_fst_3936_; lean_object* v_snd_3937_; lean_object* v___x_3938_; uint64_t v___x_3939_; uint64_t v___y_3941_; uint64_t v___y_3963_; 
v_fst_3935_ = lean_ctor_get(v_key_3928_, 0);
v_fst_3936_ = lean_ctor_get(v_snd_3929_, 0);
v_snd_3937_ = lean_ctor_get(v_snd_3929_, 1);
v___x_3938_ = lean_array_get_size(v_x_3926_);
v___x_3939_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_3935_);
if (lean_obj_tag(v_fst_3936_) == 0)
{
uint64_t v___x_3966_; 
v___x_3966_ = 11ULL;
v___y_3941_ = v___x_3966_;
goto v___jp_3940_;
}
else
{
lean_object* v_val_3967_; uint8_t v___x_3968_; 
v_val_3967_ = lean_ctor_get(v_fst_3936_, 0);
v___x_3968_ = lean_unbox(v_val_3967_);
if (v___x_3968_ == 0)
{
uint64_t v___x_3969_; 
v___x_3969_ = 13ULL;
v___y_3963_ = v___x_3969_;
goto v___jp_3962_;
}
else
{
uint64_t v___x_3970_; 
v___x_3970_ = 11ULL;
v___y_3963_ = v___x_3970_;
goto v___jp_3962_;
}
}
v___jp_3940_:
{
uint64_t v___x_3942_; uint64_t v___x_3943_; uint64_t v___x_3944_; uint64_t v___x_3945_; uint64_t v___x_3946_; uint64_t v_fold_3947_; uint64_t v___x_3948_; uint64_t v___x_3949_; uint64_t v___x_3950_; size_t v___x_3951_; size_t v___x_3952_; size_t v___x_3953_; size_t v___x_3954_; size_t v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3942_ = l_Lean_Lsp_instHashableRange_hash(v_snd_3937_);
v___x_3943_ = lean_uint64_mix_hash(v___y_3941_, v___x_3942_);
v___x_3944_ = lean_uint64_mix_hash(v___x_3939_, v___x_3943_);
v___x_3945_ = 32ULL;
v___x_3946_ = lean_uint64_shift_right(v___x_3944_, v___x_3945_);
v_fold_3947_ = lean_uint64_xor(v___x_3944_, v___x_3946_);
v___x_3948_ = 16ULL;
v___x_3949_ = lean_uint64_shift_right(v_fold_3947_, v___x_3948_);
v___x_3950_ = lean_uint64_xor(v_fold_3947_, v___x_3949_);
v___x_3951_ = lean_uint64_to_usize(v___x_3950_);
v___x_3952_ = lean_usize_of_nat(v___x_3938_);
v___x_3953_ = ((size_t)1ULL);
v___x_3954_ = lean_usize_sub(v___x_3952_, v___x_3953_);
v___x_3955_ = lean_usize_land(v___x_3951_, v___x_3954_);
v___x_3956_ = lean_array_uget_borrowed(v_x_3926_, v___x_3955_);
lean_inc(v___x_3956_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 2, v___x_3956_);
v___x_3958_ = v___x_3933_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_key_3928_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_value_3930_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3959_; 
v___x_3959_ = lean_array_uset(v_x_3926_, v___x_3955_, v___x_3958_);
v_x_3926_ = v___x_3959_;
v_x_3927_ = v_tail_3931_;
goto _start;
}
}
v___jp_3962_:
{
uint64_t v___x_3964_; uint64_t v___x_3965_; 
v___x_3964_ = 13ULL;
v___x_3965_ = lean_uint64_mix_hash(v___y_3963_, v___x_3964_);
v___y_3941_ = v___x_3965_;
goto v___jp_3940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object* v_i_3973_, lean_object* v_source_3974_, lean_object* v_target_3975_){
_start:
{
lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3976_ = lean_array_get_size(v_source_3974_);
v___x_3977_ = lean_nat_dec_lt(v_i_3973_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_dec_ref(v_source_3974_);
lean_dec(v_i_3973_);
return v_target_3975_;
}
else
{
lean_object* v_es_3978_; lean_object* v___x_3979_; lean_object* v_source_3980_; lean_object* v_target_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_es_3978_ = lean_array_fget(v_source_3974_, v_i_3973_);
v___x_3979_ = lean_box(0);
v_source_3980_ = lean_array_fset(v_source_3974_, v_i_3973_, v___x_3979_);
v_target_3981_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_target_3975_, v_es_3978_);
v___x_3982_ = lean_unsigned_to_nat(1u);
v___x_3983_ = lean_nat_add(v_i_3973_, v___x_3982_);
lean_dec(v_i_3973_);
v_i_3973_ = v___x_3983_;
v_source_3974_ = v_source_3980_;
v_target_3975_ = v_target_3981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object* v_data_3985_){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v_nbuckets_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3986_ = lean_array_get_size(v_data_3985_);
v___x_3987_ = lean_unsigned_to_nat(2u);
v_nbuckets_3988_ = lean_nat_mul(v___x_3986_, v___x_3987_);
v___x_3989_ = lean_unsigned_to_nat(0u);
v___x_3990_ = lean_box(0);
v___x_3991_ = lean_mk_array(v_nbuckets_3988_, v___x_3990_);
v___x_3992_ = lean_array_propagate_mark(v_data_3985_, v___x_3991_);
v___x_3993_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v___x_3989_, v_data_3985_, v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object* v_x_3994_, lean_object* v_x_3995_){
_start:
{
if (lean_obj_tag(v_x_3994_) == 0)
{
if (lean_obj_tag(v_x_3995_) == 0)
{
uint8_t v___x_3996_; 
v___x_3996_ = 1;
return v___x_3996_;
}
else
{
uint8_t v___x_3997_; 
v___x_3997_ = 0;
return v___x_3997_;
}
}
else
{
if (lean_obj_tag(v_x_3995_) == 0)
{
uint8_t v___x_3998_; 
v___x_3998_ = 0;
return v___x_3998_;
}
else
{
lean_object* v_val_3999_; uint8_t v___x_4000_; 
v_val_3999_ = lean_ctor_get(v_x_3995_, 0);
v___x_4000_ = lean_unbox(v_val_3999_);
if (v___x_4000_ == 0)
{
lean_object* v_val_4001_; uint8_t v___x_4002_; 
v_val_4001_ = lean_ctor_get(v_x_3994_, 0);
v___x_4002_ = lean_unbox(v_val_4001_);
if (v___x_4002_ == 0)
{
uint8_t v___x_4003_; 
v___x_4003_ = 1;
return v___x_4003_;
}
else
{
uint8_t v___x_4004_; 
v___x_4004_ = lean_unbox(v_val_3999_);
return v___x_4004_;
}
}
else
{
lean_object* v_val_4005_; uint8_t v___x_4006_; 
v_val_4005_ = lean_ctor_get(v_x_3994_, 0);
v___x_4006_ = lean_unbox(v_val_4005_);
return v___x_4006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object* v_x_4007_, lean_object* v_x_4008_){
_start:
{
uint8_t v_res_4009_; lean_object* v_r_4010_; 
v_res_4009_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_x_4007_, v_x_4008_);
lean_dec(v_x_4008_);
lean_dec(v_x_4007_);
v_r_4010_ = lean_box(v_res_4009_);
return v_r_4010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object* v_a_4011_, lean_object* v_x_4012_){
_start:
{
if (lean_obj_tag(v_x_4012_) == 0)
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4013_, 0, v_a_4011_);
return v___x_4013_;
}
else
{
lean_object* v_val_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4042_; 
v_val_4014_ = lean_ctor_get(v_x_4012_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_x_4012_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4016_ = v_x_4012_;
v_isShared_4017_ = v_isSharedCheck_4042_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_val_4014_);
lean_dec(v_x_4012_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4042_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v_ident_4018_; lean_object* v_aliases_4019_; lean_object* v_range_4020_; lean_object* v_stx_4021_; lean_object* v_ci_4022_; lean_object* v_info_4023_; uint8_t v_isBinder_4024_; lean_object* v_aliases_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4036_; 
v_ident_4018_ = lean_ctor_get(v_val_4014_, 0);
lean_inc_ref(v_ident_4018_);
v_aliases_4019_ = lean_ctor_get(v_val_4014_, 1);
lean_inc_ref(v_aliases_4019_);
v_range_4020_ = lean_ctor_get(v_val_4014_, 2);
lean_inc_ref(v_range_4020_);
v_stx_4021_ = lean_ctor_get(v_val_4014_, 3);
lean_inc(v_stx_4021_);
v_ci_4022_ = lean_ctor_get(v_val_4014_, 4);
lean_inc_ref(v_ci_4022_);
v_info_4023_ = lean_ctor_get(v_val_4014_, 5);
lean_inc_ref(v_info_4023_);
v_isBinder_4024_ = lean_ctor_get_uint8(v_val_4014_, sizeof(void*)*6);
lean_dec(v_val_4014_);
v_aliases_4025_ = lean_ctor_get(v_a_4011_, 1);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_a_4011_);
if (v_isSharedCheck_4036_ == 0)
{
lean_object* v_unused_4037_; lean_object* v_unused_4038_; lean_object* v_unused_4039_; lean_object* v_unused_4040_; lean_object* v_unused_4041_; 
v_unused_4037_ = lean_ctor_get(v_a_4011_, 5);
lean_dec(v_unused_4037_);
v_unused_4038_ = lean_ctor_get(v_a_4011_, 4);
lean_dec(v_unused_4038_);
v_unused_4039_ = lean_ctor_get(v_a_4011_, 3);
lean_dec(v_unused_4039_);
v_unused_4040_ = lean_ctor_get(v_a_4011_, 2);
lean_dec(v_unused_4040_);
v_unused_4041_ = lean_ctor_get(v_a_4011_, 0);
lean_dec(v_unused_4041_);
v___x_4027_ = v_a_4011_;
v_isShared_4028_ = v_isSharedCheck_4036_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_aliases_4025_);
lean_dec(v_a_4011_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4036_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4029_; lean_object* v___x_4031_; 
v___x_4029_ = l_Array_append___redArg(v_aliases_4019_, v_aliases_4025_);
lean_dec_ref(v_aliases_4025_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 5, v_info_4023_);
lean_ctor_set(v___x_4027_, 4, v_ci_4022_);
lean_ctor_set(v___x_4027_, 3, v_stx_4021_);
lean_ctor_set(v___x_4027_, 2, v_range_4020_);
lean_ctor_set(v___x_4027_, 1, v___x_4029_);
lean_ctor_set(v___x_4027_, 0, v_ident_4018_);
v___x_4031_ = v___x_4027_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_ident_4018_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_4029_);
lean_ctor_set(v_reuseFailAlloc_4035_, 2, v_range_4020_);
lean_ctor_set(v_reuseFailAlloc_4035_, 3, v_stx_4021_);
lean_ctor_set(v_reuseFailAlloc_4035_, 4, v_ci_4022_);
lean_ctor_set(v_reuseFailAlloc_4035_, 5, v_info_4023_);
v___x_4031_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4033_; 
lean_ctor_set_uint8(v___x_4031_, sizeof(void*)*6, v_isBinder_4024_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4031_);
v___x_4033_ = v___x_4016_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_x_4045_){
_start:
{
if (lean_obj_tag(v_x_4045_) == 0)
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v_val_4048_; lean_object* v___x_4049_; 
v___x_4046_ = lean_box(0);
v___x_4047_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4043_, v___x_4046_);
v_val_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_val_4048_);
lean_dec(v___x_4047_);
v___x_4049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4049_, 0, v_a_4044_);
lean_ctor_set(v___x_4049_, 1, v_val_4048_);
lean_ctor_set(v___x_4049_, 2, v_x_4045_);
return v___x_4049_;
}
else
{
lean_object* v_key_4050_; lean_object* v_value_4051_; lean_object* v_tail_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4076_; 
v_key_4050_ = lean_ctor_get(v_x_4045_, 0);
v_value_4051_ = lean_ctor_get(v_x_4045_, 1);
v_tail_4052_ = lean_ctor_get(v_x_4045_, 2);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_x_4045_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4054_ = v_x_4045_;
v_isShared_4055_ = v_isSharedCheck_4076_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_tail_4052_);
lean_inc(v_value_4051_);
lean_inc(v_key_4050_);
lean_dec(v_x_4045_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4076_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v_fst_4061_; lean_object* v_snd_4062_; lean_object* v_fst_4063_; lean_object* v_snd_4064_; uint8_t v___x_4065_; 
v_fst_4061_ = lean_ctor_get(v_key_4050_, 0);
v_snd_4062_ = lean_ctor_get(v_key_4050_, 1);
v_fst_4063_ = lean_ctor_get(v_a_4044_, 0);
v_snd_4064_ = lean_ctor_get(v_a_4044_, 1);
v___x_4065_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4061_, v_fst_4063_);
if (v___x_4065_ == 0)
{
goto v___jp_4056_;
}
else
{
lean_object* v_fst_4066_; lean_object* v_snd_4067_; lean_object* v_fst_4068_; lean_object* v_snd_4069_; uint8_t v___x_4070_; 
v_fst_4066_ = lean_ctor_get(v_snd_4062_, 0);
v_snd_4067_ = lean_ctor_get(v_snd_4062_, 1);
v_fst_4068_ = lean_ctor_get(v_snd_4064_, 0);
v_snd_4069_ = lean_ctor_get(v_snd_4064_, 1);
v___x_4070_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4066_, v_fst_4068_);
if (v___x_4070_ == 0)
{
goto v___jp_4056_;
}
else
{
uint8_t v___x_4071_; 
v___x_4071_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4067_, v_snd_4069_);
if (v___x_4071_ == 0)
{
goto v___jp_4056_;
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v_val_4074_; lean_object* v___x_4075_; 
lean_del_object(v___x_4054_);
lean_dec(v_key_4050_);
v___x_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4072_, 0, v_value_4051_);
v___x_4073_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4043_, v___x_4072_);
v_val_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_val_4074_);
lean_dec(v___x_4073_);
v___x_4075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4075_, 0, v_a_4044_);
lean_ctor_set(v___x_4075_, 1, v_val_4074_);
lean_ctor_set(v___x_4075_, 2, v_tail_4052_);
return v___x_4075_;
}
}
}
v___jp_4056_:
{
lean_object* v_tail_4057_; lean_object* v___x_4059_; 
v_tail_4057_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4043_, v_a_4044_, v_tail_4052_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 2, v_tail_4057_);
v___x_4059_ = v___x_4054_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_key_4050_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v_value_4051_);
lean_ctor_set(v_reuseFailAlloc_4060_, 2, v_tail_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_a_4077_, lean_object* v_x_4078_){
_start:
{
if (lean_obj_tag(v_x_4078_) == 0)
{
uint8_t v___x_4079_; 
v___x_4079_ = 0;
return v___x_4079_;
}
else
{
lean_object* v_key_4080_; lean_object* v_tail_4081_; lean_object* v_fst_4082_; lean_object* v_snd_4083_; lean_object* v_fst_4084_; lean_object* v_snd_4085_; uint8_t v___x_4086_; 
v_key_4080_ = lean_ctor_get(v_x_4078_, 0);
v_tail_4081_ = lean_ctor_get(v_x_4078_, 2);
v_fst_4082_ = lean_ctor_get(v_key_4080_, 0);
v_snd_4083_ = lean_ctor_get(v_key_4080_, 1);
v_fst_4084_ = lean_ctor_get(v_a_4077_, 0);
v_snd_4085_ = lean_ctor_get(v_a_4077_, 1);
v___x_4086_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4082_, v_fst_4084_);
if (v___x_4086_ == 0)
{
v_x_4078_ = v_tail_4081_;
goto _start;
}
else
{
lean_object* v_fst_4088_; lean_object* v_snd_4089_; lean_object* v_fst_4090_; lean_object* v_snd_4091_; uint8_t v___x_4092_; 
v_fst_4088_ = lean_ctor_get(v_snd_4083_, 0);
v_snd_4089_ = lean_ctor_get(v_snd_4083_, 1);
v_fst_4090_ = lean_ctor_get(v_snd_4085_, 0);
v_snd_4091_ = lean_ctor_get(v_snd_4085_, 1);
v___x_4092_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4088_, v_fst_4090_);
if (v___x_4092_ == 0)
{
v_x_4078_ = v_tail_4081_;
goto _start;
}
else
{
uint8_t v___x_4094_; 
v___x_4094_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4089_, v_snd_4091_);
if (v___x_4094_ == 0)
{
v_x_4078_ = v_tail_4081_;
goto _start;
}
else
{
return v___x_4094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object* v_a_4096_, lean_object* v_x_4097_){
_start:
{
uint8_t v_res_4098_; lean_object* v_r_4099_; 
v_res_4098_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4096_, v_x_4097_);
lean_dec(v_x_4097_);
lean_dec_ref(v_a_4096_);
v_r_4099_ = lean_box(v_res_4098_);
return v_r_4099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4100_, lean_object* v_m_4101_, lean_object* v_a_4102_){
_start:
{
size_t v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v_snd_4110_; lean_object* v_size_4111_; lean_object* v_buckets_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4171_; 
v_snd_4110_ = lean_ctor_get(v_a_4102_, 1);
v_size_4111_ = lean_ctor_get(v_m_4101_, 0);
v_buckets_4112_ = lean_ctor_get(v_m_4101_, 1);
v_isSharedCheck_4171_ = !lean_is_exclusive(v_m_4101_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4114_ = v_m_4101_;
v_isShared_4115_ = v_isSharedCheck_4171_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_buckets_4112_);
lean_inc(v_size_4111_);
lean_dec(v_m_4101_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4171_;
goto v_resetjp_4113_;
}
v___jp_4103_:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_array_uset(v___y_4106_, v___y_4104_, v___y_4105_);
v___x_4109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___y_4107_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
return v___x_4109_;
}
v_resetjp_4113_:
{
lean_object* v_fst_4116_; lean_object* v_fst_4117_; lean_object* v_snd_4118_; lean_object* v___x_4119_; uint64_t v___x_4120_; uint64_t v___y_4122_; uint64_t v___y_4163_; 
v_fst_4116_ = lean_ctor_get(v_a_4102_, 0);
v_fst_4117_ = lean_ctor_get(v_snd_4110_, 0);
v_snd_4118_ = lean_ctor_get(v_snd_4110_, 1);
v___x_4119_ = lean_array_get_size(v_buckets_4112_);
v___x_4120_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4116_);
if (lean_obj_tag(v_fst_4117_) == 0)
{
uint64_t v___x_4166_; 
v___x_4166_ = 11ULL;
v___y_4122_ = v___x_4166_;
goto v___jp_4121_;
}
else
{
lean_object* v_val_4167_; uint8_t v___x_4168_; 
v_val_4167_ = lean_ctor_get(v_fst_4117_, 0);
v___x_4168_ = lean_unbox(v_val_4167_);
if (v___x_4168_ == 0)
{
uint64_t v___x_4169_; 
v___x_4169_ = 13ULL;
v___y_4163_ = v___x_4169_;
goto v___jp_4162_;
}
else
{
uint64_t v___x_4170_; 
v___x_4170_ = 11ULL;
v___y_4163_ = v___x_4170_;
goto v___jp_4162_;
}
}
v___jp_4121_:
{
uint64_t v___x_4123_; uint64_t v___x_4124_; uint64_t v___x_4125_; uint64_t v___x_4126_; uint64_t v___x_4127_; uint64_t v_fold_4128_; uint64_t v___x_4129_; uint64_t v___x_4130_; uint64_t v___x_4131_; size_t v___x_4132_; size_t v___x_4133_; size_t v___x_4134_; size_t v___x_4135_; size_t v___x_4136_; lean_object* v_bkt_4137_; uint8_t v___x_4138_; 
v___x_4123_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4118_);
v___x_4124_ = lean_uint64_mix_hash(v___y_4122_, v___x_4123_);
v___x_4125_ = lean_uint64_mix_hash(v___x_4120_, v___x_4124_);
v___x_4126_ = 32ULL;
v___x_4127_ = lean_uint64_shift_right(v___x_4125_, v___x_4126_);
v_fold_4128_ = lean_uint64_xor(v___x_4125_, v___x_4127_);
v___x_4129_ = 16ULL;
v___x_4130_ = lean_uint64_shift_right(v_fold_4128_, v___x_4129_);
v___x_4131_ = lean_uint64_xor(v_fold_4128_, v___x_4130_);
v___x_4132_ = lean_uint64_to_usize(v___x_4131_);
v___x_4133_ = lean_usize_of_nat(v___x_4119_);
v___x_4134_ = ((size_t)1ULL);
v___x_4135_ = lean_usize_sub(v___x_4133_, v___x_4134_);
v___x_4136_ = lean_usize_land(v___x_4132_, v___x_4135_);
v_bkt_4137_ = lean_array_uget_borrowed(v_buckets_4112_, v___x_4136_);
v___x_4138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4102_, v_bkt_4137_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4139_; lean_object* v_size_x27_4140_; lean_object* v___x_4141_; lean_object* v_buckets_x27_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; uint8_t v___x_4148_; 
v___x_4139_ = lean_unsigned_to_nat(1u);
v_size_x27_4140_ = lean_nat_add(v_size_4111_, v___x_4139_);
lean_dec(v_size_4111_);
lean_inc(v_bkt_4137_);
v___x_4141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4141_, 0, v_a_4102_);
lean_ctor_set(v___x_4141_, 1, v_a_4100_);
lean_ctor_set(v___x_4141_, 2, v_bkt_4137_);
v_buckets_x27_4142_ = lean_array_uset(v_buckets_4112_, v___x_4136_, v___x_4141_);
v___x_4143_ = lean_unsigned_to_nat(4u);
v___x_4144_ = lean_nat_mul(v_size_x27_4140_, v___x_4143_);
v___x_4145_ = lean_unsigned_to_nat(3u);
v___x_4146_ = lean_nat_div(v___x_4144_, v___x_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_array_get_size(v_buckets_x27_4142_);
v___x_4148_ = lean_nat_dec_le(v___x_4146_, v___x_4147_);
lean_dec(v___x_4146_);
if (v___x_4148_ == 0)
{
lean_object* v_val_4149_; lean_object* v___x_4151_; 
v_val_4149_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_buckets_x27_4142_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 1, v_val_4149_);
lean_ctor_set(v___x_4114_, 0, v_size_x27_4140_);
v___x_4151_ = v___x_4114_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_size_x27_4140_);
lean_ctor_set(v_reuseFailAlloc_4152_, 1, v_val_4149_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
else
{
lean_object* v___x_4154_; 
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 1, v_buckets_x27_4142_);
lean_ctor_set(v___x_4114_, 0, v_size_x27_4140_);
v___x_4154_ = v___x_4114_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_size_x27_4140_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_buckets_x27_4142_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
else
{
lean_object* v___x_4156_; lean_object* v_buckets_x27_4157_; lean_object* v_bkt_x27_4158_; uint8_t v___x_4159_; 
lean_inc(v_bkt_4137_);
lean_del_object(v___x_4114_);
v___x_4156_ = lean_box(0);
v_buckets_x27_4157_ = lean_array_uset(v_buckets_4112_, v___x_4136_, v___x_4156_);
lean_inc_ref(v_a_4102_);
v_bkt_x27_4158_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4100_, v_a_4102_, v_bkt_4137_);
v___x_4159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4102_, v_bkt_x27_4158_);
lean_dec_ref(v_a_4102_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4160_ = lean_unsigned_to_nat(1u);
v___x_4161_ = lean_nat_sub(v_size_4111_, v___x_4160_);
lean_dec(v_size_4111_);
v___y_4104_ = v___x_4136_;
v___y_4105_ = v_bkt_x27_4158_;
v___y_4106_ = v_buckets_x27_4157_;
v___y_4107_ = v___x_4161_;
goto v___jp_4103_;
}
else
{
v___y_4104_ = v___x_4136_;
v___y_4105_ = v_bkt_x27_4158_;
v___y_4106_ = v_buckets_x27_4157_;
v___y_4107_ = v_size_4111_;
goto v___jp_4103_;
}
}
}
v___jp_4162_:
{
uint64_t v___x_4164_; uint64_t v___x_4165_; 
v___x_4164_ = 13ULL;
v___x_4165_ = lean_uint64_mix_hash(v___y_4163_, v___x_4164_);
v___y_4122_ = v___x_4165_;
goto v___jp_4121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4172_, lean_object* v_as_4173_, size_t v_sz_4174_, size_t v_i_4175_, lean_object* v_b_4176_){
_start:
{
uint8_t v___x_4177_; 
v___x_4177_ = lean_usize_dec_lt(v_i_4175_, v_sz_4174_);
if (v___x_4177_ == 0)
{
return v_b_4176_;
}
else
{
lean_object* v_a_4178_; lean_object* v___y_4180_; 
v_a_4178_ = lean_array_uget_borrowed(v_as_4173_, v_i_4175_);
if (v_allowSimultaneousBinderUse_4172_ == 0)
{
lean_object* v___x_4189_; 
v___x_4189_ = lean_box(0);
v___y_4180_ = v___x_4189_;
goto v___jp_4179_;
}
else
{
uint8_t v_isBinder_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v_isBinder_4190_ = lean_ctor_get_uint8(v_a_4178_, sizeof(void*)*6);
v___x_4191_ = lean_box(v_isBinder_4190_);
v___x_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
v___y_4180_ = v___x_4192_;
goto v___jp_4179_;
}
v___jp_4179_:
{
lean_object* v_ident_4181_; lean_object* v_range_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; size_t v___x_4186_; size_t v___x_4187_; 
v_ident_4181_ = lean_ctor_get(v_a_4178_, 0);
v_range_4182_ = lean_ctor_get(v_a_4178_, 2);
lean_inc_ref(v_range_4182_);
v___x_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___y_4180_);
lean_ctor_set(v___x_4183_, 1, v_range_4182_);
lean_inc_ref(v_ident_4181_);
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v_ident_4181_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
lean_inc(v_a_4178_);
v___x_4185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4178_, v_b_4176_, v___x_4184_);
v___x_4186_ = ((size_t)1ULL);
v___x_4187_ = lean_usize_add(v_i_4175_, v___x_4186_);
v_i_4175_ = v___x_4187_;
v_b_4176_ = v___x_4185_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4193_, lean_object* v_as_4194_, lean_object* v_sz_4195_, lean_object* v_i_4196_, lean_object* v_b_4197_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4198_; size_t v_sz_boxed_4199_; size_t v_i_boxed_4200_; lean_object* v_res_4201_; 
v_allowSimultaneousBinderUse_boxed_4198_ = lean_unbox(v_allowSimultaneousBinderUse_4193_);
v_sz_boxed_4199_ = lean_unbox_usize(v_sz_4195_);
lean_dec(v_sz_4195_);
v_i_boxed_4200_ = lean_unbox_usize(v_i_4196_);
lean_dec(v_i_4196_);
v_res_4201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4198_, v_as_4194_, v_sz_boxed_4199_, v_i_boxed_4200_, v_b_4197_);
lean_dec_ref(v_as_4194_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4202_, lean_object* v_x_4203_){
_start:
{
if (lean_obj_tag(v_x_4203_) == 0)
{
return v_x_4202_;
}
else
{
lean_object* v_value_4204_; lean_object* v_tail_4205_; lean_object* v___x_4206_; 
v_value_4204_ = lean_ctor_get(v_x_4203_, 1);
lean_inc(v_value_4204_);
v_tail_4205_ = lean_ctor_get(v_x_4203_, 2);
lean_inc(v_tail_4205_);
lean_dec_ref_known(v_x_4203_, 3);
v___x_4206_ = lean_array_push(v_x_4202_, v_value_4204_);
v_x_4202_ = v___x_4206_;
v_x_4203_ = v_tail_4205_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4208_, size_t v_i_4209_, size_t v_stop_4210_, lean_object* v_b_4211_){
_start:
{
uint8_t v___x_4212_; 
v___x_4212_ = lean_usize_dec_eq(v_i_4209_, v_stop_4210_);
if (v___x_4212_ == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4214_; size_t v___x_4215_; size_t v___x_4216_; 
v___x_4213_ = lean_array_uget_borrowed(v_as_4208_, v_i_4209_);
lean_inc(v___x_4213_);
v___x_4214_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4211_, v___x_4213_);
v___x_4215_ = ((size_t)1ULL);
v___x_4216_ = lean_usize_add(v_i_4209_, v___x_4215_);
v_i_4209_ = v___x_4216_;
v_b_4211_ = v___x_4214_;
goto _start;
}
else
{
return v_b_4211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4218_, lean_object* v_i_4219_, lean_object* v_stop_4220_, lean_object* v_b_4221_){
_start:
{
size_t v_i_boxed_4222_; size_t v_stop_boxed_4223_; lean_object* v_res_4224_; 
v_i_boxed_4222_ = lean_unbox_usize(v_i_4219_);
lean_dec(v_i_4219_);
v_stop_boxed_4223_ = lean_unbox_usize(v_stop_4220_);
lean_dec(v_stop_4220_);
v_res_4224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4218_, v_i_boxed_4222_, v_stop_boxed_4223_, v_b_4221_);
lean_dec_ref(v_as_4218_);
return v_res_4224_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = lean_box(0);
v___x_4226_ = lean_unsigned_to_nat(16u);
v___x_4227_ = lean_mk_array(v___x_4226_, v___x_4225_);
return v___x_4227_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v_refsByIdAndRange_4230_; 
v___x_4228_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4229_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4230_, 0, v___x_4229_);
lean_ctor_set(v_refsByIdAndRange_4230_, 1, v___x_4228_);
return v_refsByIdAndRange_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4231_, uint8_t v_allowSimultaneousBinderUse_4232_){
_start:
{
lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4242_; lean_object* v___x_4249_; lean_object* v_refsByIdAndRange_4250_; size_t v_sz_4251_; size_t v___x_4252_; lean_object* v___x_4253_; lean_object* v_buckets_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v___x_4249_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4250_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4251_ = lean_array_size(v_refs_4231_);
v___x_4252_ = ((size_t)0ULL);
v___x_4253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4232_, v_refs_4231_, v_sz_4251_, v___x_4252_, v_refsByIdAndRange_4250_);
v_buckets_4254_ = lean_ctor_get(v___x_4253_, 1);
lean_inc_ref(v_buckets_4254_);
lean_dec_ref(v___x_4253_);
v___x_4255_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4256_ = lean_array_get_size(v_buckets_4254_);
v___x_4257_ = lean_nat_dec_lt(v___x_4249_, v___x_4256_);
if (v___x_4257_ == 0)
{
lean_dec_ref(v_buckets_4254_);
v___y_4242_ = v___x_4255_;
goto v___jp_4241_;
}
else
{
size_t v___x_4258_; lean_object* v___x_4259_; 
v___x_4258_ = lean_usize_of_nat(v___x_4256_);
v___x_4259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4254_, v___x_4252_, v___x_4258_, v___x_4255_);
lean_dec_ref(v_buckets_4254_);
v___y_4242_ = v___x_4259_;
goto v___jp_4241_;
}
v___jp_4233_:
{
uint8_t v___x_4238_; 
v___x_4238_ = lean_nat_dec_le(v___y_4237_, v___y_4234_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; 
lean_dec(v___y_4234_);
lean_inc(v___y_4237_);
v___x_4239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4236_, v___y_4235_, v___y_4237_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec(v___y_4236_);
return v___x_4239_;
}
else
{
lean_object* v___x_4240_; 
v___x_4240_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4236_, v___y_4235_, v___y_4237_, v___y_4234_);
lean_dec(v___y_4234_);
lean_dec(v___y_4236_);
return v___x_4240_;
}
}
v___jp_4241_:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; uint8_t v___x_4245_; 
v___x_4243_ = lean_array_get_size(v___y_4242_);
v___x_4244_ = lean_unsigned_to_nat(0u);
v___x_4245_ = lean_nat_dec_eq(v___x_4243_, v___x_4244_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; lean_object* v___x_4247_; uint8_t v___x_4248_; 
v___x_4246_ = lean_unsigned_to_nat(1u);
v___x_4247_ = lean_nat_sub(v___x_4243_, v___x_4246_);
v___x_4248_ = lean_nat_dec_le(v___x_4244_, v___x_4247_);
if (v___x_4248_ == 0)
{
lean_inc(v___x_4247_);
v___y_4234_ = v___x_4247_;
v___y_4235_ = v___y_4242_;
v___y_4236_ = v___x_4243_;
v___y_4237_ = v___x_4247_;
goto v___jp_4233_;
}
else
{
v___y_4234_ = v___x_4247_;
v___y_4235_ = v___y_4242_;
v___y_4236_ = v___x_4243_;
v___y_4237_ = v___x_4244_;
goto v___jp_4233_;
}
}
else
{
return v___y_4242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object* v_refs_4260_, lean_object* v_allowSimultaneousBinderUse_4261_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4262_; lean_object* v_res_4263_; 
v_allowSimultaneousBinderUse_boxed_4262_ = lean_unbox(v_allowSimultaneousBinderUse_4261_);
v_res_4263_ = l_Lean_Server_dedupReferences(v_refs_4260_, v_allowSimultaneousBinderUse_boxed_4262_);
lean_dec_ref(v_refs_4260_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object* v_n_4264_, lean_object* v_as_4265_, lean_object* v_lo_4266_, lean_object* v_hi_4267_, lean_object* v_w_4268_, lean_object* v_hlo_4269_, lean_object* v_hhi_4270_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4264_, v_as_4265_, v_lo_4266_, v_hi_4267_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object* v_n_4272_, lean_object* v_as_4273_, lean_object* v_lo_4274_, lean_object* v_hi_4275_, lean_object* v_w_4276_, lean_object* v_hlo_4277_, lean_object* v_hhi_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(v_n_4272_, v_as_4273_, v_lo_4274_, v_hi_4275_, v_w_4276_, v_hlo_4277_, v_hhi_4278_);
lean_dec(v_hi_4275_);
lean_dec(v_n_4272_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(lean_object* v_n_4280_, lean_object* v_lo_4281_, lean_object* v_hi_4282_, lean_object* v_hhi_4283_, lean_object* v_pivot_4284_, lean_object* v_as_4285_, lean_object* v_i_4286_, lean_object* v_k_4287_, lean_object* v_ilo_4288_, lean_object* v_ik_4289_, lean_object* v_w_4290_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_4282_, v_pivot_4284_, v_as_4285_, v_i_4286_, v_k_4287_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___boxed(lean_object* v_n_4292_, lean_object* v_lo_4293_, lean_object* v_hi_4294_, lean_object* v_hhi_4295_, lean_object* v_pivot_4296_, lean_object* v_as_4297_, lean_object* v_i_4298_, lean_object* v_k_4299_, lean_object* v_ilo_4300_, lean_object* v_ik_4301_, lean_object* v_w_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(v_n_4292_, v_lo_4293_, v_hi_4294_, v_hhi_4295_, v_pivot_4296_, v_as_4297_, v_i_4298_, v_k_4299_, v_ilo_4300_, v_ik_4301_, v_w_4302_);
lean_dec_ref(v_pivot_4296_);
lean_dec(v_hi_4294_);
lean_dec(v_lo_4293_);
lean_dec(v_n_4292_);
return v_res_4303_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object* v_00_u03b2_4304_, lean_object* v_a_4305_, lean_object* v_x_4306_){
_start:
{
uint8_t v___x_4307_; 
v___x_4307_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4305_, v_x_4306_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4308_, lean_object* v_a_4309_, lean_object* v_x_4310_){
_start:
{
uint8_t v_res_4311_; lean_object* v_r_4312_; 
v_res_4311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(v_00_u03b2_4308_, v_a_4309_, v_x_4310_);
lean_dec(v_x_4310_);
lean_dec_ref(v_a_4309_);
v_r_4312_ = lean_box(v_res_4311_);
return v_r_4312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object* v_00_u03b2_4313_, lean_object* v_data_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_data_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4316_, lean_object* v_i_4317_, lean_object* v_source_4318_, lean_object* v_target_4319_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v_i_4317_, v_source_4318_, v_target_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4321_, lean_object* v_x_4322_, lean_object* v_x_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_x_4322_, v_x_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object* v_as_4325_, size_t v_i_4326_, size_t v_stop_4327_, lean_object* v_b_4328_){
_start:
{
uint8_t v___x_4329_; 
v___x_4329_ = lean_usize_dec_eq(v_i_4326_, v_stop_4327_);
if (v___x_4329_ == 0)
{
lean_object* v___x_4330_; lean_object* v___x_4331_; size_t v___x_4332_; size_t v___x_4333_; 
v___x_4330_ = lean_array_uget_borrowed(v_as_4325_, v_i_4326_);
lean_inc(v___x_4330_);
v___x_4331_ = l_Lean_Server_ModuleRefs_addRef(v_b_4328_, v___x_4330_);
v___x_4332_ = ((size_t)1ULL);
v___x_4333_ = lean_usize_add(v_i_4326_, v___x_4332_);
v_i_4326_ = v___x_4333_;
v_b_4328_ = v___x_4331_;
goto _start;
}
else
{
return v_b_4328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object* v_as_4335_, lean_object* v_i_4336_, lean_object* v_stop_4337_, lean_object* v_b_4338_){
_start:
{
size_t v_i_boxed_4339_; size_t v_stop_boxed_4340_; lean_object* v_res_4341_; 
v_i_boxed_4339_ = lean_unbox_usize(v_i_4336_);
lean_dec(v_i_4336_);
v_stop_boxed_4340_ = lean_unbox_usize(v_stop_4337_);
lean_dec(v_stop_4337_);
v_res_4341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_as_4335_, v_i_boxed_4339_, v_stop_boxed_4340_, v_b_4338_);
lean_dec_ref(v_as_4335_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object* v_as_4342_, size_t v_i_4343_, size_t v_stop_4344_, lean_object* v_b_4345_){
_start:
{
lean_object* v___y_4347_; uint8_t v___x_4351_; 
v___x_4351_ = lean_usize_dec_eq(v_i_4343_, v_stop_4344_);
if (v___x_4351_ == 0)
{
lean_object* v___x_4352_; lean_object* v_ident_4353_; 
v___x_4352_ = lean_array_uget_borrowed(v_as_4342_, v_i_4343_);
v_ident_4353_ = lean_ctor_get(v___x_4352_, 0);
if (lean_obj_tag(v_ident_4353_) == 1)
{
v___y_4347_ = v_b_4345_;
goto v___jp_4346_;
}
else
{
lean_object* v___x_4354_; 
lean_inc(v___x_4352_);
v___x_4354_ = lean_array_push(v_b_4345_, v___x_4352_);
v___y_4347_ = v___x_4354_;
goto v___jp_4346_;
}
}
else
{
return v_b_4345_;
}
v___jp_4346_:
{
size_t v___x_4348_; size_t v___x_4349_; 
v___x_4348_ = ((size_t)1ULL);
v___x_4349_ = lean_usize_add(v_i_4343_, v___x_4348_);
v_i_4343_ = v___x_4349_;
v_b_4345_ = v___y_4347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object* v_as_4355_, lean_object* v_i_4356_, lean_object* v_stop_4357_, lean_object* v_b_4358_){
_start:
{
size_t v_i_boxed_4359_; size_t v_stop_boxed_4360_; lean_object* v_res_4361_; 
v_i_boxed_4359_ = lean_unbox_usize(v_i_4356_);
lean_dec(v_i_4356_);
v_stop_boxed_4360_ = lean_unbox_usize(v_stop_4357_);
lean_dec(v_stop_4357_);
v_res_4361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_as_4355_, v_i_boxed_4359_, v_stop_boxed_4360_, v_b_4358_);
lean_dec_ref(v_as_4355_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object* v_text_4362_, lean_object* v_trees_4363_, uint8_t v_localVars_4364_, uint8_t v_allowSimultaneousBinderUse_4365_){
_start:
{
lean_object* v_refs_4367_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v_refs_4377_; 
v___x_4375_ = l_Lean_Server_findReferences(v_text_4362_, v_trees_4363_);
v___x_4376_ = l_Lean_Server_combineIdents(v_trees_4363_, v___x_4375_);
lean_dec_ref(v___x_4375_);
v_refs_4377_ = l_Lean_Server_dedupReferences(v___x_4376_, v_allowSimultaneousBinderUse_4365_);
lean_dec_ref(v___x_4376_);
if (v_localVars_4364_ == 0)
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; uint8_t v___x_4381_; 
v___x_4378_ = lean_unsigned_to_nat(0u);
v___x_4379_ = lean_array_get_size(v_refs_4377_);
v___x_4380_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4381_ = lean_nat_dec_lt(v___x_4378_, v___x_4379_);
if (v___x_4381_ == 0)
{
lean_dec_ref(v_refs_4377_);
v_refs_4367_ = v___x_4380_;
goto v___jp_4366_;
}
else
{
size_t v___x_4382_; size_t v___x_4383_; lean_object* v___x_4384_; 
v___x_4382_ = ((size_t)0ULL);
v___x_4383_ = lean_usize_of_nat(v___x_4379_);
v___x_4384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4377_, v___x_4382_, v___x_4383_, v___x_4380_);
lean_dec_ref(v_refs_4377_);
v_refs_4367_ = v___x_4384_;
goto v___jp_4366_;
}
}
else
{
v_refs_4367_ = v_refs_4377_;
goto v___jp_4366_;
}
v___jp_4366_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; 
v___x_4368_ = lean_box(1);
v___x_4369_ = lean_unsigned_to_nat(0u);
v___x_4370_ = lean_array_get_size(v_refs_4367_);
v___x_4371_ = lean_nat_dec_lt(v___x_4369_, v___x_4370_);
if (v___x_4371_ == 0)
{
lean_dec_ref(v_refs_4367_);
return v___x_4368_;
}
else
{
size_t v___x_4372_; size_t v___x_4373_; lean_object* v___x_4374_; 
v___x_4372_ = ((size_t)0ULL);
v___x_4373_ = lean_usize_of_nat(v___x_4370_);
v___x_4374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4367_, v___x_4372_, v___x_4373_, v___x_4368_);
lean_dec_ref(v_refs_4367_);
return v___x_4374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object* v_text_4385_, lean_object* v_trees_4386_, lean_object* v_localVars_4387_, lean_object* v_allowSimultaneousBinderUse_4388_){
_start:
{
uint8_t v_localVars_boxed_4389_; uint8_t v_allowSimultaneousBinderUse_boxed_4390_; lean_object* v_res_4391_; 
v_localVars_boxed_4389_ = lean_unbox(v_localVars_4387_);
v_allowSimultaneousBinderUse_boxed_4390_ = lean_unbox(v_allowSimultaneousBinderUse_4388_);
v_res_4391_ = l_Lean_Server_findModuleRefs(v_text_4385_, v_trees_4386_, v_localVars_boxed_4389_, v_allowSimultaneousBinderUse_boxed_4390_);
lean_dec_ref(v_trees_4386_);
return v_res_4391_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t v_a_4399_, uint8_t v_a_4400_){
_start:
{
switch(v_a_4399_)
{
case 0:
{
if (v_a_4400_ == 1)
{
uint8_t v___x_4401_; 
v___x_4401_ = 2;
return v___x_4401_;
}
else
{
return v_a_4400_;
}
}
case 1:
{
if (v_a_4400_ == 0)
{
uint8_t v___x_4402_; 
v___x_4402_ = 2;
return v___x_4402_;
}
else
{
return v_a_4400_;
}
}
default: 
{
return v_a_4399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
uint8_t v_a_46__boxed_4405_; uint8_t v_a_47__boxed_4406_; uint8_t v_res_4407_; lean_object* v_r_4408_; 
v_a_46__boxed_4405_ = lean_unbox(v_a_4403_);
v_a_47__boxed_4406_ = lean_unbox(v_a_4404_);
v_res_4407_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_a_46__boxed_4405_, v_a_47__boxed_4406_);
v_r_4408_ = lean_box(v_res_4407_);
return v_r_4408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object* v_upperBound_4409_, lean_object* v_identicalImports_4410_, lean_object* v_a_4411_, lean_object* v_b_4412_){
_start:
{
uint8_t v___x_4413_; 
v___x_4413_ = lean_nat_dec_lt(v_a_4411_, v_upperBound_4409_);
if (v___x_4413_ == 0)
{
lean_object* v___x_4414_; 
lean_dec(v_a_4411_);
v___x_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4414_, 0, v_b_4412_);
return v___x_4414_;
}
else
{
lean_object* v_module_4415_; lean_object* v_uri_4416_; uint8_t v_isAll_4417_; uint8_t v_isPrivate_4418_; uint8_t v_metaKind_4419_; lean_object* v___x_4420_; lean_object* v_module_4421_; lean_object* v_uri_4422_; uint8_t v_isAll_4423_; uint8_t v_isPrivate_4424_; uint8_t v_metaKind_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4445_; 
v_module_4415_ = lean_ctor_get(v_b_4412_, 0);
lean_inc(v_module_4415_);
v_uri_4416_ = lean_ctor_get(v_b_4412_, 1);
lean_inc_ref(v_uri_4416_);
v_isAll_4417_ = lean_ctor_get_uint8(v_b_4412_, sizeof(void*)*2);
v_isPrivate_4418_ = lean_ctor_get_uint8(v_b_4412_, sizeof(void*)*2 + 1);
v_metaKind_4419_ = lean_ctor_get_uint8(v_b_4412_, sizeof(void*)*2 + 2);
lean_dec_ref(v_b_4412_);
v___x_4420_ = lean_array_fget(v_identicalImports_4410_, v_a_4411_);
v_module_4421_ = lean_ctor_get(v___x_4420_, 0);
v_uri_4422_ = lean_ctor_get(v___x_4420_, 1);
v_isAll_4423_ = lean_ctor_get_uint8(v___x_4420_, sizeof(void*)*2);
v_isPrivate_4424_ = lean_ctor_get_uint8(v___x_4420_, sizeof(void*)*2 + 1);
v_metaKind_4425_ = lean_ctor_get_uint8(v___x_4420_, sizeof(void*)*2 + 2);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4427_ = v___x_4420_;
v_isShared_4428_ = v_isSharedCheck_4445_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_uri_4422_);
lean_inc(v_module_4421_);
lean_dec(v___x_4420_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4445_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
uint8_t v___y_4430_; uint8_t v___y_4431_; uint8_t v___y_4440_; uint8_t v___x_4441_; 
v___x_4441_ = lean_name_eq(v_module_4415_, v_module_4421_);
lean_dec(v_module_4421_);
if (v___x_4441_ == 0)
{
lean_object* v___x_4442_; 
lean_del_object(v___x_4427_);
lean_dec_ref(v_uri_4422_);
lean_dec_ref(v_uri_4416_);
lean_dec(v_module_4415_);
lean_dec(v_a_4411_);
v___x_4442_ = lean_box(0);
return v___x_4442_;
}
else
{
uint8_t v___x_4443_; 
v___x_4443_ = lean_string_dec_eq(v_uri_4416_, v_uri_4422_);
lean_dec_ref(v_uri_4422_);
if (v___x_4443_ == 0)
{
lean_object* v___x_4444_; 
lean_del_object(v___x_4427_);
lean_dec_ref(v_uri_4416_);
lean_dec(v_module_4415_);
lean_dec(v_a_4411_);
v___x_4444_ = lean_box(0);
return v___x_4444_;
}
else
{
if (v_isAll_4417_ == 0)
{
v___y_4440_ = v_isAll_4423_;
goto v___jp_4439_;
}
else
{
v___y_4440_ = v___x_4413_;
goto v___jp_4439_;
}
}
}
v___jp_4429_:
{
uint8_t v___x_4432_; lean_object* v___x_4434_; 
v___x_4432_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_metaKind_4419_, v_metaKind_4425_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 1, v_uri_4416_);
lean_ctor_set(v___x_4427_, 0, v_module_4415_);
v___x_4434_ = v___x_4427_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_module_4415_);
lean_ctor_set(v_reuseFailAlloc_4438_, 1, v_uri_4416_);
v___x_4434_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*2, v___y_4430_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*2 + 1, v___y_4431_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*2 + 2, v___x_4432_);
v___x_4435_ = lean_unsigned_to_nat(1u);
v___x_4436_ = lean_nat_add(v_a_4411_, v___x_4435_);
lean_dec(v_a_4411_);
v_a_4411_ = v___x_4436_;
v_b_4412_ = v___x_4434_;
goto _start;
}
}
v___jp_4439_:
{
if (v_isPrivate_4418_ == 0)
{
v___y_4430_ = v___y_4440_;
v___y_4431_ = v_isPrivate_4418_;
goto v___jp_4429_;
}
else
{
v___y_4430_ = v___y_4440_;
v___y_4431_ = v_isPrivate_4424_;
goto v___jp_4429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_4446_, lean_object* v_identicalImports_4447_, lean_object* v_a_4448_, lean_object* v_b_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4446_, v_identicalImports_4447_, v_a_4448_, v_b_4449_);
lean_dec_ref(v_identicalImports_4447_);
lean_dec(v_upperBound_4446_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object* v_identicalImports_4451_){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; uint8_t v___x_4454_; 
v___x_4452_ = lean_unsigned_to_nat(0u);
v___x_4453_ = lean_array_get_size(v_identicalImports_4451_);
v___x_4454_ = lean_nat_dec_lt(v___x_4452_, v___x_4453_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; 
v___x_4455_ = lean_box(0);
return v___x_4455_;
}
else
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4456_ = lean_unsigned_to_nat(1u);
v___x_4457_ = lean_array_fget_borrowed(v_identicalImports_4451_, v___x_4452_);
lean_inc(v___x_4457_);
v___x_4458_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v___x_4453_, v_identicalImports_4451_, v___x_4456_, v___x_4457_);
return v___x_4458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object* v_identicalImports_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_identicalImports_4459_);
lean_dec_ref(v_identicalImports_4459_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object* v_upperBound_4461_, lean_object* v_identicalImports_4462_, lean_object* v_inst_4463_, lean_object* v_R_4464_, lean_object* v_a_4465_, lean_object* v_b_4466_, lean_object* v_c_4467_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4461_, v_identicalImports_4462_, v_a_4465_, v_b_4466_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object* v_upperBound_4469_, lean_object* v_identicalImports_4470_, lean_object* v_inst_4471_, lean_object* v_R_4472_, lean_object* v_a_4473_, lean_object* v_b_4474_, lean_object* v_c_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(v_upperBound_4469_, v_identicalImports_4470_, v_inst_4471_, v_R_4472_, v_a_4473_, v_b_4474_, v_c_4475_);
lean_dec_ref(v_identicalImports_4470_);
lean_dec(v_upperBound_4469_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object* v_x_4483_){
_start:
{
lean_object* v_module_4484_; 
v_module_4484_ = lean_ctor_get(v_x_4483_, 0);
lean_inc(v_module_4484_);
return v_module_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object* v_x_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_Server_DirectImports_convertImportInfos___lam__0(v_x_4485_);
lean_dec_ref(v_x_4485_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object* v_x_4487_, lean_object* v_x_4488_){
_start:
{
if (lean_obj_tag(v_x_4488_) == 0)
{
return v_x_4487_;
}
else
{
lean_object* v_key_4489_; lean_object* v_value_4490_; lean_object* v_tail_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v_key_4489_ = lean_ctor_get(v_x_4488_, 0);
v_value_4490_ = lean_ctor_get(v_x_4488_, 1);
v_tail_4491_ = lean_ctor_get(v_x_4488_, 2);
lean_inc(v_value_4490_);
lean_inc(v_key_4489_);
v___x_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4492_, 0, v_key_4489_);
lean_ctor_set(v___x_4492_, 1, v_value_4490_);
v___x_4493_ = lean_array_push(v_x_4487_, v___x_4492_);
v_x_4487_ = v___x_4493_;
v_x_4488_ = v_tail_4491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object* v_x_4495_, lean_object* v_x_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_x_4495_, v_x_4496_);
lean_dec(v_x_4496_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object* v_as_4498_, size_t v_i_4499_, size_t v_stop_4500_, lean_object* v_b_4501_){
_start:
{
uint8_t v___x_4502_; 
v___x_4502_ = lean_usize_dec_eq(v_i_4499_, v_stop_4500_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4503_; lean_object* v___x_4504_; size_t v___x_4505_; size_t v___x_4506_; 
v___x_4503_ = lean_array_uget_borrowed(v_as_4498_, v_i_4499_);
v___x_4504_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_b_4501_, v___x_4503_);
v___x_4505_ = ((size_t)1ULL);
v___x_4506_ = lean_usize_add(v_i_4499_, v___x_4505_);
v_i_4499_ = v___x_4506_;
v_b_4501_ = v___x_4504_;
goto _start;
}
else
{
return v_b_4501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object* v_as_4508_, lean_object* v_i_4509_, lean_object* v_stop_4510_, lean_object* v_b_4511_){
_start:
{
size_t v_i_boxed_4512_; size_t v_stop_boxed_4513_; lean_object* v_res_4514_; 
v_i_boxed_4512_ = lean_unbox_usize(v_i_4509_);
lean_dec(v_i_4509_);
v_stop_boxed_4513_ = lean_unbox_usize(v_stop_4510_);
lean_dec(v_stop_4510_);
v_res_4514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_as_4508_, v_i_boxed_4512_, v_stop_boxed_4513_, v_b_4511_);
lean_dec_ref(v_as_4508_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object* v_as_4515_, size_t v_i_4516_, size_t v_stop_4517_, lean_object* v_b_4518_){
_start:
{
lean_object* v_a_4521_; uint8_t v___x_4525_; 
v___x_4525_ = lean_usize_dec_eq(v_i_4516_, v_stop_4517_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; lean_object* v_module_4527_; uint8_t v_isPrivate_4528_; uint8_t v_isAll_4529_; uint8_t v_isMeta_4530_; lean_object* v_module_4531_; lean_object* v___x_4532_; 
v___x_4526_ = lean_array_uget_borrowed(v_as_4515_, v_i_4516_);
v_module_4527_ = lean_ctor_get(v___x_4526_, 0);
v_isPrivate_4528_ = lean_ctor_get_uint8(v___x_4526_, sizeof(void*)*1);
v_isAll_4529_ = lean_ctor_get_uint8(v___x_4526_, sizeof(void*)*1 + 1);
v_isMeta_4530_ = lean_ctor_get_uint8(v___x_4526_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4527_);
v_module_4531_ = l_String_toName(v_module_4527_);
lean_inc(v_module_4531_);
v___x_4532_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4531_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v___x_4532_, 1);
if (lean_obj_tag(v_a_4533_) == 1)
{
lean_object* v_val_4534_; uint8_t v___y_4536_; 
v_val_4534_ = lean_ctor_get(v_a_4533_, 0);
lean_inc(v_val_4534_);
lean_dec_ref_known(v_a_4533_, 1);
if (v_isMeta_4530_ == 0)
{
uint8_t v___x_4539_; 
v___x_4539_ = 0;
v___y_4536_ = v___x_4539_;
goto v___jp_4535_;
}
else
{
uint8_t v___x_4540_; 
v___x_4540_ = 1;
v___y_4536_ = v___x_4540_;
goto v___jp_4535_;
}
v___jp_4535_:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4537_, 0, v_module_4531_);
lean_ctor_set(v___x_4537_, 1, v_val_4534_);
lean_ctor_set_uint8(v___x_4537_, sizeof(void*)*2, v_isAll_4529_);
lean_ctor_set_uint8(v___x_4537_, sizeof(void*)*2 + 1, v_isPrivate_4528_);
lean_ctor_set_uint8(v___x_4537_, sizeof(void*)*2 + 2, v___y_4536_);
v___x_4538_ = lean_array_push(v_b_4518_, v___x_4537_);
v_a_4521_ = v___x_4538_;
goto v___jp_4520_;
}
}
else
{
lean_dec(v_a_4533_);
lean_dec(v_module_4531_);
v_a_4521_ = v_b_4518_;
goto v___jp_4520_;
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
lean_dec(v_module_4531_);
lean_dec_ref(v_b_4518_);
v_a_4541_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4532_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4532_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
}
else
{
lean_object* v___x_4549_; 
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v_b_4518_);
return v___x_4549_;
}
v___jp_4520_:
{
size_t v___x_4522_; size_t v___x_4523_; 
v___x_4522_ = ((size_t)1ULL);
v___x_4523_ = lean_usize_add(v_i_4516_, v___x_4522_);
v_i_4516_ = v___x_4523_;
v_b_4518_ = v_a_4521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object* v_as_4550_, lean_object* v_i_4551_, lean_object* v_stop_4552_, lean_object* v_b_4553_, lean_object* v___y_4554_){
_start:
{
size_t v_i_boxed_4555_; size_t v_stop_boxed_4556_; lean_object* v_res_4557_; 
v_i_boxed_4555_ = lean_unbox_usize(v_i_4551_);
lean_dec(v_i_4551_);
v_stop_boxed_4556_ = lean_unbox_usize(v_stop_4552_);
lean_dec(v_stop_4552_);
v_res_4557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4550_, v_i_boxed_4555_, v_stop_boxed_4556_, v_b_4553_);
lean_dec_ref(v_as_4550_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object* v_as_4558_, lean_object* v_start_4559_, lean_object* v_stop_4560_){
_start:
{
lean_object* v___x_4562_; uint8_t v___x_4563_; 
v___x_4562_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_4563_ = lean_nat_dec_lt(v_start_4559_, v_stop_4560_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; 
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4562_);
return v___x_4564_;
}
else
{
lean_object* v___x_4565_; uint8_t v___x_4566_; 
v___x_4565_ = lean_array_get_size(v_as_4558_);
v___x_4566_ = lean_nat_dec_le(v_stop_4560_, v___x_4565_);
if (v___x_4566_ == 0)
{
uint8_t v___x_4567_; 
v___x_4567_ = lean_nat_dec_lt(v_start_4559_, v___x_4565_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; 
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4562_);
return v___x_4568_;
}
else
{
size_t v___x_4569_; size_t v___x_4570_; lean_object* v___x_4571_; 
v___x_4569_ = lean_usize_of_nat(v_start_4559_);
v___x_4570_ = lean_usize_of_nat(v___x_4565_);
v___x_4571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4558_, v___x_4569_, v___x_4570_, v___x_4562_);
return v___x_4571_;
}
}
else
{
size_t v___x_4572_; size_t v___x_4573_; lean_object* v___x_4574_; 
v___x_4572_ = lean_usize_of_nat(v_start_4559_);
v___x_4573_ = lean_usize_of_nat(v_stop_4560_);
v___x_4574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4558_, v___x_4572_, v___x_4573_, v___x_4562_);
return v___x_4574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object* v_as_4575_, lean_object* v_start_4576_, lean_object* v_stop_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_as_4575_, v_start_4576_, v_stop_4577_);
lean_dec(v_stop_4577_);
lean_dec(v_start_4576_);
lean_dec_ref(v_as_4575_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object* v_k_4580_, lean_object* v_v_4581_, lean_object* v_t_4582_){
_start:
{
if (lean_obj_tag(v_t_4582_) == 0)
{
lean_object* v_size_4583_; lean_object* v_k_4584_; lean_object* v_v_4585_; lean_object* v_l_4586_; lean_object* v_r_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4867_; 
v_size_4583_ = lean_ctor_get(v_t_4582_, 0);
v_k_4584_ = lean_ctor_get(v_t_4582_, 1);
v_v_4585_ = lean_ctor_get(v_t_4582_, 2);
v_l_4586_ = lean_ctor_get(v_t_4582_, 3);
v_r_4587_ = lean_ctor_get(v_t_4582_, 4);
v_isSharedCheck_4867_ = !lean_is_exclusive(v_t_4582_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4589_ = v_t_4582_;
v_isShared_4590_ = v_isSharedCheck_4867_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_r_4587_);
lean_inc(v_l_4586_);
lean_inc(v_v_4585_);
lean_inc(v_k_4584_);
lean_inc(v_size_4583_);
lean_dec(v_t_4582_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4867_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
uint8_t v___x_4591_; 
v___x_4591_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4580_, v_k_4584_);
switch(v___x_4591_)
{
case 0:
{
lean_object* v_impl_4592_; lean_object* v___x_4593_; 
lean_dec(v_size_4583_);
v_impl_4592_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4580_, v_v_4581_, v_l_4586_);
v___x_4593_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4587_) == 0)
{
lean_object* v_size_4594_; lean_object* v_size_4595_; lean_object* v_k_4596_; lean_object* v_v_4597_; lean_object* v_l_4598_; lean_object* v_r_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; uint8_t v___x_4602_; 
v_size_4594_ = lean_ctor_get(v_r_4587_, 0);
v_size_4595_ = lean_ctor_get(v_impl_4592_, 0);
v_k_4596_ = lean_ctor_get(v_impl_4592_, 1);
v_v_4597_ = lean_ctor_get(v_impl_4592_, 2);
v_l_4598_ = lean_ctor_get(v_impl_4592_, 3);
v_r_4599_ = lean_ctor_get(v_impl_4592_, 4);
lean_inc(v_r_4599_);
v___x_4600_ = lean_unsigned_to_nat(3u);
v___x_4601_ = lean_nat_mul(v___x_4600_, v_size_4594_);
v___x_4602_ = lean_nat_dec_lt(v___x_4601_, v_size_4595_);
lean_dec(v___x_4601_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4606_; 
lean_dec(v_r_4599_);
v___x_4603_ = lean_nat_add(v___x_4593_, v_size_4595_);
v___x_4604_ = lean_nat_add(v___x_4603_, v_size_4594_);
lean_dec(v___x_4603_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 3, v_impl_4592_);
lean_ctor_set(v___x_4589_, 0, v___x_4604_);
v___x_4606_ = v___x_4589_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
lean_ctor_set(v_reuseFailAlloc_4607_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4607_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4607_, 3, v_impl_4592_);
lean_ctor_set(v_reuseFailAlloc_4607_, 4, v_r_4587_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
else
{
lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4673_; 
lean_inc(v_l_4598_);
lean_inc(v_v_4597_);
lean_inc(v_k_4596_);
lean_inc(v_size_4595_);
v_isSharedCheck_4673_ = !lean_is_exclusive(v_impl_4592_);
if (v_isSharedCheck_4673_ == 0)
{
lean_object* v_unused_4674_; lean_object* v_unused_4675_; lean_object* v_unused_4676_; lean_object* v_unused_4677_; lean_object* v_unused_4678_; 
v_unused_4674_ = lean_ctor_get(v_impl_4592_, 4);
lean_dec(v_unused_4674_);
v_unused_4675_ = lean_ctor_get(v_impl_4592_, 3);
lean_dec(v_unused_4675_);
v_unused_4676_ = lean_ctor_get(v_impl_4592_, 2);
lean_dec(v_unused_4676_);
v_unused_4677_ = lean_ctor_get(v_impl_4592_, 1);
lean_dec(v_unused_4677_);
v_unused_4678_ = lean_ctor_get(v_impl_4592_, 0);
lean_dec(v_unused_4678_);
v___x_4609_ = v_impl_4592_;
v_isShared_4610_ = v_isSharedCheck_4673_;
goto v_resetjp_4608_;
}
else
{
lean_dec(v_impl_4592_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4673_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v_size_4611_; lean_object* v_size_4612_; lean_object* v_k_4613_; lean_object* v_v_4614_; lean_object* v_l_4615_; lean_object* v_r_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; 
v_size_4611_ = lean_ctor_get(v_l_4598_, 0);
v_size_4612_ = lean_ctor_get(v_r_4599_, 0);
v_k_4613_ = lean_ctor_get(v_r_4599_, 1);
v_v_4614_ = lean_ctor_get(v_r_4599_, 2);
v_l_4615_ = lean_ctor_get(v_r_4599_, 3);
v_r_4616_ = lean_ctor_get(v_r_4599_, 4);
v___x_4617_ = lean_unsigned_to_nat(2u);
v___x_4618_ = lean_nat_mul(v___x_4617_, v_size_4611_);
v___x_4619_ = lean_nat_dec_lt(v_size_4612_, v___x_4618_);
lean_dec(v___x_4618_);
if (v___x_4619_ == 0)
{
lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4648_; 
lean_inc(v_r_4616_);
lean_inc(v_l_4615_);
lean_inc(v_v_4614_);
lean_inc(v_k_4613_);
v_isSharedCheck_4648_ = !lean_is_exclusive(v_r_4599_);
if (v_isSharedCheck_4648_ == 0)
{
lean_object* v_unused_4649_; lean_object* v_unused_4650_; lean_object* v_unused_4651_; lean_object* v_unused_4652_; lean_object* v_unused_4653_; 
v_unused_4649_ = lean_ctor_get(v_r_4599_, 4);
lean_dec(v_unused_4649_);
v_unused_4650_ = lean_ctor_get(v_r_4599_, 3);
lean_dec(v_unused_4650_);
v_unused_4651_ = lean_ctor_get(v_r_4599_, 2);
lean_dec(v_unused_4651_);
v_unused_4652_ = lean_ctor_get(v_r_4599_, 1);
lean_dec(v_unused_4652_);
v_unused_4653_ = lean_ctor_get(v_r_4599_, 0);
lean_dec(v_unused_4653_);
v___x_4621_ = v_r_4599_;
v_isShared_4622_ = v_isSharedCheck_4648_;
goto v_resetjp_4620_;
}
else
{
lean_dec(v_r_4599_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4648_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___x_4636_; lean_object* v___y_4638_; 
v___x_4623_ = lean_nat_add(v___x_4593_, v_size_4595_);
lean_dec(v_size_4595_);
v___x_4624_ = lean_nat_add(v___x_4623_, v_size_4594_);
lean_dec(v___x_4623_);
v___x_4636_ = lean_nat_add(v___x_4593_, v_size_4611_);
if (lean_obj_tag(v_l_4615_) == 0)
{
lean_object* v_size_4646_; 
v_size_4646_ = lean_ctor_get(v_l_4615_, 0);
lean_inc(v_size_4646_);
v___y_4638_ = v_size_4646_;
goto v___jp_4637_;
}
else
{
lean_object* v___x_4647_; 
v___x_4647_ = lean_unsigned_to_nat(0u);
v___y_4638_ = v___x_4647_;
goto v___jp_4637_;
}
v___jp_4625_:
{
lean_object* v___x_4629_; lean_object* v___x_4631_; 
v___x_4629_ = lean_nat_add(v___y_4627_, v___y_4628_);
lean_dec(v___y_4628_);
lean_dec(v___y_4627_);
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 4, v_r_4587_);
lean_ctor_set(v___x_4621_, 3, v_r_4616_);
lean_ctor_set(v___x_4621_, 2, v_v_4585_);
lean_ctor_set(v___x_4621_, 1, v_k_4584_);
lean_ctor_set(v___x_4621_, 0, v___x_4629_);
v___x_4631_ = v___x_4621_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4635_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4635_, 3, v_r_4616_);
lean_ctor_set(v_reuseFailAlloc_4635_, 4, v_r_4587_);
v___x_4631_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4633_; 
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 4, v___x_4631_);
lean_ctor_set(v___x_4609_, 3, v___y_4626_);
lean_ctor_set(v___x_4609_, 2, v_v_4614_);
lean_ctor_set(v___x_4609_, 1, v_k_4613_);
lean_ctor_set(v___x_4609_, 0, v___x_4624_);
v___x_4633_ = v___x_4609_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4634_, 1, v_k_4613_);
lean_ctor_set(v_reuseFailAlloc_4634_, 2, v_v_4614_);
lean_ctor_set(v_reuseFailAlloc_4634_, 3, v___y_4626_);
lean_ctor_set(v_reuseFailAlloc_4634_, 4, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
v___jp_4637_:
{
lean_object* v___x_4639_; lean_object* v___x_4641_; 
v___x_4639_ = lean_nat_add(v___x_4636_, v___y_4638_);
lean_dec(v___y_4638_);
lean_dec(v___x_4636_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 4, v_l_4615_);
lean_ctor_set(v___x_4589_, 3, v_l_4598_);
lean_ctor_set(v___x_4589_, 2, v_v_4597_);
lean_ctor_set(v___x_4589_, 1, v_k_4596_);
lean_ctor_set(v___x_4589_, 0, v___x_4639_);
v___x_4641_ = v___x_4589_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v___x_4639_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v_k_4596_);
lean_ctor_set(v_reuseFailAlloc_4645_, 2, v_v_4597_);
lean_ctor_set(v_reuseFailAlloc_4645_, 3, v_l_4598_);
lean_ctor_set(v_reuseFailAlloc_4645_, 4, v_l_4615_);
v___x_4641_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
lean_object* v___x_4642_; 
v___x_4642_ = lean_nat_add(v___x_4593_, v_size_4594_);
if (lean_obj_tag(v_r_4616_) == 0)
{
lean_object* v_size_4643_; 
v_size_4643_ = lean_ctor_get(v_r_4616_, 0);
lean_inc(v_size_4643_);
v___y_4626_ = v___x_4641_;
v___y_4627_ = v___x_4642_;
v___y_4628_ = v_size_4643_;
goto v___jp_4625_;
}
else
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_unsigned_to_nat(0u);
v___y_4626_ = v___x_4641_;
v___y_4627_ = v___x_4642_;
v___y_4628_ = v___x_4644_;
goto v___jp_4625_;
}
}
}
}
}
else
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4659_; 
lean_del_object(v___x_4589_);
v___x_4654_ = lean_nat_add(v___x_4593_, v_size_4595_);
lean_dec(v_size_4595_);
v___x_4655_ = lean_nat_add(v___x_4654_, v_size_4594_);
lean_dec(v___x_4654_);
v___x_4656_ = lean_nat_add(v___x_4593_, v_size_4594_);
v___x_4657_ = lean_nat_add(v___x_4656_, v_size_4612_);
lean_dec(v___x_4656_);
lean_inc_ref(v_r_4587_);
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 4, v_r_4587_);
lean_ctor_set(v___x_4609_, 3, v_r_4599_);
lean_ctor_set(v___x_4609_, 2, v_v_4585_);
lean_ctor_set(v___x_4609_, 1, v_k_4584_);
lean_ctor_set(v___x_4609_, 0, v___x_4657_);
v___x_4659_ = v___x_4609_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4672_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4672_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4672_, 3, v_r_4599_);
lean_ctor_set(v_reuseFailAlloc_4672_, 4, v_r_4587_);
v___x_4659_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
v_isSharedCheck_4666_ = !lean_is_exclusive(v_r_4587_);
if (v_isSharedCheck_4666_ == 0)
{
lean_object* v_unused_4667_; lean_object* v_unused_4668_; lean_object* v_unused_4669_; lean_object* v_unused_4670_; lean_object* v_unused_4671_; 
v_unused_4667_ = lean_ctor_get(v_r_4587_, 4);
lean_dec(v_unused_4667_);
v_unused_4668_ = lean_ctor_get(v_r_4587_, 3);
lean_dec(v_unused_4668_);
v_unused_4669_ = lean_ctor_get(v_r_4587_, 2);
lean_dec(v_unused_4669_);
v_unused_4670_ = lean_ctor_get(v_r_4587_, 1);
lean_dec(v_unused_4670_);
v_unused_4671_ = lean_ctor_get(v_r_4587_, 0);
lean_dec(v_unused_4671_);
v___x_4661_ = v_r_4587_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_dec(v_r_4587_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 4, v___x_4659_);
lean_ctor_set(v___x_4661_, 3, v_l_4598_);
lean_ctor_set(v___x_4661_, 2, v_v_4597_);
lean_ctor_set(v___x_4661_, 1, v_k_4596_);
lean_ctor_set(v___x_4661_, 0, v___x_4655_);
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v_k_4596_);
lean_ctor_set(v_reuseFailAlloc_4665_, 2, v_v_4597_);
lean_ctor_set(v_reuseFailAlloc_4665_, 3, v_l_4598_);
lean_ctor_set(v_reuseFailAlloc_4665_, 4, v___x_4659_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4679_; 
v_l_4679_ = lean_ctor_get(v_impl_4592_, 3);
if (lean_obj_tag(v_l_4679_) == 0)
{
lean_object* v_r_4680_; lean_object* v_k_4681_; lean_object* v_v_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4693_; 
lean_inc_ref(v_l_4679_);
v_r_4680_ = lean_ctor_get(v_impl_4592_, 4);
v_k_4681_ = lean_ctor_get(v_impl_4592_, 1);
v_v_4682_ = lean_ctor_get(v_impl_4592_, 2);
v_isSharedCheck_4693_ = !lean_is_exclusive(v_impl_4592_);
if (v_isSharedCheck_4693_ == 0)
{
lean_object* v_unused_4694_; lean_object* v_unused_4695_; 
v_unused_4694_ = lean_ctor_get(v_impl_4592_, 3);
lean_dec(v_unused_4694_);
v_unused_4695_ = lean_ctor_get(v_impl_4592_, 0);
lean_dec(v_unused_4695_);
v___x_4684_ = v_impl_4592_;
v_isShared_4685_ = v_isSharedCheck_4693_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_r_4680_);
lean_inc(v_v_4682_);
lean_inc(v_k_4681_);
lean_dec(v_impl_4592_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4693_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4686_; lean_object* v___x_4688_; 
v___x_4686_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4680_);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 3, v_r_4680_);
lean_ctor_set(v___x_4684_, 2, v_v_4585_);
lean_ctor_set(v___x_4684_, 1, v_k_4584_);
lean_ctor_set(v___x_4684_, 0, v___x_4593_);
v___x_4688_ = v___x_4684_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4593_);
lean_ctor_set(v_reuseFailAlloc_4692_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4692_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4692_, 3, v_r_4680_);
lean_ctor_set(v_reuseFailAlloc_4692_, 4, v_r_4680_);
v___x_4688_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4690_; 
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 4, v___x_4688_);
lean_ctor_set(v___x_4589_, 3, v_l_4679_);
lean_ctor_set(v___x_4589_, 2, v_v_4682_);
lean_ctor_set(v___x_4589_, 1, v_k_4681_);
lean_ctor_set(v___x_4589_, 0, v___x_4686_);
v___x_4690_ = v___x_4589_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4691_, 1, v_k_4681_);
lean_ctor_set(v_reuseFailAlloc_4691_, 2, v_v_4682_);
lean_ctor_set(v_reuseFailAlloc_4691_, 3, v_l_4679_);
lean_ctor_set(v_reuseFailAlloc_4691_, 4, v___x_4688_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
else
{
lean_object* v_r_4696_; 
v_r_4696_ = lean_ctor_get(v_impl_4592_, 4);
lean_inc(v_r_4696_);
if (lean_obj_tag(v_r_4696_) == 0)
{
lean_object* v_k_4697_; lean_object* v_v_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4721_; 
lean_inc(v_l_4679_);
v_k_4697_ = lean_ctor_get(v_impl_4592_, 1);
v_v_4698_ = lean_ctor_get(v_impl_4592_, 2);
v_isSharedCheck_4721_ = !lean_is_exclusive(v_impl_4592_);
if (v_isSharedCheck_4721_ == 0)
{
lean_object* v_unused_4722_; lean_object* v_unused_4723_; lean_object* v_unused_4724_; 
v_unused_4722_ = lean_ctor_get(v_impl_4592_, 4);
lean_dec(v_unused_4722_);
v_unused_4723_ = lean_ctor_get(v_impl_4592_, 3);
lean_dec(v_unused_4723_);
v_unused_4724_ = lean_ctor_get(v_impl_4592_, 0);
lean_dec(v_unused_4724_);
v___x_4700_ = v_impl_4592_;
v_isShared_4701_ = v_isSharedCheck_4721_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_v_4698_);
lean_inc(v_k_4697_);
lean_dec(v_impl_4592_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4721_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v_k_4702_; lean_object* v_v_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4717_; 
v_k_4702_ = lean_ctor_get(v_r_4696_, 1);
v_v_4703_ = lean_ctor_get(v_r_4696_, 2);
v_isSharedCheck_4717_ = !lean_is_exclusive(v_r_4696_);
if (v_isSharedCheck_4717_ == 0)
{
lean_object* v_unused_4718_; lean_object* v_unused_4719_; lean_object* v_unused_4720_; 
v_unused_4718_ = lean_ctor_get(v_r_4696_, 4);
lean_dec(v_unused_4718_);
v_unused_4719_ = lean_ctor_get(v_r_4696_, 3);
lean_dec(v_unused_4719_);
v_unused_4720_ = lean_ctor_get(v_r_4696_, 0);
lean_dec(v_unused_4720_);
v___x_4705_ = v_r_4696_;
v_isShared_4706_ = v_isSharedCheck_4717_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_v_4703_);
lean_inc(v_k_4702_);
lean_dec(v_r_4696_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4717_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4707_; lean_object* v___x_4709_; 
v___x_4707_ = lean_unsigned_to_nat(3u);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 4, v_l_4679_);
lean_ctor_set(v___x_4705_, 3, v_l_4679_);
lean_ctor_set(v___x_4705_, 2, v_v_4698_);
lean_ctor_set(v___x_4705_, 1, v_k_4697_);
lean_ctor_set(v___x_4705_, 0, v___x_4593_);
v___x_4709_ = v___x_4705_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4593_);
lean_ctor_set(v_reuseFailAlloc_4716_, 1, v_k_4697_);
lean_ctor_set(v_reuseFailAlloc_4716_, 2, v_v_4698_);
lean_ctor_set(v_reuseFailAlloc_4716_, 3, v_l_4679_);
lean_ctor_set(v_reuseFailAlloc_4716_, 4, v_l_4679_);
v___x_4709_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
lean_object* v___x_4711_; 
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 4, v_l_4679_);
lean_ctor_set(v___x_4700_, 2, v_v_4585_);
lean_ctor_set(v___x_4700_, 1, v_k_4584_);
lean_ctor_set(v___x_4700_, 0, v___x_4593_);
v___x_4711_ = v___x_4700_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4593_);
lean_ctor_set(v_reuseFailAlloc_4715_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4715_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4715_, 3, v_l_4679_);
lean_ctor_set(v_reuseFailAlloc_4715_, 4, v_l_4679_);
v___x_4711_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
lean_object* v___x_4713_; 
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 4, v___x_4711_);
lean_ctor_set(v___x_4589_, 3, v___x_4709_);
lean_ctor_set(v___x_4589_, 2, v_v_4703_);
lean_ctor_set(v___x_4589_, 1, v_k_4702_);
lean_ctor_set(v___x_4589_, 0, v___x_4707_);
v___x_4713_ = v___x_4589_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4707_);
lean_ctor_set(v_reuseFailAlloc_4714_, 1, v_k_4702_);
lean_ctor_set(v_reuseFailAlloc_4714_, 2, v_v_4703_);
lean_ctor_set(v_reuseFailAlloc_4714_, 3, v___x_4709_);
lean_ctor_set(v_reuseFailAlloc_4714_, 4, v___x_4711_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
}
else
{
lean_object* v___x_4725_; lean_object* v___x_4727_; 
v___x_4725_ = lean_unsigned_to_nat(2u);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 4, v_r_4696_);
lean_ctor_set(v___x_4589_, 3, v_impl_4592_);
lean_ctor_set(v___x_4589_, 0, v___x_4725_);
v___x_4727_ = v___x_4589_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4725_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4728_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4728_, 3, v_impl_4592_);
lean_ctor_set(v_reuseFailAlloc_4728_, 4, v_r_4696_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4730_; 
lean_dec(v_v_4585_);
lean_dec(v_k_4584_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 2, v_v_4581_);
lean_ctor_set(v___x_4589_, 1, v_k_4580_);
v___x_4730_ = v___x_4589_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_size_4583_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_k_4580_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_v_4581_);
lean_ctor_set(v_reuseFailAlloc_4731_, 3, v_l_4586_);
lean_ctor_set(v_reuseFailAlloc_4731_, 4, v_r_4587_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
default: 
{
lean_object* v_impl_4732_; lean_object* v___x_4733_; 
lean_dec(v_size_4583_);
v_impl_4732_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4580_, v_v_4581_, v_r_4587_);
v___x_4733_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4586_) == 0)
{
lean_object* v_size_4734_; lean_object* v_size_4735_; lean_object* v_k_4736_; lean_object* v_v_4737_; lean_object* v_l_4738_; lean_object* v_r_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v_size_4734_ = lean_ctor_get(v_l_4586_, 0);
v_size_4735_ = lean_ctor_get(v_impl_4732_, 0);
v_k_4736_ = lean_ctor_get(v_impl_4732_, 1);
v_v_4737_ = lean_ctor_get(v_impl_4732_, 2);
v_l_4738_ = lean_ctor_get(v_impl_4732_, 3);
lean_inc(v_l_4738_);
v_r_4739_ = lean_ctor_get(v_impl_4732_, 4);
v___x_4740_ = lean_unsigned_to_nat(3u);
v___x_4741_ = lean_nat_mul(v___x_4740_, v_size_4734_);
v___x_4742_ = lean_nat_dec_lt(v___x_4741_, v_size_4735_);
lean_dec(v___x_4741_);
if (v___x_4742_ == 0)
{
lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4746_; 
lean_dec(v_l_4738_);
v___x_4743_ = lean_nat_add(v___x_4733_, v_size_4734_);
v___x_4744_ = lean_nat_add(v___x_4743_, v_size_4735_);
lean_dec(v___x_4743_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 4, v_impl_4732_);
lean_ctor_set(v___x_4589_, 0, v___x_4744_);
v___x_4746_ = v___x_4589_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4747_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4747_, 3, v_l_4586_);
lean_ctor_set(v_reuseFailAlloc_4747_, 4, v_impl_4732_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
else
{
lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4811_; 
lean_inc(v_r_4739_);
lean_inc(v_v_4737_);
lean_inc(v_k_4736_);
lean_inc(v_size_4735_);
v_isSharedCheck_4811_ = !lean_is_exclusive(v_impl_4732_);
if (v_isSharedCheck_4811_ == 0)
{
lean_object* v_unused_4812_; lean_object* v_unused_4813_; lean_object* v_unused_4814_; lean_object* v_unused_4815_; lean_object* v_unused_4816_; 
v_unused_4812_ = lean_ctor_get(v_impl_4732_, 4);
lean_dec(v_unused_4812_);
v_unused_4813_ = lean_ctor_get(v_impl_4732_, 3);
lean_dec(v_unused_4813_);
v_unused_4814_ = lean_ctor_get(v_impl_4732_, 2);
lean_dec(v_unused_4814_);
v_unused_4815_ = lean_ctor_get(v_impl_4732_, 1);
lean_dec(v_unused_4815_);
v_unused_4816_ = lean_ctor_get(v_impl_4732_, 0);
lean_dec(v_unused_4816_);
v___x_4749_ = v_impl_4732_;
v_isShared_4750_ = v_isSharedCheck_4811_;
goto v_resetjp_4748_;
}
else
{
lean_dec(v_impl_4732_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4811_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v_size_4751_; lean_object* v_k_4752_; lean_object* v_v_4753_; lean_object* v_l_4754_; lean_object* v_r_4755_; lean_object* v_size_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; uint8_t v___x_4759_; 
v_size_4751_ = lean_ctor_get(v_l_4738_, 0);
v_k_4752_ = lean_ctor_get(v_l_4738_, 1);
v_v_4753_ = lean_ctor_get(v_l_4738_, 2);
v_l_4754_ = lean_ctor_get(v_l_4738_, 3);
v_r_4755_ = lean_ctor_get(v_l_4738_, 4);
v_size_4756_ = lean_ctor_get(v_r_4739_, 0);
v___x_4757_ = lean_unsigned_to_nat(2u);
v___x_4758_ = lean_nat_mul(v___x_4757_, v_size_4756_);
v___x_4759_ = lean_nat_dec_lt(v_size_4751_, v___x_4758_);
lean_dec(v___x_4758_);
if (v___x_4759_ == 0)
{
lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4787_; 
lean_inc(v_r_4755_);
lean_inc(v_l_4754_);
lean_inc(v_v_4753_);
lean_inc(v_k_4752_);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_l_4738_);
if (v_isSharedCheck_4787_ == 0)
{
lean_object* v_unused_4788_; lean_object* v_unused_4789_; lean_object* v_unused_4790_; lean_object* v_unused_4791_; lean_object* v_unused_4792_; 
v_unused_4788_ = lean_ctor_get(v_l_4738_, 4);
lean_dec(v_unused_4788_);
v_unused_4789_ = lean_ctor_get(v_l_4738_, 3);
lean_dec(v_unused_4789_);
v_unused_4790_ = lean_ctor_get(v_l_4738_, 2);
lean_dec(v_unused_4790_);
v_unused_4791_ = lean_ctor_get(v_l_4738_, 1);
lean_dec(v_unused_4791_);
v_unused_4792_ = lean_ctor_get(v_l_4738_, 0);
lean_dec(v_unused_4792_);
v___x_4761_ = v_l_4738_;
v_isShared_4762_ = v_isSharedCheck_4787_;
goto v_resetjp_4760_;
}
else
{
lean_dec(v_l_4738_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4787_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4768_; lean_object* v___y_4777_; 
v___x_4763_ = lean_nat_add(v___x_4733_, v_size_4734_);
v___x_4764_ = lean_nat_add(v___x_4763_, v_size_4735_);
lean_dec(v_size_4735_);
if (lean_obj_tag(v_l_4754_) == 0)
{
lean_object* v_size_4785_; 
v_size_4785_ = lean_ctor_get(v_l_4754_, 0);
lean_inc(v_size_4785_);
v___y_4777_ = v_size_4785_;
goto v___jp_4776_;
}
else
{
lean_object* v___x_4786_; 
v___x_4786_ = lean_unsigned_to_nat(0u);
v___y_4777_ = v___x_4786_;
goto v___jp_4776_;
}
v___jp_4765_:
{
lean_object* v___x_4769_; lean_object* v___x_4771_; 
v___x_4769_ = lean_nat_add(v___y_4767_, v___y_4768_);
lean_dec(v___y_4768_);
lean_dec(v___y_4767_);
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 4, v_r_4739_);
lean_ctor_set(v___x_4761_, 3, v_r_4755_);
lean_ctor_set(v___x_4761_, 2, v_v_4737_);
lean_ctor_set(v___x_4761_, 1, v_k_4736_);
lean_ctor_set(v___x_4761_, 0, v___x_4769_);
v___x_4771_ = v___x_4761_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4769_);
lean_ctor_set(v_reuseFailAlloc_4775_, 1, v_k_4736_);
lean_ctor_set(v_reuseFailAlloc_4775_, 2, v_v_4737_);
lean_ctor_set(v_reuseFailAlloc_4775_, 3, v_r_4755_);
lean_ctor_set(v_reuseFailAlloc_4775_, 4, v_r_4739_);
v___x_4771_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4773_; 
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 4, v___x_4771_);
lean_ctor_set(v___x_4749_, 3, v___y_4766_);
lean_ctor_set(v___x_4749_, 2, v_v_4753_);
lean_ctor_set(v___x_4749_, 1, v_k_4752_);
lean_ctor_set(v___x_4749_, 0, v___x_4764_);
v___x_4773_ = v___x_4749_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v_k_4752_);
lean_ctor_set(v_reuseFailAlloc_4774_, 2, v_v_4753_);
lean_ctor_set(v_reuseFailAlloc_4774_, 3, v___y_4766_);
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
v___jp_4776_:
{
lean_object* v___x_4778_; lean_object* v___x_4780_; 
v___x_4778_ = lean_nat_add(v___x_4763_, v___y_4777_);
lean_dec(v___y_4777_);
lean_dec(v___x_4763_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 4, v_l_4754_);
lean_ctor_set(v___x_4589_, 0, v___x_4778_);
v___x_4780_ = v___x_4589_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4778_);
lean_ctor_set(v_reuseFailAlloc_4784_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4784_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4784_, 3, v_l_4586_);
lean_ctor_set(v_reuseFailAlloc_4784_, 4, v_l_4754_);
v___x_4780_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
lean_object* v___x_4781_; 
v___x_4781_ = lean_nat_add(v___x_4733_, v_size_4756_);
if (lean_obj_tag(v_r_4755_) == 0)
{
lean_object* v_size_4782_; 
v_size_4782_ = lean_ctor_get(v_r_4755_, 0);
lean_inc(v_size_4782_);
v___y_4766_ = v___x_4780_;
v___y_4767_ = v___x_4781_;
v___y_4768_ = v_size_4782_;
goto v___jp_4765_;
}
else
{
lean_object* v___x_4783_; 
v___x_4783_ = lean_unsigned_to_nat(0u);
v___y_4766_ = v___x_4780_;
v___y_4767_ = v___x_4781_;
v___y_4768_ = v___x_4783_;
goto v___jp_4765_;
}
}
}
}
}
else
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4797_; 
lean_del_object(v___x_4589_);
v___x_4793_ = lean_nat_add(v___x_4733_, v_size_4734_);
v___x_4794_ = lean_nat_add(v___x_4793_, v_size_4735_);
lean_dec(v_size_4735_);
v___x_4795_ = lean_nat_add(v___x_4793_, v_size_4751_);
lean_dec(v___x_4793_);
lean_inc_ref(v_l_4586_);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 4, v_l_4738_);
lean_ctor_set(v___x_4749_, 3, v_l_4586_);
lean_ctor_set(v___x_4749_, 2, v_v_4585_);
lean_ctor_set(v___x_4749_, 1, v_k_4584_);
lean_ctor_set(v___x_4749_, 0, v___x_4795_);
v___x_4797_ = v___x_4749_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4795_);
lean_ctor_set(v_reuseFailAlloc_4810_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4810_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4810_, 3, v_l_4586_);
lean_ctor_set(v_reuseFailAlloc_4810_, 4, v_l_4738_);
v___x_4797_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4804_; 
v_isSharedCheck_4804_ = !lean_is_exclusive(v_l_4586_);
if (v_isSharedCheck_4804_ == 0)
{
lean_object* v_unused_4805_; lean_object* v_unused_4806_; lean_object* v_unused_4807_; lean_object* v_unused_4808_; lean_object* v_unused_4809_; 
v_unused_4805_ = lean_ctor_get(v_l_4586_, 4);
lean_dec(v_unused_4805_);
v_unused_4806_ = lean_ctor_get(v_l_4586_, 3);
lean_dec(v_unused_4806_);
v_unused_4807_ = lean_ctor_get(v_l_4586_, 2);
lean_dec(v_unused_4807_);
v_unused_4808_ = lean_ctor_get(v_l_4586_, 1);
lean_dec(v_unused_4808_);
v_unused_4809_ = lean_ctor_get(v_l_4586_, 0);
lean_dec(v_unused_4809_);
v___x_4799_ = v_l_4586_;
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
else
{
lean_dec(v_l_4586_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4802_; 
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 4, v_r_4739_);
lean_ctor_set(v___x_4799_, 3, v___x_4797_);
lean_ctor_set(v___x_4799_, 2, v_v_4737_);
lean_ctor_set(v___x_4799_, 1, v_k_4736_);
lean_ctor_set(v___x_4799_, 0, v___x_4794_);
v___x_4802_ = v___x_4799_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4794_);
lean_ctor_set(v_reuseFailAlloc_4803_, 1, v_k_4736_);
lean_ctor_set(v_reuseFailAlloc_4803_, 2, v_v_4737_);
lean_ctor_set(v_reuseFailAlloc_4803_, 3, v___x_4797_);
lean_ctor_set(v_reuseFailAlloc_4803_, 4, v_r_4739_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4817_; 
v_l_4817_ = lean_ctor_get(v_impl_4732_, 3);
lean_inc(v_l_4817_);
if (lean_obj_tag(v_l_4817_) == 0)
{
lean_object* v_r_4818_; lean_object* v_k_4819_; lean_object* v_v_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4843_; 
v_r_4818_ = lean_ctor_get(v_impl_4732_, 4);
v_k_4819_ = lean_ctor_get(v_impl_4732_, 1);
v_v_4820_ = lean_ctor_get(v_impl_4732_, 2);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_impl_4732_);
if (v_isSharedCheck_4843_ == 0)
{
lean_object* v_unused_4844_; lean_object* v_unused_4845_; 
v_unused_4844_ = lean_ctor_get(v_impl_4732_, 3);
lean_dec(v_unused_4844_);
v_unused_4845_ = lean_ctor_get(v_impl_4732_, 0);
lean_dec(v_unused_4845_);
v___x_4822_ = v_impl_4732_;
v_isShared_4823_ = v_isSharedCheck_4843_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_r_4818_);
lean_inc(v_v_4820_);
lean_inc(v_k_4819_);
lean_dec(v_impl_4732_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4843_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v_k_4824_; lean_object* v_v_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4839_; 
v_k_4824_ = lean_ctor_get(v_l_4817_, 1);
v_v_4825_ = lean_ctor_get(v_l_4817_, 2);
v_isSharedCheck_4839_ = !lean_is_exclusive(v_l_4817_);
if (v_isSharedCheck_4839_ == 0)
{
lean_object* v_unused_4840_; lean_object* v_unused_4841_; lean_object* v_unused_4842_; 
v_unused_4840_ = lean_ctor_get(v_l_4817_, 4);
lean_dec(v_unused_4840_);
v_unused_4841_ = lean_ctor_get(v_l_4817_, 3);
lean_dec(v_unused_4841_);
v_unused_4842_ = lean_ctor_get(v_l_4817_, 0);
lean_dec(v_unused_4842_);
v___x_4827_ = v_l_4817_;
v_isShared_4828_ = v_isSharedCheck_4839_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_v_4825_);
lean_inc(v_k_4824_);
lean_dec(v_l_4817_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4839_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4829_; lean_object* v___x_4831_; 
v___x_4829_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4818_, 2);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 4, v_r_4818_);
lean_ctor_set(v___x_4827_, 3, v_r_4818_);
lean_ctor_set(v___x_4827_, 2, v_v_4585_);
lean_ctor_set(v___x_4827_, 1, v_k_4584_);
lean_ctor_set(v___x_4827_, 0, v___x_4733_);
v___x_4831_ = v___x_4827_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4838_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4838_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4838_, 3, v_r_4818_);
lean_ctor_set(v_reuseFailAlloc_4838_, 4, v_r_4818_);
v___x_4831_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4833_; 
lean_inc(v_r_4818_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 3, v_r_4818_);
lean_ctor_set(v___x_4822_, 0, v___x_4733_);
v___x_4833_ = v___x_4822_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4837_, 1, v_k_4819_);
lean_ctor_set(v_reuseFailAlloc_4837_, 2, v_v_4820_);
lean_ctor_set(v_reuseFailAlloc_4837_, 3, v_r_4818_);
lean_ctor_set(v_reuseFailAlloc_4837_, 4, v_r_4818_);
v___x_4833_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
lean_object* v___x_4835_; 
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 4, v___x_4833_);
lean_ctor_set(v___x_4589_, 3, v___x_4831_);
lean_ctor_set(v___x_4589_, 2, v_v_4825_);
lean_ctor_set(v___x_4589_, 1, v_k_4824_);
lean_ctor_set(v___x_4589_, 0, v___x_4829_);
v___x_4835_ = v___x_4589_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4829_);
lean_ctor_set(v_reuseFailAlloc_4836_, 1, v_k_4824_);
lean_ctor_set(v_reuseFailAlloc_4836_, 2, v_v_4825_);
lean_ctor_set(v_reuseFailAlloc_4836_, 3, v___x_4831_);
lean_ctor_set(v_reuseFailAlloc_4836_, 4, v___x_4833_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
}
}
else
{
lean_object* v_r_4846_; 
v_r_4846_ = lean_ctor_get(v_impl_4732_, 4);
lean_inc(v_r_4846_);
if (lean_obj_tag(v_r_4846_) == 0)
{
lean_object* v_k_4847_; lean_object* v_v_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4859_; 
v_k_4847_ = lean_ctor_get(v_impl_4732_, 1);
v_v_4848_ = lean_ctor_get(v_impl_4732_, 2);
v_isSharedCheck_4859_ = !lean_is_exclusive(v_impl_4732_);
if (v_isSharedCheck_4859_ == 0)
{
lean_object* v_unused_4860_; lean_object* v_unused_4861_; lean_object* v_unused_4862_; 
v_unused_4860_ = lean_ctor_get(v_impl_4732_, 4);
lean_dec(v_unused_4860_);
v_unused_4861_ = lean_ctor_get(v_impl_4732_, 3);
lean_dec(v_unused_4861_);
v_unused_4862_ = lean_ctor_get(v_impl_4732_, 0);
lean_dec(v_unused_4862_);
v___x_4850_ = v_impl_4732_;
v_isShared_4851_ = v_isSharedCheck_4859_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_v_4848_);
lean_inc(v_k_4847_);
lean_dec(v_impl_4732_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4859_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4852_; lean_object* v___x_4854_; 
v___x_4852_ = lean_unsigned_to_nat(3u);
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 4, v_l_4817_);
lean_ctor_set(v___x_4850_, 2, v_v_4585_);
lean_ctor_set(v___x_4850_, 1, v_k_4584_);
lean_ctor_set(v___x_4850_, 0, v___x_4733_);
v___x_4854_ = v___x_4850_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4858_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4858_, 3, v_l_4817_);
lean_ctor_set(v_reuseFailAlloc_4858_, 4, v_l_4817_);
v___x_4854_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
lean_object* v___x_4856_; 
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 4, v_r_4846_);
lean_ctor_set(v___x_4589_, 3, v___x_4854_);
lean_ctor_set(v___x_4589_, 2, v_v_4848_);
lean_ctor_set(v___x_4589_, 1, v_k_4847_);
lean_ctor_set(v___x_4589_, 0, v___x_4852_);
v___x_4856_ = v___x_4589_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4852_);
lean_ctor_set(v_reuseFailAlloc_4857_, 1, v_k_4847_);
lean_ctor_set(v_reuseFailAlloc_4857_, 2, v_v_4848_);
lean_ctor_set(v_reuseFailAlloc_4857_, 3, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4857_, 4, v_r_4846_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
}
else
{
lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4863_ = lean_unsigned_to_nat(2u);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 4, v_impl_4732_);
lean_ctor_set(v___x_4589_, 3, v_r_4846_);
lean_ctor_set(v___x_4589_, 0, v___x_4863_);
v___x_4865_ = v___x_4589_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4863_);
lean_ctor_set(v_reuseFailAlloc_4866_, 1, v_k_4584_);
lean_ctor_set(v_reuseFailAlloc_4866_, 2, v_v_4585_);
lean_ctor_set(v_reuseFailAlloc_4866_, 3, v_r_4846_);
lean_ctor_set(v_reuseFailAlloc_4866_, 4, v_impl_4732_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
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
lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4868_ = lean_unsigned_to_nat(1u);
v___x_4869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4868_);
lean_ctor_set(v___x_4869_, 1, v_k_4580_);
lean_ctor_set(v___x_4869_, 2, v_v_4581_);
lean_ctor_set(v___x_4869_, 3, v_t_4582_);
lean_ctor_set(v___x_4869_, 4, v_t_4582_);
return v___x_4869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object* v_as_4870_, size_t v_sz_4871_, size_t v_i_4872_, lean_object* v_b_4873_){
_start:
{
uint8_t v___x_4874_; 
v___x_4874_ = lean_usize_dec_lt(v_i_4872_, v_sz_4871_);
if (v___x_4874_ == 0)
{
return v_b_4873_;
}
else
{
lean_object* v_a_4875_; lean_object* v_fst_4876_; lean_object* v_snd_4877_; lean_object* v_r_4878_; size_t v___x_4879_; size_t v___x_4880_; 
v_a_4875_ = lean_array_uget_borrowed(v_as_4870_, v_i_4872_);
v_fst_4876_ = lean_ctor_get(v_a_4875_, 0);
v_snd_4877_ = lean_ctor_get(v_a_4875_, 1);
lean_inc(v_snd_4877_);
lean_inc(v_fst_4876_);
v_r_4878_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_fst_4876_, v_snd_4877_, v_b_4873_);
v___x_4879_ = ((size_t)1ULL);
v___x_4880_ = lean_usize_add(v_i_4872_, v___x_4879_);
v_i_4872_ = v___x_4880_;
v_b_4873_ = v_r_4878_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object* v_as_4882_, lean_object* v_sz_4883_, lean_object* v_i_4884_, lean_object* v_b_4885_){
_start:
{
size_t v_sz_boxed_4886_; size_t v_i_boxed_4887_; lean_object* v_res_4888_; 
v_sz_boxed_4886_ = lean_unbox_usize(v_sz_4883_);
lean_dec(v_sz_4883_);
v_i_boxed_4887_ = lean_unbox_usize(v_i_4884_);
lean_dec(v_i_4884_);
v_res_4888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v_as_4882_, v_sz_boxed_4886_, v_i_boxed_4887_, v_b_4885_);
lean_dec_ref(v_as_4882_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object* v_a_4891_, lean_object* v_x_4892_){
_start:
{
lean_object* v___y_4894_; 
if (lean_obj_tag(v_x_4892_) == 0)
{
lean_object* v___x_4897_; 
v___x_4897_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___y_4894_ = v___x_4897_;
goto v___jp_4893_;
}
else
{
lean_object* v_val_4898_; 
v_val_4898_ = lean_ctor_get(v_x_4892_, 0);
lean_inc(v_val_4898_);
lean_dec_ref_known(v_x_4892_, 1);
v___y_4894_ = v_val_4898_;
goto v___jp_4893_;
}
v___jp_4893_:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = lean_array_push(v___y_4894_, v_a_4891_);
v___x_4896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4895_);
return v___x_4896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_x_4901_){
_start:
{
if (lean_obj_tag(v_x_4901_) == 0)
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v_val_4904_; lean_object* v___x_4905_; 
v___x_4902_ = lean_box(0);
v___x_4903_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4899_, v___x_4902_);
v_val_4904_ = lean_ctor_get(v___x_4903_, 0);
lean_inc(v_val_4904_);
lean_dec(v___x_4903_);
v___x_4905_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4905_, 0, v_a_4900_);
lean_ctor_set(v___x_4905_, 1, v_val_4904_);
lean_ctor_set(v___x_4905_, 2, v_x_4901_);
return v___x_4905_;
}
else
{
lean_object* v_key_4906_; lean_object* v_value_4907_; lean_object* v_tail_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4923_; 
v_key_4906_ = lean_ctor_get(v_x_4901_, 0);
v_value_4907_ = lean_ctor_get(v_x_4901_, 1);
v_tail_4908_ = lean_ctor_get(v_x_4901_, 2);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_x_4901_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4910_ = v_x_4901_;
v_isShared_4911_ = v_isSharedCheck_4923_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_tail_4908_);
lean_inc(v_value_4907_);
lean_inc(v_key_4906_);
lean_dec(v_x_4901_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4923_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
uint8_t v___x_4912_; 
v___x_4912_ = lean_name_eq(v_key_4906_, v_a_4900_);
if (v___x_4912_ == 0)
{
lean_object* v_tail_4913_; lean_object* v___x_4915_; 
v_tail_4913_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4899_, v_a_4900_, v_tail_4908_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 2, v_tail_4913_);
v___x_4915_ = v___x_4910_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_key_4906_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v_value_4907_);
lean_ctor_set(v_reuseFailAlloc_4916_, 2, v_tail_4913_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
else
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v_val_4919_; lean_object* v___x_4921_; 
lean_dec(v_key_4906_);
v___x_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4917_, 0, v_value_4907_);
v___x_4918_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4899_, v___x_4917_);
v_val_4919_ = lean_ctor_get(v___x_4918_, 0);
lean_inc(v_val_4919_);
lean_dec(v___x_4918_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 1, v_val_4919_);
lean_ctor_set(v___x_4910_, 0, v_a_4900_);
v___x_4921_ = v___x_4910_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4900_);
lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_val_4919_);
lean_ctor_set(v_reuseFailAlloc_4922_, 2, v_tail_4908_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_4924_, lean_object* v_x_4925_){
_start:
{
if (lean_obj_tag(v_x_4925_) == 0)
{
return v_x_4924_;
}
else
{
lean_object* v_key_4926_; lean_object* v_value_4927_; lean_object* v_tail_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4954_; 
v_key_4926_ = lean_ctor_get(v_x_4925_, 0);
v_value_4927_ = lean_ctor_get(v_x_4925_, 1);
v_tail_4928_ = lean_ctor_get(v_x_4925_, 2);
v_isSharedCheck_4954_ = !lean_is_exclusive(v_x_4925_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4930_ = v_x_4925_;
v_isShared_4931_ = v_isSharedCheck_4954_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_tail_4928_);
lean_inc(v_value_4927_);
lean_inc(v_key_4926_);
lean_dec(v_x_4925_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4954_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4932_; uint64_t v___y_4934_; 
v___x_4932_ = lean_array_get_size(v_x_4924_);
if (lean_obj_tag(v_key_4926_) == 0)
{
uint64_t v___x_4952_; 
v___x_4952_ = 1723ULL;
v___y_4934_ = v___x_4952_;
goto v___jp_4933_;
}
else
{
uint64_t v_hash_4953_; 
v_hash_4953_ = lean_ctor_get_uint64(v_key_4926_, sizeof(void*)*2);
v___y_4934_ = v_hash_4953_;
goto v___jp_4933_;
}
v___jp_4933_:
{
uint64_t v___x_4935_; uint64_t v___x_4936_; uint64_t v_fold_4937_; uint64_t v___x_4938_; uint64_t v___x_4939_; uint64_t v___x_4940_; size_t v___x_4941_; size_t v___x_4942_; size_t v___x_4943_; size_t v___x_4944_; size_t v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4948_; 
v___x_4935_ = 32ULL;
v___x_4936_ = lean_uint64_shift_right(v___y_4934_, v___x_4935_);
v_fold_4937_ = lean_uint64_xor(v___y_4934_, v___x_4936_);
v___x_4938_ = 16ULL;
v___x_4939_ = lean_uint64_shift_right(v_fold_4937_, v___x_4938_);
v___x_4940_ = lean_uint64_xor(v_fold_4937_, v___x_4939_);
v___x_4941_ = lean_uint64_to_usize(v___x_4940_);
v___x_4942_ = lean_usize_of_nat(v___x_4932_);
v___x_4943_ = ((size_t)1ULL);
v___x_4944_ = lean_usize_sub(v___x_4942_, v___x_4943_);
v___x_4945_ = lean_usize_land(v___x_4941_, v___x_4944_);
v___x_4946_ = lean_array_uget_borrowed(v_x_4924_, v___x_4945_);
lean_inc(v___x_4946_);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 2, v___x_4946_);
v___x_4948_ = v___x_4930_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_key_4926_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_value_4927_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v___x_4946_);
v___x_4948_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
lean_object* v___x_4949_; 
v___x_4949_ = lean_array_uset(v_x_4924_, v___x_4945_, v___x_4948_);
v_x_4924_ = v___x_4949_;
v_x_4925_ = v_tail_4928_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object* v_i_4955_, lean_object* v_source_4956_, lean_object* v_target_4957_){
_start:
{
lean_object* v___x_4958_; uint8_t v___x_4959_; 
v___x_4958_ = lean_array_get_size(v_source_4956_);
v___x_4959_ = lean_nat_dec_lt(v_i_4955_, v___x_4958_);
if (v___x_4959_ == 0)
{
lean_dec_ref(v_source_4956_);
lean_dec(v_i_4955_);
return v_target_4957_;
}
else
{
lean_object* v_es_4960_; lean_object* v___x_4961_; lean_object* v_source_4962_; lean_object* v_target_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v_es_4960_ = lean_array_fget(v_source_4956_, v_i_4955_);
v___x_4961_ = lean_box(0);
v_source_4962_ = lean_array_fset(v_source_4956_, v_i_4955_, v___x_4961_);
v_target_4963_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_target_4957_, v_es_4960_);
v___x_4964_ = lean_unsigned_to_nat(1u);
v___x_4965_ = lean_nat_add(v_i_4955_, v___x_4964_);
lean_dec(v_i_4955_);
v_i_4955_ = v___x_4965_;
v_source_4956_ = v_source_4962_;
v_target_4957_ = v_target_4963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object* v_data_4967_){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v_nbuckets_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4968_ = lean_array_get_size(v_data_4967_);
v___x_4969_ = lean_unsigned_to_nat(2u);
v_nbuckets_4970_ = lean_nat_mul(v___x_4968_, v___x_4969_);
v___x_4971_ = lean_unsigned_to_nat(0u);
v___x_4972_ = lean_box(0);
v___x_4973_ = lean_mk_array(v_nbuckets_4970_, v___x_4972_);
v___x_4974_ = lean_array_propagate_mark(v_data_4967_, v___x_4973_);
v___x_4975_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_4971_, v_data_4967_, v___x_4974_);
return v___x_4975_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_4976_, lean_object* v_x_4977_){
_start:
{
if (lean_obj_tag(v_x_4977_) == 0)
{
uint8_t v___x_4978_; 
v___x_4978_ = 0;
return v___x_4978_;
}
else
{
lean_object* v_key_4979_; lean_object* v_tail_4980_; uint8_t v___x_4981_; 
v_key_4979_ = lean_ctor_get(v_x_4977_, 0);
v_tail_4980_ = lean_ctor_get(v_x_4977_, 2);
v___x_4981_ = lean_name_eq(v_key_4979_, v_a_4976_);
if (v___x_4981_ == 0)
{
v_x_4977_ = v_tail_4980_;
goto _start;
}
else
{
return v___x_4981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_4983_, lean_object* v_x_4984_){
_start:
{
uint8_t v_res_4985_; lean_object* v_r_4986_; 
v_res_4985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_4983_, v_x_4984_);
lean_dec(v_x_4984_);
lean_dec(v_a_4983_);
v_r_4986_ = lean_box(v_res_4985_);
return v_r_4986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_4987_, lean_object* v_m_4988_, lean_object* v_a_4989_){
_start:
{
size_t v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v_size_4997_; lean_object* v_buckets_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5045_; 
v_size_4997_ = lean_ctor_get(v_m_4988_, 0);
v_buckets_4998_ = lean_ctor_get(v_m_4988_, 1);
v_isSharedCheck_5045_ = !lean_is_exclusive(v_m_4988_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5000_ = v_m_4988_;
v_isShared_5001_ = v_isSharedCheck_5045_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_buckets_4998_);
lean_inc(v_size_4997_);
lean_dec(v_m_4988_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5045_;
goto v_resetjp_4999_;
}
v___jp_4990_:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4995_ = lean_array_uset(v___y_4992_, v___y_4991_, v___y_4993_);
v___x_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4996_, 0, v___y_4994_);
lean_ctor_set(v___x_4996_, 1, v___x_4995_);
return v___x_4996_;
}
v_resetjp_4999_:
{
lean_object* v___x_5002_; uint64_t v___y_5004_; 
v___x_5002_ = lean_array_get_size(v_buckets_4998_);
if (lean_obj_tag(v_a_4989_) == 0)
{
uint64_t v___x_5043_; 
v___x_5043_ = 1723ULL;
v___y_5004_ = v___x_5043_;
goto v___jp_5003_;
}
else
{
uint64_t v_hash_5044_; 
v_hash_5044_ = lean_ctor_get_uint64(v_a_4989_, sizeof(void*)*2);
v___y_5004_ = v_hash_5044_;
goto v___jp_5003_;
}
v___jp_5003_:
{
uint64_t v___x_5005_; uint64_t v___x_5006_; uint64_t v_fold_5007_; uint64_t v___x_5008_; uint64_t v___x_5009_; uint64_t v___x_5010_; size_t v___x_5011_; size_t v___x_5012_; size_t v___x_5013_; size_t v___x_5014_; size_t v___x_5015_; lean_object* v_bkt_5016_; uint8_t v___x_5017_; 
v___x_5005_ = 32ULL;
v___x_5006_ = lean_uint64_shift_right(v___y_5004_, v___x_5005_);
v_fold_5007_ = lean_uint64_xor(v___y_5004_, v___x_5006_);
v___x_5008_ = 16ULL;
v___x_5009_ = lean_uint64_shift_right(v_fold_5007_, v___x_5008_);
v___x_5010_ = lean_uint64_xor(v_fold_5007_, v___x_5009_);
v___x_5011_ = lean_uint64_to_usize(v___x_5010_);
v___x_5012_ = lean_usize_of_nat(v___x_5002_);
v___x_5013_ = ((size_t)1ULL);
v___x_5014_ = lean_usize_sub(v___x_5012_, v___x_5013_);
v___x_5015_ = lean_usize_land(v___x_5011_, v___x_5014_);
v_bkt_5016_ = lean_array_uget_borrowed(v_buckets_4998_, v___x_5015_);
v___x_5017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_4989_, v_bkt_5016_);
if (v___x_5017_ == 0)
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v_size_x27_5021_; lean_object* v___x_5022_; lean_object* v_buckets_x27_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; uint8_t v___x_5029_; 
v___x_5018_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_5019_ = lean_array_push(v___x_5018_, v_a_4987_);
v___x_5020_ = lean_unsigned_to_nat(1u);
v_size_x27_5021_ = lean_nat_add(v_size_4997_, v___x_5020_);
lean_dec(v_size_4997_);
lean_inc(v_bkt_5016_);
v___x_5022_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5022_, 0, v_a_4989_);
lean_ctor_set(v___x_5022_, 1, v___x_5019_);
lean_ctor_set(v___x_5022_, 2, v_bkt_5016_);
v_buckets_x27_5023_ = lean_array_uset(v_buckets_4998_, v___x_5015_, v___x_5022_);
v___x_5024_ = lean_unsigned_to_nat(4u);
v___x_5025_ = lean_nat_mul(v_size_x27_5021_, v___x_5024_);
v___x_5026_ = lean_unsigned_to_nat(3u);
v___x_5027_ = lean_nat_div(v___x_5025_, v___x_5026_);
lean_dec(v___x_5025_);
v___x_5028_ = lean_array_get_size(v_buckets_x27_5023_);
v___x_5029_ = lean_nat_dec_le(v___x_5027_, v___x_5028_);
lean_dec(v___x_5027_);
if (v___x_5029_ == 0)
{
lean_object* v_val_5030_; lean_object* v___x_5032_; 
v_val_5030_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5023_);
if (v_isShared_5001_ == 0)
{
lean_ctor_set(v___x_5000_, 1, v_val_5030_);
lean_ctor_set(v___x_5000_, 0, v_size_x27_5021_);
v___x_5032_ = v___x_5000_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_size_x27_5021_);
lean_ctor_set(v_reuseFailAlloc_5033_, 1, v_val_5030_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
return v___x_5032_;
}
}
else
{
lean_object* v___x_5035_; 
if (v_isShared_5001_ == 0)
{
lean_ctor_set(v___x_5000_, 1, v_buckets_x27_5023_);
lean_ctor_set(v___x_5000_, 0, v_size_x27_5021_);
v___x_5035_ = v___x_5000_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_size_x27_5021_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v_buckets_x27_5023_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
}
else
{
lean_object* v___x_5037_; lean_object* v_buckets_x27_5038_; lean_object* v_bkt_x27_5039_; uint8_t v___x_5040_; 
lean_inc(v_bkt_5016_);
lean_del_object(v___x_5000_);
v___x_5037_ = lean_box(0);
v_buckets_x27_5038_ = lean_array_uset(v_buckets_4998_, v___x_5015_, v___x_5037_);
lean_inc(v_a_4989_);
v_bkt_x27_5039_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4987_, v_a_4989_, v_bkt_5016_);
v___x_5040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_4989_, v_bkt_x27_5039_);
lean_dec(v_a_4989_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5041_ = lean_unsigned_to_nat(1u);
v___x_5042_ = lean_nat_sub(v_size_4997_, v___x_5041_);
lean_dec(v_size_4997_);
v___y_4991_ = v___x_5015_;
v___y_4992_ = v_buckets_x27_5038_;
v___y_4993_ = v_bkt_x27_5039_;
v___y_4994_ = v___x_5042_;
goto v___jp_4990_;
}
else
{
v___y_4991_ = v___x_5015_;
v___y_4992_ = v_buckets_x27_5038_;
v___y_4993_ = v_bkt_x27_5039_;
v___y_4994_ = v_size_4997_;
goto v___jp_4990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5046_, lean_object* v_as_5047_, size_t v_sz_5048_, size_t v_i_5049_, lean_object* v_b_5050_){
_start:
{
uint8_t v___x_5051_; 
v___x_5051_ = lean_usize_dec_lt(v_i_5049_, v_sz_5048_);
if (v___x_5051_ == 0)
{
lean_dec_ref(v_key_5046_);
return v_b_5050_;
}
else
{
lean_object* v_a_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; size_t v___x_5055_; size_t v___x_5056_; 
v_a_5052_ = lean_array_uget_borrowed(v_as_5047_, v_i_5049_);
lean_inc_ref(v_key_5046_);
lean_inc_n(v_a_5052_, 2);
v___x_5053_ = lean_apply_1(v_key_5046_, v_a_5052_);
v___x_5054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5052_, v_b_5050_, v___x_5053_);
v___x_5055_ = ((size_t)1ULL);
v___x_5056_ = lean_usize_add(v_i_5049_, v___x_5055_);
v_i_5049_ = v___x_5056_;
v_b_5050_ = v___x_5054_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5058_, lean_object* v_as_5059_, lean_object* v_sz_5060_, lean_object* v_i_5061_, lean_object* v_b_5062_){
_start:
{
size_t v_sz_boxed_5063_; size_t v_i_boxed_5064_; lean_object* v_res_5065_; 
v_sz_boxed_5063_ = lean_unbox_usize(v_sz_5060_);
lean_dec(v_sz_5060_);
v_i_boxed_5064_ = lean_unbox_usize(v_i_5061_);
lean_dec(v_i_5061_);
v_res_5065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5058_, v_as_5059_, v_sz_boxed_5063_, v_i_boxed_5064_, v_b_5062_);
lean_dec_ref(v_as_5059_);
return v_res_5065_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5066_ = lean_box(0);
v___x_5067_ = lean_unsigned_to_nat(16u);
v___x_5068_ = lean_mk_array(v___x_5067_, v___x_5066_);
return v___x_5068_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v_groups_5071_; 
v___x_5069_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5070_ = lean_unsigned_to_nat(0u);
v_groups_5071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5071_, 0, v___x_5070_);
lean_ctor_set(v_groups_5071_, 1, v___x_5069_);
return v_groups_5071_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5072_, lean_object* v_xs_5073_){
_start:
{
lean_object* v_groups_5074_; size_t v_sz_5075_; size_t v___x_5076_; lean_object* v___x_5077_; 
v_groups_5074_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5075_ = lean_array_size(v_xs_5073_);
v___x_5076_ = ((size_t)0ULL);
v___x_5077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5072_, v_xs_5073_, v_sz_5075_, v___x_5076_, v_groups_5074_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5078_, lean_object* v_xs_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5078_, v_xs_5079_);
lean_dec_ref(v_xs_5079_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5082_){
_start:
{
lean_object* v___f_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___f_5084_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5085_ = lean_unsigned_to_nat(0u);
v___x_5086_ = lean_array_get_size(v_infos_5082_);
v___x_5087_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5082_, v___x_5085_, v___x_5086_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5111_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5090_ = v___x_5087_;
v_isShared_5091_ = v_isSharedCheck_5111_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5087_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5111_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___y_5093_; lean_object* v___x_5102_; lean_object* v_size_5103_; lean_object* v_buckets_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; uint8_t v___x_5107_; 
v___x_5102_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5084_, v_a_5088_);
v_size_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_size_5103_);
v_buckets_5104_ = lean_ctor_get(v___x_5102_, 1);
lean_inc_ref(v_buckets_5104_);
lean_dec_ref(v___x_5102_);
v___x_5105_ = lean_mk_empty_array_with_capacity(v_size_5103_);
lean_dec(v_size_5103_);
v___x_5106_ = lean_array_get_size(v_buckets_5104_);
v___x_5107_ = lean_nat_dec_lt(v___x_5085_, v___x_5106_);
if (v___x_5107_ == 0)
{
lean_dec_ref(v_buckets_5104_);
v___y_5093_ = v___x_5105_;
goto v___jp_5092_;
}
else
{
size_t v___x_5108_; size_t v___x_5109_; lean_object* v___x_5110_; 
v___x_5108_ = ((size_t)0ULL);
v___x_5109_ = lean_usize_of_nat(v___x_5106_);
v___x_5110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5104_, v___x_5108_, v___x_5109_, v___x_5105_);
lean_dec_ref(v_buckets_5104_);
v___y_5093_ = v___x_5110_;
goto v___jp_5092_;
}
v___jp_5092_:
{
lean_object* v_r_5094_; size_t v_sz_5095_; size_t v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5100_; 
v_r_5094_ = lean_box(1);
v_sz_5095_ = lean_array_size(v___y_5093_);
v___x_5096_ = ((size_t)0ULL);
v___x_5097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5093_, v_sz_5095_, v___x_5096_, v_r_5094_);
lean_dec_ref(v___y_5093_);
v___x_5098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5098_, 0, v_a_5088_);
lean_ctor_set(v___x_5098_, 1, v___x_5097_);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 0, v___x_5098_);
v___x_5100_ = v___x_5090_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v___x_5098_);
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
else
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
v_a_5112_ = lean_ctor_get(v___x_5087_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___x_5087_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5087_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5120_, lean_object* v_a_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5120_);
lean_dec_ref(v_infos_5120_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5123_, lean_object* v_k_5124_, lean_object* v_v_5125_, lean_object* v_t_5126_, lean_object* v_hl_5127_){
_start:
{
lean_object* v___x_5128_; 
v___x_5128_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5124_, v_v_5125_, v_t_5126_);
return v___x_5128_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5129_, lean_object* v_key_5130_, lean_object* v_xs_5131_){
_start:
{
lean_object* v___x_5132_; 
v___x_5132_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5130_, v_xs_5131_);
return v___x_5132_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5133_, lean_object* v_key_5134_, lean_object* v_xs_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5133_, v_key_5134_, v_xs_5135_);
lean_dec_ref(v_xs_5135_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5137_, lean_object* v_a_5138_, lean_object* v_m_5139_, lean_object* v_a_5140_){
_start:
{
lean_object* v___x_5141_; 
v___x_5141_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5138_, v_m_5139_, v_a_5140_);
return v___x_5141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5142_, lean_object* v_key_5143_, lean_object* v_as_5144_, size_t v_sz_5145_, size_t v_i_5146_, lean_object* v_b_5147_){
_start:
{
lean_object* v___x_5148_; 
v___x_5148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5143_, v_as_5144_, v_sz_5145_, v_i_5146_, v_b_5147_);
return v___x_5148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5149_, lean_object* v_key_5150_, lean_object* v_as_5151_, lean_object* v_sz_5152_, lean_object* v_i_5153_, lean_object* v_b_5154_){
_start:
{
size_t v_sz_boxed_5155_; size_t v_i_boxed_5156_; lean_object* v_res_5157_; 
v_sz_boxed_5155_ = lean_unbox_usize(v_sz_5152_);
lean_dec(v_sz_5152_);
v_i_boxed_5156_ = lean_unbox_usize(v_i_5153_);
lean_dec(v_i_5153_);
v_res_5157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5149_, v_key_5150_, v_as_5151_, v_sz_boxed_5155_, v_i_boxed_5156_, v_b_5154_);
lean_dec_ref(v_as_5151_);
return v_res_5157_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5158_, lean_object* v_a_5159_, lean_object* v_x_5160_){
_start:
{
uint8_t v___x_5161_; 
v___x_5161_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5159_, v_x_5160_);
return v___x_5161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5162_, lean_object* v_a_5163_, lean_object* v_x_5164_){
_start:
{
uint8_t v_res_5165_; lean_object* v_r_5166_; 
v_res_5165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5162_, v_a_5163_, v_x_5164_);
lean_dec(v_x_5164_);
lean_dec(v_a_5163_);
v_r_5166_ = lean_box(v_res_5165_);
return v_r_5166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5167_, lean_object* v_data_5168_){
_start:
{
lean_object* v___x_5169_; 
v___x_5169_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5168_);
return v___x_5169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_x_5173_){
_start:
{
lean_object* v___x_5174_; 
v___x_5174_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5171_, v_a_5172_, v_x_5173_);
return v___x_5174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5175_, lean_object* v_i_5176_, lean_object* v_source_5177_, lean_object* v_target_5178_){
_start:
{
lean_object* v___x_5179_; 
v___x_5179_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5176_, v_source_5177_, v_target_5178_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5180_, lean_object* v_x_5181_, lean_object* v_x_5182_){
_start:
{
lean_object* v___x_5183_; 
v___x_5183_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5181_, v_x_5182_);
return v___x_5183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5184_){
_start:
{
lean_object* v_isSetupFailure_x3f_5185_; 
v_isSetupFailure_x3f_5185_ = lean_ctor_get(v_i_5184_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5185_) == 0)
{
uint8_t v___x_5186_; 
v___x_5186_ = 0;
return v___x_5186_;
}
else
{
lean_object* v_val_5187_; uint8_t v___x_5188_; 
v_val_5187_ = lean_ctor_get(v_isSetupFailure_x3f_5185_, 0);
v___x_5188_ = lean_unbox(v_val_5187_);
if (v___x_5188_ == 0)
{
uint8_t v___x_5189_; 
v___x_5189_ = 1;
return v___x_5189_;
}
else
{
uint8_t v___x_5190_; 
v___x_5190_ = 0;
return v___x_5190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5191_){
_start:
{
uint8_t v_res_5192_; lean_object* v_r_5193_; 
v_res_5192_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5191_);
lean_dec_ref(v_i_5191_);
v_r_5193_ = lean_box(v_res_5192_);
return v_r_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5199_, lean_object* v_path_5200_, lean_object* v_ilean_5201_){
_start:
{
lean_object* v_module_5203_; lean_object* v_directImports_5204_; lean_object* v_references_5205_; lean_object* v_decls_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5258_; 
v_module_5203_ = lean_ctor_get(v_ilean_5201_, 1);
v_directImports_5204_ = lean_ctor_get(v_ilean_5201_, 2);
v_references_5205_ = lean_ctor_get(v_ilean_5201_, 3);
v_decls_5206_ = lean_ctor_get(v_ilean_5201_, 4);
v_isSharedCheck_5258_ = !lean_is_exclusive(v_ilean_5201_);
if (v_isSharedCheck_5258_ == 0)
{
lean_object* v_unused_5259_; 
v_unused_5259_ = lean_ctor_get(v_ilean_5201_, 0);
lean_dec(v_unused_5259_);
v___x_5208_ = v_ilean_5201_;
v_isShared_5209_ = v_isSharedCheck_5258_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_decls_5206_);
lean_inc(v_references_5205_);
lean_inc(v_directImports_5204_);
lean_inc(v_module_5203_);
lean_dec(v_ilean_5201_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5258_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5210_; 
lean_inc(v_module_5203_);
v___x_5210_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5203_);
if (lean_obj_tag(v___x_5210_) == 0)
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5249_; 
v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5213_ = v___x_5210_;
v_isShared_5214_ = v_isSharedCheck_5249_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5210_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5249_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
if (lean_obj_tag(v_a_5211_) == 1)
{
lean_object* v_val_5215_; lean_object* v___x_5216_; 
lean_del_object(v___x_5213_);
v_val_5215_ = lean_ctor_get(v_a_5211_, 0);
lean_inc(v_val_5215_);
lean_dec_ref_known(v_a_5211_, 1);
v___x_5216_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5204_);
lean_dec_ref(v_directImports_5204_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5237_; 
v_a_5217_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5219_ = v___x_5216_;
v_isShared_5220_ = v_isSharedCheck_5237_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_a_5217_);
lean_dec(v___x_5216_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5237_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v_ileans_5221_; lean_object* v_workers_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5236_; 
v_ileans_5221_ = lean_ctor_get(v_self_5199_, 0);
v_workers_5222_ = lean_ctor_get(v_self_5199_, 1);
v_isSharedCheck_5236_ = !lean_is_exclusive(v_self_5199_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5224_ = v_self_5199_;
v_isShared_5225_ = v_isSharedCheck_5236_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_workers_5222_);
lean_inc(v_ileans_5221_);
lean_dec(v_self_5199_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5236_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5227_; 
if (v_isShared_5209_ == 0)
{
lean_ctor_set(v___x_5208_, 2, v_a_5217_);
lean_ctor_set(v___x_5208_, 1, v_path_5200_);
lean_ctor_set(v___x_5208_, 0, v_val_5215_);
v___x_5227_ = v___x_5208_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_val_5215_);
lean_ctor_set(v_reuseFailAlloc_5235_, 1, v_path_5200_);
lean_ctor_set(v_reuseFailAlloc_5235_, 2, v_a_5217_);
lean_ctor_set(v_reuseFailAlloc_5235_, 3, v_references_5205_);
lean_ctor_set(v_reuseFailAlloc_5235_, 4, v_decls_5206_);
v___x_5227_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
lean_object* v___x_5228_; lean_object* v___x_5230_; 
v___x_5228_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5203_, v___x_5227_, v_ileans_5221_);
if (v_isShared_5225_ == 0)
{
lean_ctor_set(v___x_5224_, 0, v___x_5228_);
v___x_5230_ = v___x_5224_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5228_);
lean_ctor_set(v_reuseFailAlloc_5234_, 1, v_workers_5222_);
v___x_5230_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
lean_object* v___x_5232_; 
if (v_isShared_5220_ == 0)
{
lean_ctor_set(v___x_5219_, 0, v___x_5230_);
v___x_5232_ = v___x_5219_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5230_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
}
}
}
}
else
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5245_; 
lean_dec(v_val_5215_);
lean_del_object(v___x_5208_);
lean_dec(v_decls_5206_);
lean_dec(v_references_5205_);
lean_dec(v_module_5203_);
lean_dec_ref(v_path_5200_);
lean_dec_ref(v_self_5199_);
v_a_5238_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5240_ = v___x_5216_;
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5216_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5243_; 
if (v_isShared_5241_ == 0)
{
v___x_5243_ = v___x_5240_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
else
{
lean_object* v___x_5247_; 
lean_dec(v_a_5211_);
lean_del_object(v___x_5208_);
lean_dec(v_decls_5206_);
lean_dec(v_references_5205_);
lean_dec_ref(v_directImports_5204_);
lean_dec(v_module_5203_);
lean_dec_ref(v_path_5200_);
if (v_isShared_5214_ == 0)
{
lean_ctor_set(v___x_5213_, 0, v_self_5199_);
v___x_5247_ = v___x_5213_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_self_5199_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
}
else
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5257_; 
lean_del_object(v___x_5208_);
lean_dec(v_decls_5206_);
lean_dec(v_references_5205_);
lean_dec_ref(v_directImports_5204_);
lean_dec(v_module_5203_);
lean_dec_ref(v_path_5200_);
lean_dec_ref(v_self_5199_);
v_a_5250_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5252_ = v___x_5210_;
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5210_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v___x_5255_; 
if (v_isShared_5253_ == 0)
{
v___x_5255_ = v___x_5252_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_a_5250_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5260_, lean_object* v_path_5261_, lean_object* v_ilean_5262_, lean_object* v_a_5263_){
_start:
{
lean_object* v_res_5264_; 
v_res_5264_ = l_Lean_Server_References_addIlean(v_self_5260_, v_path_5261_, v_ilean_5262_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5265_, lean_object* v_t_5266_){
_start:
{
if (lean_obj_tag(v_t_5266_) == 0)
{
lean_object* v_v_5267_; lean_object* v_k_5268_; lean_object* v_l_5269_; lean_object* v_r_5270_; lean_object* v_ileanPath_5271_; uint8_t v___x_5272_; 
v_v_5267_ = lean_ctor_get(v_t_5266_, 2);
lean_inc(v_v_5267_);
v_k_5268_ = lean_ctor_get(v_t_5266_, 1);
lean_inc(v_k_5268_);
v_l_5269_ = lean_ctor_get(v_t_5266_, 3);
lean_inc(v_l_5269_);
v_r_5270_ = lean_ctor_get(v_t_5266_, 4);
lean_inc(v_r_5270_);
lean_dec_ref_known(v_t_5266_, 5);
v_ileanPath_5271_ = lean_ctor_get(v_v_5267_, 1);
v___x_5272_ = lean_string_dec_eq(v_ileanPath_5271_, v_path_5265_);
if (v___x_5272_ == 0)
{
lean_object* v_impl_5273_; lean_object* v_impl_5274_; lean_object* v___x_5275_; 
lean_dec(v_k_5268_);
lean_dec(v_v_5267_);
v_impl_5273_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5265_, v_l_5269_);
v_impl_5274_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5265_, v_r_5270_);
v___x_5275_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5273_, v_impl_5274_);
return v___x_5275_;
}
else
{
lean_object* v_impl_5276_; lean_object* v_impl_5277_; lean_object* v___x_5278_; 
v_impl_5276_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5265_, v_l_5269_);
v_impl_5277_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5265_, v_r_5270_);
v___x_5278_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5268_, v_v_5267_, v_impl_5276_, v_impl_5277_);
return v___x_5278_;
}
}
else
{
return v_t_5266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5279_, lean_object* v_t_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5279_, v_t_5280_);
lean_dec_ref(v_path_5279_);
return v_res_5281_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5282_, lean_object* v_t_5283_){
_start:
{
if (lean_obj_tag(v_t_5283_) == 0)
{
lean_object* v_k_5284_; lean_object* v_v_5285_; lean_object* v_l_5286_; lean_object* v_r_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5941_; 
v_k_5284_ = lean_ctor_get(v_t_5283_, 1);
v_v_5285_ = lean_ctor_get(v_t_5283_, 2);
v_l_5286_ = lean_ctor_get(v_t_5283_, 3);
v_r_5287_ = lean_ctor_get(v_t_5283_, 4);
v_isSharedCheck_5941_ = !lean_is_exclusive(v_t_5283_);
if (v_isSharedCheck_5941_ == 0)
{
lean_object* v_unused_5942_; 
v_unused_5942_ = lean_ctor_get(v_t_5283_, 0);
lean_dec(v_unused_5942_);
v___x_5289_ = v_t_5283_;
v_isShared_5290_ = v_isSharedCheck_5941_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_r_5287_);
lean_inc(v_l_5286_);
lean_inc(v_v_5285_);
lean_inc(v_k_5284_);
lean_dec(v_t_5283_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5941_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
uint8_t v___x_5291_; 
v___x_5291_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5282_, v_k_5284_);
switch(v___x_5291_)
{
case 0:
{
lean_object* v_impl_5292_; lean_object* v___x_5293_; 
v_impl_5292_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5282_, v_l_5286_);
v___x_5293_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5292_) == 0)
{
if (lean_obj_tag(v_r_5287_) == 0)
{
lean_object* v_size_5294_; lean_object* v_size_5295_; lean_object* v_k_5296_; lean_object* v_v_5297_; lean_object* v_l_5298_; lean_object* v_r_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; uint8_t v___x_5302_; 
v_size_5294_ = lean_ctor_get(v_impl_5292_, 0);
v_size_5295_ = lean_ctor_get(v_r_5287_, 0);
v_k_5296_ = lean_ctor_get(v_r_5287_, 1);
v_v_5297_ = lean_ctor_get(v_r_5287_, 2);
v_l_5298_ = lean_ctor_get(v_r_5287_, 3);
lean_inc(v_l_5298_);
v_r_5299_ = lean_ctor_get(v_r_5287_, 4);
v___x_5300_ = lean_unsigned_to_nat(3u);
v___x_5301_ = lean_nat_mul(v___x_5300_, v_size_5294_);
v___x_5302_ = lean_nat_dec_lt(v___x_5301_, v_size_5295_);
lean_dec(v___x_5301_);
if (v___x_5302_ == 0)
{
lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5306_; 
lean_dec(v_l_5298_);
v___x_5303_ = lean_nat_add(v___x_5293_, v_size_5294_);
v___x_5304_ = lean_nat_add(v___x_5303_, v_size_5295_);
lean_dec(v___x_5303_);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 3, v_impl_5292_);
lean_ctor_set(v___x_5289_, 0, v___x_5304_);
v___x_5306_ = v___x_5289_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v___x_5304_);
lean_ctor_set(v_reuseFailAlloc_5307_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5307_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5307_, 3, v_impl_5292_);
lean_ctor_set(v_reuseFailAlloc_5307_, 4, v_r_5287_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
else
{
lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5371_; 
lean_inc(v_r_5299_);
lean_inc(v_v_5297_);
lean_inc(v_k_5296_);
lean_inc(v_size_5295_);
v_isSharedCheck_5371_ = !lean_is_exclusive(v_r_5287_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; lean_object* v_unused_5373_; lean_object* v_unused_5374_; lean_object* v_unused_5375_; lean_object* v_unused_5376_; 
v_unused_5372_ = lean_ctor_get(v_r_5287_, 4);
lean_dec(v_unused_5372_);
v_unused_5373_ = lean_ctor_get(v_r_5287_, 3);
lean_dec(v_unused_5373_);
v_unused_5374_ = lean_ctor_get(v_r_5287_, 2);
lean_dec(v_unused_5374_);
v_unused_5375_ = lean_ctor_get(v_r_5287_, 1);
lean_dec(v_unused_5375_);
v_unused_5376_ = lean_ctor_get(v_r_5287_, 0);
lean_dec(v_unused_5376_);
v___x_5309_ = v_r_5287_;
v_isShared_5310_ = v_isSharedCheck_5371_;
goto v_resetjp_5308_;
}
else
{
lean_dec(v_r_5287_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5371_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v_size_5311_; lean_object* v_k_5312_; lean_object* v_v_5313_; lean_object* v_l_5314_; lean_object* v_r_5315_; lean_object* v_size_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; uint8_t v___x_5319_; 
v_size_5311_ = lean_ctor_get(v_l_5298_, 0);
v_k_5312_ = lean_ctor_get(v_l_5298_, 1);
v_v_5313_ = lean_ctor_get(v_l_5298_, 2);
v_l_5314_ = lean_ctor_get(v_l_5298_, 3);
v_r_5315_ = lean_ctor_get(v_l_5298_, 4);
v_size_5316_ = lean_ctor_get(v_r_5299_, 0);
v___x_5317_ = lean_unsigned_to_nat(2u);
v___x_5318_ = lean_nat_mul(v___x_5317_, v_size_5316_);
v___x_5319_ = lean_nat_dec_lt(v_size_5311_, v___x_5318_);
lean_dec(v___x_5318_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5347_; 
lean_inc(v_r_5315_);
lean_inc(v_l_5314_);
lean_inc(v_v_5313_);
lean_inc(v_k_5312_);
v_isSharedCheck_5347_ = !lean_is_exclusive(v_l_5298_);
if (v_isSharedCheck_5347_ == 0)
{
lean_object* v_unused_5348_; lean_object* v_unused_5349_; lean_object* v_unused_5350_; lean_object* v_unused_5351_; lean_object* v_unused_5352_; 
v_unused_5348_ = lean_ctor_get(v_l_5298_, 4);
lean_dec(v_unused_5348_);
v_unused_5349_ = lean_ctor_get(v_l_5298_, 3);
lean_dec(v_unused_5349_);
v_unused_5350_ = lean_ctor_get(v_l_5298_, 2);
lean_dec(v_unused_5350_);
v_unused_5351_ = lean_ctor_get(v_l_5298_, 1);
lean_dec(v_unused_5351_);
v_unused_5352_ = lean_ctor_get(v_l_5298_, 0);
lean_dec(v_unused_5352_);
v___x_5321_ = v_l_5298_;
v_isShared_5322_ = v_isSharedCheck_5347_;
goto v_resetjp_5320_;
}
else
{
lean_dec(v_l_5298_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5347_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___y_5326_; lean_object* v___y_5327_; lean_object* v___y_5328_; lean_object* v___y_5337_; 
v___x_5323_ = lean_nat_add(v___x_5293_, v_size_5294_);
v___x_5324_ = lean_nat_add(v___x_5323_, v_size_5295_);
lean_dec(v_size_5295_);
if (lean_obj_tag(v_l_5314_) == 0)
{
lean_object* v_size_5345_; 
v_size_5345_ = lean_ctor_get(v_l_5314_, 0);
lean_inc(v_size_5345_);
v___y_5337_ = v_size_5345_;
goto v___jp_5336_;
}
else
{
lean_object* v___x_5346_; 
v___x_5346_ = lean_unsigned_to_nat(0u);
v___y_5337_ = v___x_5346_;
goto v___jp_5336_;
}
v___jp_5325_:
{
lean_object* v___x_5329_; lean_object* v___x_5331_; 
v___x_5329_ = lean_nat_add(v___y_5327_, v___y_5328_);
lean_dec(v___y_5328_);
lean_dec(v___y_5327_);
if (v_isShared_5322_ == 0)
{
lean_ctor_set(v___x_5321_, 4, v_r_5299_);
lean_ctor_set(v___x_5321_, 3, v_r_5315_);
lean_ctor_set(v___x_5321_, 2, v_v_5297_);
lean_ctor_set(v___x_5321_, 1, v_k_5296_);
lean_ctor_set(v___x_5321_, 0, v___x_5329_);
v___x_5331_ = v___x_5321_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5329_);
lean_ctor_set(v_reuseFailAlloc_5335_, 1, v_k_5296_);
lean_ctor_set(v_reuseFailAlloc_5335_, 2, v_v_5297_);
lean_ctor_set(v_reuseFailAlloc_5335_, 3, v_r_5315_);
lean_ctor_set(v_reuseFailAlloc_5335_, 4, v_r_5299_);
v___x_5331_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
lean_object* v___x_5333_; 
if (v_isShared_5310_ == 0)
{
lean_ctor_set(v___x_5309_, 4, v___x_5331_);
lean_ctor_set(v___x_5309_, 3, v___y_5326_);
lean_ctor_set(v___x_5309_, 2, v_v_5313_);
lean_ctor_set(v___x_5309_, 1, v_k_5312_);
lean_ctor_set(v___x_5309_, 0, v___x_5324_);
v___x_5333_ = v___x_5309_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5324_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v_k_5312_);
lean_ctor_set(v_reuseFailAlloc_5334_, 2, v_v_5313_);
lean_ctor_set(v_reuseFailAlloc_5334_, 3, v___y_5326_);
lean_ctor_set(v_reuseFailAlloc_5334_, 4, v___x_5331_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
v___jp_5336_:
{
lean_object* v___x_5338_; lean_object* v___x_5340_; 
v___x_5338_ = lean_nat_add(v___x_5323_, v___y_5337_);
lean_dec(v___y_5337_);
lean_dec(v___x_5323_);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v_l_5314_);
lean_ctor_set(v___x_5289_, 3, v_impl_5292_);
lean_ctor_set(v___x_5289_, 0, v___x_5338_);
v___x_5340_ = v___x_5289_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v___x_5338_);
lean_ctor_set(v_reuseFailAlloc_5344_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5344_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5344_, 3, v_impl_5292_);
lean_ctor_set(v_reuseFailAlloc_5344_, 4, v_l_5314_);
v___x_5340_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
lean_object* v___x_5341_; 
v___x_5341_ = lean_nat_add(v___x_5293_, v_size_5316_);
if (lean_obj_tag(v_r_5315_) == 0)
{
lean_object* v_size_5342_; 
v_size_5342_ = lean_ctor_get(v_r_5315_, 0);
lean_inc(v_size_5342_);
v___y_5326_ = v___x_5340_;
v___y_5327_ = v___x_5341_;
v___y_5328_ = v_size_5342_;
goto v___jp_5325_;
}
else
{
lean_object* v___x_5343_; 
v___x_5343_ = lean_unsigned_to_nat(0u);
v___y_5326_ = v___x_5340_;
v___y_5327_ = v___x_5341_;
v___y_5328_ = v___x_5343_;
goto v___jp_5325_;
}
}
}
}
}
else
{
lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5357_; 
lean_del_object(v___x_5289_);
v___x_5353_ = lean_nat_add(v___x_5293_, v_size_5294_);
v___x_5354_ = lean_nat_add(v___x_5353_, v_size_5295_);
lean_dec(v_size_5295_);
v___x_5355_ = lean_nat_add(v___x_5353_, v_size_5311_);
lean_dec(v___x_5353_);
lean_inc_ref(v_impl_5292_);
if (v_isShared_5310_ == 0)
{
lean_ctor_set(v___x_5309_, 4, v_l_5298_);
lean_ctor_set(v___x_5309_, 3, v_impl_5292_);
lean_ctor_set(v___x_5309_, 2, v_v_5285_);
lean_ctor_set(v___x_5309_, 1, v_k_5284_);
lean_ctor_set(v___x_5309_, 0, v___x_5355_);
v___x_5357_ = v___x_5309_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5355_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5370_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5370_, 3, v_impl_5292_);
lean_ctor_set(v_reuseFailAlloc_5370_, 4, v_l_5298_);
v___x_5357_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
v_isSharedCheck_5364_ = !lean_is_exclusive(v_impl_5292_);
if (v_isSharedCheck_5364_ == 0)
{
lean_object* v_unused_5365_; lean_object* v_unused_5366_; lean_object* v_unused_5367_; lean_object* v_unused_5368_; lean_object* v_unused_5369_; 
v_unused_5365_ = lean_ctor_get(v_impl_5292_, 4);
lean_dec(v_unused_5365_);
v_unused_5366_ = lean_ctor_get(v_impl_5292_, 3);
lean_dec(v_unused_5366_);
v_unused_5367_ = lean_ctor_get(v_impl_5292_, 2);
lean_dec(v_unused_5367_);
v_unused_5368_ = lean_ctor_get(v_impl_5292_, 1);
lean_dec(v_unused_5368_);
v_unused_5369_ = lean_ctor_get(v_impl_5292_, 0);
lean_dec(v_unused_5369_);
v___x_5359_ = v_impl_5292_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_dec(v_impl_5292_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
lean_ctor_set(v___x_5359_, 4, v_r_5299_);
lean_ctor_set(v___x_5359_, 3, v___x_5357_);
lean_ctor_set(v___x_5359_, 2, v_v_5297_);
lean_ctor_set(v___x_5359_, 1, v_k_5296_);
lean_ctor_set(v___x_5359_, 0, v___x_5354_);
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5354_);
lean_ctor_set(v_reuseFailAlloc_5363_, 1, v_k_5296_);
lean_ctor_set(v_reuseFailAlloc_5363_, 2, v_v_5297_);
lean_ctor_set(v_reuseFailAlloc_5363_, 3, v___x_5357_);
lean_ctor_set(v_reuseFailAlloc_5363_, 4, v_r_5299_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5377_; lean_object* v___x_5378_; lean_object* v___x_5380_; 
v_size_5377_ = lean_ctor_get(v_impl_5292_, 0);
v___x_5378_ = lean_nat_add(v___x_5293_, v_size_5377_);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 3, v_impl_5292_);
lean_ctor_set(v___x_5289_, 0, v___x_5378_);
v___x_5380_ = v___x_5289_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5378_);
lean_ctor_set(v_reuseFailAlloc_5381_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5381_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5381_, 3, v_impl_5292_);
lean_ctor_set(v_reuseFailAlloc_5381_, 4, v_r_5287_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
else
{
if (lean_obj_tag(v_r_5287_) == 0)
{
lean_object* v_l_5382_; 
v_l_5382_ = lean_ctor_get(v_r_5287_, 3);
lean_inc(v_l_5382_);
if (lean_obj_tag(v_l_5382_) == 0)
{
lean_object* v_r_5383_; 
v_r_5383_ = lean_ctor_get(v_r_5287_, 4);
lean_inc(v_r_5383_);
if (lean_obj_tag(v_r_5383_) == 0)
{
lean_object* v_size_5384_; lean_object* v_k_5385_; lean_object* v_v_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5399_; 
v_size_5384_ = lean_ctor_get(v_r_5287_, 0);
v_k_5385_ = lean_ctor_get(v_r_5287_, 1);
v_v_5386_ = lean_ctor_get(v_r_5287_, 2);
v_isSharedCheck_5399_ = !lean_is_exclusive(v_r_5287_);
if (v_isSharedCheck_5399_ == 0)
{
lean_object* v_unused_5400_; lean_object* v_unused_5401_; 
v_unused_5400_ = lean_ctor_get(v_r_5287_, 4);
lean_dec(v_unused_5400_);
v_unused_5401_ = lean_ctor_get(v_r_5287_, 3);
lean_dec(v_unused_5401_);
v___x_5388_ = v_r_5287_;
v_isShared_5389_ = v_isSharedCheck_5399_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_v_5386_);
lean_inc(v_k_5385_);
lean_inc(v_size_5384_);
lean_dec(v_r_5287_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5399_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v_size_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5394_; 
v_size_5390_ = lean_ctor_get(v_l_5382_, 0);
v___x_5391_ = lean_nat_add(v___x_5293_, v_size_5384_);
lean_dec(v_size_5384_);
v___x_5392_ = lean_nat_add(v___x_5293_, v_size_5390_);
if (v_isShared_5389_ == 0)
{
lean_ctor_set(v___x_5388_, 4, v_l_5382_);
lean_ctor_set(v___x_5388_, 3, v_impl_5292_);
lean_ctor_set(v___x_5388_, 2, v_v_5285_);
lean_ctor_set(v___x_5388_, 1, v_k_5284_);
lean_ctor_set(v___x_5388_, 0, v___x_5392_);
v___x_5394_ = v___x_5388_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v___x_5392_);
lean_ctor_set(v_reuseFailAlloc_5398_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5398_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5398_, 3, v_impl_5292_);
lean_ctor_set(v_reuseFailAlloc_5398_, 4, v_l_5382_);
v___x_5394_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5396_; 
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v_r_5383_);
lean_ctor_set(v___x_5289_, 3, v___x_5394_);
lean_ctor_set(v___x_5289_, 2, v_v_5386_);
lean_ctor_set(v___x_5289_, 1, v_k_5385_);
lean_ctor_set(v___x_5289_, 0, v___x_5391_);
v___x_5396_ = v___x_5289_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v___x_5391_);
lean_ctor_set(v_reuseFailAlloc_5397_, 1, v_k_5385_);
lean_ctor_set(v_reuseFailAlloc_5397_, 2, v_v_5386_);
lean_ctor_set(v_reuseFailAlloc_5397_, 3, v___x_5394_);
lean_ctor_set(v_reuseFailAlloc_5397_, 4, v_r_5383_);
v___x_5396_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
return v___x_5396_;
}
}
}
}
else
{
lean_object* v_k_5402_; lean_object* v_v_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5426_; 
v_k_5402_ = lean_ctor_get(v_r_5287_, 1);
v_v_5403_ = lean_ctor_get(v_r_5287_, 2);
v_isSharedCheck_5426_ = !lean_is_exclusive(v_r_5287_);
if (v_isSharedCheck_5426_ == 0)
{
lean_object* v_unused_5427_; lean_object* v_unused_5428_; lean_object* v_unused_5429_; 
v_unused_5427_ = lean_ctor_get(v_r_5287_, 4);
lean_dec(v_unused_5427_);
v_unused_5428_ = lean_ctor_get(v_r_5287_, 3);
lean_dec(v_unused_5428_);
v_unused_5429_ = lean_ctor_get(v_r_5287_, 0);
lean_dec(v_unused_5429_);
v___x_5405_ = v_r_5287_;
v_isShared_5406_ = v_isSharedCheck_5426_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_v_5403_);
lean_inc(v_k_5402_);
lean_dec(v_r_5287_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5426_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v_k_5407_; lean_object* v_v_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5422_; 
v_k_5407_ = lean_ctor_get(v_l_5382_, 1);
v_v_5408_ = lean_ctor_get(v_l_5382_, 2);
v_isSharedCheck_5422_ = !lean_is_exclusive(v_l_5382_);
if (v_isSharedCheck_5422_ == 0)
{
lean_object* v_unused_5423_; lean_object* v_unused_5424_; lean_object* v_unused_5425_; 
v_unused_5423_ = lean_ctor_get(v_l_5382_, 4);
lean_dec(v_unused_5423_);
v_unused_5424_ = lean_ctor_get(v_l_5382_, 3);
lean_dec(v_unused_5424_);
v_unused_5425_ = lean_ctor_get(v_l_5382_, 0);
lean_dec(v_unused_5425_);
v___x_5410_ = v_l_5382_;
v_isShared_5411_ = v_isSharedCheck_5422_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_v_5408_);
lean_inc(v_k_5407_);
lean_dec(v_l_5382_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5422_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5412_; lean_object* v___x_5414_; 
v___x_5412_ = lean_unsigned_to_nat(3u);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 4, v_r_5383_);
lean_ctor_set(v___x_5410_, 3, v_r_5383_);
lean_ctor_set(v___x_5410_, 2, v_v_5285_);
lean_ctor_set(v___x_5410_, 1, v_k_5284_);
lean_ctor_set(v___x_5410_, 0, v___x_5293_);
v___x_5414_ = v___x_5410_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v___x_5293_);
lean_ctor_set(v_reuseFailAlloc_5421_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5421_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5421_, 3, v_r_5383_);
lean_ctor_set(v_reuseFailAlloc_5421_, 4, v_r_5383_);
v___x_5414_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
lean_object* v___x_5416_; 
if (v_isShared_5406_ == 0)
{
lean_ctor_set(v___x_5405_, 3, v_r_5383_);
lean_ctor_set(v___x_5405_, 0, v___x_5293_);
v___x_5416_ = v___x_5405_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v___x_5293_);
lean_ctor_set(v_reuseFailAlloc_5420_, 1, v_k_5402_);
lean_ctor_set(v_reuseFailAlloc_5420_, 2, v_v_5403_);
lean_ctor_set(v_reuseFailAlloc_5420_, 3, v_r_5383_);
lean_ctor_set(v_reuseFailAlloc_5420_, 4, v_r_5383_);
v___x_5416_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
lean_object* v___x_5418_; 
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v___x_5416_);
lean_ctor_set(v___x_5289_, 3, v___x_5414_);
lean_ctor_set(v___x_5289_, 2, v_v_5408_);
lean_ctor_set(v___x_5289_, 1, v_k_5407_);
lean_ctor_set(v___x_5289_, 0, v___x_5412_);
v___x_5418_ = v___x_5289_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5412_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v_k_5407_);
lean_ctor_set(v_reuseFailAlloc_5419_, 2, v_v_5408_);
lean_ctor_set(v_reuseFailAlloc_5419_, 3, v___x_5414_);
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
}
}
}
}
else
{
lean_object* v_r_5430_; 
v_r_5430_ = lean_ctor_get(v_r_5287_, 4);
lean_inc(v_r_5430_);
if (lean_obj_tag(v_r_5430_) == 0)
{
lean_object* v_k_5431_; lean_object* v_v_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5443_; 
v_k_5431_ = lean_ctor_get(v_r_5287_, 1);
v_v_5432_ = lean_ctor_get(v_r_5287_, 2);
v_isSharedCheck_5443_ = !lean_is_exclusive(v_r_5287_);
if (v_isSharedCheck_5443_ == 0)
{
lean_object* v_unused_5444_; lean_object* v_unused_5445_; lean_object* v_unused_5446_; 
v_unused_5444_ = lean_ctor_get(v_r_5287_, 4);
lean_dec(v_unused_5444_);
v_unused_5445_ = lean_ctor_get(v_r_5287_, 3);
lean_dec(v_unused_5445_);
v_unused_5446_ = lean_ctor_get(v_r_5287_, 0);
lean_dec(v_unused_5446_);
v___x_5434_ = v_r_5287_;
v_isShared_5435_ = v_isSharedCheck_5443_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_v_5432_);
lean_inc(v_k_5431_);
lean_dec(v_r_5287_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5443_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5436_; lean_object* v___x_5438_; 
v___x_5436_ = lean_unsigned_to_nat(3u);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v_l_5382_);
lean_ctor_set(v___x_5434_, 2, v_v_5285_);
lean_ctor_set(v___x_5434_, 1, v_k_5284_);
lean_ctor_set(v___x_5434_, 0, v___x_5293_);
v___x_5438_ = v___x_5434_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v___x_5293_);
lean_ctor_set(v_reuseFailAlloc_5442_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5442_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5442_, 3, v_l_5382_);
lean_ctor_set(v_reuseFailAlloc_5442_, 4, v_l_5382_);
v___x_5438_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
lean_object* v___x_5440_; 
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v_r_5430_);
lean_ctor_set(v___x_5289_, 3, v___x_5438_);
lean_ctor_set(v___x_5289_, 2, v_v_5432_);
lean_ctor_set(v___x_5289_, 1, v_k_5431_);
lean_ctor_set(v___x_5289_, 0, v___x_5436_);
v___x_5440_ = v___x_5289_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5436_);
lean_ctor_set(v_reuseFailAlloc_5441_, 1, v_k_5431_);
lean_ctor_set(v_reuseFailAlloc_5441_, 2, v_v_5432_);
lean_ctor_set(v_reuseFailAlloc_5441_, 3, v___x_5438_);
lean_ctor_set(v_reuseFailAlloc_5441_, 4, v_r_5430_);
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
else
{
lean_object* v_size_5447_; lean_object* v_k_5448_; lean_object* v_v_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5460_; 
v_size_5447_ = lean_ctor_get(v_r_5287_, 0);
v_k_5448_ = lean_ctor_get(v_r_5287_, 1);
v_v_5449_ = lean_ctor_get(v_r_5287_, 2);
v_isSharedCheck_5460_ = !lean_is_exclusive(v_r_5287_);
if (v_isSharedCheck_5460_ == 0)
{
lean_object* v_unused_5461_; lean_object* v_unused_5462_; 
v_unused_5461_ = lean_ctor_get(v_r_5287_, 4);
lean_dec(v_unused_5461_);
v_unused_5462_ = lean_ctor_get(v_r_5287_, 3);
lean_dec(v_unused_5462_);
v___x_5451_ = v_r_5287_;
v_isShared_5452_ = v_isSharedCheck_5460_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_v_5449_);
lean_inc(v_k_5448_);
lean_inc(v_size_5447_);
lean_dec(v_r_5287_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5460_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5454_; 
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 3, v_r_5430_);
v___x_5454_ = v___x_5451_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_size_5447_);
lean_ctor_set(v_reuseFailAlloc_5459_, 1, v_k_5448_);
lean_ctor_set(v_reuseFailAlloc_5459_, 2, v_v_5449_);
lean_ctor_set(v_reuseFailAlloc_5459_, 3, v_r_5430_);
lean_ctor_set(v_reuseFailAlloc_5459_, 4, v_r_5430_);
v___x_5454_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
lean_object* v___x_5455_; lean_object* v___x_5457_; 
v___x_5455_ = lean_unsigned_to_nat(2u);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v___x_5454_);
lean_ctor_set(v___x_5289_, 3, v_r_5430_);
lean_ctor_set(v___x_5289_, 0, v___x_5455_);
v___x_5457_ = v___x_5289_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5455_);
lean_ctor_set(v_reuseFailAlloc_5458_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5458_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5458_, 3, v_r_5430_);
lean_ctor_set(v_reuseFailAlloc_5458_, 4, v___x_5454_);
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
}
}
else
{
lean_object* v___x_5464_; 
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 3, v_r_5287_);
lean_ctor_set(v___x_5289_, 0, v___x_5293_);
v___x_5464_ = v___x_5289_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v___x_5293_);
lean_ctor_set(v_reuseFailAlloc_5465_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5465_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5465_, 3, v_r_5287_);
lean_ctor_set(v_reuseFailAlloc_5465_, 4, v_r_5287_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
case 1:
{
lean_del_object(v___x_5289_);
lean_dec(v_v_5285_);
lean_dec(v_k_5284_);
if (lean_obj_tag(v_l_5286_) == 0)
{
if (lean_obj_tag(v_r_5287_) == 0)
{
lean_object* v_size_5466_; lean_object* v_k_5467_; lean_object* v_v_5468_; lean_object* v_l_5469_; lean_object* v_r_5470_; lean_object* v_size_5471_; lean_object* v_k_5472_; lean_object* v_v_5473_; lean_object* v_l_5474_; lean_object* v_r_5475_; lean_object* v___x_5476_; uint8_t v___x_5477_; 
v_size_5466_ = lean_ctor_get(v_l_5286_, 0);
v_k_5467_ = lean_ctor_get(v_l_5286_, 1);
v_v_5468_ = lean_ctor_get(v_l_5286_, 2);
v_l_5469_ = lean_ctor_get(v_l_5286_, 3);
v_r_5470_ = lean_ctor_get(v_l_5286_, 4);
lean_inc(v_r_5470_);
v_size_5471_ = lean_ctor_get(v_r_5287_, 0);
v_k_5472_ = lean_ctor_get(v_r_5287_, 1);
v_v_5473_ = lean_ctor_get(v_r_5287_, 2);
v_l_5474_ = lean_ctor_get(v_r_5287_, 3);
lean_inc(v_l_5474_);
v_r_5475_ = lean_ctor_get(v_r_5287_, 4);
v___x_5476_ = lean_unsigned_to_nat(1u);
v___x_5477_ = lean_nat_dec_lt(v_size_5466_, v_size_5471_);
if (v___x_5477_ == 0)
{
lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5613_; 
lean_inc(v_l_5469_);
lean_inc(v_v_5468_);
lean_inc(v_k_5467_);
v_isSharedCheck_5613_ = !lean_is_exclusive(v_l_5286_);
if (v_isSharedCheck_5613_ == 0)
{
lean_object* v_unused_5614_; lean_object* v_unused_5615_; lean_object* v_unused_5616_; lean_object* v_unused_5617_; lean_object* v_unused_5618_; 
v_unused_5614_ = lean_ctor_get(v_l_5286_, 4);
lean_dec(v_unused_5614_);
v_unused_5615_ = lean_ctor_get(v_l_5286_, 3);
lean_dec(v_unused_5615_);
v_unused_5616_ = lean_ctor_get(v_l_5286_, 2);
lean_dec(v_unused_5616_);
v_unused_5617_ = lean_ctor_get(v_l_5286_, 1);
lean_dec(v_unused_5617_);
v_unused_5618_ = lean_ctor_get(v_l_5286_, 0);
lean_dec(v_unused_5618_);
v___x_5479_ = v_l_5286_;
v_isShared_5480_ = v_isSharedCheck_5613_;
goto v_resetjp_5478_;
}
else
{
lean_dec(v_l_5286_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5613_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v___x_5481_; lean_object* v_tree_5482_; 
v___x_5481_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5467_, v_v_5468_, v_l_5469_, v_r_5470_);
v_tree_5482_ = lean_ctor_get(v___x_5481_, 2);
if (lean_obj_tag(v_tree_5482_) == 0)
{
lean_object* v_k_5483_; lean_object* v_v_5484_; lean_object* v_size_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; uint8_t v___x_5488_; 
lean_inc_ref(v_tree_5482_);
v_k_5483_ = lean_ctor_get(v___x_5481_, 0);
lean_inc(v_k_5483_);
v_v_5484_ = lean_ctor_get(v___x_5481_, 1);
lean_inc(v_v_5484_);
lean_dec_ref(v___x_5481_);
v_size_5485_ = lean_ctor_get(v_tree_5482_, 0);
v___x_5486_ = lean_unsigned_to_nat(3u);
v___x_5487_ = lean_nat_mul(v___x_5486_, v_size_5485_);
v___x_5488_ = lean_nat_dec_lt(v___x_5487_, v_size_5471_);
lean_dec(v___x_5487_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5492_; 
lean_dec(v_l_5474_);
v___x_5489_ = lean_nat_add(v___x_5476_, v_size_5485_);
v___x_5490_ = lean_nat_add(v___x_5489_, v_size_5471_);
lean_dec(v___x_5489_);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 4, v_r_5287_);
lean_ctor_set(v___x_5479_, 3, v_tree_5482_);
lean_ctor_set(v___x_5479_, 2, v_v_5484_);
lean_ctor_set(v___x_5479_, 1, v_k_5483_);
lean_ctor_set(v___x_5479_, 0, v___x_5490_);
v___x_5492_ = v___x_5479_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5490_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_k_5483_);
lean_ctor_set(v_reuseFailAlloc_5493_, 2, v_v_5484_);
lean_ctor_set(v_reuseFailAlloc_5493_, 3, v_tree_5482_);
lean_ctor_set(v_reuseFailAlloc_5493_, 4, v_r_5287_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
else
{
lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5548_; 
lean_inc(v_r_5475_);
lean_inc(v_v_5473_);
lean_inc(v_k_5472_);
lean_inc(v_size_5471_);
v_isSharedCheck_5548_ = !lean_is_exclusive(v_r_5287_);
if (v_isSharedCheck_5548_ == 0)
{
lean_object* v_unused_5549_; lean_object* v_unused_5550_; lean_object* v_unused_5551_; lean_object* v_unused_5552_; lean_object* v_unused_5553_; 
v_unused_5549_ = lean_ctor_get(v_r_5287_, 4);
lean_dec(v_unused_5549_);
v_unused_5550_ = lean_ctor_get(v_r_5287_, 3);
lean_dec(v_unused_5550_);
v_unused_5551_ = lean_ctor_get(v_r_5287_, 2);
lean_dec(v_unused_5551_);
v_unused_5552_ = lean_ctor_get(v_r_5287_, 1);
lean_dec(v_unused_5552_);
v_unused_5553_ = lean_ctor_get(v_r_5287_, 0);
lean_dec(v_unused_5553_);
v___x_5495_ = v_r_5287_;
v_isShared_5496_ = v_isSharedCheck_5548_;
goto v_resetjp_5494_;
}
else
{
lean_dec(v_r_5287_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5548_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v_size_5497_; lean_object* v_k_5498_; lean_object* v_v_5499_; lean_object* v_l_5500_; lean_object* v_r_5501_; lean_object* v_size_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; uint8_t v___x_5505_; 
v_size_5497_ = lean_ctor_get(v_l_5474_, 0);
v_k_5498_ = lean_ctor_get(v_l_5474_, 1);
v_v_5499_ = lean_ctor_get(v_l_5474_, 2);
v_l_5500_ = lean_ctor_get(v_l_5474_, 3);
v_r_5501_ = lean_ctor_get(v_l_5474_, 4);
v_size_5502_ = lean_ctor_get(v_r_5475_, 0);
v___x_5503_ = lean_unsigned_to_nat(2u);
v___x_5504_ = lean_nat_mul(v___x_5503_, v_size_5502_);
v___x_5505_ = lean_nat_dec_lt(v_size_5497_, v___x_5504_);
lean_dec(v___x_5504_);
if (v___x_5505_ == 0)
{
lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5533_; 
lean_inc(v_r_5501_);
lean_inc(v_l_5500_);
lean_inc(v_v_5499_);
lean_inc(v_k_5498_);
v_isSharedCheck_5533_ = !lean_is_exclusive(v_l_5474_);
if (v_isSharedCheck_5533_ == 0)
{
lean_object* v_unused_5534_; lean_object* v_unused_5535_; lean_object* v_unused_5536_; lean_object* v_unused_5537_; lean_object* v_unused_5538_; 
v_unused_5534_ = lean_ctor_get(v_l_5474_, 4);
lean_dec(v_unused_5534_);
v_unused_5535_ = lean_ctor_get(v_l_5474_, 3);
lean_dec(v_unused_5535_);
v_unused_5536_ = lean_ctor_get(v_l_5474_, 2);
lean_dec(v_unused_5536_);
v_unused_5537_ = lean_ctor_get(v_l_5474_, 1);
lean_dec(v_unused_5537_);
v_unused_5538_ = lean_ctor_get(v_l_5474_, 0);
lean_dec(v_unused_5538_);
v___x_5507_ = v_l_5474_;
v_isShared_5508_ = v_isSharedCheck_5533_;
goto v_resetjp_5506_;
}
else
{
lean_dec(v_l_5474_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5533_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___y_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___y_5523_; 
v___x_5509_ = lean_nat_add(v___x_5476_, v_size_5485_);
v___x_5510_ = lean_nat_add(v___x_5509_, v_size_5471_);
lean_dec(v_size_5471_);
if (lean_obj_tag(v_l_5500_) == 0)
{
lean_object* v_size_5531_; 
v_size_5531_ = lean_ctor_get(v_l_5500_, 0);
lean_inc(v_size_5531_);
v___y_5523_ = v_size_5531_;
goto v___jp_5522_;
}
else
{
lean_object* v___x_5532_; 
v___x_5532_ = lean_unsigned_to_nat(0u);
v___y_5523_ = v___x_5532_;
goto v___jp_5522_;
}
v___jp_5511_:
{
lean_object* v___x_5515_; lean_object* v___x_5517_; 
v___x_5515_ = lean_nat_add(v___y_5512_, v___y_5514_);
lean_dec(v___y_5514_);
lean_dec(v___y_5512_);
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 4, v_r_5475_);
lean_ctor_set(v___x_5507_, 3, v_r_5501_);
lean_ctor_set(v___x_5507_, 2, v_v_5473_);
lean_ctor_set(v___x_5507_, 1, v_k_5472_);
lean_ctor_set(v___x_5507_, 0, v___x_5515_);
v___x_5517_ = v___x_5507_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5515_);
lean_ctor_set(v_reuseFailAlloc_5521_, 1, v_k_5472_);
lean_ctor_set(v_reuseFailAlloc_5521_, 2, v_v_5473_);
lean_ctor_set(v_reuseFailAlloc_5521_, 3, v_r_5501_);
lean_ctor_set(v_reuseFailAlloc_5521_, 4, v_r_5475_);
v___x_5517_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
lean_object* v___x_5519_; 
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 4, v___x_5517_);
lean_ctor_set(v___x_5495_, 3, v___y_5513_);
lean_ctor_set(v___x_5495_, 2, v_v_5499_);
lean_ctor_set(v___x_5495_, 1, v_k_5498_);
lean_ctor_set(v___x_5495_, 0, v___x_5510_);
v___x_5519_ = v___x_5495_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5510_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v_k_5498_);
lean_ctor_set(v_reuseFailAlloc_5520_, 2, v_v_5499_);
lean_ctor_set(v_reuseFailAlloc_5520_, 3, v___y_5513_);
lean_ctor_set(v_reuseFailAlloc_5520_, 4, v___x_5517_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
v___jp_5522_:
{
lean_object* v___x_5524_; lean_object* v___x_5526_; 
v___x_5524_ = lean_nat_add(v___x_5509_, v___y_5523_);
lean_dec(v___y_5523_);
lean_dec(v___x_5509_);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 4, v_l_5500_);
lean_ctor_set(v___x_5479_, 3, v_tree_5482_);
lean_ctor_set(v___x_5479_, 2, v_v_5484_);
lean_ctor_set(v___x_5479_, 1, v_k_5483_);
lean_ctor_set(v___x_5479_, 0, v___x_5524_);
v___x_5526_ = v___x_5479_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5524_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_k_5483_);
lean_ctor_set(v_reuseFailAlloc_5530_, 2, v_v_5484_);
lean_ctor_set(v_reuseFailAlloc_5530_, 3, v_tree_5482_);
lean_ctor_set(v_reuseFailAlloc_5530_, 4, v_l_5500_);
v___x_5526_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5527_; 
v___x_5527_ = lean_nat_add(v___x_5476_, v_size_5502_);
if (lean_obj_tag(v_r_5501_) == 0)
{
lean_object* v_size_5528_; 
v_size_5528_ = lean_ctor_get(v_r_5501_, 0);
lean_inc(v_size_5528_);
v___y_5512_ = v___x_5527_;
v___y_5513_ = v___x_5526_;
v___y_5514_ = v_size_5528_;
goto v___jp_5511_;
}
else
{
lean_object* v___x_5529_; 
v___x_5529_ = lean_unsigned_to_nat(0u);
v___y_5512_ = v___x_5527_;
v___y_5513_ = v___x_5526_;
v___y_5514_ = v___x_5529_;
goto v___jp_5511_;
}
}
}
}
}
else
{
lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5543_; 
v___x_5539_ = lean_nat_add(v___x_5476_, v_size_5485_);
v___x_5540_ = lean_nat_add(v___x_5539_, v_size_5471_);
lean_dec(v_size_5471_);
v___x_5541_ = lean_nat_add(v___x_5539_, v_size_5497_);
lean_dec(v___x_5539_);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 4, v_l_5474_);
lean_ctor_set(v___x_5495_, 3, v_tree_5482_);
lean_ctor_set(v___x_5495_, 2, v_v_5484_);
lean_ctor_set(v___x_5495_, 1, v_k_5483_);
lean_ctor_set(v___x_5495_, 0, v___x_5541_);
v___x_5543_ = v___x_5495_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5541_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_k_5483_);
lean_ctor_set(v_reuseFailAlloc_5547_, 2, v_v_5484_);
lean_ctor_set(v_reuseFailAlloc_5547_, 3, v_tree_5482_);
lean_ctor_set(v_reuseFailAlloc_5547_, 4, v_l_5474_);
v___x_5543_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
lean_object* v___x_5545_; 
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 4, v_r_5475_);
lean_ctor_set(v___x_5479_, 3, v___x_5543_);
lean_ctor_set(v___x_5479_, 2, v_v_5473_);
lean_ctor_set(v___x_5479_, 1, v_k_5472_);
lean_ctor_set(v___x_5479_, 0, v___x_5540_);
v___x_5545_ = v___x_5479_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v___x_5540_);
lean_ctor_set(v_reuseFailAlloc_5546_, 1, v_k_5472_);
lean_ctor_set(v_reuseFailAlloc_5546_, 2, v_v_5473_);
lean_ctor_set(v_reuseFailAlloc_5546_, 3, v___x_5543_);
lean_ctor_set(v_reuseFailAlloc_5546_, 4, v_r_5475_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
}
}
else
{
lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5607_; 
lean_inc(v_r_5475_);
lean_inc(v_v_5473_);
lean_inc(v_k_5472_);
lean_inc(v_size_5471_);
v_isSharedCheck_5607_ = !lean_is_exclusive(v_r_5287_);
if (v_isSharedCheck_5607_ == 0)
{
lean_object* v_unused_5608_; lean_object* v_unused_5609_; lean_object* v_unused_5610_; lean_object* v_unused_5611_; lean_object* v_unused_5612_; 
v_unused_5608_ = lean_ctor_get(v_r_5287_, 4);
lean_dec(v_unused_5608_);
v_unused_5609_ = lean_ctor_get(v_r_5287_, 3);
lean_dec(v_unused_5609_);
v_unused_5610_ = lean_ctor_get(v_r_5287_, 2);
lean_dec(v_unused_5610_);
v_unused_5611_ = lean_ctor_get(v_r_5287_, 1);
lean_dec(v_unused_5611_);
v_unused_5612_ = lean_ctor_get(v_r_5287_, 0);
lean_dec(v_unused_5612_);
v___x_5555_ = v_r_5287_;
v_isShared_5556_ = v_isSharedCheck_5607_;
goto v_resetjp_5554_;
}
else
{
lean_dec(v_r_5287_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5607_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
if (lean_obj_tag(v_l_5474_) == 0)
{
if (lean_obj_tag(v_r_5475_) == 0)
{
lean_object* v_k_5557_; lean_object* v_v_5558_; lean_object* v_size_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5563_; 
lean_inc(v_tree_5482_);
v_k_5557_ = lean_ctor_get(v___x_5481_, 0);
lean_inc(v_k_5557_);
v_v_5558_ = lean_ctor_get(v___x_5481_, 1);
lean_inc(v_v_5558_);
lean_dec_ref(v___x_5481_);
v_size_5559_ = lean_ctor_get(v_l_5474_, 0);
v___x_5560_ = lean_nat_add(v___x_5476_, v_size_5471_);
lean_dec(v_size_5471_);
v___x_5561_ = lean_nat_add(v___x_5476_, v_size_5559_);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v_l_5474_);
lean_ctor_set(v___x_5555_, 3, v_tree_5482_);
lean_ctor_set(v___x_5555_, 2, v_v_5558_);
lean_ctor_set(v___x_5555_, 1, v_k_5557_);
lean_ctor_set(v___x_5555_, 0, v___x_5561_);
v___x_5563_ = v___x_5555_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v_k_5557_);
lean_ctor_set(v_reuseFailAlloc_5567_, 2, v_v_5558_);
lean_ctor_set(v_reuseFailAlloc_5567_, 3, v_tree_5482_);
lean_ctor_set(v_reuseFailAlloc_5567_, 4, v_l_5474_);
v___x_5563_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
lean_object* v___x_5565_; 
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 4, v_r_5475_);
lean_ctor_set(v___x_5479_, 3, v___x_5563_);
lean_ctor_set(v___x_5479_, 2, v_v_5473_);
lean_ctor_set(v___x_5479_, 1, v_k_5472_);
lean_ctor_set(v___x_5479_, 0, v___x_5560_);
v___x_5565_ = v___x_5479_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v___x_5560_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v_k_5472_);
lean_ctor_set(v_reuseFailAlloc_5566_, 2, v_v_5473_);
lean_ctor_set(v_reuseFailAlloc_5566_, 3, v___x_5563_);
lean_ctor_set(v_reuseFailAlloc_5566_, 4, v_r_5475_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
return v___x_5565_;
}
}
}
else
{
lean_object* v_k_5568_; lean_object* v_v_5569_; lean_object* v_k_5570_; lean_object* v_v_5571_; lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5585_; 
lean_dec(v_size_5471_);
v_k_5568_ = lean_ctor_get(v___x_5481_, 0);
lean_inc(v_k_5568_);
v_v_5569_ = lean_ctor_get(v___x_5481_, 1);
lean_inc(v_v_5569_);
lean_dec_ref(v___x_5481_);
v_k_5570_ = lean_ctor_get(v_l_5474_, 1);
v_v_5571_ = lean_ctor_get(v_l_5474_, 2);
v_isSharedCheck_5585_ = !lean_is_exclusive(v_l_5474_);
if (v_isSharedCheck_5585_ == 0)
{
lean_object* v_unused_5586_; lean_object* v_unused_5587_; lean_object* v_unused_5588_; 
v_unused_5586_ = lean_ctor_get(v_l_5474_, 4);
lean_dec(v_unused_5586_);
v_unused_5587_ = lean_ctor_get(v_l_5474_, 3);
lean_dec(v_unused_5587_);
v_unused_5588_ = lean_ctor_get(v_l_5474_, 0);
lean_dec(v_unused_5588_);
v___x_5573_ = v_l_5474_;
v_isShared_5574_ = v_isSharedCheck_5585_;
goto v_resetjp_5572_;
}
else
{
lean_inc(v_v_5571_);
lean_inc(v_k_5570_);
lean_dec(v_l_5474_);
v___x_5573_ = lean_box(0);
v_isShared_5574_ = v_isSharedCheck_5585_;
goto v_resetjp_5572_;
}
v_resetjp_5572_:
{
lean_object* v___x_5575_; lean_object* v___x_5577_; 
v___x_5575_ = lean_unsigned_to_nat(3u);
if (v_isShared_5574_ == 0)
{
lean_ctor_set(v___x_5573_, 4, v_r_5475_);
lean_ctor_set(v___x_5573_, 3, v_r_5475_);
lean_ctor_set(v___x_5573_, 2, v_v_5569_);
lean_ctor_set(v___x_5573_, 1, v_k_5568_);
lean_ctor_set(v___x_5573_, 0, v___x_5476_);
v___x_5577_ = v___x_5573_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v_k_5568_);
lean_ctor_set(v_reuseFailAlloc_5584_, 2, v_v_5569_);
lean_ctor_set(v_reuseFailAlloc_5584_, 3, v_r_5475_);
lean_ctor_set(v_reuseFailAlloc_5584_, 4, v_r_5475_);
v___x_5577_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
lean_object* v___x_5579_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 3, v_r_5475_);
lean_ctor_set(v___x_5555_, 0, v___x_5476_);
v___x_5579_ = v___x_5555_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5583_, 1, v_k_5472_);
lean_ctor_set(v_reuseFailAlloc_5583_, 2, v_v_5473_);
lean_ctor_set(v_reuseFailAlloc_5583_, 3, v_r_5475_);
lean_ctor_set(v_reuseFailAlloc_5583_, 4, v_r_5475_);
v___x_5579_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
lean_object* v___x_5581_; 
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 4, v___x_5579_);
lean_ctor_set(v___x_5479_, 3, v___x_5577_);
lean_ctor_set(v___x_5479_, 2, v_v_5571_);
lean_ctor_set(v___x_5479_, 1, v_k_5570_);
lean_ctor_set(v___x_5479_, 0, v___x_5575_);
v___x_5581_ = v___x_5479_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v___x_5575_);
lean_ctor_set(v_reuseFailAlloc_5582_, 1, v_k_5570_);
lean_ctor_set(v_reuseFailAlloc_5582_, 2, v_v_5571_);
lean_ctor_set(v_reuseFailAlloc_5582_, 3, v___x_5577_);
lean_ctor_set(v_reuseFailAlloc_5582_, 4, v___x_5579_);
v___x_5581_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
return v___x_5581_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5475_) == 0)
{
lean_object* v_k_5589_; lean_object* v_v_5590_; lean_object* v___x_5591_; lean_object* v___x_5593_; 
lean_dec(v_size_5471_);
v_k_5589_ = lean_ctor_get(v___x_5481_, 0);
lean_inc(v_k_5589_);
v_v_5590_ = lean_ctor_get(v___x_5481_, 1);
lean_inc(v_v_5590_);
lean_dec_ref(v___x_5481_);
v___x_5591_ = lean_unsigned_to_nat(3u);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v_l_5474_);
lean_ctor_set(v___x_5555_, 2, v_v_5590_);
lean_ctor_set(v___x_5555_, 1, v_k_5589_);
lean_ctor_set(v___x_5555_, 0, v___x_5476_);
v___x_5593_ = v___x_5555_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5597_, 1, v_k_5589_);
lean_ctor_set(v_reuseFailAlloc_5597_, 2, v_v_5590_);
lean_ctor_set(v_reuseFailAlloc_5597_, 3, v_l_5474_);
lean_ctor_set(v_reuseFailAlloc_5597_, 4, v_l_5474_);
v___x_5593_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
lean_object* v___x_5595_; 
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 4, v_r_5475_);
lean_ctor_set(v___x_5479_, 3, v___x_5593_);
lean_ctor_set(v___x_5479_, 2, v_v_5473_);
lean_ctor_set(v___x_5479_, 1, v_k_5472_);
lean_ctor_set(v___x_5479_, 0, v___x_5591_);
v___x_5595_ = v___x_5479_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5591_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_k_5472_);
lean_ctor_set(v_reuseFailAlloc_5596_, 2, v_v_5473_);
lean_ctor_set(v_reuseFailAlloc_5596_, 3, v___x_5593_);
lean_ctor_set(v_reuseFailAlloc_5596_, 4, v_r_5475_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
else
{
lean_object* v_k_5598_; lean_object* v_v_5599_; lean_object* v___x_5601_; 
v_k_5598_ = lean_ctor_get(v___x_5481_, 0);
lean_inc(v_k_5598_);
v_v_5599_ = lean_ctor_get(v___x_5481_, 1);
lean_inc(v_v_5599_);
lean_dec_ref(v___x_5481_);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 3, v_r_5475_);
v___x_5601_ = v___x_5555_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_size_5471_);
lean_ctor_set(v_reuseFailAlloc_5606_, 1, v_k_5472_);
lean_ctor_set(v_reuseFailAlloc_5606_, 2, v_v_5473_);
lean_ctor_set(v_reuseFailAlloc_5606_, 3, v_r_5475_);
lean_ctor_set(v_reuseFailAlloc_5606_, 4, v_r_5475_);
v___x_5601_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
lean_object* v___x_5602_; lean_object* v___x_5604_; 
v___x_5602_ = lean_unsigned_to_nat(2u);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 4, v___x_5601_);
lean_ctor_set(v___x_5479_, 3, v_r_5475_);
lean_ctor_set(v___x_5479_, 2, v_v_5599_);
lean_ctor_set(v___x_5479_, 1, v_k_5598_);
lean_ctor_set(v___x_5479_, 0, v___x_5602_);
v___x_5604_ = v___x_5479_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v_k_5598_);
lean_ctor_set(v_reuseFailAlloc_5605_, 2, v_v_5599_);
lean_ctor_set(v_reuseFailAlloc_5605_, 3, v_r_5475_);
lean_ctor_set(v_reuseFailAlloc_5605_, 4, v___x_5601_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
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
lean_object* v___x_5620_; uint8_t v_isShared_5621_; uint8_t v_isSharedCheck_5771_; 
lean_inc(v_r_5475_);
lean_inc(v_v_5473_);
lean_inc(v_k_5472_);
v_isSharedCheck_5771_ = !lean_is_exclusive(v_r_5287_);
if (v_isSharedCheck_5771_ == 0)
{
lean_object* v_unused_5772_; lean_object* v_unused_5773_; lean_object* v_unused_5774_; lean_object* v_unused_5775_; lean_object* v_unused_5776_; 
v_unused_5772_ = lean_ctor_get(v_r_5287_, 4);
lean_dec(v_unused_5772_);
v_unused_5773_ = lean_ctor_get(v_r_5287_, 3);
lean_dec(v_unused_5773_);
v_unused_5774_ = lean_ctor_get(v_r_5287_, 2);
lean_dec(v_unused_5774_);
v_unused_5775_ = lean_ctor_get(v_r_5287_, 1);
lean_dec(v_unused_5775_);
v_unused_5776_ = lean_ctor_get(v_r_5287_, 0);
lean_dec(v_unused_5776_);
v___x_5620_ = v_r_5287_;
v_isShared_5621_ = v_isSharedCheck_5771_;
goto v_resetjp_5619_;
}
else
{
lean_dec(v_r_5287_);
v___x_5620_ = lean_box(0);
v_isShared_5621_ = v_isSharedCheck_5771_;
goto v_resetjp_5619_;
}
v_resetjp_5619_:
{
lean_object* v___x_5622_; lean_object* v_tree_5623_; 
v___x_5622_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5472_, v_v_5473_, v_l_5474_, v_r_5475_);
v_tree_5623_ = lean_ctor_get(v___x_5622_, 2);
lean_inc(v_tree_5623_);
if (lean_obj_tag(v_tree_5623_) == 0)
{
lean_object* v_k_5624_; lean_object* v_v_5625_; lean_object* v_size_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; uint8_t v___x_5629_; 
v_k_5624_ = lean_ctor_get(v___x_5622_, 0);
lean_inc(v_k_5624_);
v_v_5625_ = lean_ctor_get(v___x_5622_, 1);
lean_inc(v_v_5625_);
lean_dec_ref(v___x_5622_);
v_size_5626_ = lean_ctor_get(v_tree_5623_, 0);
v___x_5627_ = lean_unsigned_to_nat(3u);
v___x_5628_ = lean_nat_mul(v___x_5627_, v_size_5626_);
v___x_5629_ = lean_nat_dec_lt(v___x_5628_, v_size_5466_);
lean_dec(v___x_5628_);
if (v___x_5629_ == 0)
{
lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5633_; 
lean_dec(v_r_5470_);
v___x_5630_ = lean_nat_add(v___x_5476_, v_size_5466_);
v___x_5631_ = lean_nat_add(v___x_5630_, v_size_5626_);
lean_dec(v___x_5630_);
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 4, v_tree_5623_);
lean_ctor_set(v___x_5620_, 3, v_l_5286_);
lean_ctor_set(v___x_5620_, 2, v_v_5625_);
lean_ctor_set(v___x_5620_, 1, v_k_5624_);
lean_ctor_set(v___x_5620_, 0, v___x_5631_);
v___x_5633_ = v___x_5620_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v___x_5631_);
lean_ctor_set(v_reuseFailAlloc_5634_, 1, v_k_5624_);
lean_ctor_set(v_reuseFailAlloc_5634_, 2, v_v_5625_);
lean_ctor_set(v_reuseFailAlloc_5634_, 3, v_l_5286_);
lean_ctor_set(v_reuseFailAlloc_5634_, 4, v_tree_5623_);
v___x_5633_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
return v___x_5633_;
}
}
else
{
lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5700_; 
lean_inc(v_l_5469_);
lean_inc(v_v_5468_);
lean_inc(v_k_5467_);
lean_inc(v_size_5466_);
v_isSharedCheck_5700_ = !lean_is_exclusive(v_l_5286_);
if (v_isSharedCheck_5700_ == 0)
{
lean_object* v_unused_5701_; lean_object* v_unused_5702_; lean_object* v_unused_5703_; lean_object* v_unused_5704_; lean_object* v_unused_5705_; 
v_unused_5701_ = lean_ctor_get(v_l_5286_, 4);
lean_dec(v_unused_5701_);
v_unused_5702_ = lean_ctor_get(v_l_5286_, 3);
lean_dec(v_unused_5702_);
v_unused_5703_ = lean_ctor_get(v_l_5286_, 2);
lean_dec(v_unused_5703_);
v_unused_5704_ = lean_ctor_get(v_l_5286_, 1);
lean_dec(v_unused_5704_);
v_unused_5705_ = lean_ctor_get(v_l_5286_, 0);
lean_dec(v_unused_5705_);
v___x_5636_ = v_l_5286_;
v_isShared_5637_ = v_isSharedCheck_5700_;
goto v_resetjp_5635_;
}
else
{
lean_dec(v_l_5286_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5700_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v_size_5638_; lean_object* v_size_5639_; lean_object* v_k_5640_; lean_object* v_v_5641_; lean_object* v_l_5642_; lean_object* v_r_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; uint8_t v___x_5646_; 
v_size_5638_ = lean_ctor_get(v_l_5469_, 0);
v_size_5639_ = lean_ctor_get(v_r_5470_, 0);
v_k_5640_ = lean_ctor_get(v_r_5470_, 1);
v_v_5641_ = lean_ctor_get(v_r_5470_, 2);
v_l_5642_ = lean_ctor_get(v_r_5470_, 3);
v_r_5643_ = lean_ctor_get(v_r_5470_, 4);
v___x_5644_ = lean_unsigned_to_nat(2u);
v___x_5645_ = lean_nat_mul(v___x_5644_, v_size_5638_);
v___x_5646_ = lean_nat_dec_lt(v_size_5639_, v___x_5645_);
lean_dec(v___x_5645_);
if (v___x_5646_ == 0)
{
lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5684_; 
lean_inc(v_r_5643_);
lean_inc(v_l_5642_);
lean_inc(v_v_5641_);
lean_inc(v_k_5640_);
lean_del_object(v___x_5636_);
v_isSharedCheck_5684_ = !lean_is_exclusive(v_r_5470_);
if (v_isSharedCheck_5684_ == 0)
{
lean_object* v_unused_5685_; lean_object* v_unused_5686_; lean_object* v_unused_5687_; lean_object* v_unused_5688_; lean_object* v_unused_5689_; 
v_unused_5685_ = lean_ctor_get(v_r_5470_, 4);
lean_dec(v_unused_5685_);
v_unused_5686_ = lean_ctor_get(v_r_5470_, 3);
lean_dec(v_unused_5686_);
v_unused_5687_ = lean_ctor_get(v_r_5470_, 2);
lean_dec(v_unused_5687_);
v_unused_5688_ = lean_ctor_get(v_r_5470_, 1);
lean_dec(v_unused_5688_);
v_unused_5689_ = lean_ctor_get(v_r_5470_, 0);
lean_dec(v_unused_5689_);
v___x_5648_ = v_r_5470_;
v_isShared_5649_ = v_isSharedCheck_5684_;
goto v_resetjp_5647_;
}
else
{
lean_dec(v_r_5470_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5684_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___y_5653_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___x_5672_; lean_object* v___y_5674_; 
v___x_5650_ = lean_nat_add(v___x_5476_, v_size_5466_);
lean_dec(v_size_5466_);
v___x_5651_ = lean_nat_add(v___x_5650_, v_size_5626_);
lean_dec(v___x_5650_);
v___x_5672_ = lean_nat_add(v___x_5476_, v_size_5638_);
if (lean_obj_tag(v_l_5642_) == 0)
{
lean_object* v_size_5682_; 
v_size_5682_ = lean_ctor_get(v_l_5642_, 0);
lean_inc(v_size_5682_);
v___y_5674_ = v_size_5682_;
goto v___jp_5673_;
}
else
{
lean_object* v___x_5683_; 
v___x_5683_ = lean_unsigned_to_nat(0u);
v___y_5674_ = v___x_5683_;
goto v___jp_5673_;
}
v___jp_5652_:
{
lean_object* v___x_5656_; lean_object* v___x_5658_; 
v___x_5656_ = lean_nat_add(v___y_5654_, v___y_5655_);
lean_dec(v___y_5655_);
lean_dec(v___y_5654_);
lean_inc_ref(v_tree_5623_);
if (v_isShared_5649_ == 0)
{
lean_ctor_set(v___x_5648_, 4, v_tree_5623_);
lean_ctor_set(v___x_5648_, 3, v_r_5643_);
lean_ctor_set(v___x_5648_, 2, v_v_5625_);
lean_ctor_set(v___x_5648_, 1, v_k_5624_);
lean_ctor_set(v___x_5648_, 0, v___x_5656_);
v___x_5658_ = v___x_5648_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v___x_5656_);
lean_ctor_set(v_reuseFailAlloc_5671_, 1, v_k_5624_);
lean_ctor_set(v_reuseFailAlloc_5671_, 2, v_v_5625_);
lean_ctor_set(v_reuseFailAlloc_5671_, 3, v_r_5643_);
lean_ctor_set(v_reuseFailAlloc_5671_, 4, v_tree_5623_);
v___x_5658_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
v_isSharedCheck_5665_ = !lean_is_exclusive(v_tree_5623_);
if (v_isSharedCheck_5665_ == 0)
{
lean_object* v_unused_5666_; lean_object* v_unused_5667_; lean_object* v_unused_5668_; lean_object* v_unused_5669_; lean_object* v_unused_5670_; 
v_unused_5666_ = lean_ctor_get(v_tree_5623_, 4);
lean_dec(v_unused_5666_);
v_unused_5667_ = lean_ctor_get(v_tree_5623_, 3);
lean_dec(v_unused_5667_);
v_unused_5668_ = lean_ctor_get(v_tree_5623_, 2);
lean_dec(v_unused_5668_);
v_unused_5669_ = lean_ctor_get(v_tree_5623_, 1);
lean_dec(v_unused_5669_);
v_unused_5670_ = lean_ctor_get(v_tree_5623_, 0);
lean_dec(v_unused_5670_);
v___x_5660_ = v_tree_5623_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_dec(v_tree_5623_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
lean_ctor_set(v___x_5660_, 4, v___x_5658_);
lean_ctor_set(v___x_5660_, 3, v___y_5653_);
lean_ctor_set(v___x_5660_, 2, v_v_5641_);
lean_ctor_set(v___x_5660_, 1, v_k_5640_);
lean_ctor_set(v___x_5660_, 0, v___x_5651_);
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v___x_5651_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v_k_5640_);
lean_ctor_set(v_reuseFailAlloc_5664_, 2, v_v_5641_);
lean_ctor_set(v_reuseFailAlloc_5664_, 3, v___y_5653_);
lean_ctor_set(v_reuseFailAlloc_5664_, 4, v___x_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
v___jp_5673_:
{
lean_object* v___x_5675_; lean_object* v___x_5677_; 
v___x_5675_ = lean_nat_add(v___x_5672_, v___y_5674_);
lean_dec(v___y_5674_);
lean_dec(v___x_5672_);
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 4, v_l_5642_);
lean_ctor_set(v___x_5620_, 3, v_l_5469_);
lean_ctor_set(v___x_5620_, 2, v_v_5468_);
lean_ctor_set(v___x_5620_, 1, v_k_5467_);
lean_ctor_set(v___x_5620_, 0, v___x_5675_);
v___x_5677_ = v___x_5620_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v___x_5675_);
lean_ctor_set(v_reuseFailAlloc_5681_, 1, v_k_5467_);
lean_ctor_set(v_reuseFailAlloc_5681_, 2, v_v_5468_);
lean_ctor_set(v_reuseFailAlloc_5681_, 3, v_l_5469_);
lean_ctor_set(v_reuseFailAlloc_5681_, 4, v_l_5642_);
v___x_5677_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
lean_object* v___x_5678_; 
v___x_5678_ = lean_nat_add(v___x_5476_, v_size_5626_);
if (lean_obj_tag(v_r_5643_) == 0)
{
lean_object* v_size_5679_; 
v_size_5679_ = lean_ctor_get(v_r_5643_, 0);
lean_inc(v_size_5679_);
v___y_5653_ = v___x_5677_;
v___y_5654_ = v___x_5678_;
v___y_5655_ = v_size_5679_;
goto v___jp_5652_;
}
else
{
lean_object* v___x_5680_; 
v___x_5680_ = lean_unsigned_to_nat(0u);
v___y_5653_ = v___x_5677_;
v___y_5654_ = v___x_5678_;
v___y_5655_ = v___x_5680_;
goto v___jp_5652_;
}
}
}
}
}
else
{
lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5695_; 
v___x_5690_ = lean_nat_add(v___x_5476_, v_size_5466_);
lean_dec(v_size_5466_);
v___x_5691_ = lean_nat_add(v___x_5690_, v_size_5626_);
lean_dec(v___x_5690_);
v___x_5692_ = lean_nat_add(v___x_5476_, v_size_5626_);
v___x_5693_ = lean_nat_add(v___x_5692_, v_size_5639_);
lean_dec(v___x_5692_);
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 4, v_tree_5623_);
lean_ctor_set(v___x_5620_, 3, v_r_5470_);
lean_ctor_set(v___x_5620_, 2, v_v_5625_);
lean_ctor_set(v___x_5620_, 1, v_k_5624_);
lean_ctor_set(v___x_5620_, 0, v___x_5693_);
v___x_5695_ = v___x_5620_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v___x_5693_);
lean_ctor_set(v_reuseFailAlloc_5699_, 1, v_k_5624_);
lean_ctor_set(v_reuseFailAlloc_5699_, 2, v_v_5625_);
lean_ctor_set(v_reuseFailAlloc_5699_, 3, v_r_5470_);
lean_ctor_set(v_reuseFailAlloc_5699_, 4, v_tree_5623_);
v___x_5695_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
lean_object* v___x_5697_; 
if (v_isShared_5637_ == 0)
{
lean_ctor_set(v___x_5636_, 4, v___x_5695_);
lean_ctor_set(v___x_5636_, 0, v___x_5691_);
v___x_5697_ = v___x_5636_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5691_);
lean_ctor_set(v_reuseFailAlloc_5698_, 1, v_k_5467_);
lean_ctor_set(v_reuseFailAlloc_5698_, 2, v_v_5468_);
lean_ctor_set(v_reuseFailAlloc_5698_, 3, v_l_5469_);
lean_ctor_set(v_reuseFailAlloc_5698_, 4, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_5469_) == 0)
{
lean_object* v___x_5707_; uint8_t v_isShared_5708_; uint8_t v_isSharedCheck_5729_; 
lean_inc_ref(v_l_5469_);
lean_inc(v_v_5468_);
lean_inc(v_k_5467_);
lean_inc(v_size_5466_);
v_isSharedCheck_5729_ = !lean_is_exclusive(v_l_5286_);
if (v_isSharedCheck_5729_ == 0)
{
lean_object* v_unused_5730_; lean_object* v_unused_5731_; lean_object* v_unused_5732_; lean_object* v_unused_5733_; lean_object* v_unused_5734_; 
v_unused_5730_ = lean_ctor_get(v_l_5286_, 4);
lean_dec(v_unused_5730_);
v_unused_5731_ = lean_ctor_get(v_l_5286_, 3);
lean_dec(v_unused_5731_);
v_unused_5732_ = lean_ctor_get(v_l_5286_, 2);
lean_dec(v_unused_5732_);
v_unused_5733_ = lean_ctor_get(v_l_5286_, 1);
lean_dec(v_unused_5733_);
v_unused_5734_ = lean_ctor_get(v_l_5286_, 0);
lean_dec(v_unused_5734_);
v___x_5707_ = v_l_5286_;
v_isShared_5708_ = v_isSharedCheck_5729_;
goto v_resetjp_5706_;
}
else
{
lean_dec(v_l_5286_);
v___x_5707_ = lean_box(0);
v_isShared_5708_ = v_isSharedCheck_5729_;
goto v_resetjp_5706_;
}
v_resetjp_5706_:
{
if (lean_obj_tag(v_r_5470_) == 0)
{
lean_object* v_k_5709_; lean_object* v_v_5710_; lean_object* v_size_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5715_; 
v_k_5709_ = lean_ctor_get(v___x_5622_, 0);
lean_inc(v_k_5709_);
v_v_5710_ = lean_ctor_get(v___x_5622_, 1);
lean_inc(v_v_5710_);
lean_dec_ref(v___x_5622_);
v_size_5711_ = lean_ctor_get(v_r_5470_, 0);
v___x_5712_ = lean_nat_add(v___x_5476_, v_size_5466_);
lean_dec(v_size_5466_);
v___x_5713_ = lean_nat_add(v___x_5476_, v_size_5711_);
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 4, v_tree_5623_);
lean_ctor_set(v___x_5620_, 3, v_r_5470_);
lean_ctor_set(v___x_5620_, 2, v_v_5710_);
lean_ctor_set(v___x_5620_, 1, v_k_5709_);
lean_ctor_set(v___x_5620_, 0, v___x_5713_);
v___x_5715_ = v___x_5620_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5719_; 
v_reuseFailAlloc_5719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5719_, 0, v___x_5713_);
lean_ctor_set(v_reuseFailAlloc_5719_, 1, v_k_5709_);
lean_ctor_set(v_reuseFailAlloc_5719_, 2, v_v_5710_);
lean_ctor_set(v_reuseFailAlloc_5719_, 3, v_r_5470_);
lean_ctor_set(v_reuseFailAlloc_5719_, 4, v_tree_5623_);
v___x_5715_ = v_reuseFailAlloc_5719_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
lean_object* v___x_5717_; 
if (v_isShared_5708_ == 0)
{
lean_ctor_set(v___x_5707_, 4, v___x_5715_);
lean_ctor_set(v___x_5707_, 0, v___x_5712_);
v___x_5717_ = v___x_5707_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v___x_5712_);
lean_ctor_set(v_reuseFailAlloc_5718_, 1, v_k_5467_);
lean_ctor_set(v_reuseFailAlloc_5718_, 2, v_v_5468_);
lean_ctor_set(v_reuseFailAlloc_5718_, 3, v_l_5469_);
lean_ctor_set(v_reuseFailAlloc_5718_, 4, v___x_5715_);
v___x_5717_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
return v___x_5717_;
}
}
}
else
{
lean_object* v_k_5720_; lean_object* v_v_5721_; lean_object* v___x_5722_; lean_object* v___x_5724_; 
lean_dec(v_size_5466_);
v_k_5720_ = lean_ctor_get(v___x_5622_, 0);
lean_inc(v_k_5720_);
v_v_5721_ = lean_ctor_get(v___x_5622_, 1);
lean_inc(v_v_5721_);
lean_dec_ref(v___x_5622_);
v___x_5722_ = lean_unsigned_to_nat(3u);
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 4, v_r_5470_);
lean_ctor_set(v___x_5620_, 3, v_r_5470_);
lean_ctor_set(v___x_5620_, 2, v_v_5721_);
lean_ctor_set(v___x_5620_, 1, v_k_5720_);
lean_ctor_set(v___x_5620_, 0, v___x_5476_);
v___x_5724_ = v___x_5620_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5728_, 1, v_k_5720_);
lean_ctor_set(v_reuseFailAlloc_5728_, 2, v_v_5721_);
lean_ctor_set(v_reuseFailAlloc_5728_, 3, v_r_5470_);
lean_ctor_set(v_reuseFailAlloc_5728_, 4, v_r_5470_);
v___x_5724_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
lean_object* v___x_5726_; 
if (v_isShared_5708_ == 0)
{
lean_ctor_set(v___x_5707_, 4, v___x_5724_);
lean_ctor_set(v___x_5707_, 0, v___x_5722_);
v___x_5726_ = v___x_5707_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v___x_5722_);
lean_ctor_set(v_reuseFailAlloc_5727_, 1, v_k_5467_);
lean_ctor_set(v_reuseFailAlloc_5727_, 2, v_v_5468_);
lean_ctor_set(v_reuseFailAlloc_5727_, 3, v_l_5469_);
lean_ctor_set(v_reuseFailAlloc_5727_, 4, v___x_5724_);
v___x_5726_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
return v___x_5726_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5470_) == 0)
{
lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5759_; 
lean_inc(v_l_5469_);
lean_inc(v_v_5468_);
lean_inc(v_k_5467_);
v_isSharedCheck_5759_ = !lean_is_exclusive(v_l_5286_);
if (v_isSharedCheck_5759_ == 0)
{
lean_object* v_unused_5760_; lean_object* v_unused_5761_; lean_object* v_unused_5762_; lean_object* v_unused_5763_; lean_object* v_unused_5764_; 
v_unused_5760_ = lean_ctor_get(v_l_5286_, 4);
lean_dec(v_unused_5760_);
v_unused_5761_ = lean_ctor_get(v_l_5286_, 3);
lean_dec(v_unused_5761_);
v_unused_5762_ = lean_ctor_get(v_l_5286_, 2);
lean_dec(v_unused_5762_);
v_unused_5763_ = lean_ctor_get(v_l_5286_, 1);
lean_dec(v_unused_5763_);
v_unused_5764_ = lean_ctor_get(v_l_5286_, 0);
lean_dec(v_unused_5764_);
v___x_5736_ = v_l_5286_;
v_isShared_5737_ = v_isSharedCheck_5759_;
goto v_resetjp_5735_;
}
else
{
lean_dec(v_l_5286_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5759_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v_k_5738_; lean_object* v_v_5739_; lean_object* v_k_5740_; lean_object* v_v_5741_; lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5755_; 
v_k_5738_ = lean_ctor_get(v___x_5622_, 0);
lean_inc(v_k_5738_);
v_v_5739_ = lean_ctor_get(v___x_5622_, 1);
lean_inc(v_v_5739_);
lean_dec_ref(v___x_5622_);
v_k_5740_ = lean_ctor_get(v_r_5470_, 1);
v_v_5741_ = lean_ctor_get(v_r_5470_, 2);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_r_5470_);
if (v_isSharedCheck_5755_ == 0)
{
lean_object* v_unused_5756_; lean_object* v_unused_5757_; lean_object* v_unused_5758_; 
v_unused_5756_ = lean_ctor_get(v_r_5470_, 4);
lean_dec(v_unused_5756_);
v_unused_5757_ = lean_ctor_get(v_r_5470_, 3);
lean_dec(v_unused_5757_);
v_unused_5758_ = lean_ctor_get(v_r_5470_, 0);
lean_dec(v_unused_5758_);
v___x_5743_ = v_r_5470_;
v_isShared_5744_ = v_isSharedCheck_5755_;
goto v_resetjp_5742_;
}
else
{
lean_inc(v_v_5741_);
lean_inc(v_k_5740_);
lean_dec(v_r_5470_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5755_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v___x_5745_; lean_object* v___x_5747_; 
v___x_5745_ = lean_unsigned_to_nat(3u);
if (v_isShared_5744_ == 0)
{
lean_ctor_set(v___x_5743_, 4, v_l_5469_);
lean_ctor_set(v___x_5743_, 3, v_l_5469_);
lean_ctor_set(v___x_5743_, 2, v_v_5468_);
lean_ctor_set(v___x_5743_, 1, v_k_5467_);
lean_ctor_set(v___x_5743_, 0, v___x_5476_);
v___x_5747_ = v___x_5743_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5754_, 1, v_k_5467_);
lean_ctor_set(v_reuseFailAlloc_5754_, 2, v_v_5468_);
lean_ctor_set(v_reuseFailAlloc_5754_, 3, v_l_5469_);
lean_ctor_set(v_reuseFailAlloc_5754_, 4, v_l_5469_);
v___x_5747_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
lean_object* v___x_5749_; 
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 4, v_l_5469_);
lean_ctor_set(v___x_5620_, 3, v_l_5469_);
lean_ctor_set(v___x_5620_, 2, v_v_5739_);
lean_ctor_set(v___x_5620_, 1, v_k_5738_);
lean_ctor_set(v___x_5620_, 0, v___x_5476_);
v___x_5749_ = v___x_5620_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5753_, 1, v_k_5738_);
lean_ctor_set(v_reuseFailAlloc_5753_, 2, v_v_5739_);
lean_ctor_set(v_reuseFailAlloc_5753_, 3, v_l_5469_);
lean_ctor_set(v_reuseFailAlloc_5753_, 4, v_l_5469_);
v___x_5749_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
lean_object* v___x_5751_; 
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 4, v___x_5749_);
lean_ctor_set(v___x_5736_, 3, v___x_5747_);
lean_ctor_set(v___x_5736_, 2, v_v_5741_);
lean_ctor_set(v___x_5736_, 1, v_k_5740_);
lean_ctor_set(v___x_5736_, 0, v___x_5745_);
v___x_5751_ = v___x_5736_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v___x_5745_);
lean_ctor_set(v_reuseFailAlloc_5752_, 1, v_k_5740_);
lean_ctor_set(v_reuseFailAlloc_5752_, 2, v_v_5741_);
lean_ctor_set(v_reuseFailAlloc_5752_, 3, v___x_5747_);
lean_ctor_set(v_reuseFailAlloc_5752_, 4, v___x_5749_);
v___x_5751_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
return v___x_5751_;
}
}
}
}
}
}
else
{
lean_object* v_k_5765_; lean_object* v_v_5766_; lean_object* v___x_5767_; lean_object* v___x_5769_; 
v_k_5765_ = lean_ctor_get(v___x_5622_, 0);
lean_inc(v_k_5765_);
v_v_5766_ = lean_ctor_get(v___x_5622_, 1);
lean_inc(v_v_5766_);
lean_dec_ref(v___x_5622_);
v___x_5767_ = lean_unsigned_to_nat(2u);
if (v_isShared_5621_ == 0)
{
lean_ctor_set(v___x_5620_, 4, v_r_5470_);
lean_ctor_set(v___x_5620_, 3, v_l_5286_);
lean_ctor_set(v___x_5620_, 2, v_v_5766_);
lean_ctor_set(v___x_5620_, 1, v_k_5765_);
lean_ctor_set(v___x_5620_, 0, v___x_5767_);
v___x_5769_ = v___x_5620_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v___x_5767_);
lean_ctor_set(v_reuseFailAlloc_5770_, 1, v_k_5765_);
lean_ctor_set(v_reuseFailAlloc_5770_, 2, v_v_5766_);
lean_ctor_set(v_reuseFailAlloc_5770_, 3, v_l_5286_);
lean_ctor_set(v_reuseFailAlloc_5770_, 4, v_r_5470_);
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
}
else
{
return v_l_5286_;
}
}
else
{
return v_r_5287_;
}
}
default: 
{
lean_object* v_impl_5777_; lean_object* v___x_5778_; 
v_impl_5777_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5282_, v_r_5287_);
v___x_5778_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5777_) == 0)
{
if (lean_obj_tag(v_l_5286_) == 0)
{
lean_object* v_size_5779_; lean_object* v_size_5780_; lean_object* v_k_5781_; lean_object* v_v_5782_; lean_object* v_l_5783_; lean_object* v_r_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; uint8_t v___x_5787_; 
v_size_5779_ = lean_ctor_get(v_impl_5777_, 0);
v_size_5780_ = lean_ctor_get(v_l_5286_, 0);
v_k_5781_ = lean_ctor_get(v_l_5286_, 1);
v_v_5782_ = lean_ctor_get(v_l_5286_, 2);
v_l_5783_ = lean_ctor_get(v_l_5286_, 3);
v_r_5784_ = lean_ctor_get(v_l_5286_, 4);
lean_inc(v_r_5784_);
v___x_5785_ = lean_unsigned_to_nat(3u);
v___x_5786_ = lean_nat_mul(v___x_5785_, v_size_5779_);
v___x_5787_ = lean_nat_dec_lt(v___x_5786_, v_size_5780_);
lean_dec(v___x_5786_);
if (v___x_5787_ == 0)
{
lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5791_; 
lean_dec(v_r_5784_);
v___x_5788_ = lean_nat_add(v___x_5778_, v_size_5780_);
v___x_5789_ = lean_nat_add(v___x_5788_, v_size_5779_);
lean_dec(v___x_5788_);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v_impl_5777_);
lean_ctor_set(v___x_5289_, 0, v___x_5789_);
v___x_5791_ = v___x_5289_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v___x_5789_);
lean_ctor_set(v_reuseFailAlloc_5792_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5792_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5792_, 3, v_l_5286_);
lean_ctor_set(v_reuseFailAlloc_5792_, 4, v_impl_5777_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
else
{
lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5858_; 
lean_inc(v_l_5783_);
lean_inc(v_v_5782_);
lean_inc(v_k_5781_);
lean_inc(v_size_5780_);
v_isSharedCheck_5858_ = !lean_is_exclusive(v_l_5286_);
if (v_isSharedCheck_5858_ == 0)
{
lean_object* v_unused_5859_; lean_object* v_unused_5860_; lean_object* v_unused_5861_; lean_object* v_unused_5862_; lean_object* v_unused_5863_; 
v_unused_5859_ = lean_ctor_get(v_l_5286_, 4);
lean_dec(v_unused_5859_);
v_unused_5860_ = lean_ctor_get(v_l_5286_, 3);
lean_dec(v_unused_5860_);
v_unused_5861_ = lean_ctor_get(v_l_5286_, 2);
lean_dec(v_unused_5861_);
v_unused_5862_ = lean_ctor_get(v_l_5286_, 1);
lean_dec(v_unused_5862_);
v_unused_5863_ = lean_ctor_get(v_l_5286_, 0);
lean_dec(v_unused_5863_);
v___x_5794_ = v_l_5286_;
v_isShared_5795_ = v_isSharedCheck_5858_;
goto v_resetjp_5793_;
}
else
{
lean_dec(v_l_5286_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5858_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
lean_object* v_size_5796_; lean_object* v_size_5797_; lean_object* v_k_5798_; lean_object* v_v_5799_; lean_object* v_l_5800_; lean_object* v_r_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; uint8_t v___x_5804_; 
v_size_5796_ = lean_ctor_get(v_l_5783_, 0);
v_size_5797_ = lean_ctor_get(v_r_5784_, 0);
v_k_5798_ = lean_ctor_get(v_r_5784_, 1);
v_v_5799_ = lean_ctor_get(v_r_5784_, 2);
v_l_5800_ = lean_ctor_get(v_r_5784_, 3);
v_r_5801_ = lean_ctor_get(v_r_5784_, 4);
v___x_5802_ = lean_unsigned_to_nat(2u);
v___x_5803_ = lean_nat_mul(v___x_5802_, v_size_5796_);
v___x_5804_ = lean_nat_dec_lt(v_size_5797_, v___x_5803_);
lean_dec(v___x_5803_);
if (v___x_5804_ == 0)
{
lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5833_; 
lean_inc(v_r_5801_);
lean_inc(v_l_5800_);
lean_inc(v_v_5799_);
lean_inc(v_k_5798_);
v_isSharedCheck_5833_ = !lean_is_exclusive(v_r_5784_);
if (v_isSharedCheck_5833_ == 0)
{
lean_object* v_unused_5834_; lean_object* v_unused_5835_; lean_object* v_unused_5836_; lean_object* v_unused_5837_; lean_object* v_unused_5838_; 
v_unused_5834_ = lean_ctor_get(v_r_5784_, 4);
lean_dec(v_unused_5834_);
v_unused_5835_ = lean_ctor_get(v_r_5784_, 3);
lean_dec(v_unused_5835_);
v_unused_5836_ = lean_ctor_get(v_r_5784_, 2);
lean_dec(v_unused_5836_);
v_unused_5837_ = lean_ctor_get(v_r_5784_, 1);
lean_dec(v_unused_5837_);
v_unused_5838_ = lean_ctor_get(v_r_5784_, 0);
lean_dec(v_unused_5838_);
v___x_5806_ = v_r_5784_;
v_isShared_5807_ = v_isSharedCheck_5833_;
goto v_resetjp_5805_;
}
else
{
lean_dec(v_r_5784_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5833_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___y_5811_; lean_object* v___y_5812_; lean_object* v___y_5813_; lean_object* v___x_5821_; lean_object* v___y_5823_; 
v___x_5808_ = lean_nat_add(v___x_5778_, v_size_5780_);
lean_dec(v_size_5780_);
v___x_5809_ = lean_nat_add(v___x_5808_, v_size_5779_);
lean_dec(v___x_5808_);
v___x_5821_ = lean_nat_add(v___x_5778_, v_size_5796_);
if (lean_obj_tag(v_l_5800_) == 0)
{
lean_object* v_size_5831_; 
v_size_5831_ = lean_ctor_get(v_l_5800_, 0);
lean_inc(v_size_5831_);
v___y_5823_ = v_size_5831_;
goto v___jp_5822_;
}
else
{
lean_object* v___x_5832_; 
v___x_5832_ = lean_unsigned_to_nat(0u);
v___y_5823_ = v___x_5832_;
goto v___jp_5822_;
}
v___jp_5810_:
{
lean_object* v___x_5814_; lean_object* v___x_5816_; 
v___x_5814_ = lean_nat_add(v___y_5812_, v___y_5813_);
lean_dec(v___y_5813_);
lean_dec(v___y_5812_);
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 4, v_impl_5777_);
lean_ctor_set(v___x_5806_, 3, v_r_5801_);
lean_ctor_set(v___x_5806_, 2, v_v_5285_);
lean_ctor_set(v___x_5806_, 1, v_k_5284_);
lean_ctor_set(v___x_5806_, 0, v___x_5814_);
v___x_5816_ = v___x_5806_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v___x_5814_);
lean_ctor_set(v_reuseFailAlloc_5820_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5820_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5820_, 3, v_r_5801_);
lean_ctor_set(v_reuseFailAlloc_5820_, 4, v_impl_5777_);
v___x_5816_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
lean_object* v___x_5818_; 
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 4, v___x_5816_);
lean_ctor_set(v___x_5794_, 3, v___y_5811_);
lean_ctor_set(v___x_5794_, 2, v_v_5799_);
lean_ctor_set(v___x_5794_, 1, v_k_5798_);
lean_ctor_set(v___x_5794_, 0, v___x_5809_);
v___x_5818_ = v___x_5794_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v___x_5809_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v_k_5798_);
lean_ctor_set(v_reuseFailAlloc_5819_, 2, v_v_5799_);
lean_ctor_set(v_reuseFailAlloc_5819_, 3, v___y_5811_);
lean_ctor_set(v_reuseFailAlloc_5819_, 4, v___x_5816_);
v___x_5818_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
return v___x_5818_;
}
}
}
v___jp_5822_:
{
lean_object* v___x_5824_; lean_object* v___x_5826_; 
v___x_5824_ = lean_nat_add(v___x_5821_, v___y_5823_);
lean_dec(v___y_5823_);
lean_dec(v___x_5821_);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v_l_5800_);
lean_ctor_set(v___x_5289_, 3, v_l_5783_);
lean_ctor_set(v___x_5289_, 2, v_v_5782_);
lean_ctor_set(v___x_5289_, 1, v_k_5781_);
lean_ctor_set(v___x_5289_, 0, v___x_5824_);
v___x_5826_ = v___x_5289_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v___x_5824_);
lean_ctor_set(v_reuseFailAlloc_5830_, 1, v_k_5781_);
lean_ctor_set(v_reuseFailAlloc_5830_, 2, v_v_5782_);
lean_ctor_set(v_reuseFailAlloc_5830_, 3, v_l_5783_);
lean_ctor_set(v_reuseFailAlloc_5830_, 4, v_l_5800_);
v___x_5826_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
lean_object* v___x_5827_; 
v___x_5827_ = lean_nat_add(v___x_5778_, v_size_5779_);
if (lean_obj_tag(v_r_5801_) == 0)
{
lean_object* v_size_5828_; 
v_size_5828_ = lean_ctor_get(v_r_5801_, 0);
lean_inc(v_size_5828_);
v___y_5811_ = v___x_5826_;
v___y_5812_ = v___x_5827_;
v___y_5813_ = v_size_5828_;
goto v___jp_5810_;
}
else
{
lean_object* v___x_5829_; 
v___x_5829_ = lean_unsigned_to_nat(0u);
v___y_5811_ = v___x_5826_;
v___y_5812_ = v___x_5827_;
v___y_5813_ = v___x_5829_;
goto v___jp_5810_;
}
}
}
}
}
else
{
lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5844_; 
lean_del_object(v___x_5289_);
v___x_5839_ = lean_nat_add(v___x_5778_, v_size_5780_);
lean_dec(v_size_5780_);
v___x_5840_ = lean_nat_add(v___x_5839_, v_size_5779_);
lean_dec(v___x_5839_);
v___x_5841_ = lean_nat_add(v___x_5778_, v_size_5779_);
v___x_5842_ = lean_nat_add(v___x_5841_, v_size_5797_);
lean_dec(v___x_5841_);
lean_inc_ref(v_impl_5777_);
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 4, v_impl_5777_);
lean_ctor_set(v___x_5794_, 3, v_r_5784_);
lean_ctor_set(v___x_5794_, 2, v_v_5285_);
lean_ctor_set(v___x_5794_, 1, v_k_5284_);
lean_ctor_set(v___x_5794_, 0, v___x_5842_);
v___x_5844_ = v___x_5794_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v___x_5842_);
lean_ctor_set(v_reuseFailAlloc_5857_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5857_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5857_, 3, v_r_5784_);
lean_ctor_set(v_reuseFailAlloc_5857_, 4, v_impl_5777_);
v___x_5844_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
lean_object* v___x_5846_; uint8_t v_isShared_5847_; uint8_t v_isSharedCheck_5851_; 
v_isSharedCheck_5851_ = !lean_is_exclusive(v_impl_5777_);
if (v_isSharedCheck_5851_ == 0)
{
lean_object* v_unused_5852_; lean_object* v_unused_5853_; lean_object* v_unused_5854_; lean_object* v_unused_5855_; lean_object* v_unused_5856_; 
v_unused_5852_ = lean_ctor_get(v_impl_5777_, 4);
lean_dec(v_unused_5852_);
v_unused_5853_ = lean_ctor_get(v_impl_5777_, 3);
lean_dec(v_unused_5853_);
v_unused_5854_ = lean_ctor_get(v_impl_5777_, 2);
lean_dec(v_unused_5854_);
v_unused_5855_ = lean_ctor_get(v_impl_5777_, 1);
lean_dec(v_unused_5855_);
v_unused_5856_ = lean_ctor_get(v_impl_5777_, 0);
lean_dec(v_unused_5856_);
v___x_5846_ = v_impl_5777_;
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
else
{
lean_dec(v_impl_5777_);
v___x_5846_ = lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
v_resetjp_5845_:
{
lean_object* v___x_5849_; 
if (v_isShared_5847_ == 0)
{
lean_ctor_set(v___x_5846_, 4, v___x_5844_);
lean_ctor_set(v___x_5846_, 3, v_l_5783_);
lean_ctor_set(v___x_5846_, 2, v_v_5782_);
lean_ctor_set(v___x_5846_, 1, v_k_5781_);
lean_ctor_set(v___x_5846_, 0, v___x_5840_);
v___x_5849_ = v___x_5846_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v___x_5840_);
lean_ctor_set(v_reuseFailAlloc_5850_, 1, v_k_5781_);
lean_ctor_set(v_reuseFailAlloc_5850_, 2, v_v_5782_);
lean_ctor_set(v_reuseFailAlloc_5850_, 3, v_l_5783_);
lean_ctor_set(v_reuseFailAlloc_5850_, 4, v___x_5844_);
v___x_5849_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
return v___x_5849_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5864_; lean_object* v___x_5865_; lean_object* v___x_5867_; 
v_size_5864_ = lean_ctor_get(v_impl_5777_, 0);
v___x_5865_ = lean_nat_add(v___x_5778_, v_size_5864_);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v_impl_5777_);
lean_ctor_set(v___x_5289_, 0, v___x_5865_);
v___x_5867_ = v___x_5289_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v___x_5865_);
lean_ctor_set(v_reuseFailAlloc_5868_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5868_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5868_, 3, v_l_5286_);
lean_ctor_set(v_reuseFailAlloc_5868_, 4, v_impl_5777_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
}
else
{
if (lean_obj_tag(v_l_5286_) == 0)
{
lean_object* v_l_5869_; 
v_l_5869_ = lean_ctor_get(v_l_5286_, 3);
if (lean_obj_tag(v_l_5869_) == 0)
{
lean_object* v_r_5870_; 
lean_inc_ref(v_l_5869_);
v_r_5870_ = lean_ctor_get(v_l_5286_, 4);
lean_inc(v_r_5870_);
if (lean_obj_tag(v_r_5870_) == 0)
{
lean_object* v_size_5871_; lean_object* v_k_5872_; lean_object* v_v_5873_; lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_5886_; 
v_size_5871_ = lean_ctor_get(v_l_5286_, 0);
v_k_5872_ = lean_ctor_get(v_l_5286_, 1);
v_v_5873_ = lean_ctor_get(v_l_5286_, 2);
v_isSharedCheck_5886_ = !lean_is_exclusive(v_l_5286_);
if (v_isSharedCheck_5886_ == 0)
{
lean_object* v_unused_5887_; lean_object* v_unused_5888_; 
v_unused_5887_ = lean_ctor_get(v_l_5286_, 4);
lean_dec(v_unused_5887_);
v_unused_5888_ = lean_ctor_get(v_l_5286_, 3);
lean_dec(v_unused_5888_);
v___x_5875_ = v_l_5286_;
v_isShared_5876_ = v_isSharedCheck_5886_;
goto v_resetjp_5874_;
}
else
{
lean_inc(v_v_5873_);
lean_inc(v_k_5872_);
lean_inc(v_size_5871_);
lean_dec(v_l_5286_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_5886_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
lean_object* v_size_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5881_; 
v_size_5877_ = lean_ctor_get(v_r_5870_, 0);
v___x_5878_ = lean_nat_add(v___x_5778_, v_size_5871_);
lean_dec(v_size_5871_);
v___x_5879_ = lean_nat_add(v___x_5778_, v_size_5877_);
if (v_isShared_5876_ == 0)
{
lean_ctor_set(v___x_5875_, 4, v_impl_5777_);
lean_ctor_set(v___x_5875_, 3, v_r_5870_);
lean_ctor_set(v___x_5875_, 2, v_v_5285_);
lean_ctor_set(v___x_5875_, 1, v_k_5284_);
lean_ctor_set(v___x_5875_, 0, v___x_5879_);
v___x_5881_ = v___x_5875_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v___x_5879_);
lean_ctor_set(v_reuseFailAlloc_5885_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5885_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5885_, 3, v_r_5870_);
lean_ctor_set(v_reuseFailAlloc_5885_, 4, v_impl_5777_);
v___x_5881_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
lean_object* v___x_5883_; 
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v___x_5881_);
lean_ctor_set(v___x_5289_, 3, v_l_5869_);
lean_ctor_set(v___x_5289_, 2, v_v_5873_);
lean_ctor_set(v___x_5289_, 1, v_k_5872_);
lean_ctor_set(v___x_5289_, 0, v___x_5878_);
v___x_5883_ = v___x_5289_;
goto v_reusejp_5882_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v___x_5878_);
lean_ctor_set(v_reuseFailAlloc_5884_, 1, v_k_5872_);
lean_ctor_set(v_reuseFailAlloc_5884_, 2, v_v_5873_);
lean_ctor_set(v_reuseFailAlloc_5884_, 3, v_l_5869_);
lean_ctor_set(v_reuseFailAlloc_5884_, 4, v___x_5881_);
v___x_5883_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5882_;
}
v_reusejp_5882_:
{
return v___x_5883_;
}
}
}
}
else
{
lean_object* v_k_5889_; lean_object* v_v_5890_; lean_object* v___x_5892_; uint8_t v_isShared_5893_; uint8_t v_isSharedCheck_5901_; 
v_k_5889_ = lean_ctor_get(v_l_5286_, 1);
v_v_5890_ = lean_ctor_get(v_l_5286_, 2);
v_isSharedCheck_5901_ = !lean_is_exclusive(v_l_5286_);
if (v_isSharedCheck_5901_ == 0)
{
lean_object* v_unused_5902_; lean_object* v_unused_5903_; lean_object* v_unused_5904_; 
v_unused_5902_ = lean_ctor_get(v_l_5286_, 4);
lean_dec(v_unused_5902_);
v_unused_5903_ = lean_ctor_get(v_l_5286_, 3);
lean_dec(v_unused_5903_);
v_unused_5904_ = lean_ctor_get(v_l_5286_, 0);
lean_dec(v_unused_5904_);
v___x_5892_ = v_l_5286_;
v_isShared_5893_ = v_isSharedCheck_5901_;
goto v_resetjp_5891_;
}
else
{
lean_inc(v_v_5890_);
lean_inc(v_k_5889_);
lean_dec(v_l_5286_);
v___x_5892_ = lean_box(0);
v_isShared_5893_ = v_isSharedCheck_5901_;
goto v_resetjp_5891_;
}
v_resetjp_5891_:
{
lean_object* v___x_5894_; lean_object* v___x_5896_; 
v___x_5894_ = lean_unsigned_to_nat(3u);
if (v_isShared_5893_ == 0)
{
lean_ctor_set(v___x_5892_, 3, v_r_5870_);
lean_ctor_set(v___x_5892_, 2, v_v_5285_);
lean_ctor_set(v___x_5892_, 1, v_k_5284_);
lean_ctor_set(v___x_5892_, 0, v___x_5778_);
v___x_5896_ = v___x_5892_;
goto v_reusejp_5895_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v___x_5778_);
lean_ctor_set(v_reuseFailAlloc_5900_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5900_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5900_, 3, v_r_5870_);
lean_ctor_set(v_reuseFailAlloc_5900_, 4, v_r_5870_);
v___x_5896_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5895_;
}
v_reusejp_5895_:
{
lean_object* v___x_5898_; 
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v___x_5896_);
lean_ctor_set(v___x_5289_, 3, v_l_5869_);
lean_ctor_set(v___x_5289_, 2, v_v_5890_);
lean_ctor_set(v___x_5289_, 1, v_k_5889_);
lean_ctor_set(v___x_5289_, 0, v___x_5894_);
v___x_5898_ = v___x_5289_;
goto v_reusejp_5897_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v___x_5894_);
lean_ctor_set(v_reuseFailAlloc_5899_, 1, v_k_5889_);
lean_ctor_set(v_reuseFailAlloc_5899_, 2, v_v_5890_);
lean_ctor_set(v_reuseFailAlloc_5899_, 3, v_l_5869_);
lean_ctor_set(v_reuseFailAlloc_5899_, 4, v___x_5896_);
v___x_5898_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5897_;
}
v_reusejp_5897_:
{
return v___x_5898_;
}
}
}
}
}
else
{
lean_object* v_r_5905_; 
v_r_5905_ = lean_ctor_get(v_l_5286_, 4);
lean_inc(v_r_5905_);
if (lean_obj_tag(v_r_5905_) == 0)
{
lean_object* v_k_5906_; lean_object* v_v_5907_; lean_object* v___x_5909_; uint8_t v_isShared_5910_; uint8_t v_isSharedCheck_5930_; 
lean_inc(v_l_5869_);
v_k_5906_ = lean_ctor_get(v_l_5286_, 1);
v_v_5907_ = lean_ctor_get(v_l_5286_, 2);
v_isSharedCheck_5930_ = !lean_is_exclusive(v_l_5286_);
if (v_isSharedCheck_5930_ == 0)
{
lean_object* v_unused_5931_; lean_object* v_unused_5932_; lean_object* v_unused_5933_; 
v_unused_5931_ = lean_ctor_get(v_l_5286_, 4);
lean_dec(v_unused_5931_);
v_unused_5932_ = lean_ctor_get(v_l_5286_, 3);
lean_dec(v_unused_5932_);
v_unused_5933_ = lean_ctor_get(v_l_5286_, 0);
lean_dec(v_unused_5933_);
v___x_5909_ = v_l_5286_;
v_isShared_5910_ = v_isSharedCheck_5930_;
goto v_resetjp_5908_;
}
else
{
lean_inc(v_v_5907_);
lean_inc(v_k_5906_);
lean_dec(v_l_5286_);
v___x_5909_ = lean_box(0);
v_isShared_5910_ = v_isSharedCheck_5930_;
goto v_resetjp_5908_;
}
v_resetjp_5908_:
{
lean_object* v_k_5911_; lean_object* v_v_5912_; lean_object* v___x_5914_; uint8_t v_isShared_5915_; uint8_t v_isSharedCheck_5926_; 
v_k_5911_ = lean_ctor_get(v_r_5905_, 1);
v_v_5912_ = lean_ctor_get(v_r_5905_, 2);
v_isSharedCheck_5926_ = !lean_is_exclusive(v_r_5905_);
if (v_isSharedCheck_5926_ == 0)
{
lean_object* v_unused_5927_; lean_object* v_unused_5928_; lean_object* v_unused_5929_; 
v_unused_5927_ = lean_ctor_get(v_r_5905_, 4);
lean_dec(v_unused_5927_);
v_unused_5928_ = lean_ctor_get(v_r_5905_, 3);
lean_dec(v_unused_5928_);
v_unused_5929_ = lean_ctor_get(v_r_5905_, 0);
lean_dec(v_unused_5929_);
v___x_5914_ = v_r_5905_;
v_isShared_5915_ = v_isSharedCheck_5926_;
goto v_resetjp_5913_;
}
else
{
lean_inc(v_v_5912_);
lean_inc(v_k_5911_);
lean_dec(v_r_5905_);
v___x_5914_ = lean_box(0);
v_isShared_5915_ = v_isSharedCheck_5926_;
goto v_resetjp_5913_;
}
v_resetjp_5913_:
{
lean_object* v___x_5916_; lean_object* v___x_5918_; 
v___x_5916_ = lean_unsigned_to_nat(3u);
if (v_isShared_5915_ == 0)
{
lean_ctor_set(v___x_5914_, 4, v_l_5869_);
lean_ctor_set(v___x_5914_, 3, v_l_5869_);
lean_ctor_set(v___x_5914_, 2, v_v_5907_);
lean_ctor_set(v___x_5914_, 1, v_k_5906_);
lean_ctor_set(v___x_5914_, 0, v___x_5778_);
v___x_5918_ = v___x_5914_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5925_; 
v_reuseFailAlloc_5925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5925_, 0, v___x_5778_);
lean_ctor_set(v_reuseFailAlloc_5925_, 1, v_k_5906_);
lean_ctor_set(v_reuseFailAlloc_5925_, 2, v_v_5907_);
lean_ctor_set(v_reuseFailAlloc_5925_, 3, v_l_5869_);
lean_ctor_set(v_reuseFailAlloc_5925_, 4, v_l_5869_);
v___x_5918_ = v_reuseFailAlloc_5925_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
lean_object* v___x_5920_; 
if (v_isShared_5910_ == 0)
{
lean_ctor_set(v___x_5909_, 4, v_l_5869_);
lean_ctor_set(v___x_5909_, 2, v_v_5285_);
lean_ctor_set(v___x_5909_, 1, v_k_5284_);
lean_ctor_set(v___x_5909_, 0, v___x_5778_);
v___x_5920_ = v___x_5909_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5924_; 
v_reuseFailAlloc_5924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5924_, 0, v___x_5778_);
lean_ctor_set(v_reuseFailAlloc_5924_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5924_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5924_, 3, v_l_5869_);
lean_ctor_set(v_reuseFailAlloc_5924_, 4, v_l_5869_);
v___x_5920_ = v_reuseFailAlloc_5924_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
lean_object* v___x_5922_; 
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v___x_5920_);
lean_ctor_set(v___x_5289_, 3, v___x_5918_);
lean_ctor_set(v___x_5289_, 2, v_v_5912_);
lean_ctor_set(v___x_5289_, 1, v_k_5911_);
lean_ctor_set(v___x_5289_, 0, v___x_5916_);
v___x_5922_ = v___x_5289_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v___x_5916_);
lean_ctor_set(v_reuseFailAlloc_5923_, 1, v_k_5911_);
lean_ctor_set(v_reuseFailAlloc_5923_, 2, v_v_5912_);
lean_ctor_set(v_reuseFailAlloc_5923_, 3, v___x_5918_);
lean_ctor_set(v_reuseFailAlloc_5923_, 4, v___x_5920_);
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
else
{
lean_object* v___x_5934_; lean_object* v___x_5936_; 
v___x_5934_ = lean_unsigned_to_nat(2u);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v_r_5905_);
lean_ctor_set(v___x_5289_, 0, v___x_5934_);
v___x_5936_ = v___x_5289_;
goto v_reusejp_5935_;
}
else
{
lean_object* v_reuseFailAlloc_5937_; 
v_reuseFailAlloc_5937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5937_, 0, v___x_5934_);
lean_ctor_set(v_reuseFailAlloc_5937_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5937_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5937_, 3, v_l_5286_);
lean_ctor_set(v_reuseFailAlloc_5937_, 4, v_r_5905_);
v___x_5936_ = v_reuseFailAlloc_5937_;
goto v_reusejp_5935_;
}
v_reusejp_5935_:
{
return v___x_5936_;
}
}
}
}
else
{
lean_object* v___x_5939_; 
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 4, v_l_5286_);
lean_ctor_set(v___x_5289_, 0, v___x_5778_);
v___x_5939_ = v___x_5289_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v___x_5778_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5940_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5940_, 3, v_l_5286_);
lean_ctor_set(v_reuseFailAlloc_5940_, 4, v_l_5286_);
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
}
}
}
else
{
return v_t_5283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_5943_, lean_object* v_t_5944_){
_start:
{
lean_object* v_res_5945_; 
v_res_5945_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5943_, v_t_5944_);
lean_dec(v_k_5943_);
return v_res_5945_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_5946_, lean_object* v_x_5947_){
_start:
{
if (lean_obj_tag(v_x_5947_) == 0)
{
lean_object* v_k_5948_; lean_object* v_l_5949_; lean_object* v_r_5950_; lean_object* v___x_5951_; lean_object* v_ileans_5952_; lean_object* v_workers_5953_; lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_5962_; 
v_k_5948_ = lean_ctor_get(v_x_5947_, 1);
v_l_5949_ = lean_ctor_get(v_x_5947_, 3);
v_r_5950_ = lean_ctor_get(v_x_5947_, 4);
v___x_5951_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_5946_, v_l_5949_);
v_ileans_5952_ = lean_ctor_get(v___x_5951_, 0);
v_workers_5953_ = lean_ctor_get(v___x_5951_, 1);
v_isSharedCheck_5962_ = !lean_is_exclusive(v___x_5951_);
if (v_isSharedCheck_5962_ == 0)
{
v___x_5955_ = v___x_5951_;
v_isShared_5956_ = v_isSharedCheck_5962_;
goto v_resetjp_5954_;
}
else
{
lean_inc(v_workers_5953_);
lean_inc(v_ileans_5952_);
lean_dec(v___x_5951_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_5962_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
lean_object* v___x_5957_; lean_object* v___x_5959_; 
v___x_5957_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5948_, v_ileans_5952_);
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 0, v___x_5957_);
v___x_5959_ = v___x_5955_;
goto v_reusejp_5958_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v___x_5957_);
lean_ctor_set(v_reuseFailAlloc_5961_, 1, v_workers_5953_);
v___x_5959_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5958_;
}
v_reusejp_5958_:
{
v_init_5946_ = v___x_5959_;
v_x_5947_ = v_r_5950_;
goto _start;
}
}
}
else
{
return v_init_5946_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_5963_, lean_object* v_x_5964_){
_start:
{
lean_object* v_res_5965_; 
v_res_5965_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_5963_, v_x_5964_);
lean_dec(v_x_5964_);
return v_res_5965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_5966_, lean_object* v_path_5967_){
_start:
{
lean_object* v_ileans_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; 
v_ileans_5968_ = lean_ctor_get(v_self_5966_, 0);
lean_inc(v_ileans_5968_);
v___x_5969_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5967_, v_ileans_5968_);
v___x_5970_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_5966_, v___x_5969_);
lean_dec(v___x_5969_);
return v___x_5970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_5971_, lean_object* v_path_5972_){
_start:
{
lean_object* v_res_5973_; 
v_res_5973_ = l_Lean_Server_References_removeIlean(v_self_5971_, v_path_5972_);
lean_dec_ref(v_path_5972_);
return v_res_5973_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_5974_, lean_object* v_k_5975_, lean_object* v_t_5976_, lean_object* v_h_5977_){
_start:
{
lean_object* v___x_5978_; 
v___x_5978_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5975_, v_t_5976_);
return v___x_5978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_5979_, lean_object* v_k_5980_, lean_object* v_t_5981_, lean_object* v_h_5982_){
_start:
{
lean_object* v_res_5983_; 
v_res_5983_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_5979_, v_k_5980_, v_t_5981_, v_h_5982_);
lean_dec(v_k_5980_);
return v_res_5983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_5984_, lean_object* v_t_5985_, lean_object* v_hl_5986_){
_start:
{
lean_object* v___x_5987_; 
v___x_5987_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5984_, v_t_5985_);
return v___x_5987_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_5988_, lean_object* v_t_5989_, lean_object* v_hl_5990_){
_start:
{
lean_object* v_res_5991_; 
v_res_5991_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_5988_, v_t_5989_, v_hl_5990_);
lean_dec_ref(v_path_5988_);
return v_res_5991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_5992_, lean_object* v_t_5993_){
_start:
{
lean_object* v___x_5994_; 
v___x_5994_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_5992_, v_t_5993_);
return v___x_5994_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_5995_, lean_object* v_t_5996_){
_start:
{
lean_object* v_res_5997_; 
v_res_5997_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_5995_, v_t_5996_);
lean_dec(v_t_5996_);
return v_res_5997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_5998_, lean_object* v_k_5999_){
_start:
{
if (lean_obj_tag(v_t_5998_) == 0)
{
lean_object* v_k_6000_; lean_object* v_v_6001_; lean_object* v_l_6002_; lean_object* v_r_6003_; uint8_t v___x_6004_; 
v_k_6000_ = lean_ctor_get(v_t_5998_, 1);
v_v_6001_ = lean_ctor_get(v_t_5998_, 2);
v_l_6002_ = lean_ctor_get(v_t_5998_, 3);
v_r_6003_ = lean_ctor_get(v_t_5998_, 4);
v___x_6004_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5999_, v_k_6000_);
switch(v___x_6004_)
{
case 0:
{
v_t_5998_ = v_l_6002_;
goto _start;
}
case 1:
{
lean_object* v___x_6006_; 
lean_inc(v_v_6001_);
v___x_6006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6006_, 0, v_v_6001_);
return v___x_6006_;
}
default: 
{
v_t_5998_ = v_r_6003_;
goto _start;
}
}
}
else
{
lean_object* v___x_6008_; 
v___x_6008_ = lean_box(0);
return v___x_6008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_6009_, lean_object* v_k_6010_){
_start:
{
lean_object* v_res_6011_; 
v_res_6011_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6009_, v_k_6010_);
lean_dec(v_k_6010_);
lean_dec(v_t_6009_);
return v_res_6011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_6012_, lean_object* v_name_6013_, lean_object* v_moduleUri_6014_, lean_object* v_version_6015_, lean_object* v_directImports_6016_, uint8_t v_isSetupFailure_6017_){
_start:
{
lean_object* v___x_6019_; lean_object* v___x_6020_; 
v___x_6019_ = lean_box(1);
v___x_6020_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_6016_);
if (lean_obj_tag(v___x_6020_) == 0)
{
lean_object* v_a_6021_; lean_object* v___x_6023_; uint8_t v_isShared_6024_; uint8_t v_isSharedCheck_6086_; 
v_a_6021_ = lean_ctor_get(v___x_6020_, 0);
v_isSharedCheck_6086_ = !lean_is_exclusive(v___x_6020_);
if (v_isSharedCheck_6086_ == 0)
{
v___x_6023_ = v___x_6020_;
v_isShared_6024_ = v_isSharedCheck_6086_;
goto v_resetjp_6022_;
}
else
{
lean_inc(v_a_6021_);
lean_dec(v___x_6020_);
v___x_6023_ = lean_box(0);
v_isShared_6024_ = v_isSharedCheck_6086_;
goto v_resetjp_6022_;
}
v_resetjp_6022_:
{
lean_object* v_ileans_6025_; lean_object* v_workers_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; 
v_ileans_6025_ = lean_ctor_get(v_self_6012_, 0);
v_workers_6026_ = lean_ctor_get(v_self_6012_, 1);
v___x_6027_ = lean_box(v_isSetupFailure_6017_);
v___x_6028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6028_, 0, v___x_6027_);
v___x_6029_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6026_, v_name_6013_);
if (lean_obj_tag(v___x_6029_) == 1)
{
lean_object* v_val_6030_; lean_object* v_version_6031_; lean_object* v_refs_6032_; lean_object* v_decls_6033_; lean_object* v___x_6035_; uint8_t v_isShared_6036_; uint8_t v_isSharedCheck_6068_; 
v_val_6030_ = lean_ctor_get(v___x_6029_, 0);
lean_inc(v_val_6030_);
lean_dec_ref_known(v___x_6029_, 1);
v_version_6031_ = lean_ctor_get(v_val_6030_, 1);
v_refs_6032_ = lean_ctor_get(v_val_6030_, 4);
v_decls_6033_ = lean_ctor_get(v_val_6030_, 5);
v_isSharedCheck_6068_ = !lean_is_exclusive(v_val_6030_);
if (v_isSharedCheck_6068_ == 0)
{
lean_object* v_unused_6069_; lean_object* v_unused_6070_; lean_object* v_unused_6071_; 
v_unused_6069_ = lean_ctor_get(v_val_6030_, 3);
lean_dec(v_unused_6069_);
v_unused_6070_ = lean_ctor_get(v_val_6030_, 2);
lean_dec(v_unused_6070_);
v_unused_6071_ = lean_ctor_get(v_val_6030_, 0);
lean_dec(v_unused_6071_);
v___x_6035_ = v_val_6030_;
v_isShared_6036_ = v_isSharedCheck_6068_;
goto v_resetjp_6034_;
}
else
{
lean_inc(v_decls_6033_);
lean_inc(v_refs_6032_);
lean_inc(v_version_6031_);
lean_dec(v_val_6030_);
v___x_6035_ = lean_box(0);
v_isShared_6036_ = v_isSharedCheck_6068_;
goto v_resetjp_6034_;
}
v_resetjp_6034_:
{
uint8_t v___x_6037_; 
v___x_6037_ = lean_nat_dec_lt(v_version_6015_, v_version_6031_);
if (v___x_6037_ == 0)
{
lean_object* v___x_6039_; uint8_t v_isShared_6040_; uint8_t v_isSharedCheck_6062_; 
lean_inc(v_workers_6026_);
lean_inc(v_ileans_6025_);
v_isSharedCheck_6062_ = !lean_is_exclusive(v_self_6012_);
if (v_isSharedCheck_6062_ == 0)
{
lean_object* v_unused_6063_; lean_object* v_unused_6064_; 
v_unused_6063_ = lean_ctor_get(v_self_6012_, 1);
lean_dec(v_unused_6063_);
v_unused_6064_ = lean_ctor_get(v_self_6012_, 0);
lean_dec(v_unused_6064_);
v___x_6039_ = v_self_6012_;
v_isShared_6040_ = v_isSharedCheck_6062_;
goto v_resetjp_6038_;
}
else
{
lean_dec(v_self_6012_);
v___x_6039_ = lean_box(0);
v_isShared_6040_ = v_isSharedCheck_6062_;
goto v_resetjp_6038_;
}
v_resetjp_6038_:
{
uint8_t v___x_6041_; 
v___x_6041_ = lean_nat_dec_eq(v_version_6015_, v_version_6031_);
lean_dec(v_version_6031_);
if (v___x_6041_ == 0)
{
lean_object* v___x_6043_; 
lean_dec(v_decls_6033_);
lean_dec(v_refs_6032_);
if (v_isShared_6036_ == 0)
{
lean_ctor_set(v___x_6035_, 5, v___x_6019_);
lean_ctor_set(v___x_6035_, 4, v___x_6019_);
lean_ctor_set(v___x_6035_, 3, v___x_6028_);
lean_ctor_set(v___x_6035_, 2, v_a_6021_);
lean_ctor_set(v___x_6035_, 1, v_version_6015_);
lean_ctor_set(v___x_6035_, 0, v_moduleUri_6014_);
v___x_6043_ = v___x_6035_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6051_; 
v_reuseFailAlloc_6051_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_moduleUri_6014_);
lean_ctor_set(v_reuseFailAlloc_6051_, 1, v_version_6015_);
lean_ctor_set(v_reuseFailAlloc_6051_, 2, v_a_6021_);
lean_ctor_set(v_reuseFailAlloc_6051_, 3, v___x_6028_);
lean_ctor_set(v_reuseFailAlloc_6051_, 4, v___x_6019_);
lean_ctor_set(v_reuseFailAlloc_6051_, 5, v___x_6019_);
v___x_6043_ = v_reuseFailAlloc_6051_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
lean_object* v___x_6044_; lean_object* v___x_6046_; 
v___x_6044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6013_, v___x_6043_, v_workers_6026_);
if (v_isShared_6040_ == 0)
{
lean_ctor_set(v___x_6039_, 1, v___x_6044_);
v___x_6046_ = v___x_6039_;
goto v_reusejp_6045_;
}
else
{
lean_object* v_reuseFailAlloc_6050_; 
v_reuseFailAlloc_6050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6050_, 0, v_ileans_6025_);
lean_ctor_set(v_reuseFailAlloc_6050_, 1, v___x_6044_);
v___x_6046_ = v_reuseFailAlloc_6050_;
goto v_reusejp_6045_;
}
v_reusejp_6045_:
{
lean_object* v___x_6048_; 
if (v_isShared_6024_ == 0)
{
lean_ctor_set(v___x_6023_, 0, v___x_6046_);
v___x_6048_ = v___x_6023_;
goto v_reusejp_6047_;
}
else
{
lean_object* v_reuseFailAlloc_6049_; 
v_reuseFailAlloc_6049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6049_, 0, v___x_6046_);
v___x_6048_ = v_reuseFailAlloc_6049_;
goto v_reusejp_6047_;
}
v_reusejp_6047_:
{
return v___x_6048_;
}
}
}
}
else
{
lean_object* v___x_6053_; 
if (v_isShared_6036_ == 0)
{
lean_ctor_set(v___x_6035_, 3, v___x_6028_);
lean_ctor_set(v___x_6035_, 2, v_a_6021_);
lean_ctor_set(v___x_6035_, 1, v_version_6015_);
lean_ctor_set(v___x_6035_, 0, v_moduleUri_6014_);
v___x_6053_ = v___x_6035_;
goto v_reusejp_6052_;
}
else
{
lean_object* v_reuseFailAlloc_6061_; 
v_reuseFailAlloc_6061_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6061_, 0, v_moduleUri_6014_);
lean_ctor_set(v_reuseFailAlloc_6061_, 1, v_version_6015_);
lean_ctor_set(v_reuseFailAlloc_6061_, 2, v_a_6021_);
lean_ctor_set(v_reuseFailAlloc_6061_, 3, v___x_6028_);
lean_ctor_set(v_reuseFailAlloc_6061_, 4, v_refs_6032_);
lean_ctor_set(v_reuseFailAlloc_6061_, 5, v_decls_6033_);
v___x_6053_ = v_reuseFailAlloc_6061_;
goto v_reusejp_6052_;
}
v_reusejp_6052_:
{
lean_object* v___x_6054_; lean_object* v___x_6056_; 
v___x_6054_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6013_, v___x_6053_, v_workers_6026_);
if (v_isShared_6040_ == 0)
{
lean_ctor_set(v___x_6039_, 1, v___x_6054_);
v___x_6056_ = v___x_6039_;
goto v_reusejp_6055_;
}
else
{
lean_object* v_reuseFailAlloc_6060_; 
v_reuseFailAlloc_6060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6060_, 0, v_ileans_6025_);
lean_ctor_set(v_reuseFailAlloc_6060_, 1, v___x_6054_);
v___x_6056_ = v_reuseFailAlloc_6060_;
goto v_reusejp_6055_;
}
v_reusejp_6055_:
{
lean_object* v___x_6058_; 
if (v_isShared_6024_ == 0)
{
lean_ctor_set(v___x_6023_, 0, v___x_6056_);
v___x_6058_ = v___x_6023_;
goto v_reusejp_6057_;
}
else
{
lean_object* v_reuseFailAlloc_6059_; 
v_reuseFailAlloc_6059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6059_, 0, v___x_6056_);
v___x_6058_ = v_reuseFailAlloc_6059_;
goto v_reusejp_6057_;
}
v_reusejp_6057_:
{
return v___x_6058_;
}
}
}
}
}
}
else
{
lean_object* v___x_6066_; 
lean_del_object(v___x_6035_);
lean_dec(v_decls_6033_);
lean_dec(v_refs_6032_);
lean_dec(v_version_6031_);
lean_dec_ref_known(v___x_6028_, 1);
lean_dec(v_a_6021_);
lean_dec(v_version_6015_);
lean_dec_ref(v_moduleUri_6014_);
lean_dec(v_name_6013_);
if (v_isShared_6024_ == 0)
{
lean_ctor_set(v___x_6023_, 0, v_self_6012_);
v___x_6066_ = v___x_6023_;
goto v_reusejp_6065_;
}
else
{
lean_object* v_reuseFailAlloc_6067_; 
v_reuseFailAlloc_6067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6067_, 0, v_self_6012_);
v___x_6066_ = v_reuseFailAlloc_6067_;
goto v_reusejp_6065_;
}
v_reusejp_6065_:
{
return v___x_6066_;
}
}
}
}
else
{
lean_object* v___x_6073_; uint8_t v_isShared_6074_; uint8_t v_isSharedCheck_6083_; 
lean_inc(v_workers_6026_);
lean_inc(v_ileans_6025_);
lean_dec(v___x_6029_);
v_isSharedCheck_6083_ = !lean_is_exclusive(v_self_6012_);
if (v_isSharedCheck_6083_ == 0)
{
lean_object* v_unused_6084_; lean_object* v_unused_6085_; 
v_unused_6084_ = lean_ctor_get(v_self_6012_, 1);
lean_dec(v_unused_6084_);
v_unused_6085_ = lean_ctor_get(v_self_6012_, 0);
lean_dec(v_unused_6085_);
v___x_6073_ = v_self_6012_;
v_isShared_6074_ = v_isSharedCheck_6083_;
goto v_resetjp_6072_;
}
else
{
lean_dec(v_self_6012_);
v___x_6073_ = lean_box(0);
v_isShared_6074_ = v_isSharedCheck_6083_;
goto v_resetjp_6072_;
}
v_resetjp_6072_:
{
lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6078_; 
v___x_6075_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6075_, 0, v_moduleUri_6014_);
lean_ctor_set(v___x_6075_, 1, v_version_6015_);
lean_ctor_set(v___x_6075_, 2, v_a_6021_);
lean_ctor_set(v___x_6075_, 3, v___x_6028_);
lean_ctor_set(v___x_6075_, 4, v___x_6019_);
lean_ctor_set(v___x_6075_, 5, v___x_6019_);
v___x_6076_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6013_, v___x_6075_, v_workers_6026_);
if (v_isShared_6074_ == 0)
{
lean_ctor_set(v___x_6073_, 1, v___x_6076_);
v___x_6078_ = v___x_6073_;
goto v_reusejp_6077_;
}
else
{
lean_object* v_reuseFailAlloc_6082_; 
v_reuseFailAlloc_6082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6082_, 0, v_ileans_6025_);
lean_ctor_set(v_reuseFailAlloc_6082_, 1, v___x_6076_);
v___x_6078_ = v_reuseFailAlloc_6082_;
goto v_reusejp_6077_;
}
v_reusejp_6077_:
{
lean_object* v___x_6080_; 
if (v_isShared_6024_ == 0)
{
lean_ctor_set(v___x_6023_, 0, v___x_6078_);
v___x_6080_ = v___x_6023_;
goto v_reusejp_6079_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v___x_6078_);
v___x_6080_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6079_;
}
v_reusejp_6079_:
{
return v___x_6080_;
}
}
}
}
}
}
else
{
lean_object* v_a_6087_; lean_object* v___x_6089_; uint8_t v_isShared_6090_; uint8_t v_isSharedCheck_6094_; 
lean_dec(v_version_6015_);
lean_dec_ref(v_moduleUri_6014_);
lean_dec(v_name_6013_);
lean_dec_ref(v_self_6012_);
v_a_6087_ = lean_ctor_get(v___x_6020_, 0);
v_isSharedCheck_6094_ = !lean_is_exclusive(v___x_6020_);
if (v_isSharedCheck_6094_ == 0)
{
v___x_6089_ = v___x_6020_;
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
else
{
lean_inc(v_a_6087_);
lean_dec(v___x_6020_);
v___x_6089_ = lean_box(0);
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
v_resetjp_6088_:
{
lean_object* v___x_6092_; 
if (v_isShared_6090_ == 0)
{
v___x_6092_ = v___x_6089_;
goto v_reusejp_6091_;
}
else
{
lean_object* v_reuseFailAlloc_6093_; 
v_reuseFailAlloc_6093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6093_, 0, v_a_6087_);
v___x_6092_ = v_reuseFailAlloc_6093_;
goto v_reusejp_6091_;
}
v_reusejp_6091_:
{
return v___x_6092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6095_, lean_object* v_name_6096_, lean_object* v_moduleUri_6097_, lean_object* v_version_6098_, lean_object* v_directImports_6099_, lean_object* v_isSetupFailure_6100_, lean_object* v_a_6101_){
_start:
{
uint8_t v_isSetupFailure_boxed_6102_; lean_object* v_res_6103_; 
v_isSetupFailure_boxed_6102_ = lean_unbox(v_isSetupFailure_6100_);
v_res_6103_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6095_, v_name_6096_, v_moduleUri_6097_, v_version_6098_, v_directImports_6099_, v_isSetupFailure_boxed_6102_);
lean_dec_ref(v_directImports_6099_);
return v_res_6103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6104_, lean_object* v_t_6105_, lean_object* v_k_6106_){
_start:
{
lean_object* v___x_6107_; 
v___x_6107_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6105_, v_k_6106_);
return v___x_6107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6108_, lean_object* v_t_6109_, lean_object* v_k_6110_){
_start:
{
lean_object* v_res_6111_; 
v_res_6111_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6108_, v_t_6109_, v_k_6110_);
lean_dec(v_k_6110_);
lean_dec(v_t_6109_);
return v_res_6111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6112_, lean_object* v_____s_6113_){
_start:
{
lean_object* v_fst_6114_; lean_object* v_snd_6115_; lean_object* v_r_6116_; lean_object* v___x_6117_; 
v_fst_6114_ = lean_ctor_get(v_x_6112_, 0);
lean_inc(v_fst_6114_);
v_snd_6115_ = lean_ctor_get(v_x_6112_, 1);
lean_inc(v_snd_6115_);
lean_dec_ref(v_x_6112_);
v_r_6116_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6114_, v_snd_6115_, v_____s_6113_);
v___x_6117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6117_, 0, v_r_6116_);
return v___x_6117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6118_, lean_object* v_k_6119_, lean_object* v_fallback_6120_){
_start:
{
if (lean_obj_tag(v_t_6118_) == 0)
{
lean_object* v_k_6121_; lean_object* v_v_6122_; lean_object* v_l_6123_; lean_object* v_r_6124_; uint8_t v___x_6125_; 
v_k_6121_ = lean_ctor_get(v_t_6118_, 1);
v_v_6122_ = lean_ctor_get(v_t_6118_, 2);
v_l_6123_ = lean_ctor_get(v_t_6118_, 3);
v_r_6124_ = lean_ctor_get(v_t_6118_, 4);
v___x_6125_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6119_, v_k_6121_);
switch(v___x_6125_)
{
case 0:
{
v_t_6118_ = v_l_6123_;
goto _start;
}
case 1:
{
lean_inc(v_v_6122_);
return v_v_6122_;
}
default: 
{
v_t_6118_ = v_r_6124_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6120_);
return v_fallback_6120_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6128_, lean_object* v_k_6129_, lean_object* v_fallback_6130_){
_start:
{
lean_object* v_res_6131_; 
v_res_6131_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6128_, v_k_6129_, v_fallback_6130_);
lean_dec(v_fallback_6130_);
lean_dec_ref(v_k_6129_);
lean_dec(v_t_6128_);
return v_res_6131_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6132_, lean_object* v_x_6133_){
_start:
{
if (lean_obj_tag(v_x_6133_) == 0)
{
lean_object* v_k_6134_; lean_object* v_v_6135_; lean_object* v_l_6136_; lean_object* v_r_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; 
v_k_6134_ = lean_ctor_get(v_x_6133_, 1);
lean_inc(v_k_6134_);
v_v_6135_ = lean_ctor_get(v_x_6133_, 2);
lean_inc(v_v_6135_);
v_l_6136_ = lean_ctor_get(v_x_6133_, 3);
lean_inc(v_l_6136_);
v_r_6137_ = lean_ctor_get(v_x_6133_, 4);
lean_inc(v_r_6137_);
lean_dec_ref_known(v_x_6133_, 5);
v___x_6138_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6132_, v_l_6136_);
v___x_6139_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6140_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6138_, v_k_6134_, v___x_6139_);
v___x_6141_ = l_Lean_Lsp_RefInfo_merge(v___x_6140_, v_v_6135_);
v___x_6142_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6134_, v___x_6141_, v___x_6138_);
v_init_6132_ = v___x_6142_;
v_x_6133_ = v_r_6137_;
goto _start;
}
else
{
return v_init_6132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6145_, lean_object* v_name_6146_, lean_object* v_moduleUri_6147_, lean_object* v_version_6148_, lean_object* v_refs_6149_, lean_object* v_decls_6150_){
_start:
{
lean_object* v_ileans_6152_; lean_object* v_workers_6153_; lean_object* v___x_6154_; 
v_ileans_6152_ = lean_ctor_get(v_self_6145_, 0);
v_workers_6153_ = lean_ctor_get(v_self_6145_, 1);
v___x_6154_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6153_, v_name_6146_);
if (lean_obj_tag(v___x_6154_) == 1)
{
lean_object* v_val_6155_; lean_object* v___x_6157_; uint8_t v_isShared_6158_; uint8_t v_isSharedCheck_6203_; 
v_val_6155_ = lean_ctor_get(v___x_6154_, 0);
v_isSharedCheck_6203_ = !lean_is_exclusive(v___x_6154_);
if (v_isSharedCheck_6203_ == 0)
{
v___x_6157_ = v___x_6154_;
v_isShared_6158_ = v_isSharedCheck_6203_;
goto v_resetjp_6156_;
}
else
{
lean_inc(v_val_6155_);
lean_dec(v___x_6154_);
v___x_6157_ = lean_box(0);
v_isShared_6158_ = v_isSharedCheck_6203_;
goto v_resetjp_6156_;
}
v_resetjp_6156_:
{
lean_object* v_version_6159_; lean_object* v_directImports_6160_; lean_object* v_isSetupFailure_x3f_6161_; lean_object* v_refs_6162_; lean_object* v_decls_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6201_; 
v_version_6159_ = lean_ctor_get(v_val_6155_, 1);
v_directImports_6160_ = lean_ctor_get(v_val_6155_, 2);
v_isSetupFailure_x3f_6161_ = lean_ctor_get(v_val_6155_, 3);
v_refs_6162_ = lean_ctor_get(v_val_6155_, 4);
v_decls_6163_ = lean_ctor_get(v_val_6155_, 5);
v_isSharedCheck_6201_ = !lean_is_exclusive(v_val_6155_);
if (v_isSharedCheck_6201_ == 0)
{
lean_object* v_unused_6202_; 
v_unused_6202_ = lean_ctor_get(v_val_6155_, 0);
lean_dec(v_unused_6202_);
v___x_6165_ = v_val_6155_;
v_isShared_6166_ = v_isSharedCheck_6201_;
goto v_resetjp_6164_;
}
else
{
lean_inc(v_decls_6163_);
lean_inc(v_refs_6162_);
lean_inc(v_isSetupFailure_x3f_6161_);
lean_inc(v_directImports_6160_);
lean_inc(v_version_6159_);
lean_dec(v_val_6155_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6201_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
uint8_t v___x_6167_; 
v___x_6167_ = lean_nat_dec_lt(v_version_6148_, v_version_6159_);
if (v___x_6167_ == 0)
{
lean_object* v___x_6169_; uint8_t v_isShared_6170_; uint8_t v_isSharedCheck_6195_; 
lean_inc(v_workers_6153_);
lean_inc(v_ileans_6152_);
v_isSharedCheck_6195_ = !lean_is_exclusive(v_self_6145_);
if (v_isSharedCheck_6195_ == 0)
{
lean_object* v_unused_6196_; lean_object* v_unused_6197_; 
v_unused_6196_ = lean_ctor_get(v_self_6145_, 1);
lean_dec(v_unused_6196_);
v_unused_6197_ = lean_ctor_get(v_self_6145_, 0);
lean_dec(v_unused_6197_);
v___x_6169_ = v_self_6145_;
v_isShared_6170_ = v_isSharedCheck_6195_;
goto v_resetjp_6168_;
}
else
{
lean_dec(v_self_6145_);
v___x_6169_ = lean_box(0);
v_isShared_6170_ = v_isSharedCheck_6195_;
goto v_resetjp_6168_;
}
v_resetjp_6168_:
{
uint8_t v___x_6171_; 
v___x_6171_ = lean_nat_dec_eq(v_version_6148_, v_version_6159_);
lean_dec(v_version_6159_);
if (v___x_6171_ == 0)
{
lean_object* v___x_6173_; 
lean_dec(v_decls_6163_);
lean_dec(v_refs_6162_);
if (v_isShared_6166_ == 0)
{
lean_ctor_set(v___x_6165_, 5, v_decls_6150_);
lean_ctor_set(v___x_6165_, 4, v_refs_6149_);
lean_ctor_set(v___x_6165_, 1, v_version_6148_);
lean_ctor_set(v___x_6165_, 0, v_moduleUri_6147_);
v___x_6173_ = v___x_6165_;
goto v_reusejp_6172_;
}
else
{
lean_object* v_reuseFailAlloc_6181_; 
v_reuseFailAlloc_6181_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_moduleUri_6147_);
lean_ctor_set(v_reuseFailAlloc_6181_, 1, v_version_6148_);
lean_ctor_set(v_reuseFailAlloc_6181_, 2, v_directImports_6160_);
lean_ctor_set(v_reuseFailAlloc_6181_, 3, v_isSetupFailure_x3f_6161_);
lean_ctor_set(v_reuseFailAlloc_6181_, 4, v_refs_6149_);
lean_ctor_set(v_reuseFailAlloc_6181_, 5, v_decls_6150_);
v___x_6173_ = v_reuseFailAlloc_6181_;
goto v_reusejp_6172_;
}
v_reusejp_6172_:
{
lean_object* v___x_6174_; lean_object* v___x_6176_; 
v___x_6174_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6146_, v___x_6173_, v_workers_6153_);
if (v_isShared_6170_ == 0)
{
lean_ctor_set(v___x_6169_, 1, v___x_6174_);
v___x_6176_ = v___x_6169_;
goto v_reusejp_6175_;
}
else
{
lean_object* v_reuseFailAlloc_6180_; 
v_reuseFailAlloc_6180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_ileans_6152_);
lean_ctor_set(v_reuseFailAlloc_6180_, 1, v___x_6174_);
v___x_6176_ = v_reuseFailAlloc_6180_;
goto v_reusejp_6175_;
}
v_reusejp_6175_:
{
lean_object* v___x_6178_; 
if (v_isShared_6158_ == 0)
{
lean_ctor_set_tag(v___x_6157_, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6176_);
v___x_6178_ = v___x_6157_;
goto v_reusejp_6177_;
}
else
{
lean_object* v_reuseFailAlloc_6179_; 
v_reuseFailAlloc_6179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6179_, 0, v___x_6176_);
v___x_6178_ = v_reuseFailAlloc_6179_;
goto v_reusejp_6177_;
}
v_reusejp_6177_:
{
return v___x_6178_;
}
}
}
}
else
{
lean_object* v___f_6182_; lean_object* v_mergedRefs_6183_; lean_object* v_mergedDecls_6184_; lean_object* v___x_6186_; 
v___f_6182_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6183_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6162_, v_refs_6149_);
v_mergedDecls_6184_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6150_, v_decls_6163_, v___f_6182_);
lean_dec(v_decls_6150_);
if (v_isShared_6166_ == 0)
{
lean_ctor_set(v___x_6165_, 5, v_mergedDecls_6184_);
lean_ctor_set(v___x_6165_, 4, v_mergedRefs_6183_);
lean_ctor_set(v___x_6165_, 1, v_version_6148_);
lean_ctor_set(v___x_6165_, 0, v_moduleUri_6147_);
v___x_6186_ = v___x_6165_;
goto v_reusejp_6185_;
}
else
{
lean_object* v_reuseFailAlloc_6194_; 
v_reuseFailAlloc_6194_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6194_, 0, v_moduleUri_6147_);
lean_ctor_set(v_reuseFailAlloc_6194_, 1, v_version_6148_);
lean_ctor_set(v_reuseFailAlloc_6194_, 2, v_directImports_6160_);
lean_ctor_set(v_reuseFailAlloc_6194_, 3, v_isSetupFailure_x3f_6161_);
lean_ctor_set(v_reuseFailAlloc_6194_, 4, v_mergedRefs_6183_);
lean_ctor_set(v_reuseFailAlloc_6194_, 5, v_mergedDecls_6184_);
v___x_6186_ = v_reuseFailAlloc_6194_;
goto v_reusejp_6185_;
}
v_reusejp_6185_:
{
lean_object* v___x_6187_; lean_object* v___x_6189_; 
v___x_6187_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6146_, v___x_6186_, v_workers_6153_);
if (v_isShared_6170_ == 0)
{
lean_ctor_set(v___x_6169_, 1, v___x_6187_);
v___x_6189_ = v___x_6169_;
goto v_reusejp_6188_;
}
else
{
lean_object* v_reuseFailAlloc_6193_; 
v_reuseFailAlloc_6193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6193_, 0, v_ileans_6152_);
lean_ctor_set(v_reuseFailAlloc_6193_, 1, v___x_6187_);
v___x_6189_ = v_reuseFailAlloc_6193_;
goto v_reusejp_6188_;
}
v_reusejp_6188_:
{
lean_object* v___x_6191_; 
if (v_isShared_6158_ == 0)
{
lean_ctor_set_tag(v___x_6157_, 0);
lean_ctor_set(v___x_6157_, 0, v___x_6189_);
v___x_6191_ = v___x_6157_;
goto v_reusejp_6190_;
}
else
{
lean_object* v_reuseFailAlloc_6192_; 
v_reuseFailAlloc_6192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6192_, 0, v___x_6189_);
v___x_6191_ = v_reuseFailAlloc_6192_;
goto v_reusejp_6190_;
}
v_reusejp_6190_:
{
return v___x_6191_;
}
}
}
}
}
}
else
{
lean_object* v___x_6199_; 
lean_del_object(v___x_6165_);
lean_dec(v_decls_6163_);
lean_dec(v_refs_6162_);
lean_dec(v_isSetupFailure_x3f_6161_);
lean_dec_ref(v_directImports_6160_);
lean_dec(v_version_6159_);
lean_dec(v_decls_6150_);
lean_dec(v_refs_6149_);
lean_dec(v_version_6148_);
lean_dec_ref(v_moduleUri_6147_);
lean_dec(v_name_6146_);
if (v_isShared_6158_ == 0)
{
lean_ctor_set_tag(v___x_6157_, 0);
lean_ctor_set(v___x_6157_, 0, v_self_6145_);
v___x_6199_ = v___x_6157_;
goto v_reusejp_6198_;
}
else
{
lean_object* v_reuseFailAlloc_6200_; 
v_reuseFailAlloc_6200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6200_, 0, v_self_6145_);
v___x_6199_ = v_reuseFailAlloc_6200_;
goto v_reusejp_6198_;
}
v_reusejp_6198_:
{
return v___x_6199_;
}
}
}
}
}
else
{
lean_object* v___x_6205_; uint8_t v_isShared_6206_; uint8_t v_isSharedCheck_6215_; 
lean_inc(v_workers_6153_);
lean_inc(v_ileans_6152_);
lean_dec(v___x_6154_);
v_isSharedCheck_6215_ = !lean_is_exclusive(v_self_6145_);
if (v_isSharedCheck_6215_ == 0)
{
lean_object* v_unused_6216_; lean_object* v_unused_6217_; 
v_unused_6216_ = lean_ctor_get(v_self_6145_, 1);
lean_dec(v_unused_6216_);
v_unused_6217_ = lean_ctor_get(v_self_6145_, 0);
lean_dec(v_unused_6217_);
v___x_6205_ = v_self_6145_;
v_isShared_6206_ = v_isSharedCheck_6215_;
goto v_resetjp_6204_;
}
else
{
lean_dec(v_self_6145_);
v___x_6205_ = lean_box(0);
v_isShared_6206_ = v_isSharedCheck_6215_;
goto v_resetjp_6204_;
}
v_resetjp_6204_:
{
lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6212_; 
v___x_6207_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6208_ = lean_box(0);
v___x_6209_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6209_, 0, v_moduleUri_6147_);
lean_ctor_set(v___x_6209_, 1, v_version_6148_);
lean_ctor_set(v___x_6209_, 2, v___x_6207_);
lean_ctor_set(v___x_6209_, 3, v___x_6208_);
lean_ctor_set(v___x_6209_, 4, v_refs_6149_);
lean_ctor_set(v___x_6209_, 5, v_decls_6150_);
v___x_6210_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6146_, v___x_6209_, v_workers_6153_);
if (v_isShared_6206_ == 0)
{
lean_ctor_set(v___x_6205_, 1, v___x_6210_);
v___x_6212_ = v___x_6205_;
goto v_reusejp_6211_;
}
else
{
lean_object* v_reuseFailAlloc_6214_; 
v_reuseFailAlloc_6214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6214_, 0, v_ileans_6152_);
lean_ctor_set(v_reuseFailAlloc_6214_, 1, v___x_6210_);
v___x_6212_ = v_reuseFailAlloc_6214_;
goto v_reusejp_6211_;
}
v_reusejp_6211_:
{
lean_object* v___x_6213_; 
v___x_6213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6213_, 0, v___x_6212_);
return v___x_6213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6218_, lean_object* v_name_6219_, lean_object* v_moduleUri_6220_, lean_object* v_version_6221_, lean_object* v_refs_6222_, lean_object* v_decls_6223_, lean_object* v_a_6224_){
_start:
{
lean_object* v_res_6225_; 
v_res_6225_ = l_Lean_Server_References_updateWorkerRefs(v_self_6218_, v_name_6219_, v_moduleUri_6220_, v_version_6221_, v_refs_6222_, v_decls_6223_);
return v_res_6225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6226_, lean_object* v_t_6227_, lean_object* v_k_6228_, lean_object* v_fallback_6229_){
_start:
{
lean_object* v___x_6230_; 
v___x_6230_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6227_, v_k_6228_, v_fallback_6229_);
return v___x_6230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6231_, lean_object* v_t_6232_, lean_object* v_k_6233_, lean_object* v_fallback_6234_){
_start:
{
lean_object* v_res_6235_; 
v_res_6235_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6231_, v_t_6232_, v_k_6233_, v_fallback_6234_);
lean_dec(v_fallback_6234_);
lean_dec_ref(v_k_6233_);
lean_dec(v_t_6232_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6236_, lean_object* v_t_6237_){
_start:
{
lean_object* v___x_6238_; 
v___x_6238_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6236_, v_t_6237_);
return v___x_6238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6239_, lean_object* v_name_6240_, lean_object* v_moduleUri_6241_, lean_object* v_version_6242_, lean_object* v_refs_6243_, lean_object* v_decls_6244_){
_start:
{
lean_object* v_ileans_6246_; lean_object* v_workers_6247_; lean_object* v___x_6248_; 
v_ileans_6246_ = lean_ctor_get(v_self_6239_, 0);
v_workers_6247_ = lean_ctor_get(v_self_6239_, 1);
v___x_6248_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6247_, v_name_6240_);
if (lean_obj_tag(v___x_6248_) == 1)
{
lean_object* v_val_6249_; lean_object* v___x_6251_; uint8_t v_isShared_6252_; uint8_t v_isSharedCheck_6283_; 
v_val_6249_ = lean_ctor_get(v___x_6248_, 0);
v_isSharedCheck_6283_ = !lean_is_exclusive(v___x_6248_);
if (v_isSharedCheck_6283_ == 0)
{
v___x_6251_ = v___x_6248_;
v_isShared_6252_ = v_isSharedCheck_6283_;
goto v_resetjp_6250_;
}
else
{
lean_inc(v_val_6249_);
lean_dec(v___x_6248_);
v___x_6251_ = lean_box(0);
v_isShared_6252_ = v_isSharedCheck_6283_;
goto v_resetjp_6250_;
}
v_resetjp_6250_:
{
lean_object* v_version_6253_; lean_object* v_directImports_6254_; lean_object* v_isSetupFailure_x3f_6255_; lean_object* v___x_6257_; uint8_t v_isShared_6258_; uint8_t v_isSharedCheck_6279_; 
v_version_6253_ = lean_ctor_get(v_val_6249_, 1);
v_directImports_6254_ = lean_ctor_get(v_val_6249_, 2);
v_isSetupFailure_x3f_6255_ = lean_ctor_get(v_val_6249_, 3);
v_isSharedCheck_6279_ = !lean_is_exclusive(v_val_6249_);
if (v_isSharedCheck_6279_ == 0)
{
lean_object* v_unused_6280_; lean_object* v_unused_6281_; lean_object* v_unused_6282_; 
v_unused_6280_ = lean_ctor_get(v_val_6249_, 5);
lean_dec(v_unused_6280_);
v_unused_6281_ = lean_ctor_get(v_val_6249_, 4);
lean_dec(v_unused_6281_);
v_unused_6282_ = lean_ctor_get(v_val_6249_, 0);
lean_dec(v_unused_6282_);
v___x_6257_ = v_val_6249_;
v_isShared_6258_ = v_isSharedCheck_6279_;
goto v_resetjp_6256_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6255_);
lean_inc(v_directImports_6254_);
lean_inc(v_version_6253_);
lean_dec(v_val_6249_);
v___x_6257_ = lean_box(0);
v_isShared_6258_ = v_isSharedCheck_6279_;
goto v_resetjp_6256_;
}
v_resetjp_6256_:
{
uint8_t v___x_6259_; 
v___x_6259_ = lean_nat_dec_lt(v_version_6242_, v_version_6253_);
lean_dec(v_version_6253_);
if (v___x_6259_ == 0)
{
lean_object* v___x_6261_; uint8_t v_isShared_6262_; uint8_t v_isSharedCheck_6273_; 
lean_inc(v_workers_6247_);
lean_inc(v_ileans_6246_);
v_isSharedCheck_6273_ = !lean_is_exclusive(v_self_6239_);
if (v_isSharedCheck_6273_ == 0)
{
lean_object* v_unused_6274_; lean_object* v_unused_6275_; 
v_unused_6274_ = lean_ctor_get(v_self_6239_, 1);
lean_dec(v_unused_6274_);
v_unused_6275_ = lean_ctor_get(v_self_6239_, 0);
lean_dec(v_unused_6275_);
v___x_6261_ = v_self_6239_;
v_isShared_6262_ = v_isSharedCheck_6273_;
goto v_resetjp_6260_;
}
else
{
lean_dec(v_self_6239_);
v___x_6261_ = lean_box(0);
v_isShared_6262_ = v_isSharedCheck_6273_;
goto v_resetjp_6260_;
}
v_resetjp_6260_:
{
lean_object* v___x_6264_; 
if (v_isShared_6258_ == 0)
{
lean_ctor_set(v___x_6257_, 5, v_decls_6244_);
lean_ctor_set(v___x_6257_, 4, v_refs_6243_);
lean_ctor_set(v___x_6257_, 1, v_version_6242_);
lean_ctor_set(v___x_6257_, 0, v_moduleUri_6241_);
v___x_6264_ = v___x_6257_;
goto v_reusejp_6263_;
}
else
{
lean_object* v_reuseFailAlloc_6272_; 
v_reuseFailAlloc_6272_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6272_, 0, v_moduleUri_6241_);
lean_ctor_set(v_reuseFailAlloc_6272_, 1, v_version_6242_);
lean_ctor_set(v_reuseFailAlloc_6272_, 2, v_directImports_6254_);
lean_ctor_set(v_reuseFailAlloc_6272_, 3, v_isSetupFailure_x3f_6255_);
lean_ctor_set(v_reuseFailAlloc_6272_, 4, v_refs_6243_);
lean_ctor_set(v_reuseFailAlloc_6272_, 5, v_decls_6244_);
v___x_6264_ = v_reuseFailAlloc_6272_;
goto v_reusejp_6263_;
}
v_reusejp_6263_:
{
lean_object* v___x_6265_; lean_object* v___x_6267_; 
v___x_6265_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6240_, v___x_6264_, v_workers_6247_);
if (v_isShared_6262_ == 0)
{
lean_ctor_set(v___x_6261_, 1, v___x_6265_);
v___x_6267_ = v___x_6261_;
goto v_reusejp_6266_;
}
else
{
lean_object* v_reuseFailAlloc_6271_; 
v_reuseFailAlloc_6271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6271_, 0, v_ileans_6246_);
lean_ctor_set(v_reuseFailAlloc_6271_, 1, v___x_6265_);
v___x_6267_ = v_reuseFailAlloc_6271_;
goto v_reusejp_6266_;
}
v_reusejp_6266_:
{
lean_object* v___x_6269_; 
if (v_isShared_6252_ == 0)
{
lean_ctor_set_tag(v___x_6251_, 0);
lean_ctor_set(v___x_6251_, 0, v___x_6267_);
v___x_6269_ = v___x_6251_;
goto v_reusejp_6268_;
}
else
{
lean_object* v_reuseFailAlloc_6270_; 
v_reuseFailAlloc_6270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6270_, 0, v___x_6267_);
v___x_6269_ = v_reuseFailAlloc_6270_;
goto v_reusejp_6268_;
}
v_reusejp_6268_:
{
return v___x_6269_;
}
}
}
}
}
else
{
lean_object* v___x_6277_; 
lean_del_object(v___x_6257_);
lean_dec(v_isSetupFailure_x3f_6255_);
lean_dec_ref(v_directImports_6254_);
lean_dec(v_decls_6244_);
lean_dec(v_refs_6243_);
lean_dec(v_version_6242_);
lean_dec_ref(v_moduleUri_6241_);
lean_dec(v_name_6240_);
if (v_isShared_6252_ == 0)
{
lean_ctor_set_tag(v___x_6251_, 0);
lean_ctor_set(v___x_6251_, 0, v_self_6239_);
v___x_6277_ = v___x_6251_;
goto v_reusejp_6276_;
}
else
{
lean_object* v_reuseFailAlloc_6278_; 
v_reuseFailAlloc_6278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6278_, 0, v_self_6239_);
v___x_6277_ = v_reuseFailAlloc_6278_;
goto v_reusejp_6276_;
}
v_reusejp_6276_:
{
return v___x_6277_;
}
}
}
}
}
else
{
lean_object* v___x_6285_; uint8_t v_isShared_6286_; uint8_t v_isSharedCheck_6295_; 
lean_inc(v_workers_6247_);
lean_inc(v_ileans_6246_);
lean_dec(v___x_6248_);
v_isSharedCheck_6295_ = !lean_is_exclusive(v_self_6239_);
if (v_isSharedCheck_6295_ == 0)
{
lean_object* v_unused_6296_; lean_object* v_unused_6297_; 
v_unused_6296_ = lean_ctor_get(v_self_6239_, 1);
lean_dec(v_unused_6296_);
v_unused_6297_ = lean_ctor_get(v_self_6239_, 0);
lean_dec(v_unused_6297_);
v___x_6285_ = v_self_6239_;
v_isShared_6286_ = v_isSharedCheck_6295_;
goto v_resetjp_6284_;
}
else
{
lean_dec(v_self_6239_);
v___x_6285_ = lean_box(0);
v_isShared_6286_ = v_isSharedCheck_6295_;
goto v_resetjp_6284_;
}
v_resetjp_6284_:
{
lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6292_; 
v___x_6287_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6288_ = lean_box(0);
v___x_6289_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6289_, 0, v_moduleUri_6241_);
lean_ctor_set(v___x_6289_, 1, v_version_6242_);
lean_ctor_set(v___x_6289_, 2, v___x_6287_);
lean_ctor_set(v___x_6289_, 3, v___x_6288_);
lean_ctor_set(v___x_6289_, 4, v_refs_6243_);
lean_ctor_set(v___x_6289_, 5, v_decls_6244_);
v___x_6290_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6240_, v___x_6289_, v_workers_6247_);
if (v_isShared_6286_ == 0)
{
lean_ctor_set(v___x_6285_, 1, v___x_6290_);
v___x_6292_ = v___x_6285_;
goto v_reusejp_6291_;
}
else
{
lean_object* v_reuseFailAlloc_6294_; 
v_reuseFailAlloc_6294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6294_, 0, v_ileans_6246_);
lean_ctor_set(v_reuseFailAlloc_6294_, 1, v___x_6290_);
v___x_6292_ = v_reuseFailAlloc_6294_;
goto v_reusejp_6291_;
}
v_reusejp_6291_:
{
lean_object* v___x_6293_; 
v___x_6293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6293_, 0, v___x_6292_);
return v___x_6293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6298_, lean_object* v_name_6299_, lean_object* v_moduleUri_6300_, lean_object* v_version_6301_, lean_object* v_refs_6302_, lean_object* v_decls_6303_, lean_object* v_a_6304_){
_start:
{
lean_object* v_res_6305_; 
v_res_6305_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6298_, v_name_6299_, v_moduleUri_6300_, v_version_6301_, v_refs_6302_, v_decls_6303_);
return v_res_6305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6306_, lean_object* v_name_6307_){
_start:
{
lean_object* v_ileans_6308_; lean_object* v_workers_6309_; lean_object* v___x_6311_; uint8_t v_isShared_6312_; uint8_t v_isSharedCheck_6317_; 
v_ileans_6308_ = lean_ctor_get(v_self_6306_, 0);
v_workers_6309_ = lean_ctor_get(v_self_6306_, 1);
v_isSharedCheck_6317_ = !lean_is_exclusive(v_self_6306_);
if (v_isSharedCheck_6317_ == 0)
{
v___x_6311_ = v_self_6306_;
v_isShared_6312_ = v_isSharedCheck_6317_;
goto v_resetjp_6310_;
}
else
{
lean_inc(v_workers_6309_);
lean_inc(v_ileans_6308_);
lean_dec(v_self_6306_);
v___x_6311_ = lean_box(0);
v_isShared_6312_ = v_isSharedCheck_6317_;
goto v_resetjp_6310_;
}
v_resetjp_6310_:
{
lean_object* v___x_6313_; lean_object* v___x_6315_; 
v___x_6313_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6307_, v_workers_6309_);
if (v_isShared_6312_ == 0)
{
lean_ctor_set(v___x_6311_, 1, v___x_6313_);
v___x_6315_ = v___x_6311_;
goto v_reusejp_6314_;
}
else
{
lean_object* v_reuseFailAlloc_6316_; 
v_reuseFailAlloc_6316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6316_, 0, v_ileans_6308_);
lean_ctor_set(v_reuseFailAlloc_6316_, 1, v___x_6313_);
v___x_6315_ = v_reuseFailAlloc_6316_;
goto v_reusejp_6314_;
}
v_reusejp_6314_:
{
return v___x_6315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6318_, lean_object* v_name_6319_){
_start:
{
lean_object* v_res_6320_; 
v_res_6320_ = l_Lean_Server_References_removeWorkerRefs(v_self_6318_, v_name_6319_);
lean_dec(v_name_6319_);
return v_res_6320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6321_, lean_object* v_x_6322_){
_start:
{
if (lean_obj_tag(v_x_6322_) == 0)
{
lean_object* v_v_6323_; lean_object* v_k_6324_; lean_object* v_l_6325_; lean_object* v_r_6326_; lean_object* v_moduleUri_6327_; lean_object* v_refs_6328_; lean_object* v_decls_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; 
v_v_6323_ = lean_ctor_get(v_x_6322_, 2);
lean_inc(v_v_6323_);
v_k_6324_ = lean_ctor_get(v_x_6322_, 1);
lean_inc(v_k_6324_);
v_l_6325_ = lean_ctor_get(v_x_6322_, 3);
lean_inc(v_l_6325_);
v_r_6326_ = lean_ctor_get(v_x_6322_, 4);
lean_inc(v_r_6326_);
lean_dec_ref_known(v_x_6322_, 5);
v_moduleUri_6327_ = lean_ctor_get(v_v_6323_, 0);
lean_inc_ref(v_moduleUri_6327_);
v_refs_6328_ = lean_ctor_get(v_v_6323_, 3);
lean_inc(v_refs_6328_);
v_decls_6329_ = lean_ctor_get(v_v_6323_, 4);
lean_inc(v_decls_6329_);
lean_dec(v_v_6323_);
v___x_6330_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6321_, v_l_6325_);
v___x_6331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6331_, 0, v_refs_6328_);
lean_ctor_set(v___x_6331_, 1, v_decls_6329_);
v___x_6332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6332_, 0, v_moduleUri_6327_);
lean_ctor_set(v___x_6332_, 1, v___x_6331_);
v___x_6333_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6324_, v___x_6332_, v___x_6330_);
v_init_6321_ = v___x_6333_;
v_x_6322_ = v_r_6326_;
goto _start;
}
else
{
return v_init_6321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6335_, lean_object* v_x_6336_){
_start:
{
if (lean_obj_tag(v_x_6336_) == 0)
{
lean_object* v_v_6337_; lean_object* v_k_6338_; lean_object* v_l_6339_; lean_object* v_r_6340_; lean_object* v_moduleUri_6341_; lean_object* v_refs_6342_; lean_object* v_decls_6343_; lean_object* v___x_6344_; uint8_t v___x_6345_; 
v_v_6337_ = lean_ctor_get(v_x_6336_, 2);
lean_inc(v_v_6337_);
v_k_6338_ = lean_ctor_get(v_x_6336_, 1);
lean_inc(v_k_6338_);
v_l_6339_ = lean_ctor_get(v_x_6336_, 3);
lean_inc(v_l_6339_);
v_r_6340_ = lean_ctor_get(v_x_6336_, 4);
lean_inc(v_r_6340_);
lean_dec_ref_known(v_x_6336_, 5);
v_moduleUri_6341_ = lean_ctor_get(v_v_6337_, 0);
lean_inc_ref(v_moduleUri_6341_);
v_refs_6342_ = lean_ctor_get(v_v_6337_, 4);
lean_inc(v_refs_6342_);
v_decls_6343_ = lean_ctor_get(v_v_6337_, 5);
lean_inc(v_decls_6343_);
v___x_6344_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6335_, v_l_6339_);
v___x_6345_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6337_);
lean_dec(v_v_6337_);
if (v___x_6345_ == 0)
{
lean_dec(v_decls_6343_);
lean_dec(v_refs_6342_);
lean_dec_ref(v_moduleUri_6341_);
lean_dec(v_k_6338_);
v_init_6335_ = v___x_6344_;
v_x_6336_ = v_r_6340_;
goto _start;
}
else
{
lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___x_6349_; 
v___x_6347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6347_, 0, v_refs_6342_);
lean_ctor_set(v___x_6347_, 1, v_decls_6343_);
v___x_6348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6348_, 0, v_moduleUri_6341_);
lean_ctor_set(v___x_6348_, 1, v___x_6347_);
v___x_6349_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6338_, v___x_6348_, v___x_6344_);
v_init_6335_ = v___x_6349_;
v_x_6336_ = v_r_6340_;
goto _start;
}
}
else
{
return v_init_6335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6351_){
_start:
{
lean_object* v_ileans_6352_; lean_object* v_workers_6353_; lean_object* v___x_6354_; lean_object* v_ileanRefs_6355_; lean_object* v___x_6356_; 
v_ileans_6352_ = lean_ctor_get(v_self_6351_, 0);
lean_inc(v_ileans_6352_);
v_workers_6353_ = lean_ctor_get(v_self_6351_, 1);
lean_inc(v_workers_6353_);
lean_dec_ref(v_self_6351_);
v___x_6354_ = lean_box(1);
v_ileanRefs_6355_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6354_, v_ileans_6352_);
v___x_6356_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6355_, v_workers_6353_);
return v___x_6356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6357_, lean_object* v_t_6358_){
_start:
{
lean_object* v___x_6359_; 
v___x_6359_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6357_, v_t_6358_);
return v___x_6359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6360_, lean_object* v_t_6361_){
_start:
{
lean_object* v___x_6362_; 
v___x_6362_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6360_, v_t_6361_);
return v___x_6362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6363_, lean_object* v_x_6364_){
_start:
{
if (lean_obj_tag(v_x_6364_) == 0)
{
lean_object* v_k_6365_; lean_object* v_v_6366_; lean_object* v_l_6367_; lean_object* v_r_6368_; lean_object* v___x_6369_; lean_object* v_a_6370_; uint8_t v___x_6371_; 
v_k_6365_ = lean_ctor_get(v_x_6364_, 1);
lean_inc(v_k_6365_);
v_v_6366_ = lean_ctor_get(v_x_6364_, 2);
lean_inc(v_v_6366_);
v_l_6367_ = lean_ctor_get(v_x_6364_, 3);
lean_inc(v_l_6367_);
v_r_6368_ = lean_ctor_get(v_x_6364_, 4);
lean_inc(v_r_6368_);
lean_dec_ref_known(v_x_6364_, 5);
v___x_6369_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6363_, v_l_6367_);
v_a_6370_ = lean_ctor_get(v___x_6369_, 0);
lean_inc(v_a_6370_);
lean_dec_ref(v___x_6369_);
v___x_6371_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6366_);
if (v___x_6371_ == 0)
{
lean_dec(v_v_6366_);
lean_dec(v_k_6365_);
v_init_6363_ = v_a_6370_;
v_x_6364_ = v_r_6368_;
goto _start;
}
else
{
lean_object* v_moduleUri_6373_; lean_object* v_directImports_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; 
v_moduleUri_6373_ = lean_ctor_get(v_v_6366_, 0);
lean_inc_ref(v_moduleUri_6373_);
v_directImports_6374_ = lean_ctor_get(v_v_6366_, 2);
lean_inc_ref(v_directImports_6374_);
lean_dec(v_v_6366_);
v___x_6375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6375_, 0, v_moduleUri_6373_);
lean_ctor_set(v___x_6375_, 1, v_directImports_6374_);
v___x_6376_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6365_, v___x_6375_, v_a_6370_);
v_init_6363_ = v___x_6376_;
v_x_6364_ = v_r_6368_;
goto _start;
}
}
else
{
lean_object* v___x_6378_; 
v___x_6378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6378_, 0, v_init_6363_);
return v___x_6378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6379_, lean_object* v_x_6380_){
_start:
{
if (lean_obj_tag(v_x_6380_) == 0)
{
lean_object* v_k_6381_; lean_object* v_v_6382_; lean_object* v_l_6383_; lean_object* v_r_6384_; lean_object* v___x_6385_; lean_object* v_a_6386_; lean_object* v_moduleUri_6387_; lean_object* v_directImports_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; 
v_k_6381_ = lean_ctor_get(v_x_6380_, 1);
lean_inc(v_k_6381_);
v_v_6382_ = lean_ctor_get(v_x_6380_, 2);
lean_inc(v_v_6382_);
v_l_6383_ = lean_ctor_get(v_x_6380_, 3);
lean_inc(v_l_6383_);
v_r_6384_ = lean_ctor_get(v_x_6380_, 4);
lean_inc(v_r_6384_);
lean_dec_ref_known(v_x_6380_, 5);
v___x_6385_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6379_, v_l_6383_);
v_a_6386_ = lean_ctor_get(v___x_6385_, 0);
lean_inc(v_a_6386_);
lean_dec_ref(v___x_6385_);
v_moduleUri_6387_ = lean_ctor_get(v_v_6382_, 0);
lean_inc_ref(v_moduleUri_6387_);
v_directImports_6388_ = lean_ctor_get(v_v_6382_, 2);
lean_inc_ref(v_directImports_6388_);
lean_dec(v_v_6382_);
v___x_6389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6389_, 0, v_moduleUri_6387_);
lean_ctor_set(v___x_6389_, 1, v_directImports_6388_);
v___x_6390_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6381_, v___x_6389_, v_a_6386_);
v_init_6379_ = v___x_6390_;
v_x_6380_ = v_r_6384_;
goto _start;
}
else
{
lean_object* v___x_6392_; 
v___x_6392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6392_, 0, v_init_6379_);
return v___x_6392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6393_){
_start:
{
lean_object* v_ileans_6394_; lean_object* v_workers_6395_; lean_object* v___y_6397_; lean_object* v_allDirectImports_6400_; lean_object* v___x_6401_; lean_object* v_a_6402_; 
v_ileans_6394_ = lean_ctor_get(v_self_6393_, 0);
lean_inc(v_ileans_6394_);
v_workers_6395_ = lean_ctor_get(v_self_6393_, 1);
lean_inc(v_workers_6395_);
lean_dec_ref(v_self_6393_);
v_allDirectImports_6400_ = lean_box(1);
v___x_6401_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6400_, v_ileans_6394_);
v_a_6402_ = lean_ctor_get(v___x_6401_, 0);
lean_inc(v_a_6402_);
lean_dec_ref(v___x_6401_);
v___y_6397_ = v_a_6402_;
goto v___jp_6396_;
v___jp_6396_:
{
lean_object* v___x_6398_; lean_object* v_a_6399_; 
v___x_6398_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6397_, v_workers_6395_);
v_a_6399_ = lean_ctor_get(v___x_6398_, 0);
lean_inc(v_a_6399_);
lean_dec_ref(v___x_6398_);
return v_a_6399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6403_, lean_object* v_mod_6404_){
_start:
{
lean_object* v_ileans_6405_; lean_object* v_workers_6406_; lean_object* v___x_6408_; uint8_t v_isShared_6409_; uint8_t v_isSharedCheck_6443_; 
v_ileans_6405_ = lean_ctor_get(v_self_6403_, 0);
v_workers_6406_ = lean_ctor_get(v_self_6403_, 1);
v_isSharedCheck_6443_ = !lean_is_exclusive(v_self_6403_);
if (v_isSharedCheck_6443_ == 0)
{
v___x_6408_ = v_self_6403_;
v_isShared_6409_ = v_isSharedCheck_6443_;
goto v_resetjp_6407_;
}
else
{
lean_inc(v_workers_6406_);
lean_inc(v_ileans_6405_);
lean_dec(v_self_6403_);
v___x_6408_ = lean_box(0);
v_isShared_6409_ = v_isSharedCheck_6443_;
goto v_resetjp_6407_;
}
v_resetjp_6407_:
{
lean_object* v___x_6428_; 
v___x_6428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6406_, v_mod_6404_);
lean_dec(v_workers_6406_);
if (lean_obj_tag(v___x_6428_) == 1)
{
lean_object* v_val_6429_; lean_object* v___x_6431_; uint8_t v_isShared_6432_; uint8_t v_isSharedCheck_6442_; 
v_val_6429_ = lean_ctor_get(v___x_6428_, 0);
v_isSharedCheck_6442_ = !lean_is_exclusive(v___x_6428_);
if (v_isSharedCheck_6442_ == 0)
{
v___x_6431_ = v___x_6428_;
v_isShared_6432_ = v_isSharedCheck_6442_;
goto v_resetjp_6430_;
}
else
{
lean_inc(v_val_6429_);
lean_dec(v___x_6428_);
v___x_6431_ = lean_box(0);
v_isShared_6432_ = v_isSharedCheck_6442_;
goto v_resetjp_6430_;
}
v_resetjp_6430_:
{
uint8_t v___x_6433_; 
v___x_6433_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6429_);
if (v___x_6433_ == 0)
{
lean_del_object(v___x_6431_);
lean_dec(v_val_6429_);
goto v___jp_6410_;
}
else
{
lean_object* v_moduleUri_6434_; lean_object* v_refs_6435_; lean_object* v_decls_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6440_; 
lean_del_object(v___x_6408_);
lean_dec(v_ileans_6405_);
v_moduleUri_6434_ = lean_ctor_get(v_val_6429_, 0);
lean_inc_ref(v_moduleUri_6434_);
v_refs_6435_ = lean_ctor_get(v_val_6429_, 4);
lean_inc(v_refs_6435_);
v_decls_6436_ = lean_ctor_get(v_val_6429_, 5);
lean_inc(v_decls_6436_);
lean_dec(v_val_6429_);
v___x_6437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6437_, 0, v_refs_6435_);
lean_ctor_set(v___x_6437_, 1, v_decls_6436_);
v___x_6438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6438_, 0, v_moduleUri_6434_);
lean_ctor_set(v___x_6438_, 1, v___x_6437_);
if (v_isShared_6432_ == 0)
{
lean_ctor_set(v___x_6431_, 0, v___x_6438_);
v___x_6440_ = v___x_6431_;
goto v_reusejp_6439_;
}
else
{
lean_object* v_reuseFailAlloc_6441_; 
v_reuseFailAlloc_6441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6441_, 0, v___x_6438_);
v___x_6440_ = v_reuseFailAlloc_6441_;
goto v_reusejp_6439_;
}
v_reusejp_6439_:
{
return v___x_6440_;
}
}
}
}
else
{
lean_dec(v___x_6428_);
goto v___jp_6410_;
}
v___jp_6410_:
{
lean_object* v___x_6411_; 
v___x_6411_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6405_, v_mod_6404_);
lean_dec(v_ileans_6405_);
if (lean_obj_tag(v___x_6411_) == 1)
{
lean_object* v_val_6412_; lean_object* v___x_6414_; uint8_t v_isShared_6415_; uint8_t v_isSharedCheck_6426_; 
v_val_6412_ = lean_ctor_get(v___x_6411_, 0);
v_isSharedCheck_6426_ = !lean_is_exclusive(v___x_6411_);
if (v_isSharedCheck_6426_ == 0)
{
v___x_6414_ = v___x_6411_;
v_isShared_6415_ = v_isSharedCheck_6426_;
goto v_resetjp_6413_;
}
else
{
lean_inc(v_val_6412_);
lean_dec(v___x_6411_);
v___x_6414_ = lean_box(0);
v_isShared_6415_ = v_isSharedCheck_6426_;
goto v_resetjp_6413_;
}
v_resetjp_6413_:
{
lean_object* v_moduleUri_6416_; lean_object* v_refs_6417_; lean_object* v_decls_6418_; lean_object* v___x_6420_; 
v_moduleUri_6416_ = lean_ctor_get(v_val_6412_, 0);
lean_inc_ref(v_moduleUri_6416_);
v_refs_6417_ = lean_ctor_get(v_val_6412_, 3);
lean_inc(v_refs_6417_);
v_decls_6418_ = lean_ctor_get(v_val_6412_, 4);
lean_inc(v_decls_6418_);
lean_dec(v_val_6412_);
if (v_isShared_6409_ == 0)
{
lean_ctor_set(v___x_6408_, 1, v_decls_6418_);
lean_ctor_set(v___x_6408_, 0, v_refs_6417_);
v___x_6420_ = v___x_6408_;
goto v_reusejp_6419_;
}
else
{
lean_object* v_reuseFailAlloc_6425_; 
v_reuseFailAlloc_6425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6425_, 0, v_refs_6417_);
lean_ctor_set(v_reuseFailAlloc_6425_, 1, v_decls_6418_);
v___x_6420_ = v_reuseFailAlloc_6425_;
goto v_reusejp_6419_;
}
v_reusejp_6419_:
{
lean_object* v___x_6421_; lean_object* v___x_6423_; 
v___x_6421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6421_, 0, v_moduleUri_6416_);
lean_ctor_set(v___x_6421_, 1, v___x_6420_);
if (v_isShared_6415_ == 0)
{
lean_ctor_set(v___x_6414_, 0, v___x_6421_);
v___x_6423_ = v___x_6414_;
goto v_reusejp_6422_;
}
else
{
lean_object* v_reuseFailAlloc_6424_; 
v_reuseFailAlloc_6424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6424_, 0, v___x_6421_);
v___x_6423_ = v_reuseFailAlloc_6424_;
goto v_reusejp_6422_;
}
v_reusejp_6422_:
{
return v___x_6423_;
}
}
}
}
else
{
lean_object* v___x_6427_; 
lean_dec(v___x_6411_);
lean_del_object(v___x_6408_);
v___x_6427_ = lean_box(0);
return v___x_6427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6444_, lean_object* v_mod_6445_){
_start:
{
lean_object* v_res_6446_; 
v_res_6446_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6444_, v_mod_6445_);
lean_dec(v_mod_6445_);
return v_res_6446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6447_, lean_object* v_mod_6448_){
_start:
{
lean_object* v_ileans_6449_; lean_object* v_workers_6450_; lean_object* v___x_6463_; 
v_ileans_6449_ = lean_ctor_get(v_self_6447_, 0);
v_workers_6450_ = lean_ctor_get(v_self_6447_, 1);
v___x_6463_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6450_, v_mod_6448_);
if (lean_obj_tag(v___x_6463_) == 1)
{
lean_object* v_val_6464_; lean_object* v___x_6466_; uint8_t v_isShared_6467_; uint8_t v_isSharedCheck_6473_; 
v_val_6464_ = lean_ctor_get(v___x_6463_, 0);
v_isSharedCheck_6473_ = !lean_is_exclusive(v___x_6463_);
if (v_isSharedCheck_6473_ == 0)
{
v___x_6466_ = v___x_6463_;
v_isShared_6467_ = v_isSharedCheck_6473_;
goto v_resetjp_6465_;
}
else
{
lean_inc(v_val_6464_);
lean_dec(v___x_6463_);
v___x_6466_ = lean_box(0);
v_isShared_6467_ = v_isSharedCheck_6473_;
goto v_resetjp_6465_;
}
v_resetjp_6465_:
{
uint8_t v___x_6468_; 
v___x_6468_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6464_);
if (v___x_6468_ == 0)
{
lean_del_object(v___x_6466_);
lean_dec(v_val_6464_);
goto v___jp_6451_;
}
else
{
lean_object* v_directImports_6469_; lean_object* v___x_6471_; 
v_directImports_6469_ = lean_ctor_get(v_val_6464_, 2);
lean_inc_ref(v_directImports_6469_);
lean_dec(v_val_6464_);
if (v_isShared_6467_ == 0)
{
lean_ctor_set(v___x_6466_, 0, v_directImports_6469_);
v___x_6471_ = v___x_6466_;
goto v_reusejp_6470_;
}
else
{
lean_object* v_reuseFailAlloc_6472_; 
v_reuseFailAlloc_6472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6472_, 0, v_directImports_6469_);
v___x_6471_ = v_reuseFailAlloc_6472_;
goto v_reusejp_6470_;
}
v_reusejp_6470_:
{
return v___x_6471_;
}
}
}
}
else
{
lean_dec(v___x_6463_);
goto v___jp_6451_;
}
v___jp_6451_:
{
lean_object* v___x_6452_; 
v___x_6452_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6449_, v_mod_6448_);
if (lean_obj_tag(v___x_6452_) == 1)
{
lean_object* v_val_6453_; lean_object* v___x_6455_; uint8_t v_isShared_6456_; uint8_t v_isSharedCheck_6461_; 
v_val_6453_ = lean_ctor_get(v___x_6452_, 0);
v_isSharedCheck_6461_ = !lean_is_exclusive(v___x_6452_);
if (v_isSharedCheck_6461_ == 0)
{
v___x_6455_ = v___x_6452_;
v_isShared_6456_ = v_isSharedCheck_6461_;
goto v_resetjp_6454_;
}
else
{
lean_inc(v_val_6453_);
lean_dec(v___x_6452_);
v___x_6455_ = lean_box(0);
v_isShared_6456_ = v_isSharedCheck_6461_;
goto v_resetjp_6454_;
}
v_resetjp_6454_:
{
lean_object* v_directImports_6457_; lean_object* v___x_6459_; 
v_directImports_6457_ = lean_ctor_get(v_val_6453_, 2);
lean_inc_ref(v_directImports_6457_);
lean_dec(v_val_6453_);
if (v_isShared_6456_ == 0)
{
lean_ctor_set(v___x_6455_, 0, v_directImports_6457_);
v___x_6459_ = v___x_6455_;
goto v_reusejp_6458_;
}
else
{
lean_object* v_reuseFailAlloc_6460_; 
v_reuseFailAlloc_6460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6460_, 0, v_directImports_6457_);
v___x_6459_ = v_reuseFailAlloc_6460_;
goto v_reusejp_6458_;
}
v_reusejp_6458_:
{
return v___x_6459_;
}
}
}
else
{
lean_object* v___x_6462_; 
lean_dec(v___x_6452_);
v___x_6462_ = lean_box(0);
return v___x_6462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6474_, lean_object* v_mod_6475_){
_start:
{
lean_object* v_res_6476_; 
v_res_6476_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6474_, v_mod_6475_);
lean_dec(v_mod_6475_);
lean_dec_ref(v_self_6474_);
return v_res_6476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6477_, lean_object* v_mod_6478_){
_start:
{
lean_object* v_ileans_6479_; lean_object* v_workers_6480_; lean_object* v___x_6493_; 
v_ileans_6479_ = lean_ctor_get(v_self_6477_, 0);
v_workers_6480_ = lean_ctor_get(v_self_6477_, 1);
v___x_6493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6480_, v_mod_6478_);
if (lean_obj_tag(v___x_6493_) == 1)
{
lean_object* v_val_6494_; lean_object* v___x_6496_; uint8_t v_isShared_6497_; uint8_t v_isSharedCheck_6503_; 
v_val_6494_ = lean_ctor_get(v___x_6493_, 0);
v_isSharedCheck_6503_ = !lean_is_exclusive(v___x_6493_);
if (v_isSharedCheck_6503_ == 0)
{
v___x_6496_ = v___x_6493_;
v_isShared_6497_ = v_isSharedCheck_6503_;
goto v_resetjp_6495_;
}
else
{
lean_inc(v_val_6494_);
lean_dec(v___x_6493_);
v___x_6496_ = lean_box(0);
v_isShared_6497_ = v_isSharedCheck_6503_;
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
goto v___jp_6481_;
}
else
{
lean_object* v_decls_6499_; lean_object* v___x_6501_; 
v_decls_6499_ = lean_ctor_get(v_val_6494_, 5);
lean_inc(v_decls_6499_);
lean_dec(v_val_6494_);
if (v_isShared_6497_ == 0)
{
lean_ctor_set(v___x_6496_, 0, v_decls_6499_);
v___x_6501_ = v___x_6496_;
goto v_reusejp_6500_;
}
else
{
lean_object* v_reuseFailAlloc_6502_; 
v_reuseFailAlloc_6502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6502_, 0, v_decls_6499_);
v___x_6501_ = v_reuseFailAlloc_6502_;
goto v_reusejp_6500_;
}
v_reusejp_6500_:
{
return v___x_6501_;
}
}
}
}
else
{
lean_dec(v___x_6493_);
goto v___jp_6481_;
}
v___jp_6481_:
{
lean_object* v___x_6482_; 
v___x_6482_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6479_, v_mod_6478_);
if (lean_obj_tag(v___x_6482_) == 1)
{
lean_object* v_val_6483_; lean_object* v___x_6485_; uint8_t v_isShared_6486_; uint8_t v_isSharedCheck_6491_; 
v_val_6483_ = lean_ctor_get(v___x_6482_, 0);
v_isSharedCheck_6491_ = !lean_is_exclusive(v___x_6482_);
if (v_isSharedCheck_6491_ == 0)
{
v___x_6485_ = v___x_6482_;
v_isShared_6486_ = v_isSharedCheck_6491_;
goto v_resetjp_6484_;
}
else
{
lean_inc(v_val_6483_);
lean_dec(v___x_6482_);
v___x_6485_ = lean_box(0);
v_isShared_6486_ = v_isSharedCheck_6491_;
goto v_resetjp_6484_;
}
v_resetjp_6484_:
{
lean_object* v_decls_6487_; lean_object* v___x_6489_; 
v_decls_6487_ = lean_ctor_get(v_val_6483_, 4);
lean_inc(v_decls_6487_);
lean_dec(v_val_6483_);
if (v_isShared_6486_ == 0)
{
lean_ctor_set(v___x_6485_, 0, v_decls_6487_);
v___x_6489_ = v___x_6485_;
goto v_reusejp_6488_;
}
else
{
lean_object* v_reuseFailAlloc_6490_; 
v_reuseFailAlloc_6490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6490_, 0, v_decls_6487_);
v___x_6489_ = v_reuseFailAlloc_6490_;
goto v_reusejp_6488_;
}
v_reusejp_6488_:
{
return v___x_6489_;
}
}
}
else
{
lean_object* v___x_6492_; 
lean_dec(v___x_6482_);
v___x_6492_ = lean_box(0);
return v___x_6492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6504_, lean_object* v_mod_6505_){
_start:
{
lean_object* v_res_6506_; 
v_res_6506_ = l_Lean_Server_References_getDecls_x3f(v_self_6504_, v_mod_6505_);
lean_dec(v_mod_6505_);
lean_dec_ref(v_self_6504_);
return v_res_6506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6507_, lean_object* v_x_6508_){
_start:
{
if (lean_obj_tag(v_x_6508_) == 0)
{
lean_object* v_k_6509_; lean_object* v_v_6510_; lean_object* v_l_6511_; lean_object* v_r_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; 
v_k_6509_ = lean_ctor_get(v_x_6508_, 1);
v_v_6510_ = lean_ctor_get(v_x_6508_, 2);
v_l_6511_ = lean_ctor_get(v_x_6508_, 3);
v_r_6512_ = lean_ctor_get(v_x_6508_, 4);
v___x_6513_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6507_, v_l_6511_);
lean_inc(v_v_6510_);
lean_inc(v_k_6509_);
v___x_6514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6514_, 0, v_k_6509_);
lean_ctor_set(v___x_6514_, 1, v_v_6510_);
v___x_6515_ = lean_array_push(v___x_6513_, v___x_6514_);
v_init_6507_ = v___x_6515_;
v_x_6508_ = v_r_6512_;
goto _start;
}
else
{
return v_init_6507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6517_, lean_object* v_x_6518_){
_start:
{
lean_object* v_res_6519_; 
v_res_6519_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6517_, v_x_6518_);
lean_dec(v_x_6518_);
return v_res_6519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6520_, lean_object* v_k_6521_){
_start:
{
if (lean_obj_tag(v_t_6520_) == 0)
{
lean_object* v_k_6522_; lean_object* v_v_6523_; lean_object* v_l_6524_; lean_object* v_r_6525_; uint8_t v___x_6526_; 
v_k_6522_ = lean_ctor_get(v_t_6520_, 1);
v_v_6523_ = lean_ctor_get(v_t_6520_, 2);
v_l_6524_ = lean_ctor_get(v_t_6520_, 3);
v_r_6525_ = lean_ctor_get(v_t_6520_, 4);
v___x_6526_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6521_, v_k_6522_);
switch(v___x_6526_)
{
case 0:
{
v_t_6520_ = v_l_6524_;
goto _start;
}
case 1:
{
lean_object* v___x_6528_; 
lean_inc(v_v_6523_);
v___x_6528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6528_, 0, v_v_6523_);
return v___x_6528_;
}
default: 
{
v_t_6520_ = v_r_6525_;
goto _start;
}
}
}
else
{
lean_object* v___x_6530_; 
v___x_6530_ = lean_box(0);
return v___x_6530_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6531_, lean_object* v_k_6532_){
_start:
{
lean_object* v_res_6533_; 
v_res_6533_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6531_, v_k_6532_);
lean_dec_ref(v_k_6532_);
lean_dec(v_t_6531_);
return v_res_6533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6534_, lean_object* v_as_6535_, size_t v_sz_6536_, size_t v_i_6537_, lean_object* v_b_6538_){
_start:
{
lean_object* v_a_6540_; uint8_t v___x_6544_; 
v___x_6544_ = lean_usize_dec_lt(v_i_6537_, v_sz_6536_);
if (v___x_6544_ == 0)
{
return v_b_6538_;
}
else
{
lean_object* v_a_6545_; lean_object* v_snd_6546_; lean_object* v_snd_6547_; lean_object* v_fst_6548_; lean_object* v___x_6550_; uint8_t v_isShared_6551_; uint8_t v_isSharedCheck_6576_; 
v_a_6545_ = lean_array_uget(v_as_6535_, v_i_6537_);
v_snd_6546_ = lean_ctor_get(v_a_6545_, 1);
lean_inc(v_snd_6546_);
v_snd_6547_ = lean_ctor_get(v_snd_6546_, 1);
lean_inc(v_snd_6547_);
v_fst_6548_ = lean_ctor_get(v_a_6545_, 0);
v_isSharedCheck_6576_ = !lean_is_exclusive(v_a_6545_);
if (v_isSharedCheck_6576_ == 0)
{
lean_object* v_unused_6577_; 
v_unused_6577_ = lean_ctor_get(v_a_6545_, 1);
lean_dec(v_unused_6577_);
v___x_6550_ = v_a_6545_;
v_isShared_6551_ = v_isSharedCheck_6576_;
goto v_resetjp_6549_;
}
else
{
lean_inc(v_fst_6548_);
lean_dec(v_a_6545_);
v___x_6550_ = lean_box(0);
v_isShared_6551_ = v_isSharedCheck_6576_;
goto v_resetjp_6549_;
}
v_resetjp_6549_:
{
lean_object* v_fst_6552_; lean_object* v___x_6554_; uint8_t v_isShared_6555_; uint8_t v_isSharedCheck_6574_; 
v_fst_6552_ = lean_ctor_get(v_snd_6546_, 0);
v_isSharedCheck_6574_ = !lean_is_exclusive(v_snd_6546_);
if (v_isSharedCheck_6574_ == 0)
{
lean_object* v_unused_6575_; 
v_unused_6575_ = lean_ctor_get(v_snd_6546_, 1);
lean_dec(v_unused_6575_);
v___x_6554_ = v_snd_6546_;
v_isShared_6555_ = v_isSharedCheck_6574_;
goto v_resetjp_6553_;
}
else
{
lean_inc(v_fst_6552_);
lean_dec(v_snd_6546_);
v___x_6554_ = lean_box(0);
v_isShared_6555_ = v_isSharedCheck_6574_;
goto v_resetjp_6553_;
}
v_resetjp_6553_:
{
lean_object* v_fst_6556_; lean_object* v_snd_6557_; lean_object* v___x_6559_; uint8_t v_isShared_6560_; uint8_t v_isSharedCheck_6573_; 
v_fst_6556_ = lean_ctor_get(v_snd_6547_, 0);
v_snd_6557_ = lean_ctor_get(v_snd_6547_, 1);
v_isSharedCheck_6573_ = !lean_is_exclusive(v_snd_6547_);
if (v_isSharedCheck_6573_ == 0)
{
v___x_6559_ = v_snd_6547_;
v_isShared_6560_ = v_isSharedCheck_6573_;
goto v_resetjp_6558_;
}
else
{
lean_inc(v_snd_6557_);
lean_inc(v_fst_6556_);
lean_dec(v_snd_6547_);
v___x_6559_ = lean_box(0);
v_isShared_6560_ = v_isSharedCheck_6573_;
goto v_resetjp_6558_;
}
v_resetjp_6558_:
{
lean_object* v___x_6561_; 
v___x_6561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6556_, v_ident_6534_);
lean_dec(v_fst_6556_);
if (lean_obj_tag(v___x_6561_) == 1)
{
lean_object* v_val_6562_; lean_object* v___x_6564_; 
v_val_6562_ = lean_ctor_get(v___x_6561_, 0);
lean_inc(v_val_6562_);
lean_dec_ref_known(v___x_6561_, 1);
if (v_isShared_6560_ == 0)
{
lean_ctor_set(v___x_6559_, 0, v_val_6562_);
v___x_6564_ = v___x_6559_;
goto v_reusejp_6563_;
}
else
{
lean_object* v_reuseFailAlloc_6572_; 
v_reuseFailAlloc_6572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6572_, 0, v_val_6562_);
lean_ctor_set(v_reuseFailAlloc_6572_, 1, v_snd_6557_);
v___x_6564_ = v_reuseFailAlloc_6572_;
goto v_reusejp_6563_;
}
v_reusejp_6563_:
{
lean_object* v___x_6566_; 
if (v_isShared_6555_ == 0)
{
lean_ctor_set(v___x_6554_, 1, v___x_6564_);
lean_ctor_set(v___x_6554_, 0, v_fst_6548_);
v___x_6566_ = v___x_6554_;
goto v_reusejp_6565_;
}
else
{
lean_object* v_reuseFailAlloc_6571_; 
v_reuseFailAlloc_6571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6571_, 0, v_fst_6548_);
lean_ctor_set(v_reuseFailAlloc_6571_, 1, v___x_6564_);
v___x_6566_ = v_reuseFailAlloc_6571_;
goto v_reusejp_6565_;
}
v_reusejp_6565_:
{
lean_object* v___x_6568_; 
if (v_isShared_6551_ == 0)
{
lean_ctor_set(v___x_6550_, 1, v___x_6566_);
lean_ctor_set(v___x_6550_, 0, v_fst_6552_);
v___x_6568_ = v___x_6550_;
goto v_reusejp_6567_;
}
else
{
lean_object* v_reuseFailAlloc_6570_; 
v_reuseFailAlloc_6570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6570_, 0, v_fst_6552_);
lean_ctor_set(v_reuseFailAlloc_6570_, 1, v___x_6566_);
v___x_6568_ = v_reuseFailAlloc_6570_;
goto v_reusejp_6567_;
}
v_reusejp_6567_:
{
lean_object* v___x_6569_; 
v___x_6569_ = lean_array_push(v_b_6538_, v___x_6568_);
v_a_6540_ = v___x_6569_;
goto v___jp_6539_;
}
}
}
}
else
{
lean_dec(v___x_6561_);
lean_del_object(v___x_6559_);
lean_dec(v_snd_6557_);
lean_del_object(v___x_6554_);
lean_dec(v_fst_6552_);
lean_del_object(v___x_6550_);
lean_dec(v_fst_6548_);
v_a_6540_ = v_b_6538_;
goto v___jp_6539_;
}
}
}
}
}
v___jp_6539_:
{
size_t v___x_6541_; size_t v___x_6542_; 
v___x_6541_ = ((size_t)1ULL);
v___x_6542_ = lean_usize_add(v_i_6537_, v___x_6541_);
v_i_6537_ = v___x_6542_;
v_b_6538_ = v_a_6540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6578_, lean_object* v_as_6579_, lean_object* v_sz_6580_, lean_object* v_i_6581_, lean_object* v_b_6582_){
_start:
{
size_t v_sz_boxed_6583_; size_t v_i_boxed_6584_; lean_object* v_res_6585_; 
v_sz_boxed_6583_ = lean_unbox_usize(v_sz_6580_);
lean_dec(v_sz_6580_);
v_i_boxed_6584_ = lean_unbox_usize(v_i_6581_);
lean_dec(v_i_6581_);
v_res_6585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6578_, v_as_6579_, v_sz_boxed_6583_, v_i_boxed_6584_, v_b_6582_);
lean_dec_ref(v_as_6579_);
lean_dec_ref(v_ident_6578_);
return v_res_6585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6592_, lean_object* v_ident_6593_){
_start:
{
lean_object* v___y_6595_; 
if (lean_obj_tag(v_ident_6593_) == 0)
{
lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; 
v___x_6600_ = l_Lean_Server_References_allRefs(v_self_6592_);
v___x_6601_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6602_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6601_, v___x_6600_);
lean_dec(v___x_6600_);
v___y_6595_ = v___x_6602_;
goto v___jp_6594_;
}
else
{
lean_object* v_moduleName_6603_; lean_object* v_identModuleName_6604_; lean_object* v___x_6605_; 
v_moduleName_6603_ = lean_ctor_get(v_ident_6593_, 0);
lean_inc_ref(v_moduleName_6603_);
v_identModuleName_6604_ = l_String_toName(v_moduleName_6603_);
v___x_6605_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6592_, v_identModuleName_6604_);
if (lean_obj_tag(v___x_6605_) == 0)
{
lean_object* v___x_6606_; 
lean_dec(v_identModuleName_6604_);
v___x_6606_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6595_ = v___x_6606_;
goto v___jp_6594_;
}
else
{
lean_object* v_val_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; 
v_val_6607_ = lean_ctor_get(v___x_6605_, 0);
lean_inc(v_val_6607_);
lean_dec_ref_known(v___x_6605_, 1);
v___x_6608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6608_, 0, v_identModuleName_6604_);
lean_ctor_set(v___x_6608_, 1, v_val_6607_);
v___x_6609_ = lean_unsigned_to_nat(1u);
v___x_6610_ = lean_mk_empty_array_with_capacity(v___x_6609_);
v___x_6611_ = lean_array_push(v___x_6610_, v___x_6608_);
v___y_6595_ = v___x_6611_;
goto v___jp_6594_;
}
}
v___jp_6594_:
{
lean_object* v_result_6596_; size_t v_sz_6597_; size_t v___x_6598_; lean_object* v___x_6599_; 
v_result_6596_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6597_ = lean_array_size(v___y_6595_);
v___x_6598_ = ((size_t)0ULL);
v___x_6599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6593_, v___y_6595_, v_sz_6597_, v___x_6598_, v_result_6596_);
lean_dec_ref(v___y_6595_);
lean_dec_ref(v_ident_6593_);
return v___x_6599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6612_, lean_object* v_t_6613_, lean_object* v_k_6614_){
_start:
{
lean_object* v___x_6615_; 
v___x_6615_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6613_, v_k_6614_);
return v___x_6615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6616_, lean_object* v_t_6617_, lean_object* v_k_6618_){
_start:
{
lean_object* v_res_6619_; 
v_res_6619_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6616_, v_t_6617_, v_k_6618_);
lean_dec_ref(v_k_6618_);
lean_dec(v_t_6617_);
return v_res_6619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6620_, lean_object* v_t_6621_){
_start:
{
lean_object* v___x_6622_; 
v___x_6622_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6620_, v_t_6621_);
return v___x_6622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6623_, lean_object* v_t_6624_){
_start:
{
lean_object* v_res_6625_; 
v_res_6625_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6623_, v_t_6624_);
lean_dec(v_t_6624_);
return v_res_6625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6626_, lean_object* v_module_6627_, lean_object* v_pos_6628_, uint8_t v_includeStop_6629_){
_start:
{
lean_object* v___x_6630_; 
v___x_6630_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6626_, v_module_6627_);
if (lean_obj_tag(v___x_6630_) == 1)
{
lean_object* v_val_6631_; lean_object* v_snd_6632_; lean_object* v_fst_6633_; lean_object* v___x_6634_; 
v_val_6631_ = lean_ctor_get(v___x_6630_, 0);
lean_inc(v_val_6631_);
lean_dec_ref_known(v___x_6630_, 1);
v_snd_6632_ = lean_ctor_get(v_val_6631_, 1);
lean_inc(v_snd_6632_);
lean_dec(v_val_6631_);
v_fst_6633_ = lean_ctor_get(v_snd_6632_, 0);
lean_inc(v_fst_6633_);
lean_dec(v_snd_6632_);
v___x_6634_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6633_, v_pos_6628_, v_includeStop_6629_);
return v___x_6634_;
}
else
{
lean_object* v___x_6635_; 
lean_dec(v___x_6630_);
v___x_6635_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6636_, lean_object* v_module_6637_, lean_object* v_pos_6638_, lean_object* v_includeStop_6639_){
_start:
{
uint8_t v_includeStop_boxed_6640_; lean_object* v_res_6641_; 
v_includeStop_boxed_6640_ = lean_unbox(v_includeStop_6639_);
v_res_6641_ = l_Lean_Server_References_findAt(v_self_6636_, v_module_6637_, v_pos_6638_, v_includeStop_boxed_6640_);
lean_dec_ref(v_pos_6638_);
lean_dec(v_module_6637_);
return v_res_6641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6642_, lean_object* v_module_6643_, lean_object* v_pos_6644_, uint8_t v_includeStop_6645_){
_start:
{
lean_object* v___x_6646_; 
v___x_6646_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6642_, v_module_6643_);
if (lean_obj_tag(v___x_6646_) == 0)
{
lean_object* v___x_6647_; 
v___x_6647_ = lean_box(0);
return v___x_6647_;
}
else
{
lean_object* v_val_6648_; lean_object* v_snd_6649_; lean_object* v_fst_6650_; lean_object* v___x_6651_; 
v_val_6648_ = lean_ctor_get(v___x_6646_, 0);
lean_inc(v_val_6648_);
lean_dec_ref_known(v___x_6646_, 1);
v_snd_6649_ = lean_ctor_get(v_val_6648_, 1);
lean_inc(v_snd_6649_);
lean_dec(v_val_6648_);
v_fst_6650_ = lean_ctor_get(v_snd_6649_, 0);
lean_inc(v_fst_6650_);
lean_dec(v_snd_6649_);
v___x_6651_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6650_, v_pos_6644_, v_includeStop_6645_);
lean_dec(v_fst_6650_);
return v___x_6651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6652_, lean_object* v_module_6653_, lean_object* v_pos_6654_, lean_object* v_includeStop_6655_){
_start:
{
uint8_t v_includeStop_boxed_6656_; lean_object* v_res_6657_; 
v_includeStop_boxed_6656_ = lean_unbox(v_includeStop_6655_);
v_res_6657_ = l_Lean_Server_References_findRange_x3f(v_self_6652_, v_module_6653_, v_pos_6654_, v_includeStop_boxed_6656_);
lean_dec_ref(v_pos_6654_);
lean_dec(v_module_6653_);
return v_res_6657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6658_, lean_object* v_k_6659_){
_start:
{
if (lean_obj_tag(v_t_6658_) == 0)
{
lean_object* v_k_6660_; lean_object* v_v_6661_; lean_object* v_l_6662_; lean_object* v_r_6663_; uint8_t v___x_6664_; 
v_k_6660_ = lean_ctor_get(v_t_6658_, 1);
v_v_6661_ = lean_ctor_get(v_t_6658_, 2);
v_l_6662_ = lean_ctor_get(v_t_6658_, 3);
v_r_6663_ = lean_ctor_get(v_t_6658_, 4);
v___x_6664_ = lean_string_compare(v_k_6659_, v_k_6660_);
switch(v___x_6664_)
{
case 0:
{
v_t_6658_ = v_l_6662_;
goto _start;
}
case 1:
{
lean_object* v___x_6666_; 
lean_inc(v_v_6661_);
v___x_6666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6666_, 0, v_v_6661_);
return v___x_6666_;
}
default: 
{
v_t_6658_ = v_r_6663_;
goto _start;
}
}
}
else
{
lean_object* v___x_6668_; 
v___x_6668_ = lean_box(0);
return v___x_6668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6669_, lean_object* v_k_6670_){
_start:
{
lean_object* v_res_6671_; 
v_res_6671_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6669_, v_k_6670_);
lean_dec_ref(v_k_6670_);
lean_dec(v_t_6669_);
return v_res_6671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6672_, lean_object* v_name_6673_){
_start:
{
lean_object* v___x_6674_; 
v___x_6674_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6672_, v_name_6673_);
if (lean_obj_tag(v___x_6674_) == 0)
{
lean_object* v___x_6675_; 
lean_dec_ref(v_name_6673_);
v___x_6675_ = lean_box(0);
return v___x_6675_;
}
else
{
lean_object* v_val_6676_; lean_object* v___x_6678_; uint8_t v_isShared_6679_; uint8_t v_isSharedCheck_6686_; 
v_val_6676_ = lean_ctor_get(v___x_6674_, 0);
v_isSharedCheck_6686_ = !lean_is_exclusive(v___x_6674_);
if (v_isSharedCheck_6686_ == 0)
{
v___x_6678_ = v___x_6674_;
v_isShared_6679_ = v_isSharedCheck_6686_;
goto v_resetjp_6677_;
}
else
{
lean_inc(v_val_6676_);
lean_dec(v___x_6674_);
v___x_6678_ = lean_box(0);
v_isShared_6679_ = v_isSharedCheck_6686_;
goto v_resetjp_6677_;
}
v_resetjp_6677_:
{
lean_object* v___x_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6684_; 
v___x_6680_ = l_Lean_Lsp_DeclInfo_range(v_val_6676_);
v___x_6681_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6676_);
lean_dec(v_val_6676_);
v___x_6682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6682_, 0, v_name_6673_);
lean_ctor_set(v___x_6682_, 1, v___x_6680_);
lean_ctor_set(v___x_6682_, 2, v___x_6681_);
if (v_isShared_6679_ == 0)
{
lean_ctor_set(v___x_6678_, 0, v___x_6682_);
v___x_6684_ = v___x_6678_;
goto v_reusejp_6683_;
}
else
{
lean_object* v_reuseFailAlloc_6685_; 
v_reuseFailAlloc_6685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6685_, 0, v___x_6682_);
v___x_6684_ = v_reuseFailAlloc_6685_;
goto v_reusejp_6683_;
}
v_reusejp_6683_:
{
return v___x_6684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6687_, lean_object* v_name_6688_){
_start:
{
lean_object* v_res_6689_; 
v_res_6689_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6687_, v_name_6688_);
lean_dec(v_ds_6687_);
return v_res_6689_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6690_, lean_object* v_t_6691_, lean_object* v_k_6692_){
_start:
{
lean_object* v___x_6693_; 
v___x_6693_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6691_, v_k_6692_);
return v___x_6693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6694_, lean_object* v_t_6695_, lean_object* v_k_6696_){
_start:
{
lean_object* v_res_6697_; 
v_res_6697_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6694_, v_t_6695_, v_k_6696_);
lean_dec_ref(v_k_6696_);
lean_dec(v_t_6695_);
return v_res_6697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6698_, lean_object* v_fst_6699_, lean_object* v_snd_6700_, lean_object* v_as_6701_, size_t v_sz_6702_, size_t v_i_6703_, lean_object* v_b_6704_){
_start:
{
uint8_t v___x_6705_; 
v___x_6705_ = lean_usize_dec_lt(v_i_6703_, v_sz_6702_);
if (v___x_6705_ == 0)
{
lean_dec(v_fst_6699_);
lean_dec_ref(v_fst_6698_);
return v_b_6704_;
}
else
{
lean_object* v_a_6706_; lean_object* v___y_6708_; lean_object* v___x_6716_; 
v_a_6706_ = lean_array_uget_borrowed(v_as_6701_, v_i_6703_);
v___x_6716_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6706_);
if (lean_obj_tag(v___x_6716_) == 0)
{
lean_object* v___x_6717_; 
v___x_6717_ = lean_box(0);
v___y_6708_ = v___x_6717_;
goto v___jp_6707_;
}
else
{
lean_object* v_val_6718_; lean_object* v___x_6719_; 
v_val_6718_ = lean_ctor_get(v___x_6716_, 0);
lean_inc(v_val_6718_);
lean_dec_ref_known(v___x_6716_, 1);
v___x_6719_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6700_, v_val_6718_);
v___y_6708_ = v___x_6719_;
goto v___jp_6707_;
}
v___jp_6707_:
{
lean_object* v___x_6709_; lean_object* v___x_6710_; lean_object* v___x_6711_; lean_object* v___x_6712_; size_t v___x_6713_; size_t v___x_6714_; 
v___x_6709_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6706_);
lean_inc_ref(v_fst_6698_);
v___x_6710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6710_, 0, v_fst_6698_);
lean_ctor_set(v___x_6710_, 1, v___x_6709_);
lean_inc(v_fst_6699_);
v___x_6711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6711_, 0, v___x_6710_);
lean_ctor_set(v___x_6711_, 1, v_fst_6699_);
lean_ctor_set(v___x_6711_, 2, v___y_6708_);
v___x_6712_ = lean_array_push(v_b_6704_, v___x_6711_);
v___x_6713_ = ((size_t)1ULL);
v___x_6714_ = lean_usize_add(v_i_6703_, v___x_6713_);
v_i_6703_ = v___x_6714_;
v_b_6704_ = v___x_6712_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6720_, lean_object* v_fst_6721_, lean_object* v_snd_6722_, lean_object* v_as_6723_, lean_object* v_sz_6724_, lean_object* v_i_6725_, lean_object* v_b_6726_){
_start:
{
size_t v_sz_boxed_6727_; size_t v_i_boxed_6728_; lean_object* v_res_6729_; 
v_sz_boxed_6727_ = lean_unbox_usize(v_sz_6724_);
lean_dec(v_sz_6724_);
v_i_boxed_6728_ = lean_unbox_usize(v_i_6725_);
lean_dec(v_i_6725_);
v_res_6729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6720_, v_fst_6721_, v_snd_6722_, v_as_6723_, v_sz_boxed_6727_, v_i_boxed_6728_, v_b_6726_);
lean_dec_ref(v_as_6723_);
lean_dec(v_snd_6722_);
return v_res_6729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6730_, lean_object* v_as_6731_, size_t v_sz_6732_, size_t v_i_6733_, lean_object* v_b_6734_){
_start:
{
uint8_t v___x_6735_; 
v___x_6735_ = lean_usize_dec_lt(v_i_6733_, v_sz_6732_);
if (v___x_6735_ == 0)
{
return v_b_6734_;
}
else
{
lean_object* v_a_6736_; lean_object* v_snd_6737_; lean_object* v_snd_6738_; lean_object* v_fst_6739_; lean_object* v_fst_6740_; lean_object* v_fst_6741_; lean_object* v_snd_6742_; lean_object* v___x_6744_; uint8_t v_isShared_6745_; uint8_t v_isSharedCheck_6769_; 
v_a_6736_ = lean_array_uget_borrowed(v_as_6731_, v_i_6733_);
v_snd_6737_ = lean_ctor_get(v_a_6736_, 1);
v_snd_6738_ = lean_ctor_get(v_snd_6737_, 1);
lean_inc(v_snd_6738_);
v_fst_6739_ = lean_ctor_get(v_a_6736_, 0);
v_fst_6740_ = lean_ctor_get(v_snd_6737_, 0);
v_fst_6741_ = lean_ctor_get(v_snd_6738_, 0);
v_snd_6742_ = lean_ctor_get(v_snd_6738_, 1);
v_isSharedCheck_6769_ = !lean_is_exclusive(v_snd_6738_);
if (v_isSharedCheck_6769_ == 0)
{
v___x_6744_ = v_snd_6738_;
v_isShared_6745_ = v_isSharedCheck_6769_;
goto v_resetjp_6743_;
}
else
{
lean_inc(v_snd_6742_);
lean_inc(v_fst_6741_);
lean_dec(v_snd_6738_);
v___x_6744_ = lean_box(0);
v_isShared_6745_ = v_isSharedCheck_6769_;
goto v_resetjp_6743_;
}
v_resetjp_6743_:
{
lean_object* v_result_6747_; 
if (v_includeDefinition_6730_ == 0)
{
lean_del_object(v___x_6744_);
v_result_6747_ = v_b_6734_;
goto v___jp_6746_;
}
else
{
lean_object* v_definition_x3f_6755_; 
v_definition_x3f_6755_ = lean_ctor_get(v_fst_6741_, 0);
if (lean_obj_tag(v_definition_x3f_6755_) == 1)
{
lean_object* v_val_6756_; lean_object* v___y_6758_; lean_object* v___x_6765_; 
v_val_6756_ = lean_ctor_get(v_definition_x3f_6755_, 0);
v___x_6765_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6756_);
if (lean_obj_tag(v___x_6765_) == 0)
{
lean_object* v___x_6766_; 
v___x_6766_ = lean_box(0);
v___y_6758_ = v___x_6766_;
goto v___jp_6757_;
}
else
{
lean_object* v_val_6767_; lean_object* v___x_6768_; 
v_val_6767_ = lean_ctor_get(v___x_6765_, 0);
lean_inc(v_val_6767_);
lean_dec_ref_known(v___x_6765_, 1);
v___x_6768_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6742_, v_val_6767_);
v___y_6758_ = v___x_6768_;
goto v___jp_6757_;
}
v___jp_6757_:
{
lean_object* v___x_6759_; lean_object* v___x_6761_; 
v___x_6759_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6756_);
lean_inc(v_fst_6739_);
if (v_isShared_6745_ == 0)
{
lean_ctor_set(v___x_6744_, 1, v___x_6759_);
lean_ctor_set(v___x_6744_, 0, v_fst_6739_);
v___x_6761_ = v___x_6744_;
goto v_reusejp_6760_;
}
else
{
lean_object* v_reuseFailAlloc_6764_; 
v_reuseFailAlloc_6764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6764_, 0, v_fst_6739_);
lean_ctor_set(v_reuseFailAlloc_6764_, 1, v___x_6759_);
v___x_6761_ = v_reuseFailAlloc_6764_;
goto v_reusejp_6760_;
}
v_reusejp_6760_:
{
lean_object* v___x_6762_; lean_object* v___x_6763_; 
lean_inc(v_fst_6740_);
v___x_6762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6762_, 0, v___x_6761_);
lean_ctor_set(v___x_6762_, 1, v_fst_6740_);
lean_ctor_set(v___x_6762_, 2, v___y_6758_);
v___x_6763_ = lean_array_push(v_b_6734_, v___x_6762_);
v_result_6747_ = v___x_6763_;
goto v___jp_6746_;
}
}
}
else
{
lean_del_object(v___x_6744_);
v_result_6747_ = v_b_6734_;
goto v___jp_6746_;
}
}
v___jp_6746_:
{
lean_object* v_usages_6748_; size_t v_sz_6749_; size_t v___x_6750_; lean_object* v___x_6751_; size_t v___x_6752_; size_t v___x_6753_; 
v_usages_6748_ = lean_ctor_get(v_fst_6741_, 1);
lean_inc_ref(v_usages_6748_);
lean_dec(v_fst_6741_);
v_sz_6749_ = lean_array_size(v_usages_6748_);
v___x_6750_ = ((size_t)0ULL);
lean_inc(v_fst_6740_);
lean_inc(v_fst_6739_);
v___x_6751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6739_, v_fst_6740_, v_snd_6742_, v_usages_6748_, v_sz_6749_, v___x_6750_, v_result_6747_);
lean_dec_ref(v_usages_6748_);
lean_dec(v_snd_6742_);
v___x_6752_ = ((size_t)1ULL);
v___x_6753_ = lean_usize_add(v_i_6733_, v___x_6752_);
v_i_6733_ = v___x_6753_;
v_b_6734_ = v___x_6751_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6770_, lean_object* v_as_6771_, lean_object* v_sz_6772_, lean_object* v_i_6773_, lean_object* v_b_6774_){
_start:
{
uint8_t v_includeDefinition_boxed_6775_; size_t v_sz_boxed_6776_; size_t v_i_boxed_6777_; lean_object* v_res_6778_; 
v_includeDefinition_boxed_6775_ = lean_unbox(v_includeDefinition_6770_);
v_sz_boxed_6776_ = lean_unbox_usize(v_sz_6772_);
lean_dec(v_sz_6772_);
v_i_boxed_6777_ = lean_unbox_usize(v_i_6773_);
lean_dec(v_i_6773_);
v_res_6778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6775_, v_as_6771_, v_sz_boxed_6776_, v_i_boxed_6777_, v_b_6774_);
lean_dec_ref(v_as_6771_);
return v_res_6778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6781_, lean_object* v_ident_6782_, uint8_t v_includeDefinition_6783_){
_start:
{
lean_object* v_result_6784_; lean_object* v___x_6785_; size_t v_sz_6786_; size_t v___x_6787_; lean_object* v___x_6788_; 
v_result_6784_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6785_ = l_Lean_Server_References_allRefsFor(v_self_6781_, v_ident_6782_);
v_sz_6786_ = lean_array_size(v___x_6785_);
v___x_6787_ = ((size_t)0ULL);
v___x_6788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6783_, v___x_6785_, v_sz_6786_, v___x_6787_, v_result_6784_);
lean_dec_ref(v___x_6785_);
return v___x_6788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6789_, lean_object* v_ident_6790_, lean_object* v_includeDefinition_6791_){
_start:
{
uint8_t v_includeDefinition_boxed_6792_; lean_object* v_res_6793_; 
v_includeDefinition_boxed_6792_ = lean_unbox(v_includeDefinition_6791_);
v_res_6793_ = l_Lean_Server_References_referringTo(v_self_6789_, v_ident_6790_, v_includeDefinition_boxed_6792_);
return v_res_6793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6797_, size_t v_sz_6798_, size_t v_i_6799_, lean_object* v_b_6800_){
_start:
{
uint8_t v___x_6801_; 
v___x_6801_ = lean_usize_dec_lt(v_i_6799_, v_sz_6798_);
if (v___x_6801_ == 0)
{
lean_inc_ref(v_b_6800_);
return v_b_6800_;
}
else
{
lean_object* v_a_6802_; lean_object* v_snd_6803_; lean_object* v_snd_6804_; lean_object* v_fst_6805_; lean_object* v_fst_6806_; lean_object* v_fst_6807_; lean_object* v_snd_6808_; lean_object* v___x_6810_; uint8_t v_isShared_6811_; uint8_t v_isSharedCheck_6846_; 
v_a_6802_ = lean_array_uget_borrowed(v_as_6797_, v_i_6799_);
v_snd_6803_ = lean_ctor_get(v_a_6802_, 1);
v_snd_6804_ = lean_ctor_get(v_snd_6803_, 1);
lean_inc(v_snd_6804_);
v_fst_6805_ = lean_ctor_get(v_snd_6804_, 0);
lean_inc(v_fst_6805_);
v_fst_6806_ = lean_ctor_get(v_a_6802_, 0);
v_fst_6807_ = lean_ctor_get(v_snd_6803_, 0);
v_snd_6808_ = lean_ctor_get(v_snd_6804_, 1);
v_isSharedCheck_6846_ = !lean_is_exclusive(v_snd_6804_);
if (v_isSharedCheck_6846_ == 0)
{
lean_object* v_unused_6847_; 
v_unused_6847_ = lean_ctor_get(v_snd_6804_, 0);
lean_dec(v_unused_6847_);
v___x_6810_ = v_snd_6804_;
v_isShared_6811_ = v_isSharedCheck_6846_;
goto v_resetjp_6809_;
}
else
{
lean_inc(v_snd_6808_);
lean_dec(v_snd_6804_);
v___x_6810_ = lean_box(0);
v_isShared_6811_ = v_isSharedCheck_6846_;
goto v_resetjp_6809_;
}
v_resetjp_6809_:
{
lean_object* v_definition_x3f_6812_; lean_object* v___x_6814_; uint8_t v_isShared_6815_; uint8_t v_isSharedCheck_6844_; 
v_definition_x3f_6812_ = lean_ctor_get(v_fst_6805_, 0);
v_isSharedCheck_6844_ = !lean_is_exclusive(v_fst_6805_);
if (v_isSharedCheck_6844_ == 0)
{
lean_object* v_unused_6845_; 
v_unused_6845_ = lean_ctor_get(v_fst_6805_, 1);
lean_dec(v_unused_6845_);
v___x_6814_ = v_fst_6805_;
v_isShared_6815_ = v_isSharedCheck_6844_;
goto v_resetjp_6813_;
}
else
{
lean_inc(v_definition_x3f_6812_);
lean_dec(v_fst_6805_);
v___x_6814_ = lean_box(0);
v_isShared_6815_ = v_isSharedCheck_6844_;
goto v_resetjp_6813_;
}
v_resetjp_6813_:
{
lean_object* v___x_6816_; 
v___x_6816_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6812_) == 1)
{
lean_object* v_val_6817_; lean_object* v___x_6819_; uint8_t v_isShared_6820_; uint8_t v_isSharedCheck_6839_; 
v_val_6817_ = lean_ctor_get(v_definition_x3f_6812_, 0);
v_isSharedCheck_6839_ = !lean_is_exclusive(v_definition_x3f_6812_);
if (v_isSharedCheck_6839_ == 0)
{
v___x_6819_ = v_definition_x3f_6812_;
v_isShared_6820_ = v_isSharedCheck_6839_;
goto v_resetjp_6818_;
}
else
{
lean_inc(v_val_6817_);
lean_dec(v_definition_x3f_6812_);
v___x_6819_ = lean_box(0);
v_isShared_6820_ = v_isSharedCheck_6839_;
goto v_resetjp_6818_;
}
v_resetjp_6818_:
{
lean_object* v___y_6822_; lean_object* v___x_6835_; 
v___x_6835_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6817_);
if (lean_obj_tag(v___x_6835_) == 0)
{
lean_object* v___x_6836_; 
lean_dec(v_snd_6808_);
v___x_6836_ = lean_box(0);
v___y_6822_ = v___x_6836_;
goto v___jp_6821_;
}
else
{
lean_object* v_val_6837_; lean_object* v___x_6838_; 
v_val_6837_ = lean_ctor_get(v___x_6835_, 0);
lean_inc(v_val_6837_);
lean_dec_ref_known(v___x_6835_, 1);
v___x_6838_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6808_, v_val_6837_);
lean_dec(v_snd_6808_);
v___y_6822_ = v___x_6838_;
goto v___jp_6821_;
}
v___jp_6821_:
{
lean_object* v___x_6823_; lean_object* v___x_6825_; 
v___x_6823_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6817_);
lean_dec(v_val_6817_);
lean_inc(v_fst_6806_);
if (v_isShared_6815_ == 0)
{
lean_ctor_set(v___x_6814_, 1, v___x_6823_);
lean_ctor_set(v___x_6814_, 0, v_fst_6806_);
v___x_6825_ = v___x_6814_;
goto v_reusejp_6824_;
}
else
{
lean_object* v_reuseFailAlloc_6834_; 
v_reuseFailAlloc_6834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6834_, 0, v_fst_6806_);
lean_ctor_set(v_reuseFailAlloc_6834_, 1, v___x_6823_);
v___x_6825_ = v_reuseFailAlloc_6834_;
goto v_reusejp_6824_;
}
v_reusejp_6824_:
{
lean_object* v___x_6826_; lean_object* v___x_6828_; 
lean_inc(v_fst_6807_);
v___x_6826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6826_, 0, v___x_6825_);
lean_ctor_set(v___x_6826_, 1, v_fst_6807_);
lean_ctor_set(v___x_6826_, 2, v___y_6822_);
if (v_isShared_6820_ == 0)
{
lean_ctor_set(v___x_6819_, 0, v___x_6826_);
v___x_6828_ = v___x_6819_;
goto v_reusejp_6827_;
}
else
{
lean_object* v_reuseFailAlloc_6833_; 
v_reuseFailAlloc_6833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6833_, 0, v___x_6826_);
v___x_6828_ = v_reuseFailAlloc_6833_;
goto v_reusejp_6827_;
}
v_reusejp_6827_:
{
lean_object* v___x_6829_; lean_object* v___x_6831_; 
v___x_6829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6829_, 0, v___x_6828_);
if (v_isShared_6811_ == 0)
{
lean_ctor_set(v___x_6810_, 1, v___x_6816_);
lean_ctor_set(v___x_6810_, 0, v___x_6829_);
v___x_6831_ = v___x_6810_;
goto v_reusejp_6830_;
}
else
{
lean_object* v_reuseFailAlloc_6832_; 
v_reuseFailAlloc_6832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6832_, 0, v___x_6829_);
lean_ctor_set(v_reuseFailAlloc_6832_, 1, v___x_6816_);
v___x_6831_ = v_reuseFailAlloc_6832_;
goto v_reusejp_6830_;
}
v_reusejp_6830_:
{
return v___x_6831_;
}
}
}
}
}
}
else
{
lean_object* v___x_6840_; size_t v___x_6841_; size_t v___x_6842_; 
lean_del_object(v___x_6814_);
lean_dec(v_definition_x3f_6812_);
lean_del_object(v___x_6810_);
lean_dec(v_snd_6808_);
v___x_6840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6841_ = ((size_t)1ULL);
v___x_6842_ = lean_usize_add(v_i_6799_, v___x_6841_);
v_i_6799_ = v___x_6842_;
v_b_6800_ = v___x_6840_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6848_, lean_object* v_sz_6849_, lean_object* v_i_6850_, lean_object* v_b_6851_){
_start:
{
size_t v_sz_boxed_6852_; size_t v_i_boxed_6853_; lean_object* v_res_6854_; 
v_sz_boxed_6852_ = lean_unbox_usize(v_sz_6849_);
lean_dec(v_sz_6849_);
v_i_boxed_6853_ = lean_unbox_usize(v_i_6850_);
lean_dec(v_i_6850_);
v_res_6854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6848_, v_sz_boxed_6852_, v_i_boxed_6853_, v_b_6851_);
lean_dec_ref(v_b_6851_);
lean_dec_ref(v_as_6848_);
return v_res_6854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6855_, lean_object* v_ident_6856_){
_start:
{
lean_object* v___x_6857_; lean_object* v___x_6858_; lean_object* v___x_6859_; size_t v_sz_6860_; size_t v___x_6861_; lean_object* v___x_6862_; lean_object* v_fst_6863_; 
v___x_6857_ = l_Lean_Server_References_allRefsFor(v_self_6855_, v_ident_6856_);
v___x_6858_ = lean_box(0);
v___x_6859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6860_ = lean_array_size(v___x_6857_);
v___x_6861_ = ((size_t)0ULL);
v___x_6862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6857_, v_sz_6860_, v___x_6861_, v___x_6859_);
lean_dec_ref(v___x_6857_);
v_fst_6863_ = lean_ctor_get(v___x_6862_, 0);
lean_inc(v_fst_6863_);
lean_dec_ref(v___x_6862_);
if (lean_obj_tag(v_fst_6863_) == 0)
{
return v___x_6858_;
}
else
{
lean_object* v_val_6864_; 
v_val_6864_ = lean_ctor_get(v_fst_6863_, 0);
lean_inc(v_val_6864_);
lean_dec_ref_known(v_fst_6863_, 1);
return v_val_6864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6865_, lean_object* v_a_6866_, lean_object* v_fst_6867_, lean_object* v_init_6868_, lean_object* v_x_6869_){
_start:
{
if (lean_obj_tag(v_x_6869_) == 0)
{
lean_object* v_k_6871_; lean_object* v_v_6872_; lean_object* v_l_6873_; lean_object* v_r_6874_; lean_object* v___x_6875_; 
v_k_6871_ = lean_ctor_get(v_x_6869_, 1);
lean_inc(v_k_6871_);
v_v_6872_ = lean_ctor_get(v_x_6869_, 2);
lean_inc(v_v_6872_);
v_l_6873_ = lean_ctor_get(v_x_6869_, 3);
lean_inc(v_l_6873_);
v_r_6874_ = lean_ctor_get(v_x_6869_, 4);
lean_inc(v_r_6874_);
lean_dec_ref_known(v_x_6869_, 5);
lean_inc_ref(v_fst_6867_);
lean_inc(v_a_6866_);
lean_inc_ref(v_filterMapIdent_6865_);
v___x_6875_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6865_, v_a_6866_, v_fst_6867_, v_init_6868_, v_l_6873_);
if (lean_obj_tag(v_k_6871_) == 0)
{
lean_object* v_definition_x3f_6876_; 
v_definition_x3f_6876_ = lean_ctor_get(v_v_6872_, 0);
lean_inc(v_definition_x3f_6876_);
lean_dec(v_v_6872_);
if (lean_obj_tag(v_definition_x3f_6876_) == 1)
{
lean_object* v_a_6877_; lean_object* v_identName_6878_; lean_object* v_val_6879_; lean_object* v___x_6880_; lean_object* v___x_6881_; 
v_a_6877_ = lean_ctor_get(v___x_6875_, 0);
lean_inc(v_a_6877_);
lean_dec_ref(v___x_6875_);
v_identName_6878_ = lean_ctor_get(v_k_6871_, 1);
lean_inc_ref(v_identName_6878_);
lean_dec_ref_known(v_k_6871_, 2);
v_val_6879_ = lean_ctor_get(v_definition_x3f_6876_, 0);
lean_inc(v_val_6879_);
lean_dec_ref_known(v_definition_x3f_6876_, 1);
v___x_6880_ = l_String_toName(v_identName_6878_);
lean_inc_ref(v_filterMapIdent_6865_);
v___x_6881_ = lean_apply_1(v_filterMapIdent_6865_, v___x_6880_);
if (lean_obj_tag(v___x_6881_) == 1)
{
lean_object* v_val_6882_; lean_object* v___x_6883_; lean_object* v___x_6884_; lean_object* v___x_6885_; 
v_val_6882_ = lean_ctor_get(v___x_6881_, 0);
lean_inc(v_val_6882_);
lean_dec_ref_known(v___x_6881_, 1);
v___x_6883_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6879_);
lean_dec(v_val_6879_);
lean_inc_ref(v_fst_6867_);
lean_inc(v_a_6866_);
v___x_6884_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6884_, 0, v_a_6866_);
lean_ctor_set(v___x_6884_, 1, v_fst_6867_);
lean_ctor_set(v___x_6884_, 2, v_val_6882_);
lean_ctor_set(v___x_6884_, 3, v___x_6883_);
v___x_6885_ = lean_array_push(v_a_6877_, v___x_6884_);
v_init_6868_ = v___x_6885_;
v_x_6869_ = v_r_6874_;
goto _start;
}
else
{
lean_dec(v___x_6881_);
lean_dec(v_val_6879_);
v_init_6868_ = v_a_6877_;
v_x_6869_ = v_r_6874_;
goto _start;
}
}
else
{
lean_object* v_a_6888_; 
lean_dec_ref_known(v_k_6871_, 2);
lean_dec(v_definition_x3f_6876_);
v_a_6888_ = lean_ctor_get(v___x_6875_, 0);
lean_inc(v_a_6888_);
lean_dec_ref(v___x_6875_);
v_init_6868_ = v_a_6888_;
v_x_6869_ = v_r_6874_;
goto _start;
}
}
else
{
lean_object* v_a_6890_; 
lean_dec(v_v_6872_);
lean_dec(v_k_6871_);
v_a_6890_ = lean_ctor_get(v___x_6875_, 0);
lean_inc(v_a_6890_);
lean_dec_ref(v___x_6875_);
v_init_6868_ = v_a_6890_;
v_x_6869_ = v_r_6874_;
goto _start;
}
}
else
{
lean_object* v___x_6892_; 
lean_dec_ref(v_fst_6867_);
lean_dec(v_a_6866_);
lean_dec_ref(v_filterMapIdent_6865_);
v___x_6892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6892_, 0, v_init_6868_);
return v___x_6892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6893_, lean_object* v_a_6894_, lean_object* v_fst_6895_, lean_object* v_init_6896_, lean_object* v_x_6897_, lean_object* v___y_6898_){
_start:
{
lean_object* v_res_6899_; 
v_res_6899_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6893_, v_a_6894_, v_fst_6895_, v_init_6896_, v_x_6897_);
return v_res_6899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6900_, lean_object* v_cancelTk_x3f_6901_, lean_object* v_init_6902_, lean_object* v_x_6903_){
_start:
{
lean_object* v_d_6906_; 
if (lean_obj_tag(v_x_6903_) == 0)
{
lean_object* v_k_6908_; lean_object* v_v_6909_; lean_object* v_l_6910_; lean_object* v_r_6911_; lean_object* v___x_6912_; lean_object* v_val_6914_; lean_object* v___x_6917_; 
v_k_6908_ = lean_ctor_get(v_x_6903_, 1);
lean_inc(v_k_6908_);
v_v_6909_ = lean_ctor_get(v_x_6903_, 2);
lean_inc(v_v_6909_);
v_l_6910_ = lean_ctor_get(v_x_6903_, 3);
lean_inc(v_l_6910_);
v_r_6911_ = lean_ctor_get(v_x_6903_, 4);
lean_inc(v_r_6911_);
lean_dec_ref_known(v_x_6903_, 5);
v___x_6912_ = lean_box(0);
lean_inc(v_cancelTk_x3f_6901_);
lean_inc_ref(v_filterMapIdent_6900_);
v___x_6917_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6900_, v_cancelTk_x3f_6901_, v_init_6902_, v_l_6910_);
if (lean_obj_tag(v___x_6917_) == 0)
{
lean_object* v_a_6918_; 
lean_dec(v_r_6911_);
lean_dec(v_v_6909_);
lean_dec(v_k_6908_);
lean_dec(v_cancelTk_x3f_6901_);
lean_dec_ref(v_filterMapIdent_6900_);
v_a_6918_ = lean_ctor_get(v___x_6917_, 0);
lean_inc(v_a_6918_);
lean_dec_ref_known(v___x_6917_, 1);
v_d_6906_ = v_a_6918_;
goto v___jp_6905_;
}
else
{
lean_object* v_snd_6919_; lean_object* v_a_6920_; lean_object* v_fst_6921_; lean_object* v_fst_6922_; lean_object* v_snd_6923_; lean_object* v___x_6925_; uint8_t v_isShared_6926_; uint8_t v_isSharedCheck_6943_; 
v_snd_6919_ = lean_ctor_get(v_v_6909_, 1);
lean_inc(v_snd_6919_);
v_a_6920_ = lean_ctor_get(v___x_6917_, 0);
lean_inc(v_a_6920_);
lean_dec_ref_known(v___x_6917_, 1);
v_fst_6921_ = lean_ctor_get(v_v_6909_, 0);
lean_inc(v_fst_6921_);
lean_dec(v_v_6909_);
v_fst_6922_ = lean_ctor_get(v_snd_6919_, 0);
lean_inc(v_fst_6922_);
lean_dec(v_snd_6919_);
v_snd_6923_ = lean_ctor_get(v_a_6920_, 1);
v_isSharedCheck_6943_ = !lean_is_exclusive(v_a_6920_);
if (v_isSharedCheck_6943_ == 0)
{
lean_object* v_unused_6944_; 
v_unused_6944_ = lean_ctor_get(v_a_6920_, 0);
lean_dec(v_unused_6944_);
v___x_6925_ = v_a_6920_;
v_isShared_6926_ = v_isSharedCheck_6943_;
goto v_resetjp_6924_;
}
else
{
lean_inc(v_snd_6923_);
lean_dec(v_a_6920_);
v___x_6925_ = lean_box(0);
v_isShared_6926_ = v_isSharedCheck_6943_;
goto v_resetjp_6924_;
}
v_resetjp_6924_:
{
if (lean_obj_tag(v_cancelTk_x3f_6901_) == 1)
{
lean_object* v_val_6930_; uint8_t v___x_6931_; 
v_val_6930_ = lean_ctor_get(v_cancelTk_x3f_6901_, 0);
v___x_6931_ = l_IO_CancelToken_isSet(v_val_6930_);
if (v___x_6931_ == 0)
{
lean_del_object(v___x_6925_);
goto v___jp_6927_;
}
else
{
lean_object* v___x_6933_; uint8_t v_isShared_6934_; uint8_t v_isSharedCheck_6941_; 
lean_dec(v_fst_6922_);
lean_dec(v_fst_6921_);
lean_dec(v_r_6911_);
lean_dec(v_k_6908_);
lean_dec_ref(v_filterMapIdent_6900_);
v_isSharedCheck_6941_ = !lean_is_exclusive(v_cancelTk_x3f_6901_);
if (v_isSharedCheck_6941_ == 0)
{
lean_object* v_unused_6942_; 
v_unused_6942_ = lean_ctor_get(v_cancelTk_x3f_6901_, 0);
lean_dec(v_unused_6942_);
v___x_6933_ = v_cancelTk_x3f_6901_;
v_isShared_6934_ = v_isSharedCheck_6941_;
goto v_resetjp_6932_;
}
else
{
lean_dec(v_cancelTk_x3f_6901_);
v___x_6933_ = lean_box(0);
v_isShared_6934_ = v_isSharedCheck_6941_;
goto v_resetjp_6932_;
}
v_resetjp_6932_:
{
lean_object* v___x_6936_; 
lean_inc(v_snd_6923_);
if (v_isShared_6934_ == 0)
{
lean_ctor_set(v___x_6933_, 0, v_snd_6923_);
v___x_6936_ = v___x_6933_;
goto v_reusejp_6935_;
}
else
{
lean_object* v_reuseFailAlloc_6940_; 
v_reuseFailAlloc_6940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6940_, 0, v_snd_6923_);
v___x_6936_ = v_reuseFailAlloc_6940_;
goto v_reusejp_6935_;
}
v_reusejp_6935_:
{
lean_object* v___x_6938_; 
if (v_isShared_6926_ == 0)
{
lean_ctor_set(v___x_6925_, 0, v___x_6936_);
v___x_6938_ = v___x_6925_;
goto v_reusejp_6937_;
}
else
{
lean_object* v_reuseFailAlloc_6939_; 
v_reuseFailAlloc_6939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6939_, 0, v___x_6936_);
lean_ctor_set(v_reuseFailAlloc_6939_, 1, v_snd_6923_);
v___x_6938_ = v_reuseFailAlloc_6939_;
goto v_reusejp_6937_;
}
v_reusejp_6937_:
{
v_d_6906_ = v___x_6938_;
goto v___jp_6905_;
}
}
}
}
}
else
{
lean_del_object(v___x_6925_);
goto v___jp_6927_;
}
v___jp_6927_:
{
lean_object* v___x_6928_; lean_object* v_a_6929_; 
lean_inc_ref(v_filterMapIdent_6900_);
v___x_6928_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6900_, v_k_6908_, v_fst_6921_, v_snd_6923_, v_fst_6922_);
v_a_6929_ = lean_ctor_get(v___x_6928_, 0);
lean_inc(v_a_6929_);
lean_dec_ref(v___x_6928_);
v_val_6914_ = v_a_6929_;
goto v___jp_6913_;
}
}
}
v___jp_6913_:
{
lean_object* v___x_6915_; 
v___x_6915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6915_, 0, v___x_6912_);
lean_ctor_set(v___x_6915_, 1, v_val_6914_);
v_init_6902_ = v___x_6915_;
v_x_6903_ = v_r_6911_;
goto _start;
}
}
else
{
lean_object* v___x_6945_; 
lean_dec(v_cancelTk_x3f_6901_);
lean_dec_ref(v_filterMapIdent_6900_);
v___x_6945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6945_, 0, v_init_6902_);
return v___x_6945_;
}
v___jp_6905_:
{
lean_object* v___x_6907_; 
v___x_6907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6907_, 0, v_d_6906_);
return v___x_6907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_6946_, lean_object* v_cancelTk_x3f_6947_, lean_object* v_init_6948_, lean_object* v_x_6949_, lean_object* v___y_6950_){
_start:
{
lean_object* v_res_6951_; 
v_res_6951_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6946_, v_cancelTk_x3f_6947_, v_init_6948_, v_x_6949_);
return v_res_6951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_6957_, lean_object* v_filterMapIdent_6958_, lean_object* v_cancelTk_x3f_6959_){
_start:
{
lean_object* v_val_6962_; lean_object* v___x_6966_; lean_object* v___x_6967_; lean_object* v___x_6968_; lean_object* v_a_6969_; 
v___x_6966_ = l_Lean_Server_References_allRefs(v_self_6957_);
v___x_6967_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_6968_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6958_, v_cancelTk_x3f_6959_, v___x_6967_, v___x_6966_);
v_a_6969_ = lean_ctor_get(v___x_6968_, 0);
lean_inc(v_a_6969_);
lean_dec_ref(v___x_6968_);
v_val_6962_ = v_a_6969_;
goto v___jp_6961_;
v___jp_6961_:
{
lean_object* v_fst_6963_; 
v_fst_6963_ = lean_ctor_get(v_val_6962_, 0);
if (lean_obj_tag(v_fst_6963_) == 0)
{
lean_object* v_snd_6964_; 
v_snd_6964_ = lean_ctor_get(v_val_6962_, 1);
lean_inc(v_snd_6964_);
lean_dec_ref(v_val_6962_);
return v_snd_6964_;
}
else
{
lean_object* v_val_6965_; 
lean_inc_ref(v_fst_6963_);
lean_dec_ref(v_val_6962_);
v_val_6965_ = lean_ctor_get(v_fst_6963_, 0);
lean_inc(v_val_6965_);
lean_dec_ref_known(v_fst_6963_, 1);
return v_val_6965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_6970_, lean_object* v_filterMapIdent_6971_, lean_object* v_cancelTk_x3f_6972_, lean_object* v_a_6973_){
_start:
{
lean_object* v_res_6974_; 
v_res_6974_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_6970_, v_filterMapIdent_6971_, v_cancelTk_x3f_6972_);
return v_res_6974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_6975_, lean_object* v_self_6976_, lean_object* v_filterMapIdent_6977_, lean_object* v_cancelTk_x3f_6978_){
_start:
{
lean_object* v___x_6980_; 
v___x_6980_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_6976_, v_filterMapIdent_6977_, v_cancelTk_x3f_6978_);
return v___x_6980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_6981_, lean_object* v_self_6982_, lean_object* v_filterMapIdent_6983_, lean_object* v_cancelTk_x3f_6984_, lean_object* v_a_6985_){
_start:
{
lean_object* v_res_6986_; 
v_res_6986_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_6981_, v_self_6982_, v_filterMapIdent_6983_, v_cancelTk_x3f_6984_);
return v_res_6986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_6987_, lean_object* v_filterMapIdent_6988_, lean_object* v_a_6989_, lean_object* v_fst_6990_, lean_object* v_init_6991_, lean_object* v_x_6992_){
_start:
{
lean_object* v___x_6994_; 
v___x_6994_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6988_, v_a_6989_, v_fst_6990_, v_init_6991_, v_x_6992_);
return v___x_6994_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_6995_, lean_object* v_filterMapIdent_6996_, lean_object* v_a_6997_, lean_object* v_fst_6998_, lean_object* v_init_6999_, lean_object* v_x_7000_, lean_object* v___y_7001_){
_start:
{
lean_object* v_res_7002_; 
v_res_7002_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_6995_, v_filterMapIdent_6996_, v_a_6997_, v_fst_6998_, v_init_6999_, v_x_7000_);
return v_res_7002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_7003_, lean_object* v_filterMapIdent_7004_, lean_object* v_cancelTk_x3f_7005_, lean_object* v_init_7006_, lean_object* v_x_7007_){
_start:
{
lean_object* v___x_7009_; 
v___x_7009_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7004_, v_cancelTk_x3f_7005_, v_init_7006_, v_x_7007_);
return v___x_7009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7010_, lean_object* v_filterMapIdent_7011_, lean_object* v_cancelTk_x3f_7012_, lean_object* v_init_7013_, lean_object* v_x_7014_, lean_object* v___y_7015_){
_start:
{
lean_object* v_res_7016_; 
v_res_7016_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7010_, v_filterMapIdent_7011_, v_cancelTk_x3f_7012_, v_init_7013_, v_x_7014_);
return v_res_7016_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7017_){
_start:
{
lean_object* v___x_7018_; lean_object* v___x_7019_; 
v___x_7018_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7019_ = lean_panic_fn_borrowed(v___x_7018_, v_msg_7017_);
return v___x_7019_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7023_; lean_object* v___x_7024_; lean_object* v___x_7025_; lean_object* v___x_7026_; lean_object* v___x_7027_; lean_object* v___x_7028_; 
v___x_7023_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7024_ = lean_unsigned_to_nat(14u);
v___x_7025_ = lean_unsigned_to_nat(22u);
v___x_7026_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7027_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7028_ = l_mkPanicMessageWithDecl(v___x_7027_, v___x_7026_, v___x_7025_, v___x_7024_, v___x_7023_);
return v___x_7028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7029_, lean_object* v_init_7030_, lean_object* v_x_7031_){
_start:
{
if (lean_obj_tag(v_x_7031_) == 0)
{
lean_object* v_k_7032_; lean_object* v_v_7033_; lean_object* v_l_7034_; lean_object* v_r_7035_; lean_object* v___x_7036_; lean_object* v_a_7037_; lean_object* v_fst_7038_; lean_object* v_snd_7039_; lean_object* v___y_7041_; lean_object* v_index_7056_; lean_object* v___x_7057_; 
v_k_7032_ = lean_ctor_get(v_x_7031_, 1);
v_v_7033_ = lean_ctor_get(v_x_7031_, 2);
v_l_7034_ = lean_ctor_get(v_x_7031_, 3);
v_r_7035_ = lean_ctor_get(v_x_7031_, 4);
v___x_7036_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7029_, v_init_7030_, v_l_7034_);
v_a_7037_ = lean_ctor_get(v___x_7036_, 0);
lean_inc(v_a_7037_);
lean_dec_ref(v___x_7036_);
v_fst_7038_ = lean_ctor_get(v_v_7033_, 0);
v_snd_7039_ = lean_ctor_get(v_v_7033_, 1);
v_index_7056_ = lean_ctor_get(v_snd_7039_, 1);
v___x_7057_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7056_, v_requestedMod_7029_);
if (lean_obj_tag(v___x_7057_) == 1)
{
lean_object* v_val_7058_; lean_object* v___x_7059_; 
v_val_7058_ = lean_ctor_get(v___x_7057_, 0);
lean_inc(v_val_7058_);
lean_dec_ref_known(v___x_7057_, 1);
v___x_7059_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7058_);
lean_dec(v_val_7058_);
if (lean_obj_tag(v___x_7059_) == 0)
{
lean_object* v___x_7060_; lean_object* v___x_7061_; 
v___x_7060_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7061_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7060_);
v___y_7041_ = v___x_7061_;
goto v___jp_7040_;
}
else
{
lean_object* v_val_7062_; 
v_val_7062_ = lean_ctor_get(v___x_7059_, 0);
lean_inc(v_val_7062_);
lean_dec_ref_known(v___x_7059_, 1);
v___y_7041_ = v_val_7062_;
goto v___jp_7040_;
}
}
else
{
lean_dec(v___x_7057_);
v_init_7030_ = v_a_7037_;
v_x_7031_ = v_r_7035_;
goto _start;
}
v___jp_7040_:
{
uint8_t v_isAll_7042_; uint8_t v_isPrivate_7043_; uint8_t v_metaKind_7044_; lean_object* v___x_7046_; uint8_t v_isShared_7047_; uint8_t v_isSharedCheck_7053_; 
v_isAll_7042_ = lean_ctor_get_uint8(v___y_7041_, sizeof(void*)*2);
v_isPrivate_7043_ = lean_ctor_get_uint8(v___y_7041_, sizeof(void*)*2 + 1);
v_metaKind_7044_ = lean_ctor_get_uint8(v___y_7041_, sizeof(void*)*2 + 2);
v_isSharedCheck_7053_ = !lean_is_exclusive(v___y_7041_);
if (v_isSharedCheck_7053_ == 0)
{
lean_object* v_unused_7054_; lean_object* v_unused_7055_; 
v_unused_7054_ = lean_ctor_get(v___y_7041_, 1);
lean_dec(v_unused_7054_);
v_unused_7055_ = lean_ctor_get(v___y_7041_, 0);
lean_dec(v_unused_7055_);
v___x_7046_ = v___y_7041_;
v_isShared_7047_ = v_isSharedCheck_7053_;
goto v_resetjp_7045_;
}
else
{
lean_dec(v___y_7041_);
v___x_7046_ = lean_box(0);
v_isShared_7047_ = v_isSharedCheck_7053_;
goto v_resetjp_7045_;
}
v_resetjp_7045_:
{
lean_object* v___x_7049_; 
lean_inc(v_fst_7038_);
lean_inc(v_k_7032_);
if (v_isShared_7047_ == 0)
{
lean_ctor_set(v___x_7046_, 1, v_fst_7038_);
lean_ctor_set(v___x_7046_, 0, v_k_7032_);
v___x_7049_ = v___x_7046_;
goto v_reusejp_7048_;
}
else
{
lean_object* v_reuseFailAlloc_7052_; 
v_reuseFailAlloc_7052_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7052_, 0, v_k_7032_);
lean_ctor_set(v_reuseFailAlloc_7052_, 1, v_fst_7038_);
lean_ctor_set_uint8(v_reuseFailAlloc_7052_, sizeof(void*)*2, v_isAll_7042_);
lean_ctor_set_uint8(v_reuseFailAlloc_7052_, sizeof(void*)*2 + 1, v_isPrivate_7043_);
lean_ctor_set_uint8(v_reuseFailAlloc_7052_, sizeof(void*)*2 + 2, v_metaKind_7044_);
v___x_7049_ = v_reuseFailAlloc_7052_;
goto v_reusejp_7048_;
}
v_reusejp_7048_:
{
lean_object* v___x_7050_; 
v___x_7050_ = lean_array_push(v_a_7037_, v___x_7049_);
v_init_7030_ = v___x_7050_;
v_x_7031_ = v_r_7035_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7064_; 
v___x_7064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7064_, 0, v_init_7030_);
return v___x_7064_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object* v_requestedMod_7065_, lean_object* v_init_7066_, lean_object* v_x_7067_){
_start:
{
lean_object* v_res_7068_; 
v_res_7068_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7065_, v_init_7066_, v_x_7067_);
lean_dec(v_x_7067_);
lean_dec(v_requestedMod_7065_);
return v_res_7068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object* v_self_7069_, lean_object* v_requestedMod_7070_){
_start:
{
lean_object* v_result_7071_; lean_object* v___x_7072_; lean_object* v___x_7073_; lean_object* v_a_7074_; 
v_result_7071_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_7072_ = l_Lean_Server_References_allDirectImports(v_self_7069_);
v___x_7073_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7070_, v_result_7071_, v___x_7072_);
lean_dec(v___x_7072_);
v_a_7074_ = lean_ctor_get(v___x_7073_, 0);
lean_inc(v_a_7074_);
lean_dec_ref(v___x_7073_);
return v_a_7074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object* v_self_7075_, lean_object* v_requestedMod_7076_){
_start:
{
lean_object* v_res_7077_; 
v_res_7077_ = l_Lean_Server_References_importedBy(v_self_7075_, v_requestedMod_7076_);
lean_dec(v_requestedMod_7076_);
return v_res_7077_;
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

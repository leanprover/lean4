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
v___x_1012_ = l_Lean_Lsp_RefInfo_contains(v_v_1007_, v_pos_1002_, v_includeStop_1003_);
lean_dec(v_v_1007_);
if (v___x_1012_ == 0)
{
lean_object* v_a_1013_; 
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
lean_inc(v_a_1011_);
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
case 17:
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
uint8_t v___x_3525__boxed_2472_; lean_object* v_res_2473_; 
v___x_3525__boxed_2472_ = lean_unbox(v___x_2467_);
v_res_2473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_findReferences_spec__1___lam__0(v___x_3525__boxed_2472_, v_x_2468_, v_x_2469_, v_x_2470_, v___y_2471_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___f_2525_; lean_object* v___f_2526_; lean_object* v___f_2527_; lean_object* v___f_2528_; lean_object* v___f_2529_; lean_object* v___f_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___f_2535_; lean_object* v___f_2536_; lean_object* v___f_2537_; lean_object* v___f_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_3116__overap_2547_; lean_object* v___x_2548_; 
v___f_2525_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_2526_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_2527_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_2528_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_2529_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_2530_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_2531_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___f_2525_);
lean_ctor_set(v___x_2532_, 1, v___f_2526_);
v___x_2533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v___f_2527_);
lean_ctor_set(v___x_2533_, 2, v___f_2528_);
lean_ctor_set(v___x_2533_, 3, v___f_2529_);
lean_ctor_set(v___x_2533_, 4, v___f_2530_);
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v___f_2531_);
lean_inc_ref_n(v___x_2534_, 6);
v___f_2535_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2535_, 0, v___x_2534_);
v___f_2536_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2536_, 0, v___x_2534_);
v___f_2537_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2537_, 0, v___x_2534_);
v___f_2538_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2538_, 0, v___x_2534_);
v___x_2539_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2539_, 0, lean_box(0));
lean_closure_set(v___x_2539_, 1, lean_box(0));
lean_closure_set(v___x_2539_, 2, v___x_2534_);
v___x_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_ctor_set(v___x_2540_, 1, v___f_2535_);
v___x_2541_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2541_, 0, lean_box(0));
lean_closure_set(v___x_2541_, 1, lean_box(0));
lean_closure_set(v___x_2541_, 2, v___x_2534_);
v___x_2542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
lean_ctor_set(v___x_2542_, 2, v___f_2536_);
lean_ctor_set(v___x_2542_, 3, v___f_2537_);
lean_ctor_set(v___x_2542_, 4, v___f_2538_);
v___x_2543_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2543_, 0, lean_box(0));
lean_closure_set(v___x_2543_, 1, lean_box(0));
lean_closure_set(v___x_2543_, 2, v___x_2534_);
v___x_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = lean_box(0);
v___x_2546_ = l_instInhabitedOfMonad___redArg(v___x_2544_, v___x_2545_);
v___x_3116__overap_2547_ = lean_panic_fn_borrowed(v___x_2546_, v_msg_2523_);
lean_dec(v___x_2546_);
v___x_2548_ = lean_apply_1(v___x_3116__overap_2547_, v___y_2524_);
return v___x_2548_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2552_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__2));
v___x_2553_ = lean_unsigned_to_nat(21u);
v___x_2554_ = lean_unsigned_to_nat(65u);
v___x_2555_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__1));
v___x_2556_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__0));
v___x_2557_ = l_mkPanicMessageWithDecl(v___x_2556_, v___x_2555_, v___x_2554_, v___x_2553_, v___x_2552_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(lean_object* v_preNode_2558_, lean_object* v_postNode_2559_, lean_object* v_x_2560_, lean_object* v_x_2561_, lean_object* v___y_2562_){
_start:
{
switch(lean_obj_tag(v_x_2561_))
{
case 0:
{
lean_object* v_i_2563_; lean_object* v_t_2564_; lean_object* v___x_2565_; 
v_i_2563_ = lean_ctor_get(v_x_2561_, 0);
lean_inc_ref(v_i_2563_);
v_t_2564_ = lean_ctor_get(v_x_2561_, 1);
lean_inc_ref(v_t_2564_);
lean_dec_ref_known(v_x_2561_, 2);
v___x_2565_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_2563_, v_x_2560_);
v_x_2560_ = v___x_2565_;
v_x_2561_ = v_t_2564_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_2560_) == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec_ref_known(v_x_2561_, 2);
lean_dec_ref(v_postNode_2559_);
lean_dec_ref(v_preNode_2558_);
v___x_2567_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_2568_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v___x_2567_, v___y_2562_);
return v___x_2568_;
}
else
{
lean_object* v_i_2569_; lean_object* v_children_2570_; lean_object* v_val_2571_; lean_object* v___x_2572_; lean_object* v_fst_2573_; uint8_t v___x_2574_; 
v_i_2569_ = lean_ctor_get(v_x_2561_, 0);
lean_inc_ref_n(v_i_2569_, 2);
v_children_2570_ = lean_ctor_get(v_x_2561_, 1);
lean_inc_ref_n(v_children_2570_, 2);
lean_dec_ref_known(v_x_2561_, 2);
v_val_2571_ = lean_ctor_get(v_x_2560_, 0);
lean_inc_n(v_val_2571_, 2);
lean_inc_ref(v_preNode_2558_);
v___x_2572_ = lean_apply_4(v_preNode_2558_, v_val_2571_, v_i_2569_, v_children_2570_, v___y_2562_);
v_fst_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_fst_2573_);
v___x_2574_ = lean_unbox(v_fst_2573_);
lean_dec(v_fst_2573_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref(v_preNode_2558_);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_x_2560_);
if (v_isSharedCheck_2593_ == 0)
{
lean_object* v_unused_2594_; 
v_unused_2594_ = lean_ctor_get(v_x_2560_, 0);
lean_dec(v_unused_2594_);
v___x_2576_ = v_x_2560_;
v_isShared_2577_ = v_isSharedCheck_2593_;
goto v_resetjp_2575_;
}
else
{
lean_dec(v_x_2560_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2593_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v_snd_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v_fst_2581_; lean_object* v_snd_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2592_; 
v_snd_2578_ = lean_ctor_get(v___x_2572_, 1);
lean_inc(v_snd_2578_);
lean_dec_ref(v___x_2572_);
v___x_2579_ = lean_box(0);
v___x_2580_ = lean_apply_5(v_postNode_2559_, v_val_2571_, v_i_2569_, v_children_2570_, v___x_2579_, v_snd_2578_);
v_fst_2581_ = lean_ctor_get(v___x_2580_, 0);
v_snd_2582_ = lean_ctor_get(v___x_2580_, 1);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2584_ = v___x_2580_;
v_isShared_2585_ = v_isSharedCheck_2592_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_snd_2582_);
lean_inc(v_fst_2581_);
lean_dec(v___x_2580_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2592_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_fst_2581_);
v___x_2587_ = v___x_2576_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_fst_2581_);
v___x_2587_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2589_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2587_);
v___x_2589_ = v___x_2584_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_snd_2582_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
else
{
lean_object* v_snd_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v_fst_2600_; lean_object* v_snd_2601_; lean_object* v___x_2602_; lean_object* v_fst_2603_; lean_object* v_snd_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2612_; 
v_snd_2595_ = lean_ctor_get(v___x_2572_, 1);
lean_inc(v_snd_2595_);
lean_dec_ref(v___x_2572_);
v___x_2596_ = l_Lean_Elab_Info_updateContext_x3f(v_x_2560_, v_i_2569_);
v___x_2597_ = l_Lean_PersistentArray_toList___redArg(v_children_2570_);
v___x_2598_ = lean_box(0);
lean_inc_ref(v_postNode_2559_);
v___x_2599_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2558_, v_postNode_2559_, v___x_2596_, v___x_2597_, v___x_2598_, v_snd_2595_);
v_fst_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_fst_2600_);
v_snd_2601_ = lean_ctor_get(v___x_2599_, 1);
lean_inc(v_snd_2601_);
lean_dec_ref(v___x_2599_);
v___x_2602_ = lean_apply_5(v_postNode_2559_, v_val_2571_, v_i_2569_, v_children_2570_, v_fst_2600_, v_snd_2601_);
v_fst_2603_ = lean_ctor_get(v___x_2602_, 0);
v_snd_2604_ = lean_ctor_get(v___x_2602_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2606_ = v___x_2602_;
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_snd_2604_);
lean_inc(v_fst_2603_);
lean_dec(v___x_2602_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_fst_2603_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2608_);
v___x_2610_ = v___x_2606_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_snd_2604_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
default: 
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec_ref_known(v_x_2561_, 1);
lean_dec(v_x_2560_);
lean_dec_ref(v_postNode_2559_);
lean_dec_ref(v_preNode_2558_);
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___y_2562_);
return v___x_2614_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_2615_, lean_object* v_postNode_2616_, lean_object* v___x_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v___y_2620_){
_start:
{
if (lean_obj_tag(v_x_2618_) == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
lean_dec(v___x_2617_);
lean_dec_ref(v_postNode_2616_);
lean_dec_ref(v_preNode_2615_);
v___x_2621_ = l_List_reverse___redArg(v_x_2619_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___y_2620_);
return v___x_2622_;
}
else
{
lean_object* v_head_2623_; lean_object* v_tail_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2635_; 
v_head_2623_ = lean_ctor_get(v_x_2618_, 0);
v_tail_2624_ = lean_ctor_get(v_x_2618_, 1);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_x_2618_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2626_ = v_x_2618_;
v_isShared_2627_ = v_isSharedCheck_2635_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_tail_2624_);
lean_inc(v_head_2623_);
lean_dec(v_x_2618_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2635_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v_fst_2629_; lean_object* v_snd_2630_; lean_object* v___x_2632_; 
lean_inc(v___x_2617_);
lean_inc_ref(v_postNode_2616_);
lean_inc_ref(v_preNode_2615_);
v___x_2628_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2615_, v_postNode_2616_, v___x_2617_, v_head_2623_, v___y_2620_);
v_fst_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_fst_2629_);
v_snd_2630_ = lean_ctor_get(v___x_2628_, 1);
lean_inc(v_snd_2630_);
lean_dec_ref(v___x_2628_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 1, v_x_2619_);
lean_ctor_set(v___x_2626_, 0, v_fst_2629_);
v___x_2632_ = v___x_2626_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_fst_2629_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_x_2619_);
v___x_2632_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
v_x_2618_ = v_tail_2624_;
v_x_2619_ = v___x_2632_;
v___y_2620_ = v_snd_2630_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(lean_object* v_postNode_2636_, lean_object* v_ci_2637_, lean_object* v_i_2638_, lean_object* v_cs_2639_, lean_object* v_x_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = lean_apply_4(v_postNode_2636_, v_ci_2637_, v_i_2638_, v_cs_2639_, v___y_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed(lean_object* v_postNode_2643_, lean_object* v_ci_2644_, lean_object* v_i_2645_, lean_object* v_cs_2646_, lean_object* v_x_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0(v_postNode_2643_, v_ci_2644_, v_i_2645_, v_cs_2646_, v_x_2647_, v___y_2648_);
lean_dec(v_x_2647_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0(lean_object* v_preNode_2650_, lean_object* v_postNode_2651_, lean_object* v_ctx_x3f_2652_, lean_object* v_t_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___f_2655_; lean_object* v___x_2656_; lean_object* v_snd_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2665_; 
v___f_2655_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2655_, 0, v_postNode_2651_);
v___x_2656_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2650_, v___f_2655_, v_ctx_x3f_2652_, v_t_2653_, v___y_2654_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2706_, lean_object* v_msg_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg(v_msg_2707_, v___y_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0(lean_object* v_00_u03b1_2710_, lean_object* v_preNode_2711_, lean_object* v_postNode_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg(v_preNode_2711_, v_postNode_2712_, v_x_2713_, v_x_2714_, v___y_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2717_, lean_object* v_preNode_2718_, lean_object* v_postNode_2719_, lean_object* v___x_2720_, lean_object* v_x_2721_, lean_object* v_x_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__2___redArg(v_preNode_2718_, v_postNode_2719_, v___x_2720_, v_x_2721_, v_x_2722_, v___y_2723_);
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
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v_nbuckets_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2937_ = lean_array_get_size(v_data_2936_);
v___x_2938_ = lean_unsigned_to_nat(2u);
v_nbuckets_2939_ = lean_nat_mul(v___x_2937_, v___x_2938_);
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_mk_array(v_nbuckets_2939_, v___x_2941_);
v___x_2943_ = lean_array_propagate_mark(v_data_2936_, v___x_2942_);
v___x_2944_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2940_, v_data_2936_, v___x_2943_);
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
lean_dec_ref_known(v_a_2994_, 3);
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
lean_dec_ref_known(v___x_3010_, 1);
return v_a_3011_;
}
else
{
lean_object* v_a_3012_; size_t v___x_3013_; size_t v___x_3014_; 
v_a_3012_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3010_, 1);
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
lean_dec_ref_known(v_a_3024_, 3);
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
lean_dec_ref_known(v___x_3042_, 1);
return v_a_3043_;
}
else
{
lean_object* v_a_3044_; size_t v___x_3045_; size_t v___x_3046_; 
v_a_3044_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3042_, 1);
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
v_representative_3196_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_3193_, v_id_3195_);
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
lean_dec_ref_known(v_a_3208_, 3);
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
lean_dec_ref_known(v___x_3228_, 1);
return v_a_3229_;
}
else
{
lean_object* v_a_3230_; size_t v___x_3231_; size_t v___x_3232_; 
v_a_3230_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3230_);
lean_dec_ref_known(v___x_3228_, 1);
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
v___x_3319_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3318_, v_id_3316_);
v___x_3320_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3318_, v_baseId_3317_);
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
lean_dec_ref_known(v_info_3328_, 1);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___f_3366_; lean_object* v___f_3367_; lean_object* v___f_3368_; lean_object* v___f_3369_; lean_object* v___f_3370_; lean_object* v___f_3371_; lean_object* v___f_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___f_3376_; lean_object* v___f_3377_; lean_object* v___f_3378_; lean_object* v___f_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3750__overap_3388_; lean_object* v___x_3389_; 
v___f_3366_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3367_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3368_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3369_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3370_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3371_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3372_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___f_3366_);
lean_ctor_set(v___x_3373_, 1, v___f_3367_);
v___x_3374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v___f_3368_);
lean_ctor_set(v___x_3374_, 2, v___f_3369_);
lean_ctor_set(v___x_3374_, 3, v___f_3370_);
lean_ctor_set(v___x_3374_, 4, v___f_3371_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
lean_ctor_set(v___x_3375_, 1, v___f_3372_);
lean_inc_ref_n(v___x_3375_, 6);
v___f_3376_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3376_, 0, v___x_3375_);
v___f_3377_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3377_, 0, v___x_3375_);
v___f_3378_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3378_, 0, v___x_3375_);
v___f_3379_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3379_, 0, v___x_3375_);
v___x_3380_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3380_, 0, lean_box(0));
lean_closure_set(v___x_3380_, 1, lean_box(0));
lean_closure_set(v___x_3380_, 2, v___x_3375_);
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v___f_3376_);
v___x_3382_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3382_, 0, lean_box(0));
lean_closure_set(v___x_3382_, 1, lean_box(0));
lean_closure_set(v___x_3382_, 2, v___x_3375_);
v___x_3383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
lean_ctor_set(v___x_3383_, 2, v___f_3377_);
lean_ctor_set(v___x_3383_, 3, v___f_3378_);
lean_ctor_set(v___x_3383_, 4, v___f_3379_);
v___x_3384_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3384_, 0, lean_box(0));
lean_closure_set(v___x_3384_, 1, lean_box(0));
lean_closure_set(v___x_3384_, 2, v___x_3375_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_box(0);
v___x_3387_ = l_instInhabitedOfMonad___redArg(v___x_3385_, v___x_3386_);
v___x_3750__overap_3388_ = lean_panic_fn_borrowed(v___x_3387_, v_msg_3364_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_apply_1(v___x_3750__overap_3388_, v___y_3365_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3390_, lean_object* v_postNode_3391_, lean_object* v_x_3392_, lean_object* v_x_3393_, lean_object* v___y_3394_){
_start:
{
switch(lean_obj_tag(v_x_3393_))
{
case 0:
{
lean_object* v_i_3395_; lean_object* v_t_3396_; lean_object* v___x_3397_; 
v_i_3395_ = lean_ctor_get(v_x_3393_, 0);
lean_inc_ref(v_i_3395_);
v_t_3396_ = lean_ctor_get(v_x_3393_, 1);
lean_inc_ref(v_t_3396_);
lean_dec_ref_known(v_x_3393_, 2);
v___x_3397_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3395_, v_x_3392_);
v_x_3392_ = v___x_3397_;
v_x_3393_ = v_t_3396_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3392_) == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec_ref_known(v_x_3393_, 2);
lean_dec_ref(v_postNode_3391_);
lean_dec_ref(v_preNode_3390_);
v___x_3399_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3400_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3399_, v___y_3394_);
return v___x_3400_;
}
else
{
lean_object* v_i_3401_; lean_object* v_children_3402_; lean_object* v_val_3403_; lean_object* v___x_3404_; lean_object* v_fst_3405_; uint8_t v___x_3406_; 
v_i_3401_ = lean_ctor_get(v_x_3393_, 0);
lean_inc_ref_n(v_i_3401_, 2);
v_children_3402_ = lean_ctor_get(v_x_3393_, 1);
lean_inc_ref_n(v_children_3402_, 2);
lean_dec_ref_known(v_x_3393_, 2);
v_val_3403_ = lean_ctor_get(v_x_3392_, 0);
lean_inc_n(v_val_3403_, 2);
lean_inc_ref(v_preNode_3390_);
v___x_3404_ = lean_apply_4(v_preNode_3390_, v_val_3403_, v_i_3401_, v_children_3402_, v___y_3394_);
v_fst_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_fst_3405_);
v___x_3406_ = lean_unbox(v_fst_3405_);
lean_dec(v_fst_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref(v_preNode_3390_);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_x_3392_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; 
v_unused_3426_ = lean_ctor_get(v_x_3392_, 0);
lean_dec(v_unused_3426_);
v___x_3408_ = v_x_3392_;
v_isShared_3409_ = v_isSharedCheck_3425_;
goto v_resetjp_3407_;
}
else
{
lean_dec(v_x_3392_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3425_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_snd_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v_fst_3413_; lean_object* v_snd_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3424_; 
v_snd_3410_ = lean_ctor_get(v___x_3404_, 1);
lean_inc(v_snd_3410_);
lean_dec_ref(v___x_3404_);
v___x_3411_ = lean_box(0);
v___x_3412_ = lean_apply_5(v_postNode_3391_, v_val_3403_, v_i_3401_, v_children_3402_, v___x_3411_, v_snd_3410_);
v_fst_3413_ = lean_ctor_get(v___x_3412_, 0);
v_snd_3414_ = lean_ctor_get(v___x_3412_, 1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3416_ = v___x_3412_;
v_isShared_3417_ = v_isSharedCheck_3424_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_snd_3414_);
lean_inc(v_fst_3413_);
lean_dec(v___x_3412_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3424_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v_fst_3413_);
v___x_3419_ = v___x_3408_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_fst_3413_);
v___x_3419_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3421_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3419_);
v___x_3421_ = v___x_3416_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_snd_3414_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
}
else
{
lean_object* v_snd_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v_fst_3432_; lean_object* v_snd_3433_; lean_object* v___x_3434_; lean_object* v_fst_3435_; lean_object* v_snd_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3444_; 
v_snd_3427_ = lean_ctor_get(v___x_3404_, 1);
lean_inc(v_snd_3427_);
lean_dec_ref(v___x_3404_);
v___x_3428_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3392_, v_i_3401_);
v___x_3429_ = l_Lean_PersistentArray_toList___redArg(v_children_3402_);
v___x_3430_ = lean_box(0);
lean_inc_ref(v_postNode_3391_);
v___x_3431_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3390_, v_postNode_3391_, v___x_3428_, v___x_3429_, v___x_3430_, v_snd_3427_);
v_fst_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_fst_3432_);
v_snd_3433_ = lean_ctor_get(v___x_3431_, 1);
lean_inc(v_snd_3433_);
lean_dec_ref(v___x_3431_);
v___x_3434_ = lean_apply_5(v_postNode_3391_, v_val_3403_, v_i_3401_, v_children_3402_, v_fst_3432_, v_snd_3433_);
v_fst_3435_ = lean_ctor_get(v___x_3434_, 0);
v_snd_3436_ = lean_ctor_get(v___x_3434_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3438_ = v___x_3434_;
v_isShared_3439_ = v_isSharedCheck_3444_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_snd_3436_);
lean_inc(v_fst_3435_);
lean_dec(v___x_3434_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3444_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3440_, 0, v_fst_3435_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_snd_3436_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
default: 
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
lean_dec_ref_known(v_x_3393_, 1);
lean_dec(v_x_3392_);
lean_dec_ref(v_postNode_3391_);
lean_dec_ref(v_preNode_3390_);
v___x_3445_ = lean_box(0);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
lean_ctor_set(v___x_3446_, 1, v___y_3394_);
return v___x_3446_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3447_, lean_object* v_postNode_3448_, lean_object* v___x_3449_, lean_object* v_x_3450_, lean_object* v_x_3451_, lean_object* v___y_3452_){
_start:
{
if (lean_obj_tag(v_x_3450_) == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec(v___x_3449_);
lean_dec_ref(v_postNode_3448_);
lean_dec_ref(v_preNode_3447_);
v___x_3453_ = l_List_reverse___redArg(v_x_3451_);
v___x_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
lean_ctor_set(v___x_3454_, 1, v___y_3452_);
return v___x_3454_;
}
else
{
lean_object* v_head_3455_; lean_object* v_tail_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3467_; 
v_head_3455_ = lean_ctor_get(v_x_3450_, 0);
v_tail_3456_ = lean_ctor_get(v_x_3450_, 1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_x_3450_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3458_ = v_x_3450_;
v_isShared_3459_ = v_isSharedCheck_3467_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_tail_3456_);
lean_inc(v_head_3455_);
lean_dec(v_x_3450_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3467_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v_fst_3461_; lean_object* v_snd_3462_; lean_object* v___x_3464_; 
lean_inc(v___x_3449_);
lean_inc_ref(v_postNode_3448_);
lean_inc_ref(v_preNode_3447_);
v___x_3460_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3447_, v_postNode_3448_, v___x_3449_, v_head_3455_, v___y_3452_);
v_fst_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_fst_3461_);
v_snd_3462_ = lean_ctor_get(v___x_3460_, 1);
lean_inc(v_snd_3462_);
lean_dec_ref(v___x_3460_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_x_3451_);
lean_ctor_set(v___x_3458_, 0, v_fst_3461_);
v___x_3464_ = v___x_3458_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_fst_3461_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_x_3451_);
v___x_3464_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
v_x_3450_ = v_tail_3456_;
v_x_3451_ = v___x_3464_;
v___y_3452_ = v_snd_3462_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3468_, lean_object* v_ci_3469_, lean_object* v_i_3470_, lean_object* v_cs_3471_, lean_object* v_x_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v___x_3474_; 
v___x_3474_ = lean_apply_4(v_postNode_3468_, v_ci_3469_, v_i_3470_, v_cs_3471_, v___y_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3475_, lean_object* v_ci_3476_, lean_object* v_i_3477_, lean_object* v_cs_3478_, lean_object* v_x_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3475_, v_ci_3476_, v_i_3477_, v_cs_3478_, v_x_3479_, v___y_3480_);
lean_dec(v_x_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3482_, lean_object* v_postNode_3483_, lean_object* v_ctx_x3f_3484_, lean_object* v_t_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v___f_3487_; lean_object* v___x_3488_; lean_object* v_snd_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3497_; 
v___f_3487_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3487_, 0, v_postNode_3483_);
v___x_3488_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3482_, v___f_3487_, v_ctx_x3f_3484_, v_t_3485_, v___y_3486_);
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
lean_dec_ref_known(v___x_3577_, 1);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3621_, lean_object* v_msg_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v_msg_3622_, v___y_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object* v_00_u03b1_3625_, lean_object* v_preNode_3626_, lean_object* v_postNode_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3626_, v_postNode_3627_, v_x_3628_, v_x_3629_, v___y_3630_);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3640_, lean_object* v_preNode_3641_, lean_object* v_postNode_3642_, lean_object* v___x_3643_, lean_object* v_x_3644_, lean_object* v_x_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3641_, v_postNode_3642_, v___x_3643_, v_x_3644_, v_x_3645_, v___y_3646_);
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
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v_nbuckets_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3707_ = lean_array_get_size(v_data_3706_);
v___x_3708_ = lean_unsigned_to_nat(2u);
v_nbuckets_3709_ = lean_nat_mul(v___x_3707_, v___x_3708_);
v___x_3710_ = lean_unsigned_to_nat(0u);
v___x_3711_ = lean_box(0);
v___x_3712_ = lean_mk_array(v_nbuckets_3709_, v___x_3711_);
v___x_3713_ = lean_array_propagate_mark(v_data_3706_, v___x_3712_);
v___x_3714_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v___x_3710_, v_data_3706_, v___x_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object* v_a_3715_, lean_object* v_x_3716_){
_start:
{
if (lean_obj_tag(v_x_3716_) == 0)
{
uint8_t v___x_3717_; 
v___x_3717_ = 0;
return v___x_3717_;
}
else
{
lean_object* v_key_3718_; lean_object* v_tail_3719_; uint8_t v___x_3720_; 
v_key_3718_ = lean_ctor_get(v_x_3716_, 0);
v_tail_3719_ = lean_ctor_get(v_x_3716_, 2);
v___x_3720_ = l_Lean_Lsp_instBEqRange_beq(v_key_3718_, v_a_3715_);
if (v___x_3720_ == 0)
{
v_x_3716_ = v_tail_3719_;
goto _start;
}
else
{
return v___x_3720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object* v_a_3722_, lean_object* v_x_3723_){
_start:
{
uint8_t v_res_3724_; lean_object* v_r_3725_; 
v_res_3724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3722_, v_x_3723_);
lean_dec(v_x_3723_);
lean_dec_ref(v_a_3722_);
v_r_3725_ = lean_box(v_res_3724_);
return v_r_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object* v_m_3726_, lean_object* v_a_3727_, lean_object* v_b_3728_){
_start:
{
lean_object* v_size_3729_; lean_object* v_buckets_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3773_; 
v_size_3729_ = lean_ctor_get(v_m_3726_, 0);
v_buckets_3730_ = lean_ctor_get(v_m_3726_, 1);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_m_3726_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3732_ = v_m_3726_;
v_isShared_3733_ = v_isSharedCheck_3773_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_buckets_3730_);
lean_inc(v_size_3729_);
lean_dec(v_m_3726_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3773_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3734_; uint64_t v___x_3735_; uint64_t v___x_3736_; uint64_t v___x_3737_; uint64_t v_fold_3738_; uint64_t v___x_3739_; uint64_t v___x_3740_; uint64_t v___x_3741_; size_t v___x_3742_; size_t v___x_3743_; size_t v___x_3744_; size_t v___x_3745_; size_t v___x_3746_; lean_object* v_bkt_3747_; uint8_t v___x_3748_; 
v___x_3734_ = lean_array_get_size(v_buckets_3730_);
v___x_3735_ = l_Lean_Lsp_instHashableRange_hash(v_a_3727_);
v___x_3736_ = 32ULL;
v___x_3737_ = lean_uint64_shift_right(v___x_3735_, v___x_3736_);
v_fold_3738_ = lean_uint64_xor(v___x_3735_, v___x_3737_);
v___x_3739_ = 16ULL;
v___x_3740_ = lean_uint64_shift_right(v_fold_3738_, v___x_3739_);
v___x_3741_ = lean_uint64_xor(v_fold_3738_, v___x_3740_);
v___x_3742_ = lean_uint64_to_usize(v___x_3741_);
v___x_3743_ = lean_usize_of_nat(v___x_3734_);
v___x_3744_ = ((size_t)1ULL);
v___x_3745_ = lean_usize_sub(v___x_3743_, v___x_3744_);
v___x_3746_ = lean_usize_land(v___x_3742_, v___x_3745_);
v_bkt_3747_ = lean_array_uget_borrowed(v_buckets_3730_, v___x_3746_);
v___x_3748_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3727_, v_bkt_3747_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; lean_object* v_size_x27_3750_; lean_object* v___x_3751_; lean_object* v_buckets_x27_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3749_ = lean_unsigned_to_nat(1u);
v_size_x27_3750_ = lean_nat_add(v_size_3729_, v___x_3749_);
lean_dec(v_size_3729_);
lean_inc(v_bkt_3747_);
v___x_3751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3751_, 0, v_a_3727_);
lean_ctor_set(v___x_3751_, 1, v_b_3728_);
lean_ctor_set(v___x_3751_, 2, v_bkt_3747_);
v_buckets_x27_3752_ = lean_array_uset(v_buckets_3730_, v___x_3746_, v___x_3751_);
v___x_3753_ = lean_unsigned_to_nat(4u);
v___x_3754_ = lean_nat_mul(v_size_x27_3750_, v___x_3753_);
v___x_3755_ = lean_unsigned_to_nat(3u);
v___x_3756_ = lean_nat_div(v___x_3754_, v___x_3755_);
lean_dec(v___x_3754_);
v___x_3757_ = lean_array_get_size(v_buckets_x27_3752_);
v___x_3758_ = lean_nat_dec_le(v___x_3756_, v___x_3757_);
lean_dec(v___x_3756_);
if (v___x_3758_ == 0)
{
lean_object* v_val_3759_; lean_object* v___x_3761_; 
v_val_3759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_buckets_x27_3752_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 1, v_val_3759_);
lean_ctor_set(v___x_3732_, 0, v_size_x27_3750_);
v___x_3761_ = v___x_3732_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_size_x27_3750_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_val_3759_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
else
{
lean_object* v___x_3764_; 
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 1, v_buckets_x27_3752_);
lean_ctor_set(v___x_3732_, 0, v_size_x27_3750_);
v___x_3764_ = v___x_3732_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_size_x27_3750_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_buckets_x27_3752_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
else
{
lean_object* v___x_3766_; lean_object* v_buckets_x27_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3771_; 
lean_inc(v_bkt_3747_);
v___x_3766_ = lean_box(0);
v_buckets_x27_3767_ = lean_array_uset(v_buckets_3730_, v___x_3746_, v___x_3766_);
v___x_3768_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3727_, v_b_3728_, v_bkt_3747_);
v___x_3769_ = lean_array_uset(v_buckets_x27_3767_, v___x_3746_, v___x_3768_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 1, v___x_3769_);
v___x_3771_ = v___x_3732_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_size_3729_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object* v_as_3774_, size_t v_sz_3775_, size_t v_i_3776_, lean_object* v_b_3777_){
_start:
{
lean_object* v_a_3779_; uint8_t v___x_3783_; 
v___x_3783_ = lean_usize_dec_lt(v_i_3776_, v_sz_3775_);
if (v___x_3783_ == 0)
{
return v_b_3777_;
}
else
{
lean_object* v_a_3784_; uint8_t v_isBinder_3785_; 
v_a_3784_ = lean_array_uget_borrowed(v_as_3774_, v_i_3776_);
v_isBinder_3785_ = lean_ctor_get_uint8(v_a_3784_, sizeof(void*)*6);
if (v_isBinder_3785_ == 1)
{
lean_object* v_ident_3786_; lean_object* v_range_3787_; lean_object* v___x_3788_; 
v_ident_3786_ = lean_ctor_get(v_a_3784_, 0);
v_range_3787_ = lean_ctor_get(v_a_3784_, 2);
lean_inc_ref(v_ident_3786_);
lean_inc_ref(v_range_3787_);
v___x_3788_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_b_3777_, v_range_3787_, v_ident_3786_);
v_a_3779_ = v___x_3788_;
goto v___jp_3778_;
}
else
{
v_a_3779_ = v_b_3777_;
goto v___jp_3778_;
}
}
v___jp_3778_:
{
size_t v___x_3780_; size_t v___x_3781_; 
v___x_3780_ = ((size_t)1ULL);
v___x_3781_ = lean_usize_add(v_i_3776_, v___x_3780_);
v_i_3776_ = v___x_3781_;
v_b_3777_ = v_a_3779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object* v_as_3789_, lean_object* v_sz_3790_, lean_object* v_i_3791_, lean_object* v_b_3792_){
_start:
{
size_t v_sz_boxed_3793_; size_t v_i_boxed_3794_; lean_object* v_res_3795_; 
v_sz_boxed_3793_ = lean_unbox_usize(v_sz_3790_);
lean_dec(v_sz_3790_);
v_i_boxed_3794_ = lean_unbox_usize(v_i_3791_);
lean_dec(v_i_3791_);
v_res_3795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_as_3789_, v_sz_boxed_3793_, v_i_boxed_3794_, v_b_3792_);
lean_dec_ref(v_as_3789_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object* v___x_3796_, lean_object* v_as_3797_, size_t v_sz_3798_, size_t v_i_3799_, lean_object* v_b_3800_){
_start:
{
lean_object* v_a_3802_; uint8_t v___x_3806_; 
v___x_3806_ = lean_usize_dec_lt(v_i_3799_, v_sz_3798_);
if (v___x_3806_ == 0)
{
return v_b_3800_;
}
else
{
lean_object* v_a_3807_; lean_object* v_ident_3810_; lean_object* v_range_3811_; lean_object* v_stx_3812_; lean_object* v_ci_3813_; lean_object* v_info_3814_; uint8_t v_isBinder_3815_; uint8_t v___x_3816_; 
v_a_3807_ = lean_array_uget(v_as_3797_, v_i_3799_);
v_ident_3810_ = lean_ctor_get(v_a_3807_, 0);
v_range_3811_ = lean_ctor_get(v_a_3807_, 2);
v_stx_3812_ = lean_ctor_get(v_a_3807_, 3);
v_ci_3813_ = lean_ctor_get(v_a_3807_, 4);
v_info_3814_ = lean_ctor_get(v_a_3807_, 5);
v_isBinder_3815_ = lean_ctor_get_uint8(v_a_3807_, sizeof(void*)*6);
v___x_3816_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v___x_3796_, v_ident_3810_);
if (v___x_3816_ == 0)
{
if (v___x_3816_ == 0)
{
goto v___jp_3808_;
}
else
{
if (v___x_3816_ == 0)
{
lean_dec(v_a_3807_);
v_a_3802_ = v_b_3800_;
goto v___jp_3801_;
}
else
{
goto v___jp_3808_;
}
}
}
else
{
lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3828_; 
lean_inc_ref(v_info_3814_);
lean_inc_ref(v_ci_3813_);
lean_inc(v_stx_3812_);
lean_inc_ref(v_range_3811_);
lean_inc_ref(v_ident_3810_);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_a_3807_);
if (v_isSharedCheck_3828_ == 0)
{
lean_object* v_unused_3829_; lean_object* v_unused_3830_; lean_object* v_unused_3831_; lean_object* v_unused_3832_; lean_object* v_unused_3833_; lean_object* v_unused_3834_; 
v_unused_3829_ = lean_ctor_get(v_a_3807_, 5);
lean_dec(v_unused_3829_);
v_unused_3830_ = lean_ctor_get(v_a_3807_, 4);
lean_dec(v_unused_3830_);
v_unused_3831_ = lean_ctor_get(v_a_3807_, 3);
lean_dec(v_unused_3831_);
v_unused_3832_ = lean_ctor_get(v_a_3807_, 2);
lean_dec(v_unused_3832_);
v_unused_3833_ = lean_ctor_get(v_a_3807_, 1);
lean_dec(v_unused_3833_);
v_unused_3834_ = lean_ctor_get(v_a_3807_, 0);
lean_dec(v_unused_3834_);
v___x_3818_ = v_a_3807_;
v_isShared_3819_ = v_isSharedCheck_3828_;
goto v_resetjp_3817_;
}
else
{
lean_dec(v_a_3807_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3828_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
lean_inc_ref(v_ident_3810_);
v___x_3820_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v___x_3796_, v_ident_3810_);
v___x_3821_ = lean_unsigned_to_nat(1u);
v___x_3822_ = lean_mk_empty_array_with_capacity(v___x_3821_);
v___x_3823_ = lean_array_push(v___x_3822_, v_ident_3810_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 1, v___x_3823_);
lean_ctor_set(v___x_3818_, 0, v___x_3820_);
v___x_3825_ = v___x_3818_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3827_, 2, v_range_3811_);
lean_ctor_set(v_reuseFailAlloc_3827_, 3, v_stx_3812_);
lean_ctor_set(v_reuseFailAlloc_3827_, 4, v_ci_3813_);
lean_ctor_set(v_reuseFailAlloc_3827_, 5, v_info_3814_);
lean_ctor_set_uint8(v_reuseFailAlloc_3827_, sizeof(void*)*6, v_isBinder_3815_);
v___x_3825_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_array_push(v_b_3800_, v___x_3825_);
v_a_3802_ = v___x_3826_;
goto v___jp_3801_;
}
}
}
v___jp_3808_:
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_array_push(v_b_3800_, v_a_3807_);
v_a_3802_ = v___x_3809_;
goto v___jp_3801_;
}
}
v___jp_3801_:
{
size_t v___x_3803_; size_t v___x_3804_; 
v___x_3803_ = ((size_t)1ULL);
v___x_3804_ = lean_usize_add(v_i_3799_, v___x_3803_);
v_i_3799_ = v___x_3804_;
v_b_3800_ = v_a_3802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object* v___x_3835_, lean_object* v_as_3836_, lean_object* v_sz_3837_, lean_object* v_i_3838_, lean_object* v_b_3839_){
_start:
{
size_t v_sz_boxed_3840_; size_t v_i_boxed_3841_; lean_object* v_res_3842_; 
v_sz_boxed_3840_ = lean_unbox_usize(v_sz_3837_);
lean_dec(v_sz_3837_);
v_i_boxed_3841_ = lean_unbox_usize(v_i_3838_);
lean_dec(v_i_3838_);
v_res_3842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3835_, v_as_3836_, v_sz_boxed_3840_, v_i_boxed_3841_, v_b_3839_);
lean_dec_ref(v_as_3836_);
lean_dec_ref(v___x_3835_);
return v_res_3842_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__0(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3843_ = lean_box(0);
v___x_3844_ = lean_unsigned_to_nat(16u);
v___x_3845_ = lean_mk_array(v___x_3844_, v___x_3843_);
return v___x_3845_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__1(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v_posMap_3848_; 
v___x_3846_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__0, &l_Lean_Server_combineIdents___closed__0_once, _init_l_Lean_Server_combineIdents___closed__0);
v___x_3847_ = lean_unsigned_to_nat(0u);
v_posMap_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_posMap_3848_, 0, v___x_3847_);
lean_ctor_set(v_posMap_3848_, 1, v___x_3846_);
return v_posMap_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object* v_trees_3849_, lean_object* v_refs_3850_){
_start:
{
lean_object* v_posMap_3851_; size_t v_sz_3852_; size_t v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v_posMap_3851_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__1, &l_Lean_Server_combineIdents___closed__1_once, _init_l_Lean_Server_combineIdents___closed__1);
v_sz_3852_ = lean_array_size(v_refs_3850_);
v___x_3853_ = ((size_t)0ULL);
v___x_3854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_refs_3850_, v_sz_3852_, v___x_3853_, v_posMap_3851_);
v___x_3855_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3849_, v_refs_3850_, v___x_3854_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v___x_3855_);
lean_dec_ref(v___x_3855_);
v___x_3857_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_3858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3856_, v_refs_3850_, v_sz_3852_, v___x_3853_, v___x_3857_);
lean_dec_ref(v___x_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object* v_trees_3859_, lean_object* v_refs_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_Server_combineIdents(v_trees_3859_, v_refs_3860_);
lean_dec_ref(v_refs_3860_);
lean_dec_ref(v_trees_3859_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object* v_00_u03b2_3862_, lean_object* v_m_3863_, lean_object* v_a_3864_, lean_object* v_b_3865_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_m_3863_, v_a_3864_, v_b_3865_);
return v___x_3866_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object* v_00_u03b2_3867_, lean_object* v_a_3868_, lean_object* v_x_3869_){
_start:
{
uint8_t v___x_3870_; 
v___x_3870_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3868_, v_x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3871_, lean_object* v_a_3872_, lean_object* v_x_3873_){
_start:
{
uint8_t v_res_3874_; lean_object* v_r_3875_; 
v_res_3874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(v_00_u03b2_3871_, v_a_3872_, v_x_3873_);
lean_dec(v_x_3873_);
lean_dec_ref(v_a_3872_);
v_r_3875_ = lean_box(v_res_3874_);
return v_r_3875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object* v_00_u03b2_3876_, lean_object* v_data_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_data_3877_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object* v_00_u03b2_3879_, lean_object* v_a_3880_, lean_object* v_b_3881_, lean_object* v_x_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3880_, v_b_3881_, v_x_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3884_, lean_object* v_i_3885_, lean_object* v_source_3886_, lean_object* v_target_3887_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v_i_3885_, v_source_3886_, v_target_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3889_, lean_object* v_x_3890_, lean_object* v_x_3891_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3890_, v_x_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object* v_hi_3893_, lean_object* v_pivot_3894_, lean_object* v_as_3895_, lean_object* v_i_3896_, lean_object* v_k_3897_){
_start:
{
uint8_t v___x_3902_; 
v___x_3902_ = lean_nat_dec_lt(v_k_3897_, v_hi_3893_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec(v_k_3897_);
v___x_3903_ = lean_array_fswap(v_as_3895_, v_i_3896_, v_hi_3893_);
v___x_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3904_, 0, v_i_3896_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
return v___x_3904_;
}
else
{
lean_object* v___x_3905_; lean_object* v_range_3906_; lean_object* v_range_3907_; uint8_t v___x_3908_; 
v___x_3905_ = lean_array_fget_borrowed(v_as_3895_, v_k_3897_);
v_range_3906_ = lean_ctor_get(v___x_3905_, 2);
v_range_3907_ = lean_ctor_get(v_pivot_3894_, 2);
v___x_3908_ = l_Lean_Lsp_instOrdRange_ord(v_range_3906_, v_range_3907_);
if (v___x_3908_ == 0)
{
if (v___x_3902_ == 0)
{
goto v___jp_3898_;
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3909_ = lean_array_fswap(v_as_3895_, v_i_3896_, v_k_3897_);
v___x_3910_ = lean_unsigned_to_nat(1u);
v___x_3911_ = lean_nat_add(v_i_3896_, v___x_3910_);
lean_dec(v_i_3896_);
v___x_3912_ = lean_nat_add(v_k_3897_, v___x_3910_);
lean_dec(v_k_3897_);
v_as_3895_ = v___x_3909_;
v_i_3896_ = v___x_3911_;
v_k_3897_ = v___x_3912_;
goto _start;
}
}
else
{
goto v___jp_3898_;
}
}
v___jp_3898_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = lean_unsigned_to_nat(1u);
v___x_3900_ = lean_nat_add(v_k_3897_, v___x_3899_);
lean_dec(v_k_3897_);
v_k_3897_ = v___x_3900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object* v_hi_3914_, lean_object* v_pivot_3915_, lean_object* v_as_3916_, lean_object* v_i_3917_, lean_object* v_k_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3914_, v_pivot_3915_, v_as_3916_, v_i_3917_, v_k_3918_);
lean_dec_ref(v_pivot_3915_);
lean_dec(v_hi_3914_);
return v_res_3919_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3920_, lean_object* v_x1_3921_, lean_object* v_x2_3922_){
_start:
{
lean_object* v_range_3923_; lean_object* v_range_3924_; uint8_t v___x_3925_; 
v_range_3923_ = lean_ctor_get(v_x1_3921_, 2);
v_range_3924_ = lean_ctor_get(v_x2_3922_, 2);
v___x_3925_ = l_Lean_Lsp_instOrdRange_ord(v_range_3923_, v_range_3924_);
if (v___x_3925_ == 0)
{
return v___x_3920_;
}
else
{
uint8_t v___x_3926_; 
v___x_3926_ = 0;
return v___x_3926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3927_, lean_object* v_x1_3928_, lean_object* v_x2_3929_){
_start:
{
uint8_t v___x_2120__boxed_3930_; uint8_t v_res_3931_; lean_object* v_r_3932_; 
v___x_2120__boxed_3930_ = lean_unbox(v___x_3927_);
v_res_3931_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_2120__boxed_3930_, v_x1_3928_, v_x2_3929_);
lean_dec_ref(v_x2_3929_);
lean_dec_ref(v_x1_3928_);
v_r_3932_ = lean_box(v_res_3931_);
return v_r_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_n_3933_, lean_object* v_as_3934_, lean_object* v_lo_3935_, lean_object* v_hi_3936_){
_start:
{
lean_object* v___y_3938_; uint8_t v___x_3948_; 
v___x_3948_ = lean_nat_dec_lt(v_lo_3935_, v_hi_3936_);
if (v___x_3948_ == 0)
{
lean_dec(v_lo_3935_);
return v_as_3934_;
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v_mid_3951_; lean_object* v___y_3953_; lean_object* v___y_3959_; lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3949_ = lean_nat_add(v_lo_3935_, v_hi_3936_);
v___x_3950_ = lean_unsigned_to_nat(1u);
v_mid_3951_ = lean_nat_shiftr(v___x_3949_, v___x_3950_);
lean_dec(v___x_3949_);
v___x_3964_ = lean_array_fget_borrowed(v_as_3934_, v_mid_3951_);
v___x_3965_ = lean_array_fget_borrowed(v_as_3934_, v_lo_3935_);
v___x_3966_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3948_, v___x_3964_, v___x_3965_);
if (v___x_3966_ == 0)
{
v___y_3959_ = v_as_3934_;
goto v___jp_3958_;
}
else
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_array_fswap(v_as_3934_, v_lo_3935_, v_mid_3951_);
v___y_3959_ = v___x_3967_;
goto v___jp_3958_;
}
v___jp_3952_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; uint8_t v___x_3956_; 
v___x_3954_ = lean_array_fget_borrowed(v___y_3953_, v_mid_3951_);
v___x_3955_ = lean_array_fget_borrowed(v___y_3953_, v_hi_3936_);
v___x_3956_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3948_, v___x_3954_, v___x_3955_);
if (v___x_3956_ == 0)
{
lean_dec(v_mid_3951_);
v___y_3938_ = v___y_3953_;
goto v___jp_3937_;
}
else
{
lean_object* v___x_3957_; 
v___x_3957_ = lean_array_fswap(v___y_3953_, v_mid_3951_, v_hi_3936_);
lean_dec(v_mid_3951_);
v___y_3938_ = v___x_3957_;
goto v___jp_3937_;
}
}
v___jp_3958_:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v___x_3960_ = lean_array_fget_borrowed(v___y_3959_, v_hi_3936_);
v___x_3961_ = lean_array_fget_borrowed(v___y_3959_, v_lo_3935_);
v___x_3962_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3948_, v___x_3960_, v___x_3961_);
if (v___x_3962_ == 0)
{
v___y_3953_ = v___y_3959_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_array_fswap(v___y_3959_, v_lo_3935_, v_hi_3936_);
v___y_3953_ = v___x_3963_;
goto v___jp_3952_;
}
}
}
v___jp_3937_:
{
lean_object* v_pivot_3939_; lean_object* v___x_3940_; lean_object* v_fst_3941_; lean_object* v_snd_3942_; uint8_t v___x_3943_; 
v_pivot_3939_ = lean_array_fget(v___y_3938_, v_hi_3936_);
lean_inc_n(v_lo_3935_, 2);
v___x_3940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3936_, v_pivot_3939_, v___y_3938_, v_lo_3935_, v_lo_3935_);
lean_dec(v_pivot_3939_);
v_fst_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_fst_3941_);
v_snd_3942_ = lean_ctor_get(v___x_3940_, 1);
lean_inc(v_snd_3942_);
lean_dec_ref(v___x_3940_);
v___x_3943_ = lean_nat_dec_le(v_hi_3936_, v_fst_3941_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3933_, v_snd_3942_, v_lo_3935_, v_fst_3941_);
v___x_3945_ = lean_unsigned_to_nat(1u);
v___x_3946_ = lean_nat_add(v_fst_3941_, v___x_3945_);
lean_dec(v_fst_3941_);
v_as_3934_ = v___x_3944_;
v_lo_3935_ = v___x_3946_;
goto _start;
}
else
{
lean_dec(v_fst_3941_);
lean_dec(v_lo_3935_);
return v_snd_3942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_n_3968_, lean_object* v_as_3969_, lean_object* v_lo_3970_, lean_object* v_hi_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3968_, v_as_3969_, v_lo_3970_, v_hi_3971_);
lean_dec(v_hi_3971_);
lean_dec(v_n_3968_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object* v_x_3973_, lean_object* v_x_3974_){
_start:
{
if (lean_obj_tag(v_x_3974_) == 0)
{
return v_x_3973_;
}
else
{
lean_object* v_key_3975_; lean_object* v_snd_3976_; lean_object* v_value_3977_; lean_object* v_tail_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4018_; 
v_key_3975_ = lean_ctor_get(v_x_3974_, 0);
lean_inc(v_key_3975_);
v_snd_3976_ = lean_ctor_get(v_key_3975_, 1);
v_value_3977_ = lean_ctor_get(v_x_3974_, 1);
v_tail_3978_ = lean_ctor_get(v_x_3974_, 2);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_x_3974_);
if (v_isSharedCheck_4018_ == 0)
{
lean_object* v_unused_4019_; 
v_unused_4019_ = lean_ctor_get(v_x_3974_, 0);
lean_dec(v_unused_4019_);
v___x_3980_ = v_x_3974_;
v_isShared_3981_ = v_isSharedCheck_4018_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_tail_3978_);
lean_inc(v_value_3977_);
lean_dec(v_x_3974_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4018_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v_fst_3982_; lean_object* v_fst_3983_; lean_object* v_snd_3984_; lean_object* v___x_3985_; uint64_t v___x_3986_; uint64_t v___y_3988_; uint64_t v___y_4010_; 
v_fst_3982_ = lean_ctor_get(v_key_3975_, 0);
v_fst_3983_ = lean_ctor_get(v_snd_3976_, 0);
v_snd_3984_ = lean_ctor_get(v_snd_3976_, 1);
v___x_3985_ = lean_array_get_size(v_x_3973_);
v___x_3986_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_3982_);
if (lean_obj_tag(v_fst_3983_) == 0)
{
uint64_t v___x_4013_; 
v___x_4013_ = 11ULL;
v___y_3988_ = v___x_4013_;
goto v___jp_3987_;
}
else
{
lean_object* v_val_4014_; uint8_t v___x_4015_; 
v_val_4014_ = lean_ctor_get(v_fst_3983_, 0);
v___x_4015_ = lean_unbox(v_val_4014_);
if (v___x_4015_ == 0)
{
uint64_t v___x_4016_; 
v___x_4016_ = 13ULL;
v___y_4010_ = v___x_4016_;
goto v___jp_4009_;
}
else
{
uint64_t v___x_4017_; 
v___x_4017_ = 11ULL;
v___y_4010_ = v___x_4017_;
goto v___jp_4009_;
}
}
v___jp_3987_:
{
uint64_t v___x_3989_; uint64_t v___x_3990_; uint64_t v___x_3991_; uint64_t v___x_3992_; uint64_t v___x_3993_; uint64_t v_fold_3994_; uint64_t v___x_3995_; uint64_t v___x_3996_; uint64_t v___x_3997_; size_t v___x_3998_; size_t v___x_3999_; size_t v___x_4000_; size_t v___x_4001_; size_t v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4005_; 
v___x_3989_ = l_Lean_Lsp_instHashableRange_hash(v_snd_3984_);
v___x_3990_ = lean_uint64_mix_hash(v___y_3988_, v___x_3989_);
v___x_3991_ = lean_uint64_mix_hash(v___x_3986_, v___x_3990_);
v___x_3992_ = 32ULL;
v___x_3993_ = lean_uint64_shift_right(v___x_3991_, v___x_3992_);
v_fold_3994_ = lean_uint64_xor(v___x_3991_, v___x_3993_);
v___x_3995_ = 16ULL;
v___x_3996_ = lean_uint64_shift_right(v_fold_3994_, v___x_3995_);
v___x_3997_ = lean_uint64_xor(v_fold_3994_, v___x_3996_);
v___x_3998_ = lean_uint64_to_usize(v___x_3997_);
v___x_3999_ = lean_usize_of_nat(v___x_3985_);
v___x_4000_ = ((size_t)1ULL);
v___x_4001_ = lean_usize_sub(v___x_3999_, v___x_4000_);
v___x_4002_ = lean_usize_land(v___x_3998_, v___x_4001_);
v___x_4003_ = lean_array_uget_borrowed(v_x_3973_, v___x_4002_);
lean_inc(v___x_4003_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 2, v___x_4003_);
v___x_4005_ = v___x_3980_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_key_3975_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v_value_3977_);
lean_ctor_set(v_reuseFailAlloc_4008_, 2, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v___x_4006_; 
v___x_4006_ = lean_array_uset(v_x_3973_, v___x_4002_, v___x_4005_);
v_x_3973_ = v___x_4006_;
v_x_3974_ = v_tail_3978_;
goto _start;
}
}
v___jp_4009_:
{
uint64_t v___x_4011_; uint64_t v___x_4012_; 
v___x_4011_ = 13ULL;
v___x_4012_ = lean_uint64_mix_hash(v___y_4010_, v___x_4011_);
v___y_3988_ = v___x_4012_;
goto v___jp_3987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object* v_i_4020_, lean_object* v_source_4021_, lean_object* v_target_4022_){
_start:
{
lean_object* v___x_4023_; uint8_t v___x_4024_; 
v___x_4023_ = lean_array_get_size(v_source_4021_);
v___x_4024_ = lean_nat_dec_lt(v_i_4020_, v___x_4023_);
if (v___x_4024_ == 0)
{
lean_dec_ref(v_source_4021_);
lean_dec(v_i_4020_);
return v_target_4022_;
}
else
{
lean_object* v_es_4025_; lean_object* v___x_4026_; lean_object* v_source_4027_; lean_object* v_target_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_es_4025_ = lean_array_fget(v_source_4021_, v_i_4020_);
v___x_4026_ = lean_box(0);
v_source_4027_ = lean_array_fset(v_source_4021_, v_i_4020_, v___x_4026_);
v_target_4028_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_target_4022_, v_es_4025_);
v___x_4029_ = lean_unsigned_to_nat(1u);
v___x_4030_ = lean_nat_add(v_i_4020_, v___x_4029_);
lean_dec(v_i_4020_);
v_i_4020_ = v___x_4030_;
v_source_4021_ = v_source_4027_;
v_target_4022_ = v_target_4028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object* v_data_4032_){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v_nbuckets_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4033_ = lean_array_get_size(v_data_4032_);
v___x_4034_ = lean_unsigned_to_nat(2u);
v_nbuckets_4035_ = lean_nat_mul(v___x_4033_, v___x_4034_);
v___x_4036_ = lean_unsigned_to_nat(0u);
v___x_4037_ = lean_box(0);
v___x_4038_ = lean_mk_array(v_nbuckets_4035_, v___x_4037_);
v___x_4039_ = lean_array_propagate_mark(v_data_4032_, v___x_4038_);
v___x_4040_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v___x_4036_, v_data_4032_, v___x_4039_);
return v___x_4040_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object* v_x_4041_, lean_object* v_x_4042_){
_start:
{
if (lean_obj_tag(v_x_4041_) == 0)
{
if (lean_obj_tag(v_x_4042_) == 0)
{
uint8_t v___x_4043_; 
v___x_4043_ = 1;
return v___x_4043_;
}
else
{
uint8_t v___x_4044_; 
v___x_4044_ = 0;
return v___x_4044_;
}
}
else
{
if (lean_obj_tag(v_x_4042_) == 0)
{
uint8_t v___x_4045_; 
v___x_4045_ = 0;
return v___x_4045_;
}
else
{
lean_object* v_val_4046_; uint8_t v___x_4047_; 
v_val_4046_ = lean_ctor_get(v_x_4042_, 0);
v___x_4047_ = lean_unbox(v_val_4046_);
if (v___x_4047_ == 0)
{
lean_object* v_val_4048_; uint8_t v___x_4049_; 
v_val_4048_ = lean_ctor_get(v_x_4041_, 0);
v___x_4049_ = lean_unbox(v_val_4048_);
if (v___x_4049_ == 0)
{
uint8_t v___x_4050_; 
v___x_4050_ = 1;
return v___x_4050_;
}
else
{
uint8_t v___x_4051_; 
v___x_4051_ = lean_unbox(v_val_4046_);
return v___x_4051_;
}
}
else
{
lean_object* v_val_4052_; uint8_t v___x_4053_; 
v_val_4052_ = lean_ctor_get(v_x_4041_, 0);
v___x_4053_ = lean_unbox(v_val_4052_);
return v___x_4053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object* v_x_4054_, lean_object* v_x_4055_){
_start:
{
uint8_t v_res_4056_; lean_object* v_r_4057_; 
v_res_4056_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_x_4054_, v_x_4055_);
lean_dec(v_x_4055_);
lean_dec(v_x_4054_);
v_r_4057_ = lean_box(v_res_4056_);
return v_r_4057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object* v_a_4058_, lean_object* v_x_4059_){
_start:
{
if (lean_obj_tag(v_x_4059_) == 0)
{
lean_object* v___x_4060_; 
v___x_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_a_4058_);
return v___x_4060_;
}
else
{
lean_object* v_val_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4089_; 
v_val_4061_ = lean_ctor_get(v_x_4059_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_x_4059_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4063_ = v_x_4059_;
v_isShared_4064_ = v_isSharedCheck_4089_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_val_4061_);
lean_dec(v_x_4059_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4089_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v_ident_4065_; lean_object* v_aliases_4066_; lean_object* v_range_4067_; lean_object* v_stx_4068_; lean_object* v_ci_4069_; lean_object* v_info_4070_; uint8_t v_isBinder_4071_; lean_object* v_aliases_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4083_; 
v_ident_4065_ = lean_ctor_get(v_val_4061_, 0);
lean_inc_ref(v_ident_4065_);
v_aliases_4066_ = lean_ctor_get(v_val_4061_, 1);
lean_inc_ref(v_aliases_4066_);
v_range_4067_ = lean_ctor_get(v_val_4061_, 2);
lean_inc_ref(v_range_4067_);
v_stx_4068_ = lean_ctor_get(v_val_4061_, 3);
lean_inc(v_stx_4068_);
v_ci_4069_ = lean_ctor_get(v_val_4061_, 4);
lean_inc_ref(v_ci_4069_);
v_info_4070_ = lean_ctor_get(v_val_4061_, 5);
lean_inc_ref(v_info_4070_);
v_isBinder_4071_ = lean_ctor_get_uint8(v_val_4061_, sizeof(void*)*6);
lean_dec(v_val_4061_);
v_aliases_4072_ = lean_ctor_get(v_a_4058_, 1);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_a_4058_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; lean_object* v_unused_4085_; lean_object* v_unused_4086_; lean_object* v_unused_4087_; lean_object* v_unused_4088_; 
v_unused_4084_ = lean_ctor_get(v_a_4058_, 5);
lean_dec(v_unused_4084_);
v_unused_4085_ = lean_ctor_get(v_a_4058_, 4);
lean_dec(v_unused_4085_);
v_unused_4086_ = lean_ctor_get(v_a_4058_, 3);
lean_dec(v_unused_4086_);
v_unused_4087_ = lean_ctor_get(v_a_4058_, 2);
lean_dec(v_unused_4087_);
v_unused_4088_ = lean_ctor_get(v_a_4058_, 0);
lean_dec(v_unused_4088_);
v___x_4074_ = v_a_4058_;
v_isShared_4075_ = v_isSharedCheck_4083_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_aliases_4072_);
lean_dec(v_a_4058_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4083_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v___x_4078_; 
v___x_4076_ = l_Array_append___redArg(v_aliases_4066_, v_aliases_4072_);
lean_dec_ref(v_aliases_4072_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 5, v_info_4070_);
lean_ctor_set(v___x_4074_, 4, v_ci_4069_);
lean_ctor_set(v___x_4074_, 3, v_stx_4068_);
lean_ctor_set(v___x_4074_, 2, v_range_4067_);
lean_ctor_set(v___x_4074_, 1, v___x_4076_);
lean_ctor_set(v___x_4074_, 0, v_ident_4065_);
v___x_4078_ = v___x_4074_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_ident_4065_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4076_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_range_4067_);
lean_ctor_set(v_reuseFailAlloc_4082_, 3, v_stx_4068_);
lean_ctor_set(v_reuseFailAlloc_4082_, 4, v_ci_4069_);
lean_ctor_set(v_reuseFailAlloc_4082_, 5, v_info_4070_);
v___x_4078_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4080_; 
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*6, v_isBinder_4071_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v___x_4078_);
v___x_4080_ = v___x_4063_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4078_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_x_4092_){
_start:
{
if (lean_obj_tag(v_x_4092_) == 0)
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v_val_4095_; lean_object* v___x_4096_; 
v___x_4093_ = lean_box(0);
v___x_4094_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4090_, v___x_4093_);
v_val_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_val_4095_);
lean_dec(v___x_4094_);
v___x_4096_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4096_, 0, v_a_4091_);
lean_ctor_set(v___x_4096_, 1, v_val_4095_);
lean_ctor_set(v___x_4096_, 2, v_x_4092_);
return v___x_4096_;
}
else
{
lean_object* v_key_4097_; lean_object* v_value_4098_; lean_object* v_tail_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4126_; 
v_key_4097_ = lean_ctor_get(v_x_4092_, 0);
v_value_4098_ = lean_ctor_get(v_x_4092_, 1);
v_tail_4099_ = lean_ctor_get(v_x_4092_, 2);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_x_4092_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4101_ = v_x_4092_;
v_isShared_4102_ = v_isSharedCheck_4126_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_tail_4099_);
lean_inc(v_value_4098_);
lean_inc(v_key_4097_);
lean_dec(v_x_4092_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4126_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
uint8_t v___y_4104_; lean_object* v_fst_4115_; lean_object* v_snd_4116_; lean_object* v_fst_4117_; lean_object* v_snd_4118_; uint8_t v___x_4119_; 
v_fst_4115_ = lean_ctor_get(v_key_4097_, 0);
v_snd_4116_ = lean_ctor_get(v_key_4097_, 1);
v_fst_4117_ = lean_ctor_get(v_a_4091_, 0);
v_snd_4118_ = lean_ctor_get(v_a_4091_, 1);
v___x_4119_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4115_, v_fst_4117_);
if (v___x_4119_ == 0)
{
v___y_4104_ = v___x_4119_;
goto v___jp_4103_;
}
else
{
lean_object* v_fst_4120_; lean_object* v_snd_4121_; lean_object* v_fst_4122_; lean_object* v_snd_4123_; uint8_t v___x_4124_; 
v_fst_4120_ = lean_ctor_get(v_snd_4116_, 0);
v_snd_4121_ = lean_ctor_get(v_snd_4116_, 1);
v_fst_4122_ = lean_ctor_get(v_snd_4118_, 0);
v_snd_4123_ = lean_ctor_get(v_snd_4118_, 1);
v___x_4124_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4120_, v_fst_4122_);
if (v___x_4124_ == 0)
{
v___y_4104_ = v___x_4124_;
goto v___jp_4103_;
}
else
{
uint8_t v___x_4125_; 
v___x_4125_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4121_, v_snd_4123_);
v___y_4104_ = v___x_4125_;
goto v___jp_4103_;
}
}
v___jp_4103_:
{
if (v___y_4104_ == 0)
{
lean_object* v_tail_4105_; lean_object* v___x_4107_; 
v_tail_4105_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4090_, v_a_4091_, v_tail_4099_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 2, v_tail_4105_);
v___x_4107_ = v___x_4101_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_key_4097_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v_value_4098_);
lean_ctor_set(v_reuseFailAlloc_4108_, 2, v_tail_4105_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v_val_4111_; lean_object* v___x_4113_; 
lean_dec(v_key_4097_);
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_value_4098_);
v___x_4110_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4090_, v___x_4109_);
v_val_4111_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_val_4111_);
lean_dec(v___x_4110_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 1, v_val_4111_);
lean_ctor_set(v___x_4101_, 0, v_a_4091_);
v___x_4113_ = v___x_4101_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4091_);
lean_ctor_set(v_reuseFailAlloc_4114_, 1, v_val_4111_);
lean_ctor_set(v_reuseFailAlloc_4114_, 2, v_tail_4099_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_a_4127_, lean_object* v_x_4128_){
_start:
{
if (lean_obj_tag(v_x_4128_) == 0)
{
uint8_t v___x_4129_; 
v___x_4129_ = 0;
return v___x_4129_;
}
else
{
lean_object* v_key_4130_; lean_object* v_tail_4131_; uint8_t v___y_4133_; lean_object* v_fst_4135_; lean_object* v_snd_4136_; lean_object* v_fst_4137_; lean_object* v_snd_4138_; uint8_t v___x_4139_; 
v_key_4130_ = lean_ctor_get(v_x_4128_, 0);
v_tail_4131_ = lean_ctor_get(v_x_4128_, 2);
v_fst_4135_ = lean_ctor_get(v_key_4130_, 0);
v_snd_4136_ = lean_ctor_get(v_key_4130_, 1);
v_fst_4137_ = lean_ctor_get(v_a_4127_, 0);
v_snd_4138_ = lean_ctor_get(v_a_4127_, 1);
v___x_4139_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4135_, v_fst_4137_);
if (v___x_4139_ == 0)
{
v___y_4133_ = v___x_4139_;
goto v___jp_4132_;
}
else
{
lean_object* v_fst_4140_; lean_object* v_snd_4141_; lean_object* v_fst_4142_; lean_object* v_snd_4143_; uint8_t v___x_4144_; 
v_fst_4140_ = lean_ctor_get(v_snd_4136_, 0);
v_snd_4141_ = lean_ctor_get(v_snd_4136_, 1);
v_fst_4142_ = lean_ctor_get(v_snd_4138_, 0);
v_snd_4143_ = lean_ctor_get(v_snd_4138_, 1);
v___x_4144_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4140_, v_fst_4142_);
if (v___x_4144_ == 0)
{
v___y_4133_ = v___x_4144_;
goto v___jp_4132_;
}
else
{
uint8_t v___x_4145_; 
v___x_4145_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4141_, v_snd_4143_);
v___y_4133_ = v___x_4145_;
goto v___jp_4132_;
}
}
v___jp_4132_:
{
if (v___y_4133_ == 0)
{
v_x_4128_ = v_tail_4131_;
goto _start;
}
else
{
return v___y_4133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object* v_a_4146_, lean_object* v_x_4147_){
_start:
{
uint8_t v_res_4148_; lean_object* v_r_4149_; 
v_res_4148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4146_, v_x_4147_);
lean_dec(v_x_4147_);
lean_dec_ref(v_a_4146_);
v_r_4149_ = lean_box(v_res_4148_);
return v_r_4149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4150_, lean_object* v_m_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v___y_4154_; size_t v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v_snd_4160_; lean_object* v_size_4161_; lean_object* v_buckets_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4221_; 
v_snd_4160_ = lean_ctor_get(v_a_4152_, 1);
v_size_4161_ = lean_ctor_get(v_m_4151_, 0);
v_buckets_4162_ = lean_ctor_get(v_m_4151_, 1);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_m_4151_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4164_ = v_m_4151_;
v_isShared_4165_ = v_isSharedCheck_4221_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_buckets_4162_);
lean_inc(v_size_4161_);
lean_dec(v_m_4151_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4221_;
goto v_resetjp_4163_;
}
v___jp_4153_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = lean_array_uset(v___y_4156_, v___y_4155_, v___y_4154_);
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___y_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
return v___x_4159_;
}
v_resetjp_4163_:
{
lean_object* v_fst_4166_; lean_object* v_fst_4167_; lean_object* v_snd_4168_; lean_object* v___x_4169_; uint64_t v___x_4170_; uint64_t v___y_4172_; uint64_t v___y_4213_; 
v_fst_4166_ = lean_ctor_get(v_a_4152_, 0);
v_fst_4167_ = lean_ctor_get(v_snd_4160_, 0);
v_snd_4168_ = lean_ctor_get(v_snd_4160_, 1);
v___x_4169_ = lean_array_get_size(v_buckets_4162_);
v___x_4170_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4166_);
if (lean_obj_tag(v_fst_4167_) == 0)
{
uint64_t v___x_4216_; 
v___x_4216_ = 11ULL;
v___y_4172_ = v___x_4216_;
goto v___jp_4171_;
}
else
{
lean_object* v_val_4217_; uint8_t v___x_4218_; 
v_val_4217_ = lean_ctor_get(v_fst_4167_, 0);
v___x_4218_ = lean_unbox(v_val_4217_);
if (v___x_4218_ == 0)
{
uint64_t v___x_4219_; 
v___x_4219_ = 13ULL;
v___y_4213_ = v___x_4219_;
goto v___jp_4212_;
}
else
{
uint64_t v___x_4220_; 
v___x_4220_ = 11ULL;
v___y_4213_ = v___x_4220_;
goto v___jp_4212_;
}
}
v___jp_4171_:
{
uint64_t v___x_4173_; uint64_t v___x_4174_; uint64_t v___x_4175_; uint64_t v___x_4176_; uint64_t v___x_4177_; uint64_t v_fold_4178_; uint64_t v___x_4179_; uint64_t v___x_4180_; uint64_t v___x_4181_; size_t v___x_4182_; size_t v___x_4183_; size_t v___x_4184_; size_t v___x_4185_; size_t v___x_4186_; lean_object* v_bkt_4187_; uint8_t v___x_4188_; 
v___x_4173_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4168_);
v___x_4174_ = lean_uint64_mix_hash(v___y_4172_, v___x_4173_);
v___x_4175_ = lean_uint64_mix_hash(v___x_4170_, v___x_4174_);
v___x_4176_ = 32ULL;
v___x_4177_ = lean_uint64_shift_right(v___x_4175_, v___x_4176_);
v_fold_4178_ = lean_uint64_xor(v___x_4175_, v___x_4177_);
v___x_4179_ = 16ULL;
v___x_4180_ = lean_uint64_shift_right(v_fold_4178_, v___x_4179_);
v___x_4181_ = lean_uint64_xor(v_fold_4178_, v___x_4180_);
v___x_4182_ = lean_uint64_to_usize(v___x_4181_);
v___x_4183_ = lean_usize_of_nat(v___x_4169_);
v___x_4184_ = ((size_t)1ULL);
v___x_4185_ = lean_usize_sub(v___x_4183_, v___x_4184_);
v___x_4186_ = lean_usize_land(v___x_4182_, v___x_4185_);
v_bkt_4187_ = lean_array_uget_borrowed(v_buckets_4162_, v___x_4186_);
v___x_4188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4152_, v_bkt_4187_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4189_; lean_object* v_size_x27_4190_; lean_object* v___x_4191_; lean_object* v_buckets_x27_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4189_ = lean_unsigned_to_nat(1u);
v_size_x27_4190_ = lean_nat_add(v_size_4161_, v___x_4189_);
lean_dec(v_size_4161_);
lean_inc(v_bkt_4187_);
v___x_4191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4191_, 0, v_a_4152_);
lean_ctor_set(v___x_4191_, 1, v_a_4150_);
lean_ctor_set(v___x_4191_, 2, v_bkt_4187_);
v_buckets_x27_4192_ = lean_array_uset(v_buckets_4162_, v___x_4186_, v___x_4191_);
v___x_4193_ = lean_unsigned_to_nat(4u);
v___x_4194_ = lean_nat_mul(v_size_x27_4190_, v___x_4193_);
v___x_4195_ = lean_unsigned_to_nat(3u);
v___x_4196_ = lean_nat_div(v___x_4194_, v___x_4195_);
lean_dec(v___x_4194_);
v___x_4197_ = lean_array_get_size(v_buckets_x27_4192_);
v___x_4198_ = lean_nat_dec_le(v___x_4196_, v___x_4197_);
lean_dec(v___x_4196_);
if (v___x_4198_ == 0)
{
lean_object* v_val_4199_; lean_object* v___x_4201_; 
v_val_4199_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_buckets_x27_4192_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 1, v_val_4199_);
lean_ctor_set(v___x_4164_, 0, v_size_x27_4190_);
v___x_4201_ = v___x_4164_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_size_x27_4190_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v_val_4199_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
else
{
lean_object* v___x_4204_; 
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 1, v_buckets_x27_4192_);
lean_ctor_set(v___x_4164_, 0, v_size_x27_4190_);
v___x_4204_ = v___x_4164_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_size_x27_4190_);
lean_ctor_set(v_reuseFailAlloc_4205_, 1, v_buckets_x27_4192_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
else
{
lean_object* v___x_4206_; lean_object* v_buckets_x27_4207_; lean_object* v_bkt_x27_4208_; uint8_t v___x_4209_; 
lean_inc(v_bkt_4187_);
lean_del_object(v___x_4164_);
v___x_4206_ = lean_box(0);
v_buckets_x27_4207_ = lean_array_uset(v_buckets_4162_, v___x_4186_, v___x_4206_);
lean_inc_ref(v_a_4152_);
v_bkt_x27_4208_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4150_, v_a_4152_, v_bkt_4187_);
v___x_4209_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4152_, v_bkt_x27_4208_);
lean_dec_ref(v_a_4152_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = lean_unsigned_to_nat(1u);
v___x_4211_ = lean_nat_sub(v_size_4161_, v___x_4210_);
lean_dec(v_size_4161_);
v___y_4154_ = v_bkt_x27_4208_;
v___y_4155_ = v___x_4186_;
v___y_4156_ = v_buckets_x27_4207_;
v___y_4157_ = v___x_4211_;
goto v___jp_4153_;
}
else
{
v___y_4154_ = v_bkt_x27_4208_;
v___y_4155_ = v___x_4186_;
v___y_4156_ = v_buckets_x27_4207_;
v___y_4157_ = v_size_4161_;
goto v___jp_4153_;
}
}
}
v___jp_4212_:
{
uint64_t v___x_4214_; uint64_t v___x_4215_; 
v___x_4214_ = 13ULL;
v___x_4215_ = lean_uint64_mix_hash(v___y_4213_, v___x_4214_);
v___y_4172_ = v___x_4215_;
goto v___jp_4171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4222_, lean_object* v_as_4223_, size_t v_sz_4224_, size_t v_i_4225_, lean_object* v_b_4226_){
_start:
{
uint8_t v___x_4227_; 
v___x_4227_ = lean_usize_dec_lt(v_i_4225_, v_sz_4224_);
if (v___x_4227_ == 0)
{
return v_b_4226_;
}
else
{
lean_object* v_a_4228_; lean_object* v___y_4230_; 
v_a_4228_ = lean_array_uget_borrowed(v_as_4223_, v_i_4225_);
if (v_allowSimultaneousBinderUse_4222_ == 0)
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_box(0);
v___y_4230_ = v___x_4239_;
goto v___jp_4229_;
}
else
{
uint8_t v_isBinder_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_isBinder_4240_ = lean_ctor_get_uint8(v_a_4228_, sizeof(void*)*6);
v___x_4241_ = lean_box(v_isBinder_4240_);
v___x_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
v___y_4230_ = v___x_4242_;
goto v___jp_4229_;
}
v___jp_4229_:
{
lean_object* v_ident_4231_; lean_object* v_range_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; size_t v___x_4236_; size_t v___x_4237_; 
v_ident_4231_ = lean_ctor_get(v_a_4228_, 0);
v_range_4232_ = lean_ctor_get(v_a_4228_, 2);
lean_inc_ref(v_range_4232_);
v___x_4233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4233_, 0, v___y_4230_);
lean_ctor_set(v___x_4233_, 1, v_range_4232_);
lean_inc_ref(v_ident_4231_);
v___x_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4234_, 0, v_ident_4231_);
lean_ctor_set(v___x_4234_, 1, v___x_4233_);
lean_inc(v_a_4228_);
v___x_4235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4228_, v_b_4226_, v___x_4234_);
v___x_4236_ = ((size_t)1ULL);
v___x_4237_ = lean_usize_add(v_i_4225_, v___x_4236_);
v_i_4225_ = v___x_4237_;
v_b_4226_ = v___x_4235_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4243_, lean_object* v_as_4244_, lean_object* v_sz_4245_, lean_object* v_i_4246_, lean_object* v_b_4247_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4248_; size_t v_sz_boxed_4249_; size_t v_i_boxed_4250_; lean_object* v_res_4251_; 
v_allowSimultaneousBinderUse_boxed_4248_ = lean_unbox(v_allowSimultaneousBinderUse_4243_);
v_sz_boxed_4249_ = lean_unbox_usize(v_sz_4245_);
lean_dec(v_sz_4245_);
v_i_boxed_4250_ = lean_unbox_usize(v_i_4246_);
lean_dec(v_i_4246_);
v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4248_, v_as_4244_, v_sz_boxed_4249_, v_i_boxed_4250_, v_b_4247_);
lean_dec_ref(v_as_4244_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4252_, lean_object* v_x_4253_){
_start:
{
if (lean_obj_tag(v_x_4253_) == 0)
{
return v_x_4252_;
}
else
{
lean_object* v_value_4254_; lean_object* v_tail_4255_; lean_object* v___x_4256_; 
v_value_4254_ = lean_ctor_get(v_x_4253_, 1);
lean_inc(v_value_4254_);
v_tail_4255_ = lean_ctor_get(v_x_4253_, 2);
lean_inc(v_tail_4255_);
lean_dec_ref_known(v_x_4253_, 3);
v___x_4256_ = lean_array_push(v_x_4252_, v_value_4254_);
v_x_4252_ = v___x_4256_;
v_x_4253_ = v_tail_4255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4258_, size_t v_i_4259_, size_t v_stop_4260_, lean_object* v_b_4261_){
_start:
{
uint8_t v___x_4262_; 
v___x_4262_ = lean_usize_dec_eq(v_i_4259_, v_stop_4260_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; lean_object* v___x_4264_; size_t v___x_4265_; size_t v___x_4266_; 
v___x_4263_ = lean_array_uget_borrowed(v_as_4258_, v_i_4259_);
lean_inc(v___x_4263_);
v___x_4264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4261_, v___x_4263_);
v___x_4265_ = ((size_t)1ULL);
v___x_4266_ = lean_usize_add(v_i_4259_, v___x_4265_);
v_i_4259_ = v___x_4266_;
v_b_4261_ = v___x_4264_;
goto _start;
}
else
{
return v_b_4261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4268_, lean_object* v_i_4269_, lean_object* v_stop_4270_, lean_object* v_b_4271_){
_start:
{
size_t v_i_boxed_4272_; size_t v_stop_boxed_4273_; lean_object* v_res_4274_; 
v_i_boxed_4272_ = lean_unbox_usize(v_i_4269_);
lean_dec(v_i_4269_);
v_stop_boxed_4273_ = lean_unbox_usize(v_stop_4270_);
lean_dec(v_stop_4270_);
v_res_4274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4268_, v_i_boxed_4272_, v_stop_boxed_4273_, v_b_4271_);
lean_dec_ref(v_as_4268_);
return v_res_4274_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = lean_box(0);
v___x_4276_ = lean_unsigned_to_nat(16u);
v___x_4277_ = lean_mk_array(v___x_4276_, v___x_4275_);
return v___x_4277_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v_refsByIdAndRange_4280_; 
v___x_4278_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4279_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4280_, 0, v___x_4279_);
lean_ctor_set(v_refsByIdAndRange_4280_, 1, v___x_4278_);
return v_refsByIdAndRange_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4281_, uint8_t v_allowSimultaneousBinderUse_4282_){
_start:
{
lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4292_; lean_object* v___x_4299_; lean_object* v_refsByIdAndRange_4300_; size_t v_sz_4301_; size_t v___x_4302_; lean_object* v___x_4303_; lean_object* v_buckets_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4299_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4300_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4301_ = lean_array_size(v_refs_4281_);
v___x_4302_ = ((size_t)0ULL);
v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4282_, v_refs_4281_, v_sz_4301_, v___x_4302_, v_refsByIdAndRange_4300_);
v_buckets_4304_ = lean_ctor_get(v___x_4303_, 1);
lean_inc_ref(v_buckets_4304_);
lean_dec_ref(v___x_4303_);
v___x_4305_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4306_ = lean_array_get_size(v_buckets_4304_);
v___x_4307_ = lean_nat_dec_lt(v___x_4299_, v___x_4306_);
if (v___x_4307_ == 0)
{
lean_dec_ref(v_buckets_4304_);
v___y_4292_ = v___x_4305_;
goto v___jp_4291_;
}
else
{
size_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_usize_of_nat(v___x_4306_);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4304_, v___x_4302_, v___x_4308_, v___x_4305_);
lean_dec_ref(v_buckets_4304_);
v___y_4292_ = v___x_4309_;
goto v___jp_4291_;
}
v___jp_4283_:
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_nat_dec_le(v___y_4287_, v___y_4284_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; 
lean_dec(v___y_4284_);
lean_inc(v___y_4287_);
v___x_4289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4285_, v___y_4286_, v___y_4287_, v___y_4287_);
lean_dec(v___y_4287_);
lean_dec(v___y_4285_);
return v___x_4289_;
}
else
{
lean_object* v___x_4290_; 
v___x_4290_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4285_, v___y_4286_, v___y_4287_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec(v___y_4285_);
return v___x_4290_;
}
}
v___jp_4291_:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4293_ = lean_array_get_size(v___y_4292_);
v___x_4294_ = lean_unsigned_to_nat(0u);
v___x_4295_ = lean_nat_dec_eq(v___x_4293_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4296_ = lean_unsigned_to_nat(1u);
v___x_4297_ = lean_nat_sub(v___x_4293_, v___x_4296_);
v___x_4298_ = lean_nat_dec_le(v___x_4294_, v___x_4297_);
if (v___x_4298_ == 0)
{
lean_inc(v___x_4297_);
v___y_4284_ = v___x_4297_;
v___y_4285_ = v___x_4293_;
v___y_4286_ = v___y_4292_;
v___y_4287_ = v___x_4297_;
goto v___jp_4283_;
}
else
{
v___y_4284_ = v___x_4297_;
v___y_4285_ = v___x_4293_;
v___y_4286_ = v___y_4292_;
v___y_4287_ = v___x_4294_;
goto v___jp_4283_;
}
}
else
{
return v___y_4292_;
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
v___y_4498_ = v___x_4471_;
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
lean_object* v_a_4579_; uint8_t v___x_4583_; 
v___x_4583_ = lean_usize_dec_eq(v_i_4574_, v_stop_4575_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4584_; lean_object* v_module_4585_; uint8_t v_isPrivate_4586_; uint8_t v_isAll_4587_; uint8_t v_isMeta_4588_; lean_object* v_module_4589_; lean_object* v___x_4590_; 
v___x_4584_ = lean_array_uget_borrowed(v_as_4573_, v_i_4574_);
v_module_4585_ = lean_ctor_get(v___x_4584_, 0);
v_isPrivate_4586_ = lean_ctor_get_uint8(v___x_4584_, sizeof(void*)*1);
v_isAll_4587_ = lean_ctor_get_uint8(v___x_4584_, sizeof(void*)*1 + 1);
v_isMeta_4588_ = lean_ctor_get_uint8(v___x_4584_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4585_);
v_module_4589_ = l_String_toName(v_module_4585_);
lean_inc(v_module_4589_);
v___x_4590_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4589_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref_known(v___x_4590_, 1);
if (lean_obj_tag(v_a_4591_) == 1)
{
lean_object* v_val_4592_; uint8_t v___y_4594_; 
v_val_4592_ = lean_ctor_get(v_a_4591_, 0);
lean_inc(v_val_4592_);
lean_dec_ref_known(v_a_4591_, 1);
if (v_isMeta_4588_ == 0)
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
lean_ctor_set(v___x_4595_, 0, v_module_4589_);
lean_ctor_set(v___x_4595_, 1, v_val_4592_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*2, v_isAll_4587_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*2 + 1, v_isPrivate_4586_);
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*2 + 2, v___y_4594_);
v___x_4596_ = lean_array_push(v_b_4576_, v___x_4595_);
v_a_4579_ = v___x_4596_;
goto v___jp_4578_;
}
}
else
{
lean_dec(v_a_4591_);
lean_dec(v_module_4589_);
v_a_4579_ = v_b_4576_;
goto v___jp_4578_;
}
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
lean_dec(v_module_4589_);
lean_dec_ref(v_b_4576_);
v_a_4599_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4590_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4590_);
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
v___jp_4578_:
{
size_t v___x_4580_; size_t v___x_4581_; 
v___x_4580_ = ((size_t)1ULL);
v___x_4581_ = lean_usize_add(v_i_4574_, v___x_4580_);
v_i_4574_ = v___x_4581_;
v_b_4576_ = v_a_4579_;
goto _start;
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
v_k_4654_ = lean_ctor_get(v_impl_4650_, 1);
v_v_4655_ = lean_ctor_get(v_impl_4650_, 2);
v_l_4656_ = lean_ctor_get(v_impl_4650_, 3);
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
v___x_4661_ = lean_nat_add(v___x_4651_, v_size_4653_);
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
lean_inc(v_l_4656_);
lean_inc(v_v_4655_);
lean_inc(v_k_4654_);
lean_inc(v_size_4653_);
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
v___x_4687_ = lean_nat_add(v___y_4684_, v___y_4686_);
lean_dec(v___y_4686_);
lean_dec(v___y_4684_);
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
lean_ctor_set(v___x_4667_, 3, v___y_4685_);
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
lean_ctor_set(v_reuseFailAlloc_4692_, 3, v___y_4685_);
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
v___y_4684_ = v___x_4700_;
v___y_4685_ = v___x_4699_;
v___y_4686_ = v_size_4701_;
goto v___jp_4683_;
}
else
{
lean_object* v___x_4702_; 
v___x_4702_ = lean_unsigned_to_nat(0u);
v___y_4684_ = v___x_4700_;
v___y_4685_ = v___x_4699_;
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
if (lean_obj_tag(v_l_4737_) == 0)
{
lean_object* v_r_4738_; lean_object* v_k_4739_; lean_object* v_v_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4751_; 
lean_inc_ref(v_l_4737_);
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
lean_inc(v_l_4737_);
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
v_k_4794_ = lean_ctor_get(v_impl_4790_, 1);
v_v_4795_ = lean_ctor_get(v_impl_4790_, 2);
v_l_4796_ = lean_ctor_get(v_impl_4790_, 3);
lean_inc(v_l_4796_);
v_r_4797_ = lean_ctor_get(v_impl_4790_, 4);
v___x_4798_ = lean_unsigned_to_nat(3u);
v___x_4799_ = lean_nat_mul(v___x_4798_, v_size_4792_);
v___x_4800_ = lean_nat_dec_lt(v___x_4799_, v_size_4793_);
lean_dec(v___x_4799_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4804_; 
lean_dec(v_l_4796_);
v___x_4801_ = lean_nat_add(v___x_4791_, v_size_4792_);
v___x_4802_ = lean_nat_add(v___x_4801_, v_size_4793_);
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
lean_inc(v_r_4797_);
lean_inc(v_v_4795_);
lean_inc(v_k_4794_);
lean_inc(v_size_4793_);
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
v___x_4827_ = lean_nat_add(v___y_4824_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec(v___y_4824_);
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
lean_ctor_set(v___x_4807_, 3, v___y_4825_);
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
lean_ctor_set(v_reuseFailAlloc_4832_, 3, v___y_4825_);
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
v___y_4824_ = v___x_4839_;
v___y_4825_ = v___x_4838_;
v___y_4826_ = v_size_4840_;
goto v___jp_4823_;
}
else
{
lean_object* v___x_4841_; 
v___x_4841_ = lean_unsigned_to_nat(0u);
v___y_4824_ = v___x_4839_;
v___y_4825_ = v___x_4838_;
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
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v_nbuckets_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5026_ = lean_array_get_size(v_data_5025_);
v___x_5027_ = lean_unsigned_to_nat(2u);
v_nbuckets_5028_ = lean_nat_mul(v___x_5026_, v___x_5027_);
v___x_5029_ = lean_unsigned_to_nat(0u);
v___x_5030_ = lean_box(0);
v___x_5031_ = lean_mk_array(v_nbuckets_5028_, v___x_5030_);
v___x_5032_ = lean_array_propagate_mark(v_data_5025_, v___x_5031_);
v___x_5033_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_5029_, v_data_5025_, v___x_5032_);
return v___x_5033_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_5034_, lean_object* v_x_5035_){
_start:
{
if (lean_obj_tag(v_x_5035_) == 0)
{
uint8_t v___x_5036_; 
v___x_5036_ = 0;
return v___x_5036_;
}
else
{
lean_object* v_key_5037_; lean_object* v_tail_5038_; uint8_t v___x_5039_; 
v_key_5037_ = lean_ctor_get(v_x_5035_, 0);
v_tail_5038_ = lean_ctor_get(v_x_5035_, 2);
v___x_5039_ = lean_name_eq(v_key_5037_, v_a_5034_);
if (v___x_5039_ == 0)
{
v_x_5035_ = v_tail_5038_;
goto _start;
}
else
{
return v___x_5039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_5041_, lean_object* v_x_5042_){
_start:
{
uint8_t v_res_5043_; lean_object* v_r_5044_; 
v_res_5043_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5041_, v_x_5042_);
lean_dec(v_x_5042_);
lean_dec(v_a_5041_);
v_r_5044_ = lean_box(v_res_5043_);
return v_r_5044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_5045_, lean_object* v_m_5046_, lean_object* v_a_5047_){
_start:
{
size_t v___y_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v_size_5055_; lean_object* v_buckets_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5103_; 
v_size_5055_ = lean_ctor_get(v_m_5046_, 0);
v_buckets_5056_ = lean_ctor_get(v_m_5046_, 1);
v_isSharedCheck_5103_ = !lean_is_exclusive(v_m_5046_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5058_ = v_m_5046_;
v_isShared_5059_ = v_isSharedCheck_5103_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_buckets_5056_);
lean_inc(v_size_5055_);
lean_dec(v_m_5046_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5103_;
goto v_resetjp_5057_;
}
v___jp_5048_:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = lean_array_uset(v___y_5051_, v___y_5049_, v___y_5050_);
v___x_5054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___y_5052_);
lean_ctor_set(v___x_5054_, 1, v___x_5053_);
return v___x_5054_;
}
v_resetjp_5057_:
{
lean_object* v___x_5060_; uint64_t v___y_5062_; 
v___x_5060_ = lean_array_get_size(v_buckets_5056_);
if (lean_obj_tag(v_a_5047_) == 0)
{
uint64_t v___x_5101_; 
v___x_5101_ = 1723ULL;
v___y_5062_ = v___x_5101_;
goto v___jp_5061_;
}
else
{
uint64_t v_hash_5102_; 
v_hash_5102_ = lean_ctor_get_uint64(v_a_5047_, sizeof(void*)*2);
v___y_5062_ = v_hash_5102_;
goto v___jp_5061_;
}
v___jp_5061_:
{
uint64_t v___x_5063_; uint64_t v___x_5064_; uint64_t v_fold_5065_; uint64_t v___x_5066_; uint64_t v___x_5067_; uint64_t v___x_5068_; size_t v___x_5069_; size_t v___x_5070_; size_t v___x_5071_; size_t v___x_5072_; size_t v___x_5073_; lean_object* v_bkt_5074_; uint8_t v___x_5075_; 
v___x_5063_ = 32ULL;
v___x_5064_ = lean_uint64_shift_right(v___y_5062_, v___x_5063_);
v_fold_5065_ = lean_uint64_xor(v___y_5062_, v___x_5064_);
v___x_5066_ = 16ULL;
v___x_5067_ = lean_uint64_shift_right(v_fold_5065_, v___x_5066_);
v___x_5068_ = lean_uint64_xor(v_fold_5065_, v___x_5067_);
v___x_5069_ = lean_uint64_to_usize(v___x_5068_);
v___x_5070_ = lean_usize_of_nat(v___x_5060_);
v___x_5071_ = ((size_t)1ULL);
v___x_5072_ = lean_usize_sub(v___x_5070_, v___x_5071_);
v___x_5073_ = lean_usize_land(v___x_5069_, v___x_5072_);
v_bkt_5074_ = lean_array_uget_borrowed(v_buckets_5056_, v___x_5073_);
v___x_5075_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5047_, v_bkt_5074_);
if (v___x_5075_ == 0)
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v_size_x27_5079_; lean_object* v___x_5080_; lean_object* v_buckets_x27_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; uint8_t v___x_5087_; 
v___x_5076_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_5077_ = lean_array_push(v___x_5076_, v_a_5045_);
v___x_5078_ = lean_unsigned_to_nat(1u);
v_size_x27_5079_ = lean_nat_add(v_size_5055_, v___x_5078_);
lean_dec(v_size_5055_);
lean_inc(v_bkt_5074_);
v___x_5080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5080_, 0, v_a_5047_);
lean_ctor_set(v___x_5080_, 1, v___x_5077_);
lean_ctor_set(v___x_5080_, 2, v_bkt_5074_);
v_buckets_x27_5081_ = lean_array_uset(v_buckets_5056_, v___x_5073_, v___x_5080_);
v___x_5082_ = lean_unsigned_to_nat(4u);
v___x_5083_ = lean_nat_mul(v_size_x27_5079_, v___x_5082_);
v___x_5084_ = lean_unsigned_to_nat(3u);
v___x_5085_ = lean_nat_div(v___x_5083_, v___x_5084_);
lean_dec(v___x_5083_);
v___x_5086_ = lean_array_get_size(v_buckets_x27_5081_);
v___x_5087_ = lean_nat_dec_le(v___x_5085_, v___x_5086_);
lean_dec(v___x_5085_);
if (v___x_5087_ == 0)
{
lean_object* v_val_5088_; lean_object* v___x_5090_; 
v_val_5088_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5081_);
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 1, v_val_5088_);
lean_ctor_set(v___x_5058_, 0, v_size_x27_5079_);
v___x_5090_ = v___x_5058_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_size_x27_5079_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v_val_5088_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
else
{
lean_object* v___x_5093_; 
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 1, v_buckets_x27_5081_);
lean_ctor_set(v___x_5058_, 0, v_size_x27_5079_);
v___x_5093_ = v___x_5058_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_size_x27_5079_);
lean_ctor_set(v_reuseFailAlloc_5094_, 1, v_buckets_x27_5081_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
else
{
lean_object* v___x_5095_; lean_object* v_buckets_x27_5096_; lean_object* v_bkt_x27_5097_; uint8_t v___x_5098_; 
lean_inc(v_bkt_5074_);
lean_del_object(v___x_5058_);
v___x_5095_ = lean_box(0);
v_buckets_x27_5096_ = lean_array_uset(v_buckets_5056_, v___x_5073_, v___x_5095_);
lean_inc(v_a_5047_);
v_bkt_x27_5097_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5045_, v_a_5047_, v_bkt_5074_);
v___x_5098_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5047_, v_bkt_x27_5097_);
lean_dec(v_a_5047_);
if (v___x_5098_ == 0)
{
lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5099_ = lean_unsigned_to_nat(1u);
v___x_5100_ = lean_nat_sub(v_size_5055_, v___x_5099_);
lean_dec(v_size_5055_);
v___y_5049_ = v___x_5073_;
v___y_5050_ = v_bkt_x27_5097_;
v___y_5051_ = v_buckets_x27_5096_;
v___y_5052_ = v___x_5100_;
goto v___jp_5048_;
}
else
{
v___y_5049_ = v___x_5073_;
v___y_5050_ = v_bkt_x27_5097_;
v___y_5051_ = v_buckets_x27_5096_;
v___y_5052_ = v_size_5055_;
goto v___jp_5048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5104_, lean_object* v_as_5105_, size_t v_sz_5106_, size_t v_i_5107_, lean_object* v_b_5108_){
_start:
{
uint8_t v___x_5109_; 
v___x_5109_ = lean_usize_dec_lt(v_i_5107_, v_sz_5106_);
if (v___x_5109_ == 0)
{
lean_dec_ref(v_key_5104_);
return v_b_5108_;
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; size_t v___x_5113_; size_t v___x_5114_; 
v_a_5110_ = lean_array_uget_borrowed(v_as_5105_, v_i_5107_);
lean_inc_ref(v_key_5104_);
lean_inc_n(v_a_5110_, 2);
v___x_5111_ = lean_apply_1(v_key_5104_, v_a_5110_);
v___x_5112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5110_, v_b_5108_, v___x_5111_);
v___x_5113_ = ((size_t)1ULL);
v___x_5114_ = lean_usize_add(v_i_5107_, v___x_5113_);
v_i_5107_ = v___x_5114_;
v_b_5108_ = v___x_5112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5116_, lean_object* v_as_5117_, lean_object* v_sz_5118_, lean_object* v_i_5119_, lean_object* v_b_5120_){
_start:
{
size_t v_sz_boxed_5121_; size_t v_i_boxed_5122_; lean_object* v_res_5123_; 
v_sz_boxed_5121_ = lean_unbox_usize(v_sz_5118_);
lean_dec(v_sz_5118_);
v_i_boxed_5122_ = lean_unbox_usize(v_i_5119_);
lean_dec(v_i_5119_);
v_res_5123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5116_, v_as_5117_, v_sz_boxed_5121_, v_i_boxed_5122_, v_b_5120_);
lean_dec_ref(v_as_5117_);
return v_res_5123_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5124_ = lean_box(0);
v___x_5125_ = lean_unsigned_to_nat(16u);
v___x_5126_ = lean_mk_array(v___x_5125_, v___x_5124_);
return v___x_5126_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v_groups_5129_; 
v___x_5127_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5128_ = lean_unsigned_to_nat(0u);
v_groups_5129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5129_, 0, v___x_5128_);
lean_ctor_set(v_groups_5129_, 1, v___x_5127_);
return v_groups_5129_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5130_, lean_object* v_xs_5131_){
_start:
{
lean_object* v_groups_5132_; size_t v_sz_5133_; size_t v___x_5134_; lean_object* v___x_5135_; 
v_groups_5132_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5133_ = lean_array_size(v_xs_5131_);
v___x_5134_ = ((size_t)0ULL);
v___x_5135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5130_, v_xs_5131_, v_sz_5133_, v___x_5134_, v_groups_5132_);
return v___x_5135_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5136_, lean_object* v_xs_5137_){
_start:
{
lean_object* v_res_5138_; 
v_res_5138_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5136_, v_xs_5137_);
lean_dec_ref(v_xs_5137_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5140_){
_start:
{
lean_object* v___f_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___f_5142_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5143_ = lean_unsigned_to_nat(0u);
v___x_5144_ = lean_array_get_size(v_infos_5140_);
v___x_5145_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5140_, v___x_5143_, v___x_5144_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5169_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5148_ = v___x_5145_;
v_isShared_5149_ = v_isSharedCheck_5169_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5145_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5169_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___y_5151_; lean_object* v___x_5160_; lean_object* v_size_5161_; lean_object* v_buckets_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; uint8_t v___x_5165_; 
v___x_5160_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5142_, v_a_5146_);
v_size_5161_ = lean_ctor_get(v___x_5160_, 0);
lean_inc(v_size_5161_);
v_buckets_5162_ = lean_ctor_get(v___x_5160_, 1);
lean_inc_ref(v_buckets_5162_);
lean_dec_ref(v___x_5160_);
v___x_5163_ = lean_mk_empty_array_with_capacity(v_size_5161_);
lean_dec(v_size_5161_);
v___x_5164_ = lean_array_get_size(v_buckets_5162_);
v___x_5165_ = lean_nat_dec_lt(v___x_5143_, v___x_5164_);
if (v___x_5165_ == 0)
{
lean_dec_ref(v_buckets_5162_);
v___y_5151_ = v___x_5163_;
goto v___jp_5150_;
}
else
{
size_t v___x_5166_; size_t v___x_5167_; lean_object* v___x_5168_; 
v___x_5166_ = ((size_t)0ULL);
v___x_5167_ = lean_usize_of_nat(v___x_5164_);
v___x_5168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5162_, v___x_5166_, v___x_5167_, v___x_5163_);
lean_dec_ref(v_buckets_5162_);
v___y_5151_ = v___x_5168_;
goto v___jp_5150_;
}
v___jp_5150_:
{
lean_object* v_r_5152_; size_t v_sz_5153_; size_t v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5158_; 
v_r_5152_ = lean_box(1);
v_sz_5153_ = lean_array_size(v___y_5151_);
v___x_5154_ = ((size_t)0ULL);
v___x_5155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5151_, v_sz_5153_, v___x_5154_, v_r_5152_);
lean_dec_ref(v___y_5151_);
v___x_5156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5156_, 0, v_a_5146_);
lean_ctor_set(v___x_5156_, 1, v___x_5155_);
if (v_isShared_5149_ == 0)
{
lean_ctor_set(v___x_5148_, 0, v___x_5156_);
v___x_5158_ = v___x_5148_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5156_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
}
else
{
lean_object* v_a_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5177_; 
v_a_5170_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5172_ = v___x_5145_;
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_a_5170_);
lean_dec(v___x_5145_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5175_; 
if (v_isShared_5173_ == 0)
{
v___x_5175_ = v___x_5172_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_a_5170_);
v___x_5175_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
return v___x_5175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5178_, lean_object* v_a_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5178_);
lean_dec_ref(v_infos_5178_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5181_, lean_object* v_k_5182_, lean_object* v_v_5183_, lean_object* v_t_5184_, lean_object* v_hl_5185_){
_start:
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5182_, v_v_5183_, v_t_5184_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5187_, lean_object* v_key_5188_, lean_object* v_xs_5189_){
_start:
{
lean_object* v___x_5190_; 
v___x_5190_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5188_, v_xs_5189_);
return v___x_5190_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5191_, lean_object* v_key_5192_, lean_object* v_xs_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5191_, v_key_5192_, v_xs_5193_);
lean_dec_ref(v_xs_5193_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5195_, lean_object* v_a_5196_, lean_object* v_m_5197_, lean_object* v_a_5198_){
_start:
{
lean_object* v___x_5199_; 
v___x_5199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5196_, v_m_5197_, v_a_5198_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5200_, lean_object* v_key_5201_, lean_object* v_as_5202_, size_t v_sz_5203_, size_t v_i_5204_, lean_object* v_b_5205_){
_start:
{
lean_object* v___x_5206_; 
v___x_5206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5201_, v_as_5202_, v_sz_5203_, v_i_5204_, v_b_5205_);
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5207_, lean_object* v_key_5208_, lean_object* v_as_5209_, lean_object* v_sz_5210_, lean_object* v_i_5211_, lean_object* v_b_5212_){
_start:
{
size_t v_sz_boxed_5213_; size_t v_i_boxed_5214_; lean_object* v_res_5215_; 
v_sz_boxed_5213_ = lean_unbox_usize(v_sz_5210_);
lean_dec(v_sz_5210_);
v_i_boxed_5214_ = lean_unbox_usize(v_i_5211_);
lean_dec(v_i_5211_);
v_res_5215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5207_, v_key_5208_, v_as_5209_, v_sz_boxed_5213_, v_i_boxed_5214_, v_b_5212_);
lean_dec_ref(v_as_5209_);
return v_res_5215_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5216_, lean_object* v_a_5217_, lean_object* v_x_5218_){
_start:
{
uint8_t v___x_5219_; 
v___x_5219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5217_, v_x_5218_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5220_, lean_object* v_a_5221_, lean_object* v_x_5222_){
_start:
{
uint8_t v_res_5223_; lean_object* v_r_5224_; 
v_res_5223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5220_, v_a_5221_, v_x_5222_);
lean_dec(v_x_5222_);
lean_dec(v_a_5221_);
v_r_5224_ = lean_box(v_res_5223_);
return v_r_5224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5225_, lean_object* v_data_5226_){
_start:
{
lean_object* v___x_5227_; 
v___x_5227_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5226_);
return v___x_5227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_x_5231_){
_start:
{
lean_object* v___x_5232_; 
v___x_5232_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5229_, v_a_5230_, v_x_5231_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5233_, lean_object* v_i_5234_, lean_object* v_source_5235_, lean_object* v_target_5236_){
_start:
{
lean_object* v___x_5237_; 
v___x_5237_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5234_, v_source_5235_, v_target_5236_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5238_, lean_object* v_x_5239_, lean_object* v_x_5240_){
_start:
{
lean_object* v___x_5241_; 
v___x_5241_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5239_, v_x_5240_);
return v___x_5241_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5242_){
_start:
{
lean_object* v_isSetupFailure_x3f_5243_; 
v_isSetupFailure_x3f_5243_ = lean_ctor_get(v_i_5242_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5243_) == 0)
{
uint8_t v___x_5244_; 
v___x_5244_ = 0;
return v___x_5244_;
}
else
{
lean_object* v_val_5245_; uint8_t v___x_5246_; 
v_val_5245_ = lean_ctor_get(v_isSetupFailure_x3f_5243_, 0);
v___x_5246_ = lean_unbox(v_val_5245_);
if (v___x_5246_ == 0)
{
uint8_t v___x_5247_; 
v___x_5247_ = 1;
return v___x_5247_;
}
else
{
uint8_t v___x_5248_; 
v___x_5248_ = 0;
return v___x_5248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5249_){
_start:
{
uint8_t v_res_5250_; lean_object* v_r_5251_; 
v_res_5250_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5249_);
lean_dec_ref(v_i_5249_);
v_r_5251_ = lean_box(v_res_5250_);
return v_r_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5257_, lean_object* v_path_5258_, lean_object* v_ilean_5259_){
_start:
{
lean_object* v_module_5261_; lean_object* v_directImports_5262_; lean_object* v_references_5263_; lean_object* v_decls_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5316_; 
v_module_5261_ = lean_ctor_get(v_ilean_5259_, 1);
v_directImports_5262_ = lean_ctor_get(v_ilean_5259_, 2);
v_references_5263_ = lean_ctor_get(v_ilean_5259_, 3);
v_decls_5264_ = lean_ctor_get(v_ilean_5259_, 4);
v_isSharedCheck_5316_ = !lean_is_exclusive(v_ilean_5259_);
if (v_isSharedCheck_5316_ == 0)
{
lean_object* v_unused_5317_; 
v_unused_5317_ = lean_ctor_get(v_ilean_5259_, 0);
lean_dec(v_unused_5317_);
v___x_5266_ = v_ilean_5259_;
v_isShared_5267_ = v_isSharedCheck_5316_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_decls_5264_);
lean_inc(v_references_5263_);
lean_inc(v_directImports_5262_);
lean_inc(v_module_5261_);
lean_dec(v_ilean_5259_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5316_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v___x_5268_; 
lean_inc(v_module_5261_);
v___x_5268_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5261_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5307_; 
v_a_5269_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5307_ == 0)
{
v___x_5271_ = v___x_5268_;
v_isShared_5272_ = v_isSharedCheck_5307_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5268_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5307_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
if (lean_obj_tag(v_a_5269_) == 1)
{
lean_object* v_val_5273_; lean_object* v___x_5274_; 
lean_del_object(v___x_5271_);
v_val_5273_ = lean_ctor_get(v_a_5269_, 0);
lean_inc(v_val_5273_);
lean_dec_ref_known(v_a_5269_, 1);
v___x_5274_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5262_);
lean_dec_ref(v_directImports_5262_);
if (lean_obj_tag(v___x_5274_) == 0)
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5295_; 
v_a_5275_ = lean_ctor_get(v___x_5274_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5274_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5277_ = v___x_5274_;
v_isShared_5278_ = v_isSharedCheck_5295_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5274_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5295_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v_ileans_5279_; lean_object* v_workers_5280_; lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5294_; 
v_ileans_5279_ = lean_ctor_get(v_self_5257_, 0);
v_workers_5280_ = lean_ctor_get(v_self_5257_, 1);
v_isSharedCheck_5294_ = !lean_is_exclusive(v_self_5257_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5282_ = v_self_5257_;
v_isShared_5283_ = v_isSharedCheck_5294_;
goto v_resetjp_5281_;
}
else
{
lean_inc(v_workers_5280_);
lean_inc(v_ileans_5279_);
lean_dec(v_self_5257_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5294_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5285_; 
if (v_isShared_5267_ == 0)
{
lean_ctor_set(v___x_5266_, 2, v_a_5275_);
lean_ctor_set(v___x_5266_, 1, v_path_5258_);
lean_ctor_set(v___x_5266_, 0, v_val_5273_);
v___x_5285_ = v___x_5266_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_val_5273_);
lean_ctor_set(v_reuseFailAlloc_5293_, 1, v_path_5258_);
lean_ctor_set(v_reuseFailAlloc_5293_, 2, v_a_5275_);
lean_ctor_set(v_reuseFailAlloc_5293_, 3, v_references_5263_);
lean_ctor_set(v_reuseFailAlloc_5293_, 4, v_decls_5264_);
v___x_5285_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
lean_object* v___x_5286_; lean_object* v___x_5288_; 
v___x_5286_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5261_, v___x_5285_, v_ileans_5279_);
if (v_isShared_5283_ == 0)
{
lean_ctor_set(v___x_5282_, 0, v___x_5286_);
v___x_5288_ = v___x_5282_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5286_);
lean_ctor_set(v_reuseFailAlloc_5292_, 1, v_workers_5280_);
v___x_5288_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
lean_object* v___x_5290_; 
if (v_isShared_5278_ == 0)
{
lean_ctor_set(v___x_5277_, 0, v___x_5288_);
v___x_5290_ = v___x_5277_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v___x_5288_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
}
}
else
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5303_; 
lean_dec(v_val_5273_);
lean_del_object(v___x_5266_);
lean_dec(v_decls_5264_);
lean_dec(v_references_5263_);
lean_dec(v_module_5261_);
lean_dec_ref(v_path_5258_);
lean_dec_ref(v_self_5257_);
v_a_5296_ = lean_ctor_get(v___x_5274_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5274_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5298_ = v___x_5274_;
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5274_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5301_; 
if (v_isShared_5299_ == 0)
{
v___x_5301_ = v___x_5298_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
}
else
{
lean_object* v___x_5305_; 
lean_dec(v_a_5269_);
lean_del_object(v___x_5266_);
lean_dec(v_decls_5264_);
lean_dec(v_references_5263_);
lean_dec_ref(v_directImports_5262_);
lean_dec(v_module_5261_);
lean_dec_ref(v_path_5258_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 0, v_self_5257_);
v___x_5305_ = v___x_5271_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_self_5257_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
}
else
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
lean_del_object(v___x_5266_);
lean_dec(v_decls_5264_);
lean_dec(v_references_5263_);
lean_dec_ref(v_directImports_5262_);
lean_dec(v_module_5261_);
lean_dec_ref(v_path_5258_);
lean_dec_ref(v_self_5257_);
v_a_5308_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5310_ = v___x_5268_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5268_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5318_, lean_object* v_path_5319_, lean_object* v_ilean_5320_, lean_object* v_a_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_Lean_Server_References_addIlean(v_self_5318_, v_path_5319_, v_ilean_5320_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5323_, lean_object* v_t_5324_){
_start:
{
if (lean_obj_tag(v_t_5324_) == 0)
{
lean_object* v_v_5325_; lean_object* v_k_5326_; lean_object* v_l_5327_; lean_object* v_r_5328_; lean_object* v_ileanPath_5329_; uint8_t v___x_5330_; 
v_v_5325_ = lean_ctor_get(v_t_5324_, 2);
lean_inc(v_v_5325_);
v_k_5326_ = lean_ctor_get(v_t_5324_, 1);
lean_inc(v_k_5326_);
v_l_5327_ = lean_ctor_get(v_t_5324_, 3);
lean_inc(v_l_5327_);
v_r_5328_ = lean_ctor_get(v_t_5324_, 4);
lean_inc(v_r_5328_);
lean_dec_ref_known(v_t_5324_, 5);
v_ileanPath_5329_ = lean_ctor_get(v_v_5325_, 1);
v___x_5330_ = lean_string_dec_eq(v_ileanPath_5329_, v_path_5323_);
if (v___x_5330_ == 0)
{
lean_object* v_impl_5331_; lean_object* v_impl_5332_; lean_object* v___x_5333_; 
lean_dec(v_k_5326_);
lean_dec(v_v_5325_);
v_impl_5331_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5323_, v_l_5327_);
v_impl_5332_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5323_, v_r_5328_);
v___x_5333_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5331_, v_impl_5332_);
return v___x_5333_;
}
else
{
lean_object* v_impl_5334_; lean_object* v_impl_5335_; lean_object* v___x_5336_; 
v_impl_5334_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5323_, v_l_5327_);
v_impl_5335_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5323_, v_r_5328_);
v___x_5336_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5326_, v_v_5325_, v_impl_5334_, v_impl_5335_);
return v___x_5336_;
}
}
else
{
return v_t_5324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5337_, lean_object* v_t_5338_){
_start:
{
lean_object* v_res_5339_; 
v_res_5339_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5337_, v_t_5338_);
lean_dec_ref(v_path_5337_);
return v_res_5339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5340_, lean_object* v_t_5341_){
_start:
{
if (lean_obj_tag(v_t_5341_) == 0)
{
lean_object* v_k_5342_; lean_object* v_v_5343_; lean_object* v_l_5344_; lean_object* v_r_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5999_; 
v_k_5342_ = lean_ctor_get(v_t_5341_, 1);
v_v_5343_ = lean_ctor_get(v_t_5341_, 2);
v_l_5344_ = lean_ctor_get(v_t_5341_, 3);
v_r_5345_ = lean_ctor_get(v_t_5341_, 4);
v_isSharedCheck_5999_ = !lean_is_exclusive(v_t_5341_);
if (v_isSharedCheck_5999_ == 0)
{
lean_object* v_unused_6000_; 
v_unused_6000_ = lean_ctor_get(v_t_5341_, 0);
lean_dec(v_unused_6000_);
v___x_5347_ = v_t_5341_;
v_isShared_5348_ = v_isSharedCheck_5999_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_r_5345_);
lean_inc(v_l_5344_);
lean_inc(v_v_5343_);
lean_inc(v_k_5342_);
lean_dec(v_t_5341_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5999_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
uint8_t v___x_5349_; 
v___x_5349_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5340_, v_k_5342_);
switch(v___x_5349_)
{
case 0:
{
lean_object* v_impl_5350_; lean_object* v___x_5351_; 
v_impl_5350_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5340_, v_l_5344_);
v___x_5351_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5350_) == 0)
{
if (lean_obj_tag(v_r_5345_) == 0)
{
lean_object* v_size_5352_; lean_object* v_size_5353_; lean_object* v_k_5354_; lean_object* v_v_5355_; lean_object* v_l_5356_; lean_object* v_r_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; uint8_t v___x_5360_; 
v_size_5352_ = lean_ctor_get(v_impl_5350_, 0);
v_size_5353_ = lean_ctor_get(v_r_5345_, 0);
v_k_5354_ = lean_ctor_get(v_r_5345_, 1);
v_v_5355_ = lean_ctor_get(v_r_5345_, 2);
v_l_5356_ = lean_ctor_get(v_r_5345_, 3);
lean_inc(v_l_5356_);
v_r_5357_ = lean_ctor_get(v_r_5345_, 4);
v___x_5358_ = lean_unsigned_to_nat(3u);
v___x_5359_ = lean_nat_mul(v___x_5358_, v_size_5352_);
v___x_5360_ = lean_nat_dec_lt(v___x_5359_, v_size_5353_);
lean_dec(v___x_5359_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5364_; 
lean_dec(v_l_5356_);
v___x_5361_ = lean_nat_add(v___x_5351_, v_size_5352_);
v___x_5362_ = lean_nat_add(v___x_5361_, v_size_5353_);
lean_dec(v___x_5361_);
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 3, v_impl_5350_);
lean_ctor_set(v___x_5347_, 0, v___x_5362_);
v___x_5364_ = v___x_5347_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v___x_5362_);
lean_ctor_set(v_reuseFailAlloc_5365_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5365_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5365_, 3, v_impl_5350_);
lean_ctor_set(v_reuseFailAlloc_5365_, 4, v_r_5345_);
v___x_5364_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
return v___x_5364_;
}
}
else
{
lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5429_; 
lean_inc(v_r_5357_);
lean_inc(v_v_5355_);
lean_inc(v_k_5354_);
lean_inc(v_size_5353_);
v_isSharedCheck_5429_ = !lean_is_exclusive(v_r_5345_);
if (v_isSharedCheck_5429_ == 0)
{
lean_object* v_unused_5430_; lean_object* v_unused_5431_; lean_object* v_unused_5432_; lean_object* v_unused_5433_; lean_object* v_unused_5434_; 
v_unused_5430_ = lean_ctor_get(v_r_5345_, 4);
lean_dec(v_unused_5430_);
v_unused_5431_ = lean_ctor_get(v_r_5345_, 3);
lean_dec(v_unused_5431_);
v_unused_5432_ = lean_ctor_get(v_r_5345_, 2);
lean_dec(v_unused_5432_);
v_unused_5433_ = lean_ctor_get(v_r_5345_, 1);
lean_dec(v_unused_5433_);
v_unused_5434_ = lean_ctor_get(v_r_5345_, 0);
lean_dec(v_unused_5434_);
v___x_5367_ = v_r_5345_;
v_isShared_5368_ = v_isSharedCheck_5429_;
goto v_resetjp_5366_;
}
else
{
lean_dec(v_r_5345_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5429_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v_size_5369_; lean_object* v_k_5370_; lean_object* v_v_5371_; lean_object* v_l_5372_; lean_object* v_r_5373_; lean_object* v_size_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; uint8_t v___x_5377_; 
v_size_5369_ = lean_ctor_get(v_l_5356_, 0);
v_k_5370_ = lean_ctor_get(v_l_5356_, 1);
v_v_5371_ = lean_ctor_get(v_l_5356_, 2);
v_l_5372_ = lean_ctor_get(v_l_5356_, 3);
v_r_5373_ = lean_ctor_get(v_l_5356_, 4);
v_size_5374_ = lean_ctor_get(v_r_5357_, 0);
v___x_5375_ = lean_unsigned_to_nat(2u);
v___x_5376_ = lean_nat_mul(v___x_5375_, v_size_5374_);
v___x_5377_ = lean_nat_dec_lt(v_size_5369_, v___x_5376_);
lean_dec(v___x_5376_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5405_; 
lean_inc(v_r_5373_);
lean_inc(v_l_5372_);
lean_inc(v_v_5371_);
lean_inc(v_k_5370_);
v_isSharedCheck_5405_ = !lean_is_exclusive(v_l_5356_);
if (v_isSharedCheck_5405_ == 0)
{
lean_object* v_unused_5406_; lean_object* v_unused_5407_; lean_object* v_unused_5408_; lean_object* v_unused_5409_; lean_object* v_unused_5410_; 
v_unused_5406_ = lean_ctor_get(v_l_5356_, 4);
lean_dec(v_unused_5406_);
v_unused_5407_ = lean_ctor_get(v_l_5356_, 3);
lean_dec(v_unused_5407_);
v_unused_5408_ = lean_ctor_get(v_l_5356_, 2);
lean_dec(v_unused_5408_);
v_unused_5409_ = lean_ctor_get(v_l_5356_, 1);
lean_dec(v_unused_5409_);
v_unused_5410_ = lean_ctor_get(v_l_5356_, 0);
lean_dec(v_unused_5410_);
v___x_5379_ = v_l_5356_;
v_isShared_5380_ = v_isSharedCheck_5405_;
goto v_resetjp_5378_;
}
else
{
lean_dec(v_l_5356_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5405_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___y_5384_; lean_object* v___y_5385_; lean_object* v___y_5386_; lean_object* v___y_5395_; 
v___x_5381_ = lean_nat_add(v___x_5351_, v_size_5352_);
v___x_5382_ = lean_nat_add(v___x_5381_, v_size_5353_);
lean_dec(v_size_5353_);
if (lean_obj_tag(v_l_5372_) == 0)
{
lean_object* v_size_5403_; 
v_size_5403_ = lean_ctor_get(v_l_5372_, 0);
lean_inc(v_size_5403_);
v___y_5395_ = v_size_5403_;
goto v___jp_5394_;
}
else
{
lean_object* v___x_5404_; 
v___x_5404_ = lean_unsigned_to_nat(0u);
v___y_5395_ = v___x_5404_;
goto v___jp_5394_;
}
v___jp_5383_:
{
lean_object* v___x_5387_; lean_object* v___x_5389_; 
v___x_5387_ = lean_nat_add(v___y_5385_, v___y_5386_);
lean_dec(v___y_5386_);
lean_dec(v___y_5385_);
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 4, v_r_5357_);
lean_ctor_set(v___x_5379_, 3, v_r_5373_);
lean_ctor_set(v___x_5379_, 2, v_v_5355_);
lean_ctor_set(v___x_5379_, 1, v_k_5354_);
lean_ctor_set(v___x_5379_, 0, v___x_5387_);
v___x_5389_ = v___x_5379_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5387_);
lean_ctor_set(v_reuseFailAlloc_5393_, 1, v_k_5354_);
lean_ctor_set(v_reuseFailAlloc_5393_, 2, v_v_5355_);
lean_ctor_set(v_reuseFailAlloc_5393_, 3, v_r_5373_);
lean_ctor_set(v_reuseFailAlloc_5393_, 4, v_r_5357_);
v___x_5389_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
lean_object* v___x_5391_; 
if (v_isShared_5368_ == 0)
{
lean_ctor_set(v___x_5367_, 4, v___x_5389_);
lean_ctor_set(v___x_5367_, 3, v___y_5384_);
lean_ctor_set(v___x_5367_, 2, v_v_5371_);
lean_ctor_set(v___x_5367_, 1, v_k_5370_);
lean_ctor_set(v___x_5367_, 0, v___x_5382_);
v___x_5391_ = v___x_5367_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v___x_5382_);
lean_ctor_set(v_reuseFailAlloc_5392_, 1, v_k_5370_);
lean_ctor_set(v_reuseFailAlloc_5392_, 2, v_v_5371_);
lean_ctor_set(v_reuseFailAlloc_5392_, 3, v___y_5384_);
lean_ctor_set(v_reuseFailAlloc_5392_, 4, v___x_5389_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
v___jp_5394_:
{
lean_object* v___x_5396_; lean_object* v___x_5398_; 
v___x_5396_ = lean_nat_add(v___x_5381_, v___y_5395_);
lean_dec(v___y_5395_);
lean_dec(v___x_5381_);
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v_l_5372_);
lean_ctor_set(v___x_5347_, 3, v_impl_5350_);
lean_ctor_set(v___x_5347_, 0, v___x_5396_);
v___x_5398_ = v___x_5347_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5396_);
lean_ctor_set(v_reuseFailAlloc_5402_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5402_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5402_, 3, v_impl_5350_);
lean_ctor_set(v_reuseFailAlloc_5402_, 4, v_l_5372_);
v___x_5398_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
lean_object* v___x_5399_; 
v___x_5399_ = lean_nat_add(v___x_5351_, v_size_5374_);
if (lean_obj_tag(v_r_5373_) == 0)
{
lean_object* v_size_5400_; 
v_size_5400_ = lean_ctor_get(v_r_5373_, 0);
lean_inc(v_size_5400_);
v___y_5384_ = v___x_5398_;
v___y_5385_ = v___x_5399_;
v___y_5386_ = v_size_5400_;
goto v___jp_5383_;
}
else
{
lean_object* v___x_5401_; 
v___x_5401_ = lean_unsigned_to_nat(0u);
v___y_5384_ = v___x_5398_;
v___y_5385_ = v___x_5399_;
v___y_5386_ = v___x_5401_;
goto v___jp_5383_;
}
}
}
}
}
else
{
lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5415_; 
lean_del_object(v___x_5347_);
v___x_5411_ = lean_nat_add(v___x_5351_, v_size_5352_);
v___x_5412_ = lean_nat_add(v___x_5411_, v_size_5353_);
lean_dec(v_size_5353_);
v___x_5413_ = lean_nat_add(v___x_5411_, v_size_5369_);
lean_dec(v___x_5411_);
lean_inc_ref(v_impl_5350_);
if (v_isShared_5368_ == 0)
{
lean_ctor_set(v___x_5367_, 4, v_l_5356_);
lean_ctor_set(v___x_5367_, 3, v_impl_5350_);
lean_ctor_set(v___x_5367_, 2, v_v_5343_);
lean_ctor_set(v___x_5367_, 1, v_k_5342_);
lean_ctor_set(v___x_5367_, 0, v___x_5413_);
v___x_5415_ = v___x_5367_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5413_);
lean_ctor_set(v_reuseFailAlloc_5428_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5428_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5428_, 3, v_impl_5350_);
lean_ctor_set(v_reuseFailAlloc_5428_, 4, v_l_5356_);
v___x_5415_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
v_isSharedCheck_5422_ = !lean_is_exclusive(v_impl_5350_);
if (v_isSharedCheck_5422_ == 0)
{
lean_object* v_unused_5423_; lean_object* v_unused_5424_; lean_object* v_unused_5425_; lean_object* v_unused_5426_; lean_object* v_unused_5427_; 
v_unused_5423_ = lean_ctor_get(v_impl_5350_, 4);
lean_dec(v_unused_5423_);
v_unused_5424_ = lean_ctor_get(v_impl_5350_, 3);
lean_dec(v_unused_5424_);
v_unused_5425_ = lean_ctor_get(v_impl_5350_, 2);
lean_dec(v_unused_5425_);
v_unused_5426_ = lean_ctor_get(v_impl_5350_, 1);
lean_dec(v_unused_5426_);
v_unused_5427_ = lean_ctor_get(v_impl_5350_, 0);
lean_dec(v_unused_5427_);
v___x_5417_ = v_impl_5350_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_dec(v_impl_5350_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 4, v_r_5357_);
lean_ctor_set(v___x_5417_, 3, v___x_5415_);
lean_ctor_set(v___x_5417_, 2, v_v_5355_);
lean_ctor_set(v___x_5417_, 1, v_k_5354_);
lean_ctor_set(v___x_5417_, 0, v___x_5412_);
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v___x_5412_);
lean_ctor_set(v_reuseFailAlloc_5421_, 1, v_k_5354_);
lean_ctor_set(v_reuseFailAlloc_5421_, 2, v_v_5355_);
lean_ctor_set(v_reuseFailAlloc_5421_, 3, v___x_5415_);
lean_ctor_set(v_reuseFailAlloc_5421_, 4, v_r_5357_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5435_; lean_object* v___x_5436_; lean_object* v___x_5438_; 
v_size_5435_ = lean_ctor_get(v_impl_5350_, 0);
v___x_5436_ = lean_nat_add(v___x_5351_, v_size_5435_);
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 3, v_impl_5350_);
lean_ctor_set(v___x_5347_, 0, v___x_5436_);
v___x_5438_ = v___x_5347_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v___x_5436_);
lean_ctor_set(v_reuseFailAlloc_5439_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5439_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5439_, 3, v_impl_5350_);
lean_ctor_set(v_reuseFailAlloc_5439_, 4, v_r_5345_);
v___x_5438_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
return v___x_5438_;
}
}
}
else
{
if (lean_obj_tag(v_r_5345_) == 0)
{
lean_object* v_l_5440_; 
v_l_5440_ = lean_ctor_get(v_r_5345_, 3);
lean_inc(v_l_5440_);
if (lean_obj_tag(v_l_5440_) == 0)
{
lean_object* v_r_5441_; 
v_r_5441_ = lean_ctor_get(v_r_5345_, 4);
lean_inc(v_r_5441_);
if (lean_obj_tag(v_r_5441_) == 0)
{
lean_object* v_size_5442_; lean_object* v_k_5443_; lean_object* v_v_5444_; lean_object* v___x_5446_; uint8_t v_isShared_5447_; uint8_t v_isSharedCheck_5457_; 
v_size_5442_ = lean_ctor_get(v_r_5345_, 0);
v_k_5443_ = lean_ctor_get(v_r_5345_, 1);
v_v_5444_ = lean_ctor_get(v_r_5345_, 2);
v_isSharedCheck_5457_ = !lean_is_exclusive(v_r_5345_);
if (v_isSharedCheck_5457_ == 0)
{
lean_object* v_unused_5458_; lean_object* v_unused_5459_; 
v_unused_5458_ = lean_ctor_get(v_r_5345_, 4);
lean_dec(v_unused_5458_);
v_unused_5459_ = lean_ctor_get(v_r_5345_, 3);
lean_dec(v_unused_5459_);
v___x_5446_ = v_r_5345_;
v_isShared_5447_ = v_isSharedCheck_5457_;
goto v_resetjp_5445_;
}
else
{
lean_inc(v_v_5444_);
lean_inc(v_k_5443_);
lean_inc(v_size_5442_);
lean_dec(v_r_5345_);
v___x_5446_ = lean_box(0);
v_isShared_5447_ = v_isSharedCheck_5457_;
goto v_resetjp_5445_;
}
v_resetjp_5445_:
{
lean_object* v_size_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5452_; 
v_size_5448_ = lean_ctor_get(v_l_5440_, 0);
v___x_5449_ = lean_nat_add(v___x_5351_, v_size_5442_);
lean_dec(v_size_5442_);
v___x_5450_ = lean_nat_add(v___x_5351_, v_size_5448_);
if (v_isShared_5447_ == 0)
{
lean_ctor_set(v___x_5446_, 4, v_l_5440_);
lean_ctor_set(v___x_5446_, 3, v_impl_5350_);
lean_ctor_set(v___x_5446_, 2, v_v_5343_);
lean_ctor_set(v___x_5446_, 1, v_k_5342_);
lean_ctor_set(v___x_5446_, 0, v___x_5450_);
v___x_5452_ = v___x_5446_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v___x_5450_);
lean_ctor_set(v_reuseFailAlloc_5456_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5456_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5456_, 3, v_impl_5350_);
lean_ctor_set(v_reuseFailAlloc_5456_, 4, v_l_5440_);
v___x_5452_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
lean_object* v___x_5454_; 
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v_r_5441_);
lean_ctor_set(v___x_5347_, 3, v___x_5452_);
lean_ctor_set(v___x_5347_, 2, v_v_5444_);
lean_ctor_set(v___x_5347_, 1, v_k_5443_);
lean_ctor_set(v___x_5347_, 0, v___x_5449_);
v___x_5454_ = v___x_5347_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v___x_5449_);
lean_ctor_set(v_reuseFailAlloc_5455_, 1, v_k_5443_);
lean_ctor_set(v_reuseFailAlloc_5455_, 2, v_v_5444_);
lean_ctor_set(v_reuseFailAlloc_5455_, 3, v___x_5452_);
lean_ctor_set(v_reuseFailAlloc_5455_, 4, v_r_5441_);
v___x_5454_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
return v___x_5454_;
}
}
}
}
else
{
lean_object* v_k_5460_; lean_object* v_v_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5484_; 
v_k_5460_ = lean_ctor_get(v_r_5345_, 1);
v_v_5461_ = lean_ctor_get(v_r_5345_, 2);
v_isSharedCheck_5484_ = !lean_is_exclusive(v_r_5345_);
if (v_isSharedCheck_5484_ == 0)
{
lean_object* v_unused_5485_; lean_object* v_unused_5486_; lean_object* v_unused_5487_; 
v_unused_5485_ = lean_ctor_get(v_r_5345_, 4);
lean_dec(v_unused_5485_);
v_unused_5486_ = lean_ctor_get(v_r_5345_, 3);
lean_dec(v_unused_5486_);
v_unused_5487_ = lean_ctor_get(v_r_5345_, 0);
lean_dec(v_unused_5487_);
v___x_5463_ = v_r_5345_;
v_isShared_5464_ = v_isSharedCheck_5484_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_v_5461_);
lean_inc(v_k_5460_);
lean_dec(v_r_5345_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5484_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v_k_5465_; lean_object* v_v_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5480_; 
v_k_5465_ = lean_ctor_get(v_l_5440_, 1);
v_v_5466_ = lean_ctor_get(v_l_5440_, 2);
v_isSharedCheck_5480_ = !lean_is_exclusive(v_l_5440_);
if (v_isSharedCheck_5480_ == 0)
{
lean_object* v_unused_5481_; lean_object* v_unused_5482_; lean_object* v_unused_5483_; 
v_unused_5481_ = lean_ctor_get(v_l_5440_, 4);
lean_dec(v_unused_5481_);
v_unused_5482_ = lean_ctor_get(v_l_5440_, 3);
lean_dec(v_unused_5482_);
v_unused_5483_ = lean_ctor_get(v_l_5440_, 0);
lean_dec(v_unused_5483_);
v___x_5468_ = v_l_5440_;
v_isShared_5469_ = v_isSharedCheck_5480_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_v_5466_);
lean_inc(v_k_5465_);
lean_dec(v_l_5440_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5480_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5470_; lean_object* v___x_5472_; 
v___x_5470_ = lean_unsigned_to_nat(3u);
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 4, v_r_5441_);
lean_ctor_set(v___x_5468_, 3, v_r_5441_);
lean_ctor_set(v___x_5468_, 2, v_v_5343_);
lean_ctor_set(v___x_5468_, 1, v_k_5342_);
lean_ctor_set(v___x_5468_, 0, v___x_5351_);
v___x_5472_ = v___x_5468_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v___x_5351_);
lean_ctor_set(v_reuseFailAlloc_5479_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5479_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5479_, 3, v_r_5441_);
lean_ctor_set(v_reuseFailAlloc_5479_, 4, v_r_5441_);
v___x_5472_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
lean_object* v___x_5474_; 
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 3, v_r_5441_);
lean_ctor_set(v___x_5463_, 0, v___x_5351_);
v___x_5474_ = v___x_5463_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v___x_5351_);
lean_ctor_set(v_reuseFailAlloc_5478_, 1, v_k_5460_);
lean_ctor_set(v_reuseFailAlloc_5478_, 2, v_v_5461_);
lean_ctor_set(v_reuseFailAlloc_5478_, 3, v_r_5441_);
lean_ctor_set(v_reuseFailAlloc_5478_, 4, v_r_5441_);
v___x_5474_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
lean_object* v___x_5476_; 
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v___x_5474_);
lean_ctor_set(v___x_5347_, 3, v___x_5472_);
lean_ctor_set(v___x_5347_, 2, v_v_5466_);
lean_ctor_set(v___x_5347_, 1, v_k_5465_);
lean_ctor_set(v___x_5347_, 0, v___x_5470_);
v___x_5476_ = v___x_5347_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v___x_5470_);
lean_ctor_set(v_reuseFailAlloc_5477_, 1, v_k_5465_);
lean_ctor_set(v_reuseFailAlloc_5477_, 2, v_v_5466_);
lean_ctor_set(v_reuseFailAlloc_5477_, 3, v___x_5472_);
lean_ctor_set(v_reuseFailAlloc_5477_, 4, v___x_5474_);
v___x_5476_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
return v___x_5476_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_5488_; 
v_r_5488_ = lean_ctor_get(v_r_5345_, 4);
lean_inc(v_r_5488_);
if (lean_obj_tag(v_r_5488_) == 0)
{
lean_object* v_k_5489_; lean_object* v_v_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5501_; 
v_k_5489_ = lean_ctor_get(v_r_5345_, 1);
v_v_5490_ = lean_ctor_get(v_r_5345_, 2);
v_isSharedCheck_5501_ = !lean_is_exclusive(v_r_5345_);
if (v_isSharedCheck_5501_ == 0)
{
lean_object* v_unused_5502_; lean_object* v_unused_5503_; lean_object* v_unused_5504_; 
v_unused_5502_ = lean_ctor_get(v_r_5345_, 4);
lean_dec(v_unused_5502_);
v_unused_5503_ = lean_ctor_get(v_r_5345_, 3);
lean_dec(v_unused_5503_);
v_unused_5504_ = lean_ctor_get(v_r_5345_, 0);
lean_dec(v_unused_5504_);
v___x_5492_ = v_r_5345_;
v_isShared_5493_ = v_isSharedCheck_5501_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_v_5490_);
lean_inc(v_k_5489_);
lean_dec(v_r_5345_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5501_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v___x_5494_; lean_object* v___x_5496_; 
v___x_5494_ = lean_unsigned_to_nat(3u);
if (v_isShared_5493_ == 0)
{
lean_ctor_set(v___x_5492_, 4, v_l_5440_);
lean_ctor_set(v___x_5492_, 2, v_v_5343_);
lean_ctor_set(v___x_5492_, 1, v_k_5342_);
lean_ctor_set(v___x_5492_, 0, v___x_5351_);
v___x_5496_ = v___x_5492_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v___x_5351_);
lean_ctor_set(v_reuseFailAlloc_5500_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5500_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5500_, 3, v_l_5440_);
lean_ctor_set(v_reuseFailAlloc_5500_, 4, v_l_5440_);
v___x_5496_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
lean_object* v___x_5498_; 
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v_r_5488_);
lean_ctor_set(v___x_5347_, 3, v___x_5496_);
lean_ctor_set(v___x_5347_, 2, v_v_5490_);
lean_ctor_set(v___x_5347_, 1, v_k_5489_);
lean_ctor_set(v___x_5347_, 0, v___x_5494_);
v___x_5498_ = v___x_5347_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v___x_5494_);
lean_ctor_set(v_reuseFailAlloc_5499_, 1, v_k_5489_);
lean_ctor_set(v_reuseFailAlloc_5499_, 2, v_v_5490_);
lean_ctor_set(v_reuseFailAlloc_5499_, 3, v___x_5496_);
lean_ctor_set(v_reuseFailAlloc_5499_, 4, v_r_5488_);
v___x_5498_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
return v___x_5498_;
}
}
}
}
else
{
lean_object* v_size_5505_; lean_object* v_k_5506_; lean_object* v_v_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5518_; 
v_size_5505_ = lean_ctor_get(v_r_5345_, 0);
v_k_5506_ = lean_ctor_get(v_r_5345_, 1);
v_v_5507_ = lean_ctor_get(v_r_5345_, 2);
v_isSharedCheck_5518_ = !lean_is_exclusive(v_r_5345_);
if (v_isSharedCheck_5518_ == 0)
{
lean_object* v_unused_5519_; lean_object* v_unused_5520_; 
v_unused_5519_ = lean_ctor_get(v_r_5345_, 4);
lean_dec(v_unused_5519_);
v_unused_5520_ = lean_ctor_get(v_r_5345_, 3);
lean_dec(v_unused_5520_);
v___x_5509_ = v_r_5345_;
v_isShared_5510_ = v_isSharedCheck_5518_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_v_5507_);
lean_inc(v_k_5506_);
lean_inc(v_size_5505_);
lean_dec(v_r_5345_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5518_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5512_; 
if (v_isShared_5510_ == 0)
{
lean_ctor_set(v___x_5509_, 3, v_r_5488_);
v___x_5512_ = v___x_5509_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_size_5505_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v_k_5506_);
lean_ctor_set(v_reuseFailAlloc_5517_, 2, v_v_5507_);
lean_ctor_set(v_reuseFailAlloc_5517_, 3, v_r_5488_);
lean_ctor_set(v_reuseFailAlloc_5517_, 4, v_r_5488_);
v___x_5512_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
lean_object* v___x_5513_; lean_object* v___x_5515_; 
v___x_5513_ = lean_unsigned_to_nat(2u);
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v___x_5512_);
lean_ctor_set(v___x_5347_, 3, v_r_5488_);
lean_ctor_set(v___x_5347_, 0, v___x_5513_);
v___x_5515_ = v___x_5347_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5513_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5516_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5516_, 3, v_r_5488_);
lean_ctor_set(v_reuseFailAlloc_5516_, 4, v___x_5512_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
}
}
else
{
lean_object* v___x_5522_; 
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 3, v_r_5345_);
lean_ctor_set(v___x_5347_, 0, v___x_5351_);
v___x_5522_ = v___x_5347_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v___x_5351_);
lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5523_, 3, v_r_5345_);
lean_ctor_set(v_reuseFailAlloc_5523_, 4, v_r_5345_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
}
case 1:
{
lean_del_object(v___x_5347_);
lean_dec(v_v_5343_);
lean_dec(v_k_5342_);
if (lean_obj_tag(v_l_5344_) == 0)
{
if (lean_obj_tag(v_r_5345_) == 0)
{
lean_object* v_size_5524_; lean_object* v_k_5525_; lean_object* v_v_5526_; lean_object* v_l_5527_; lean_object* v_r_5528_; lean_object* v_size_5529_; lean_object* v_k_5530_; lean_object* v_v_5531_; lean_object* v_l_5532_; lean_object* v_r_5533_; lean_object* v___x_5534_; uint8_t v___x_5535_; 
v_size_5524_ = lean_ctor_get(v_l_5344_, 0);
v_k_5525_ = lean_ctor_get(v_l_5344_, 1);
v_v_5526_ = lean_ctor_get(v_l_5344_, 2);
v_l_5527_ = lean_ctor_get(v_l_5344_, 3);
v_r_5528_ = lean_ctor_get(v_l_5344_, 4);
lean_inc(v_r_5528_);
v_size_5529_ = lean_ctor_get(v_r_5345_, 0);
v_k_5530_ = lean_ctor_get(v_r_5345_, 1);
v_v_5531_ = lean_ctor_get(v_r_5345_, 2);
v_l_5532_ = lean_ctor_get(v_r_5345_, 3);
lean_inc(v_l_5532_);
v_r_5533_ = lean_ctor_get(v_r_5345_, 4);
v___x_5534_ = lean_unsigned_to_nat(1u);
v___x_5535_ = lean_nat_dec_lt(v_size_5524_, v_size_5529_);
if (v___x_5535_ == 0)
{
lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5671_; 
lean_inc(v_l_5527_);
lean_inc(v_v_5526_);
lean_inc(v_k_5525_);
v_isSharedCheck_5671_ = !lean_is_exclusive(v_l_5344_);
if (v_isSharedCheck_5671_ == 0)
{
lean_object* v_unused_5672_; lean_object* v_unused_5673_; lean_object* v_unused_5674_; lean_object* v_unused_5675_; lean_object* v_unused_5676_; 
v_unused_5672_ = lean_ctor_get(v_l_5344_, 4);
lean_dec(v_unused_5672_);
v_unused_5673_ = lean_ctor_get(v_l_5344_, 3);
lean_dec(v_unused_5673_);
v_unused_5674_ = lean_ctor_get(v_l_5344_, 2);
lean_dec(v_unused_5674_);
v_unused_5675_ = lean_ctor_get(v_l_5344_, 1);
lean_dec(v_unused_5675_);
v_unused_5676_ = lean_ctor_get(v_l_5344_, 0);
lean_dec(v_unused_5676_);
v___x_5537_ = v_l_5344_;
v_isShared_5538_ = v_isSharedCheck_5671_;
goto v_resetjp_5536_;
}
else
{
lean_dec(v_l_5344_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5671_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5539_; lean_object* v_tree_5540_; 
v___x_5539_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5525_, v_v_5526_, v_l_5527_, v_r_5528_);
v_tree_5540_ = lean_ctor_get(v___x_5539_, 2);
if (lean_obj_tag(v_tree_5540_) == 0)
{
lean_object* v_k_5541_; lean_object* v_v_5542_; lean_object* v_size_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; uint8_t v___x_5546_; 
lean_inc_ref(v_tree_5540_);
v_k_5541_ = lean_ctor_get(v___x_5539_, 0);
lean_inc(v_k_5541_);
v_v_5542_ = lean_ctor_get(v___x_5539_, 1);
lean_inc(v_v_5542_);
lean_dec_ref(v___x_5539_);
v_size_5543_ = lean_ctor_get(v_tree_5540_, 0);
v___x_5544_ = lean_unsigned_to_nat(3u);
v___x_5545_ = lean_nat_mul(v___x_5544_, v_size_5543_);
v___x_5546_ = lean_nat_dec_lt(v___x_5545_, v_size_5529_);
lean_dec(v___x_5545_);
if (v___x_5546_ == 0)
{
lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5550_; 
lean_dec(v_l_5532_);
v___x_5547_ = lean_nat_add(v___x_5534_, v_size_5543_);
v___x_5548_ = lean_nat_add(v___x_5547_, v_size_5529_);
lean_dec(v___x_5547_);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 4, v_r_5345_);
lean_ctor_set(v___x_5537_, 3, v_tree_5540_);
lean_ctor_set(v___x_5537_, 2, v_v_5542_);
lean_ctor_set(v___x_5537_, 1, v_k_5541_);
lean_ctor_set(v___x_5537_, 0, v___x_5548_);
v___x_5550_ = v___x_5537_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v_k_5541_);
lean_ctor_set(v_reuseFailAlloc_5551_, 2, v_v_5542_);
lean_ctor_set(v_reuseFailAlloc_5551_, 3, v_tree_5540_);
lean_ctor_set(v_reuseFailAlloc_5551_, 4, v_r_5345_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
else
{
lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5606_; 
lean_inc(v_r_5533_);
lean_inc(v_v_5531_);
lean_inc(v_k_5530_);
lean_inc(v_size_5529_);
v_isSharedCheck_5606_ = !lean_is_exclusive(v_r_5345_);
if (v_isSharedCheck_5606_ == 0)
{
lean_object* v_unused_5607_; lean_object* v_unused_5608_; lean_object* v_unused_5609_; lean_object* v_unused_5610_; lean_object* v_unused_5611_; 
v_unused_5607_ = lean_ctor_get(v_r_5345_, 4);
lean_dec(v_unused_5607_);
v_unused_5608_ = lean_ctor_get(v_r_5345_, 3);
lean_dec(v_unused_5608_);
v_unused_5609_ = lean_ctor_get(v_r_5345_, 2);
lean_dec(v_unused_5609_);
v_unused_5610_ = lean_ctor_get(v_r_5345_, 1);
lean_dec(v_unused_5610_);
v_unused_5611_ = lean_ctor_get(v_r_5345_, 0);
lean_dec(v_unused_5611_);
v___x_5553_ = v_r_5345_;
v_isShared_5554_ = v_isSharedCheck_5606_;
goto v_resetjp_5552_;
}
else
{
lean_dec(v_r_5345_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5606_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v_size_5555_; lean_object* v_k_5556_; lean_object* v_v_5557_; lean_object* v_l_5558_; lean_object* v_r_5559_; lean_object* v_size_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; uint8_t v___x_5563_; 
v_size_5555_ = lean_ctor_get(v_l_5532_, 0);
v_k_5556_ = lean_ctor_get(v_l_5532_, 1);
v_v_5557_ = lean_ctor_get(v_l_5532_, 2);
v_l_5558_ = lean_ctor_get(v_l_5532_, 3);
v_r_5559_ = lean_ctor_get(v_l_5532_, 4);
v_size_5560_ = lean_ctor_get(v_r_5533_, 0);
v___x_5561_ = lean_unsigned_to_nat(2u);
v___x_5562_ = lean_nat_mul(v___x_5561_, v_size_5560_);
v___x_5563_ = lean_nat_dec_lt(v_size_5555_, v___x_5562_);
lean_dec(v___x_5562_);
if (v___x_5563_ == 0)
{
lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5591_; 
lean_inc(v_r_5559_);
lean_inc(v_l_5558_);
lean_inc(v_v_5557_);
lean_inc(v_k_5556_);
v_isSharedCheck_5591_ = !lean_is_exclusive(v_l_5532_);
if (v_isSharedCheck_5591_ == 0)
{
lean_object* v_unused_5592_; lean_object* v_unused_5593_; lean_object* v_unused_5594_; lean_object* v_unused_5595_; lean_object* v_unused_5596_; 
v_unused_5592_ = lean_ctor_get(v_l_5532_, 4);
lean_dec(v_unused_5592_);
v_unused_5593_ = lean_ctor_get(v_l_5532_, 3);
lean_dec(v_unused_5593_);
v_unused_5594_ = lean_ctor_get(v_l_5532_, 2);
lean_dec(v_unused_5594_);
v_unused_5595_ = lean_ctor_get(v_l_5532_, 1);
lean_dec(v_unused_5595_);
v_unused_5596_ = lean_ctor_get(v_l_5532_, 0);
lean_dec(v_unused_5596_);
v___x_5565_ = v_l_5532_;
v_isShared_5566_ = v_isSharedCheck_5591_;
goto v_resetjp_5564_;
}
else
{
lean_dec(v_l_5532_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5591_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___y_5570_; lean_object* v___y_5571_; lean_object* v___y_5572_; lean_object* v___y_5581_; 
v___x_5567_ = lean_nat_add(v___x_5534_, v_size_5543_);
v___x_5568_ = lean_nat_add(v___x_5567_, v_size_5529_);
lean_dec(v_size_5529_);
if (lean_obj_tag(v_l_5558_) == 0)
{
lean_object* v_size_5589_; 
v_size_5589_ = lean_ctor_get(v_l_5558_, 0);
lean_inc(v_size_5589_);
v___y_5581_ = v_size_5589_;
goto v___jp_5580_;
}
else
{
lean_object* v___x_5590_; 
v___x_5590_ = lean_unsigned_to_nat(0u);
v___y_5581_ = v___x_5590_;
goto v___jp_5580_;
}
v___jp_5569_:
{
lean_object* v___x_5573_; lean_object* v___x_5575_; 
v___x_5573_ = lean_nat_add(v___y_5570_, v___y_5572_);
lean_dec(v___y_5572_);
lean_dec(v___y_5570_);
if (v_isShared_5566_ == 0)
{
lean_ctor_set(v___x_5565_, 4, v_r_5533_);
lean_ctor_set(v___x_5565_, 3, v_r_5559_);
lean_ctor_set(v___x_5565_, 2, v_v_5531_);
lean_ctor_set(v___x_5565_, 1, v_k_5530_);
lean_ctor_set(v___x_5565_, 0, v___x_5573_);
v___x_5575_ = v___x_5565_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v_k_5530_);
lean_ctor_set(v_reuseFailAlloc_5579_, 2, v_v_5531_);
lean_ctor_set(v_reuseFailAlloc_5579_, 3, v_r_5559_);
lean_ctor_set(v_reuseFailAlloc_5579_, 4, v_r_5533_);
v___x_5575_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
lean_object* v___x_5577_; 
if (v_isShared_5554_ == 0)
{
lean_ctor_set(v___x_5553_, 4, v___x_5575_);
lean_ctor_set(v___x_5553_, 3, v___y_5571_);
lean_ctor_set(v___x_5553_, 2, v_v_5557_);
lean_ctor_set(v___x_5553_, 1, v_k_5556_);
lean_ctor_set(v___x_5553_, 0, v___x_5568_);
v___x_5577_ = v___x_5553_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5568_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v_k_5556_);
lean_ctor_set(v_reuseFailAlloc_5578_, 2, v_v_5557_);
lean_ctor_set(v_reuseFailAlloc_5578_, 3, v___y_5571_);
lean_ctor_set(v_reuseFailAlloc_5578_, 4, v___x_5575_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
}
v___jp_5580_:
{
lean_object* v___x_5582_; lean_object* v___x_5584_; 
v___x_5582_ = lean_nat_add(v___x_5567_, v___y_5581_);
lean_dec(v___y_5581_);
lean_dec(v___x_5567_);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 4, v_l_5558_);
lean_ctor_set(v___x_5537_, 3, v_tree_5540_);
lean_ctor_set(v___x_5537_, 2, v_v_5542_);
lean_ctor_set(v___x_5537_, 1, v_k_5541_);
lean_ctor_set(v___x_5537_, 0, v___x_5582_);
v___x_5584_ = v___x_5537_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5582_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v_k_5541_);
lean_ctor_set(v_reuseFailAlloc_5588_, 2, v_v_5542_);
lean_ctor_set(v_reuseFailAlloc_5588_, 3, v_tree_5540_);
lean_ctor_set(v_reuseFailAlloc_5588_, 4, v_l_5558_);
v___x_5584_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
lean_object* v___x_5585_; 
v___x_5585_ = lean_nat_add(v___x_5534_, v_size_5560_);
if (lean_obj_tag(v_r_5559_) == 0)
{
lean_object* v_size_5586_; 
v_size_5586_ = lean_ctor_get(v_r_5559_, 0);
lean_inc(v_size_5586_);
v___y_5570_ = v___x_5585_;
v___y_5571_ = v___x_5584_;
v___y_5572_ = v_size_5586_;
goto v___jp_5569_;
}
else
{
lean_object* v___x_5587_; 
v___x_5587_ = lean_unsigned_to_nat(0u);
v___y_5570_ = v___x_5585_;
v___y_5571_ = v___x_5584_;
v___y_5572_ = v___x_5587_;
goto v___jp_5569_;
}
}
}
}
}
else
{
lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5601_; 
v___x_5597_ = lean_nat_add(v___x_5534_, v_size_5543_);
v___x_5598_ = lean_nat_add(v___x_5597_, v_size_5529_);
lean_dec(v_size_5529_);
v___x_5599_ = lean_nat_add(v___x_5597_, v_size_5555_);
lean_dec(v___x_5597_);
if (v_isShared_5554_ == 0)
{
lean_ctor_set(v___x_5553_, 4, v_l_5532_);
lean_ctor_set(v___x_5553_, 3, v_tree_5540_);
lean_ctor_set(v___x_5553_, 2, v_v_5542_);
lean_ctor_set(v___x_5553_, 1, v_k_5541_);
lean_ctor_set(v___x_5553_, 0, v___x_5599_);
v___x_5601_ = v___x_5553_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5599_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v_k_5541_);
lean_ctor_set(v_reuseFailAlloc_5605_, 2, v_v_5542_);
lean_ctor_set(v_reuseFailAlloc_5605_, 3, v_tree_5540_);
lean_ctor_set(v_reuseFailAlloc_5605_, 4, v_l_5532_);
v___x_5601_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
lean_object* v___x_5603_; 
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 4, v_r_5533_);
lean_ctor_set(v___x_5537_, 3, v___x_5601_);
lean_ctor_set(v___x_5537_, 2, v_v_5531_);
lean_ctor_set(v___x_5537_, 1, v_k_5530_);
lean_ctor_set(v___x_5537_, 0, v___x_5598_);
v___x_5603_ = v___x_5537_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v___x_5598_);
lean_ctor_set(v_reuseFailAlloc_5604_, 1, v_k_5530_);
lean_ctor_set(v_reuseFailAlloc_5604_, 2, v_v_5531_);
lean_ctor_set(v_reuseFailAlloc_5604_, 3, v___x_5601_);
lean_ctor_set(v_reuseFailAlloc_5604_, 4, v_r_5533_);
v___x_5603_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
return v___x_5603_;
}
}
}
}
}
}
else
{
lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5665_; 
lean_inc(v_r_5533_);
lean_inc(v_v_5531_);
lean_inc(v_k_5530_);
lean_inc(v_size_5529_);
v_isSharedCheck_5665_ = !lean_is_exclusive(v_r_5345_);
if (v_isSharedCheck_5665_ == 0)
{
lean_object* v_unused_5666_; lean_object* v_unused_5667_; lean_object* v_unused_5668_; lean_object* v_unused_5669_; lean_object* v_unused_5670_; 
v_unused_5666_ = lean_ctor_get(v_r_5345_, 4);
lean_dec(v_unused_5666_);
v_unused_5667_ = lean_ctor_get(v_r_5345_, 3);
lean_dec(v_unused_5667_);
v_unused_5668_ = lean_ctor_get(v_r_5345_, 2);
lean_dec(v_unused_5668_);
v_unused_5669_ = lean_ctor_get(v_r_5345_, 1);
lean_dec(v_unused_5669_);
v_unused_5670_ = lean_ctor_get(v_r_5345_, 0);
lean_dec(v_unused_5670_);
v___x_5613_ = v_r_5345_;
v_isShared_5614_ = v_isSharedCheck_5665_;
goto v_resetjp_5612_;
}
else
{
lean_dec(v_r_5345_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5665_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
if (lean_obj_tag(v_l_5532_) == 0)
{
if (lean_obj_tag(v_r_5533_) == 0)
{
lean_object* v_k_5615_; lean_object* v_v_5616_; lean_object* v_size_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5621_; 
lean_inc(v_tree_5540_);
v_k_5615_ = lean_ctor_get(v___x_5539_, 0);
lean_inc(v_k_5615_);
v_v_5616_ = lean_ctor_get(v___x_5539_, 1);
lean_inc(v_v_5616_);
lean_dec_ref(v___x_5539_);
v_size_5617_ = lean_ctor_get(v_l_5532_, 0);
v___x_5618_ = lean_nat_add(v___x_5534_, v_size_5529_);
lean_dec(v_size_5529_);
v___x_5619_ = lean_nat_add(v___x_5534_, v_size_5617_);
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 4, v_l_5532_);
lean_ctor_set(v___x_5613_, 3, v_tree_5540_);
lean_ctor_set(v___x_5613_, 2, v_v_5616_);
lean_ctor_set(v___x_5613_, 1, v_k_5615_);
lean_ctor_set(v___x_5613_, 0, v___x_5619_);
v___x_5621_ = v___x_5613_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v___x_5619_);
lean_ctor_set(v_reuseFailAlloc_5625_, 1, v_k_5615_);
lean_ctor_set(v_reuseFailAlloc_5625_, 2, v_v_5616_);
lean_ctor_set(v_reuseFailAlloc_5625_, 3, v_tree_5540_);
lean_ctor_set(v_reuseFailAlloc_5625_, 4, v_l_5532_);
v___x_5621_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
lean_object* v___x_5623_; 
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 4, v_r_5533_);
lean_ctor_set(v___x_5537_, 3, v___x_5621_);
lean_ctor_set(v___x_5537_, 2, v_v_5531_);
lean_ctor_set(v___x_5537_, 1, v_k_5530_);
lean_ctor_set(v___x_5537_, 0, v___x_5618_);
v___x_5623_ = v___x_5537_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v___x_5618_);
lean_ctor_set(v_reuseFailAlloc_5624_, 1, v_k_5530_);
lean_ctor_set(v_reuseFailAlloc_5624_, 2, v_v_5531_);
lean_ctor_set(v_reuseFailAlloc_5624_, 3, v___x_5621_);
lean_ctor_set(v_reuseFailAlloc_5624_, 4, v_r_5533_);
v___x_5623_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
return v___x_5623_;
}
}
}
else
{
lean_object* v_k_5626_; lean_object* v_v_5627_; lean_object* v_k_5628_; lean_object* v_v_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5643_; 
lean_dec(v_size_5529_);
v_k_5626_ = lean_ctor_get(v___x_5539_, 0);
lean_inc(v_k_5626_);
v_v_5627_ = lean_ctor_get(v___x_5539_, 1);
lean_inc(v_v_5627_);
lean_dec_ref(v___x_5539_);
v_k_5628_ = lean_ctor_get(v_l_5532_, 1);
v_v_5629_ = lean_ctor_get(v_l_5532_, 2);
v_isSharedCheck_5643_ = !lean_is_exclusive(v_l_5532_);
if (v_isSharedCheck_5643_ == 0)
{
lean_object* v_unused_5644_; lean_object* v_unused_5645_; lean_object* v_unused_5646_; 
v_unused_5644_ = lean_ctor_get(v_l_5532_, 4);
lean_dec(v_unused_5644_);
v_unused_5645_ = lean_ctor_get(v_l_5532_, 3);
lean_dec(v_unused_5645_);
v_unused_5646_ = lean_ctor_get(v_l_5532_, 0);
lean_dec(v_unused_5646_);
v___x_5631_ = v_l_5532_;
v_isShared_5632_ = v_isSharedCheck_5643_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_v_5629_);
lean_inc(v_k_5628_);
lean_dec(v_l_5532_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5643_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5633_; lean_object* v___x_5635_; 
v___x_5633_ = lean_unsigned_to_nat(3u);
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 4, v_r_5533_);
lean_ctor_set(v___x_5631_, 3, v_r_5533_);
lean_ctor_set(v___x_5631_, 2, v_v_5627_);
lean_ctor_set(v___x_5631_, 1, v_k_5626_);
lean_ctor_set(v___x_5631_, 0, v___x_5534_);
v___x_5635_ = v___x_5631_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v___x_5534_);
lean_ctor_set(v_reuseFailAlloc_5642_, 1, v_k_5626_);
lean_ctor_set(v_reuseFailAlloc_5642_, 2, v_v_5627_);
lean_ctor_set(v_reuseFailAlloc_5642_, 3, v_r_5533_);
lean_ctor_set(v_reuseFailAlloc_5642_, 4, v_r_5533_);
v___x_5635_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
lean_object* v___x_5637_; 
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 3, v_r_5533_);
lean_ctor_set(v___x_5613_, 0, v___x_5534_);
v___x_5637_ = v___x_5613_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v___x_5534_);
lean_ctor_set(v_reuseFailAlloc_5641_, 1, v_k_5530_);
lean_ctor_set(v_reuseFailAlloc_5641_, 2, v_v_5531_);
lean_ctor_set(v_reuseFailAlloc_5641_, 3, v_r_5533_);
lean_ctor_set(v_reuseFailAlloc_5641_, 4, v_r_5533_);
v___x_5637_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
lean_object* v___x_5639_; 
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 4, v___x_5637_);
lean_ctor_set(v___x_5537_, 3, v___x_5635_);
lean_ctor_set(v___x_5537_, 2, v_v_5629_);
lean_ctor_set(v___x_5537_, 1, v_k_5628_);
lean_ctor_set(v___x_5537_, 0, v___x_5633_);
v___x_5639_ = v___x_5537_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v___x_5633_);
lean_ctor_set(v_reuseFailAlloc_5640_, 1, v_k_5628_);
lean_ctor_set(v_reuseFailAlloc_5640_, 2, v_v_5629_);
lean_ctor_set(v_reuseFailAlloc_5640_, 3, v___x_5635_);
lean_ctor_set(v_reuseFailAlloc_5640_, 4, v___x_5637_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5533_) == 0)
{
lean_object* v_k_5647_; lean_object* v_v_5648_; lean_object* v___x_5649_; lean_object* v___x_5651_; 
lean_dec(v_size_5529_);
v_k_5647_ = lean_ctor_get(v___x_5539_, 0);
lean_inc(v_k_5647_);
v_v_5648_ = lean_ctor_get(v___x_5539_, 1);
lean_inc(v_v_5648_);
lean_dec_ref(v___x_5539_);
v___x_5649_ = lean_unsigned_to_nat(3u);
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 4, v_l_5532_);
lean_ctor_set(v___x_5613_, 2, v_v_5648_);
lean_ctor_set(v___x_5613_, 1, v_k_5647_);
lean_ctor_set(v___x_5613_, 0, v___x_5534_);
v___x_5651_ = v___x_5613_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v___x_5534_);
lean_ctor_set(v_reuseFailAlloc_5655_, 1, v_k_5647_);
lean_ctor_set(v_reuseFailAlloc_5655_, 2, v_v_5648_);
lean_ctor_set(v_reuseFailAlloc_5655_, 3, v_l_5532_);
lean_ctor_set(v_reuseFailAlloc_5655_, 4, v_l_5532_);
v___x_5651_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
lean_object* v___x_5653_; 
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 4, v_r_5533_);
lean_ctor_set(v___x_5537_, 3, v___x_5651_);
lean_ctor_set(v___x_5537_, 2, v_v_5531_);
lean_ctor_set(v___x_5537_, 1, v_k_5530_);
lean_ctor_set(v___x_5537_, 0, v___x_5649_);
v___x_5653_ = v___x_5537_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v___x_5649_);
lean_ctor_set(v_reuseFailAlloc_5654_, 1, v_k_5530_);
lean_ctor_set(v_reuseFailAlloc_5654_, 2, v_v_5531_);
lean_ctor_set(v_reuseFailAlloc_5654_, 3, v___x_5651_);
lean_ctor_set(v_reuseFailAlloc_5654_, 4, v_r_5533_);
v___x_5653_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
return v___x_5653_;
}
}
}
else
{
lean_object* v_k_5656_; lean_object* v_v_5657_; lean_object* v___x_5659_; 
v_k_5656_ = lean_ctor_get(v___x_5539_, 0);
lean_inc(v_k_5656_);
v_v_5657_ = lean_ctor_get(v___x_5539_, 1);
lean_inc(v_v_5657_);
lean_dec_ref(v___x_5539_);
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 3, v_r_5533_);
v___x_5659_ = v___x_5613_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_size_5529_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v_k_5530_);
lean_ctor_set(v_reuseFailAlloc_5664_, 2, v_v_5531_);
lean_ctor_set(v_reuseFailAlloc_5664_, 3, v_r_5533_);
lean_ctor_set(v_reuseFailAlloc_5664_, 4, v_r_5533_);
v___x_5659_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
lean_object* v___x_5660_; lean_object* v___x_5662_; 
v___x_5660_ = lean_unsigned_to_nat(2u);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 4, v___x_5659_);
lean_ctor_set(v___x_5537_, 3, v_r_5533_);
lean_ctor_set(v___x_5537_, 2, v_v_5657_);
lean_ctor_set(v___x_5537_, 1, v_k_5656_);
lean_ctor_set(v___x_5537_, 0, v___x_5660_);
v___x_5662_ = v___x_5537_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v___x_5660_);
lean_ctor_set(v_reuseFailAlloc_5663_, 1, v_k_5656_);
lean_ctor_set(v_reuseFailAlloc_5663_, 2, v_v_5657_);
lean_ctor_set(v_reuseFailAlloc_5663_, 3, v_r_5533_);
lean_ctor_set(v_reuseFailAlloc_5663_, 4, v___x_5659_);
v___x_5662_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
return v___x_5662_;
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
lean_object* v___x_5678_; uint8_t v_isShared_5679_; uint8_t v_isSharedCheck_5829_; 
lean_inc(v_r_5533_);
lean_inc(v_v_5531_);
lean_inc(v_k_5530_);
v_isSharedCheck_5829_ = !lean_is_exclusive(v_r_5345_);
if (v_isSharedCheck_5829_ == 0)
{
lean_object* v_unused_5830_; lean_object* v_unused_5831_; lean_object* v_unused_5832_; lean_object* v_unused_5833_; lean_object* v_unused_5834_; 
v_unused_5830_ = lean_ctor_get(v_r_5345_, 4);
lean_dec(v_unused_5830_);
v_unused_5831_ = lean_ctor_get(v_r_5345_, 3);
lean_dec(v_unused_5831_);
v_unused_5832_ = lean_ctor_get(v_r_5345_, 2);
lean_dec(v_unused_5832_);
v_unused_5833_ = lean_ctor_get(v_r_5345_, 1);
lean_dec(v_unused_5833_);
v_unused_5834_ = lean_ctor_get(v_r_5345_, 0);
lean_dec(v_unused_5834_);
v___x_5678_ = v_r_5345_;
v_isShared_5679_ = v_isSharedCheck_5829_;
goto v_resetjp_5677_;
}
else
{
lean_dec(v_r_5345_);
v___x_5678_ = lean_box(0);
v_isShared_5679_ = v_isSharedCheck_5829_;
goto v_resetjp_5677_;
}
v_resetjp_5677_:
{
lean_object* v___x_5680_; lean_object* v_tree_5681_; 
v___x_5680_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5530_, v_v_5531_, v_l_5532_, v_r_5533_);
v_tree_5681_ = lean_ctor_get(v___x_5680_, 2);
lean_inc(v_tree_5681_);
if (lean_obj_tag(v_tree_5681_) == 0)
{
lean_object* v_k_5682_; lean_object* v_v_5683_; lean_object* v_size_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; uint8_t v___x_5687_; 
v_k_5682_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_k_5682_);
v_v_5683_ = lean_ctor_get(v___x_5680_, 1);
lean_inc(v_v_5683_);
lean_dec_ref(v___x_5680_);
v_size_5684_ = lean_ctor_get(v_tree_5681_, 0);
v___x_5685_ = lean_unsigned_to_nat(3u);
v___x_5686_ = lean_nat_mul(v___x_5685_, v_size_5684_);
v___x_5687_ = lean_nat_dec_lt(v___x_5686_, v_size_5524_);
lean_dec(v___x_5686_);
if (v___x_5687_ == 0)
{
lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5691_; 
lean_dec(v_r_5528_);
v___x_5688_ = lean_nat_add(v___x_5534_, v_size_5524_);
v___x_5689_ = lean_nat_add(v___x_5688_, v_size_5684_);
lean_dec(v___x_5688_);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 4, v_tree_5681_);
lean_ctor_set(v___x_5678_, 3, v_l_5344_);
lean_ctor_set(v___x_5678_, 2, v_v_5683_);
lean_ctor_set(v___x_5678_, 1, v_k_5682_);
lean_ctor_set(v___x_5678_, 0, v___x_5689_);
v___x_5691_ = v___x_5678_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v___x_5689_);
lean_ctor_set(v_reuseFailAlloc_5692_, 1, v_k_5682_);
lean_ctor_set(v_reuseFailAlloc_5692_, 2, v_v_5683_);
lean_ctor_set(v_reuseFailAlloc_5692_, 3, v_l_5344_);
lean_ctor_set(v_reuseFailAlloc_5692_, 4, v_tree_5681_);
v___x_5691_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
return v___x_5691_;
}
}
else
{
lean_object* v___x_5694_; uint8_t v_isShared_5695_; uint8_t v_isSharedCheck_5758_; 
lean_inc(v_l_5527_);
lean_inc(v_v_5526_);
lean_inc(v_k_5525_);
lean_inc(v_size_5524_);
v_isSharedCheck_5758_ = !lean_is_exclusive(v_l_5344_);
if (v_isSharedCheck_5758_ == 0)
{
lean_object* v_unused_5759_; lean_object* v_unused_5760_; lean_object* v_unused_5761_; lean_object* v_unused_5762_; lean_object* v_unused_5763_; 
v_unused_5759_ = lean_ctor_get(v_l_5344_, 4);
lean_dec(v_unused_5759_);
v_unused_5760_ = lean_ctor_get(v_l_5344_, 3);
lean_dec(v_unused_5760_);
v_unused_5761_ = lean_ctor_get(v_l_5344_, 2);
lean_dec(v_unused_5761_);
v_unused_5762_ = lean_ctor_get(v_l_5344_, 1);
lean_dec(v_unused_5762_);
v_unused_5763_ = lean_ctor_get(v_l_5344_, 0);
lean_dec(v_unused_5763_);
v___x_5694_ = v_l_5344_;
v_isShared_5695_ = v_isSharedCheck_5758_;
goto v_resetjp_5693_;
}
else
{
lean_dec(v_l_5344_);
v___x_5694_ = lean_box(0);
v_isShared_5695_ = v_isSharedCheck_5758_;
goto v_resetjp_5693_;
}
v_resetjp_5693_:
{
lean_object* v_size_5696_; lean_object* v_size_5697_; lean_object* v_k_5698_; lean_object* v_v_5699_; lean_object* v_l_5700_; lean_object* v_r_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; uint8_t v___x_5704_; 
v_size_5696_ = lean_ctor_get(v_l_5527_, 0);
v_size_5697_ = lean_ctor_get(v_r_5528_, 0);
v_k_5698_ = lean_ctor_get(v_r_5528_, 1);
v_v_5699_ = lean_ctor_get(v_r_5528_, 2);
v_l_5700_ = lean_ctor_get(v_r_5528_, 3);
v_r_5701_ = lean_ctor_get(v_r_5528_, 4);
v___x_5702_ = lean_unsigned_to_nat(2u);
v___x_5703_ = lean_nat_mul(v___x_5702_, v_size_5696_);
v___x_5704_ = lean_nat_dec_lt(v_size_5697_, v___x_5703_);
lean_dec(v___x_5703_);
if (v___x_5704_ == 0)
{
lean_object* v___x_5706_; uint8_t v_isShared_5707_; uint8_t v_isSharedCheck_5742_; 
lean_inc(v_r_5701_);
lean_inc(v_l_5700_);
lean_inc(v_v_5699_);
lean_inc(v_k_5698_);
lean_del_object(v___x_5694_);
v_isSharedCheck_5742_ = !lean_is_exclusive(v_r_5528_);
if (v_isSharedCheck_5742_ == 0)
{
lean_object* v_unused_5743_; lean_object* v_unused_5744_; lean_object* v_unused_5745_; lean_object* v_unused_5746_; lean_object* v_unused_5747_; 
v_unused_5743_ = lean_ctor_get(v_r_5528_, 4);
lean_dec(v_unused_5743_);
v_unused_5744_ = lean_ctor_get(v_r_5528_, 3);
lean_dec(v_unused_5744_);
v_unused_5745_ = lean_ctor_get(v_r_5528_, 2);
lean_dec(v_unused_5745_);
v_unused_5746_ = lean_ctor_get(v_r_5528_, 1);
lean_dec(v_unused_5746_);
v_unused_5747_ = lean_ctor_get(v_r_5528_, 0);
lean_dec(v_unused_5747_);
v___x_5706_ = v_r_5528_;
v_isShared_5707_ = v_isSharedCheck_5742_;
goto v_resetjp_5705_;
}
else
{
lean_dec(v_r_5528_);
v___x_5706_ = lean_box(0);
v_isShared_5707_ = v_isSharedCheck_5742_;
goto v_resetjp_5705_;
}
v_resetjp_5705_:
{
lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___y_5711_; lean_object* v___y_5712_; lean_object* v___y_5713_; lean_object* v___x_5730_; lean_object* v___y_5732_; 
v___x_5708_ = lean_nat_add(v___x_5534_, v_size_5524_);
lean_dec(v_size_5524_);
v___x_5709_ = lean_nat_add(v___x_5708_, v_size_5684_);
lean_dec(v___x_5708_);
v___x_5730_ = lean_nat_add(v___x_5534_, v_size_5696_);
if (lean_obj_tag(v_l_5700_) == 0)
{
lean_object* v_size_5740_; 
v_size_5740_ = lean_ctor_get(v_l_5700_, 0);
lean_inc(v_size_5740_);
v___y_5732_ = v_size_5740_;
goto v___jp_5731_;
}
else
{
lean_object* v___x_5741_; 
v___x_5741_ = lean_unsigned_to_nat(0u);
v___y_5732_ = v___x_5741_;
goto v___jp_5731_;
}
v___jp_5710_:
{
lean_object* v___x_5714_; lean_object* v___x_5716_; 
v___x_5714_ = lean_nat_add(v___y_5712_, v___y_5713_);
lean_dec(v___y_5713_);
lean_dec(v___y_5712_);
lean_inc_ref(v_tree_5681_);
if (v_isShared_5707_ == 0)
{
lean_ctor_set(v___x_5706_, 4, v_tree_5681_);
lean_ctor_set(v___x_5706_, 3, v_r_5701_);
lean_ctor_set(v___x_5706_, 2, v_v_5683_);
lean_ctor_set(v___x_5706_, 1, v_k_5682_);
lean_ctor_set(v___x_5706_, 0, v___x_5714_);
v___x_5716_ = v___x_5706_;
goto v_reusejp_5715_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v___x_5714_);
lean_ctor_set(v_reuseFailAlloc_5729_, 1, v_k_5682_);
lean_ctor_set(v_reuseFailAlloc_5729_, 2, v_v_5683_);
lean_ctor_set(v_reuseFailAlloc_5729_, 3, v_r_5701_);
lean_ctor_set(v_reuseFailAlloc_5729_, 4, v_tree_5681_);
v___x_5716_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5715_;
}
v_reusejp_5715_:
{
lean_object* v___x_5718_; uint8_t v_isShared_5719_; uint8_t v_isSharedCheck_5723_; 
v_isSharedCheck_5723_ = !lean_is_exclusive(v_tree_5681_);
if (v_isSharedCheck_5723_ == 0)
{
lean_object* v_unused_5724_; lean_object* v_unused_5725_; lean_object* v_unused_5726_; lean_object* v_unused_5727_; lean_object* v_unused_5728_; 
v_unused_5724_ = lean_ctor_get(v_tree_5681_, 4);
lean_dec(v_unused_5724_);
v_unused_5725_ = lean_ctor_get(v_tree_5681_, 3);
lean_dec(v_unused_5725_);
v_unused_5726_ = lean_ctor_get(v_tree_5681_, 2);
lean_dec(v_unused_5726_);
v_unused_5727_ = lean_ctor_get(v_tree_5681_, 1);
lean_dec(v_unused_5727_);
v_unused_5728_ = lean_ctor_get(v_tree_5681_, 0);
lean_dec(v_unused_5728_);
v___x_5718_ = v_tree_5681_;
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
else
{
lean_dec(v_tree_5681_);
v___x_5718_ = lean_box(0);
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
v_resetjp_5717_:
{
lean_object* v___x_5721_; 
if (v_isShared_5719_ == 0)
{
lean_ctor_set(v___x_5718_, 4, v___x_5716_);
lean_ctor_set(v___x_5718_, 3, v___y_5711_);
lean_ctor_set(v___x_5718_, 2, v_v_5699_);
lean_ctor_set(v___x_5718_, 1, v_k_5698_);
lean_ctor_set(v___x_5718_, 0, v___x_5709_);
v___x_5721_ = v___x_5718_;
goto v_reusejp_5720_;
}
else
{
lean_object* v_reuseFailAlloc_5722_; 
v_reuseFailAlloc_5722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5722_, 0, v___x_5709_);
lean_ctor_set(v_reuseFailAlloc_5722_, 1, v_k_5698_);
lean_ctor_set(v_reuseFailAlloc_5722_, 2, v_v_5699_);
lean_ctor_set(v_reuseFailAlloc_5722_, 3, v___y_5711_);
lean_ctor_set(v_reuseFailAlloc_5722_, 4, v___x_5716_);
v___x_5721_ = v_reuseFailAlloc_5722_;
goto v_reusejp_5720_;
}
v_reusejp_5720_:
{
return v___x_5721_;
}
}
}
}
v___jp_5731_:
{
lean_object* v___x_5733_; lean_object* v___x_5735_; 
v___x_5733_ = lean_nat_add(v___x_5730_, v___y_5732_);
lean_dec(v___y_5732_);
lean_dec(v___x_5730_);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 4, v_l_5700_);
lean_ctor_set(v___x_5678_, 3, v_l_5527_);
lean_ctor_set(v___x_5678_, 2, v_v_5526_);
lean_ctor_set(v___x_5678_, 1, v_k_5525_);
lean_ctor_set(v___x_5678_, 0, v___x_5733_);
v___x_5735_ = v___x_5678_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v___x_5733_);
lean_ctor_set(v_reuseFailAlloc_5739_, 1, v_k_5525_);
lean_ctor_set(v_reuseFailAlloc_5739_, 2, v_v_5526_);
lean_ctor_set(v_reuseFailAlloc_5739_, 3, v_l_5527_);
lean_ctor_set(v_reuseFailAlloc_5739_, 4, v_l_5700_);
v___x_5735_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
lean_object* v___x_5736_; 
v___x_5736_ = lean_nat_add(v___x_5534_, v_size_5684_);
if (lean_obj_tag(v_r_5701_) == 0)
{
lean_object* v_size_5737_; 
v_size_5737_ = lean_ctor_get(v_r_5701_, 0);
lean_inc(v_size_5737_);
v___y_5711_ = v___x_5735_;
v___y_5712_ = v___x_5736_;
v___y_5713_ = v_size_5737_;
goto v___jp_5710_;
}
else
{
lean_object* v___x_5738_; 
v___x_5738_ = lean_unsigned_to_nat(0u);
v___y_5711_ = v___x_5735_;
v___y_5712_ = v___x_5736_;
v___y_5713_ = v___x_5738_;
goto v___jp_5710_;
}
}
}
}
}
else
{
lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5753_; 
v___x_5748_ = lean_nat_add(v___x_5534_, v_size_5524_);
lean_dec(v_size_5524_);
v___x_5749_ = lean_nat_add(v___x_5748_, v_size_5684_);
lean_dec(v___x_5748_);
v___x_5750_ = lean_nat_add(v___x_5534_, v_size_5684_);
v___x_5751_ = lean_nat_add(v___x_5750_, v_size_5697_);
lean_dec(v___x_5750_);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 4, v_tree_5681_);
lean_ctor_set(v___x_5678_, 3, v_r_5528_);
lean_ctor_set(v___x_5678_, 2, v_v_5683_);
lean_ctor_set(v___x_5678_, 1, v_k_5682_);
lean_ctor_set(v___x_5678_, 0, v___x_5751_);
v___x_5753_ = v___x_5678_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v___x_5751_);
lean_ctor_set(v_reuseFailAlloc_5757_, 1, v_k_5682_);
lean_ctor_set(v_reuseFailAlloc_5757_, 2, v_v_5683_);
lean_ctor_set(v_reuseFailAlloc_5757_, 3, v_r_5528_);
lean_ctor_set(v_reuseFailAlloc_5757_, 4, v_tree_5681_);
v___x_5753_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
lean_object* v___x_5755_; 
if (v_isShared_5695_ == 0)
{
lean_ctor_set(v___x_5694_, 4, v___x_5753_);
lean_ctor_set(v___x_5694_, 0, v___x_5749_);
v___x_5755_ = v___x_5694_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v___x_5749_);
lean_ctor_set(v_reuseFailAlloc_5756_, 1, v_k_5525_);
lean_ctor_set(v_reuseFailAlloc_5756_, 2, v_v_5526_);
lean_ctor_set(v_reuseFailAlloc_5756_, 3, v_l_5527_);
lean_ctor_set(v_reuseFailAlloc_5756_, 4, v___x_5753_);
v___x_5755_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
return v___x_5755_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_5527_) == 0)
{
lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5787_; 
lean_inc_ref(v_l_5527_);
lean_inc(v_v_5526_);
lean_inc(v_k_5525_);
lean_inc(v_size_5524_);
v_isSharedCheck_5787_ = !lean_is_exclusive(v_l_5344_);
if (v_isSharedCheck_5787_ == 0)
{
lean_object* v_unused_5788_; lean_object* v_unused_5789_; lean_object* v_unused_5790_; lean_object* v_unused_5791_; lean_object* v_unused_5792_; 
v_unused_5788_ = lean_ctor_get(v_l_5344_, 4);
lean_dec(v_unused_5788_);
v_unused_5789_ = lean_ctor_get(v_l_5344_, 3);
lean_dec(v_unused_5789_);
v_unused_5790_ = lean_ctor_get(v_l_5344_, 2);
lean_dec(v_unused_5790_);
v_unused_5791_ = lean_ctor_get(v_l_5344_, 1);
lean_dec(v_unused_5791_);
v_unused_5792_ = lean_ctor_get(v_l_5344_, 0);
lean_dec(v_unused_5792_);
v___x_5765_ = v_l_5344_;
v_isShared_5766_ = v_isSharedCheck_5787_;
goto v_resetjp_5764_;
}
else
{
lean_dec(v_l_5344_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5787_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
if (lean_obj_tag(v_r_5528_) == 0)
{
lean_object* v_k_5767_; lean_object* v_v_5768_; lean_object* v_size_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5773_; 
v_k_5767_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_k_5767_);
v_v_5768_ = lean_ctor_get(v___x_5680_, 1);
lean_inc(v_v_5768_);
lean_dec_ref(v___x_5680_);
v_size_5769_ = lean_ctor_get(v_r_5528_, 0);
v___x_5770_ = lean_nat_add(v___x_5534_, v_size_5524_);
lean_dec(v_size_5524_);
v___x_5771_ = lean_nat_add(v___x_5534_, v_size_5769_);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 4, v_tree_5681_);
lean_ctor_set(v___x_5678_, 3, v_r_5528_);
lean_ctor_set(v___x_5678_, 2, v_v_5768_);
lean_ctor_set(v___x_5678_, 1, v_k_5767_);
lean_ctor_set(v___x_5678_, 0, v___x_5771_);
v___x_5773_ = v___x_5678_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v___x_5771_);
lean_ctor_set(v_reuseFailAlloc_5777_, 1, v_k_5767_);
lean_ctor_set(v_reuseFailAlloc_5777_, 2, v_v_5768_);
lean_ctor_set(v_reuseFailAlloc_5777_, 3, v_r_5528_);
lean_ctor_set(v_reuseFailAlloc_5777_, 4, v_tree_5681_);
v___x_5773_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
lean_object* v___x_5775_; 
if (v_isShared_5766_ == 0)
{
lean_ctor_set(v___x_5765_, 4, v___x_5773_);
lean_ctor_set(v___x_5765_, 0, v___x_5770_);
v___x_5775_ = v___x_5765_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v___x_5770_);
lean_ctor_set(v_reuseFailAlloc_5776_, 1, v_k_5525_);
lean_ctor_set(v_reuseFailAlloc_5776_, 2, v_v_5526_);
lean_ctor_set(v_reuseFailAlloc_5776_, 3, v_l_5527_);
lean_ctor_set(v_reuseFailAlloc_5776_, 4, v___x_5773_);
v___x_5775_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
return v___x_5775_;
}
}
}
else
{
lean_object* v_k_5778_; lean_object* v_v_5779_; lean_object* v___x_5780_; lean_object* v___x_5782_; 
lean_dec(v_size_5524_);
v_k_5778_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_k_5778_);
v_v_5779_ = lean_ctor_get(v___x_5680_, 1);
lean_inc(v_v_5779_);
lean_dec_ref(v___x_5680_);
v___x_5780_ = lean_unsigned_to_nat(3u);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 4, v_r_5528_);
lean_ctor_set(v___x_5678_, 3, v_r_5528_);
lean_ctor_set(v___x_5678_, 2, v_v_5779_);
lean_ctor_set(v___x_5678_, 1, v_k_5778_);
lean_ctor_set(v___x_5678_, 0, v___x_5534_);
v___x_5782_ = v___x_5678_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5786_; 
v_reuseFailAlloc_5786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5786_, 0, v___x_5534_);
lean_ctor_set(v_reuseFailAlloc_5786_, 1, v_k_5778_);
lean_ctor_set(v_reuseFailAlloc_5786_, 2, v_v_5779_);
lean_ctor_set(v_reuseFailAlloc_5786_, 3, v_r_5528_);
lean_ctor_set(v_reuseFailAlloc_5786_, 4, v_r_5528_);
v___x_5782_ = v_reuseFailAlloc_5786_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
lean_object* v___x_5784_; 
if (v_isShared_5766_ == 0)
{
lean_ctor_set(v___x_5765_, 4, v___x_5782_);
lean_ctor_set(v___x_5765_, 0, v___x_5780_);
v___x_5784_ = v___x_5765_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v___x_5780_);
lean_ctor_set(v_reuseFailAlloc_5785_, 1, v_k_5525_);
lean_ctor_set(v_reuseFailAlloc_5785_, 2, v_v_5526_);
lean_ctor_set(v_reuseFailAlloc_5785_, 3, v_l_5527_);
lean_ctor_set(v_reuseFailAlloc_5785_, 4, v___x_5782_);
v___x_5784_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
return v___x_5784_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5528_) == 0)
{
lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5817_; 
lean_inc(v_l_5527_);
lean_inc(v_v_5526_);
lean_inc(v_k_5525_);
v_isSharedCheck_5817_ = !lean_is_exclusive(v_l_5344_);
if (v_isSharedCheck_5817_ == 0)
{
lean_object* v_unused_5818_; lean_object* v_unused_5819_; lean_object* v_unused_5820_; lean_object* v_unused_5821_; lean_object* v_unused_5822_; 
v_unused_5818_ = lean_ctor_get(v_l_5344_, 4);
lean_dec(v_unused_5818_);
v_unused_5819_ = lean_ctor_get(v_l_5344_, 3);
lean_dec(v_unused_5819_);
v_unused_5820_ = lean_ctor_get(v_l_5344_, 2);
lean_dec(v_unused_5820_);
v_unused_5821_ = lean_ctor_get(v_l_5344_, 1);
lean_dec(v_unused_5821_);
v_unused_5822_ = lean_ctor_get(v_l_5344_, 0);
lean_dec(v_unused_5822_);
v___x_5794_ = v_l_5344_;
v_isShared_5795_ = v_isSharedCheck_5817_;
goto v_resetjp_5793_;
}
else
{
lean_dec(v_l_5344_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5817_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
lean_object* v_k_5796_; lean_object* v_v_5797_; lean_object* v_k_5798_; lean_object* v_v_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5813_; 
v_k_5796_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_k_5796_);
v_v_5797_ = lean_ctor_get(v___x_5680_, 1);
lean_inc(v_v_5797_);
lean_dec_ref(v___x_5680_);
v_k_5798_ = lean_ctor_get(v_r_5528_, 1);
v_v_5799_ = lean_ctor_get(v_r_5528_, 2);
v_isSharedCheck_5813_ = !lean_is_exclusive(v_r_5528_);
if (v_isSharedCheck_5813_ == 0)
{
lean_object* v_unused_5814_; lean_object* v_unused_5815_; lean_object* v_unused_5816_; 
v_unused_5814_ = lean_ctor_get(v_r_5528_, 4);
lean_dec(v_unused_5814_);
v_unused_5815_ = lean_ctor_get(v_r_5528_, 3);
lean_dec(v_unused_5815_);
v_unused_5816_ = lean_ctor_get(v_r_5528_, 0);
lean_dec(v_unused_5816_);
v___x_5801_ = v_r_5528_;
v_isShared_5802_ = v_isSharedCheck_5813_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_v_5799_);
lean_inc(v_k_5798_);
lean_dec(v_r_5528_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5813_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v___x_5803_; lean_object* v___x_5805_; 
v___x_5803_ = lean_unsigned_to_nat(3u);
if (v_isShared_5802_ == 0)
{
lean_ctor_set(v___x_5801_, 4, v_l_5527_);
lean_ctor_set(v___x_5801_, 3, v_l_5527_);
lean_ctor_set(v___x_5801_, 2, v_v_5526_);
lean_ctor_set(v___x_5801_, 1, v_k_5525_);
lean_ctor_set(v___x_5801_, 0, v___x_5534_);
v___x_5805_ = v___x_5801_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v___x_5534_);
lean_ctor_set(v_reuseFailAlloc_5812_, 1, v_k_5525_);
lean_ctor_set(v_reuseFailAlloc_5812_, 2, v_v_5526_);
lean_ctor_set(v_reuseFailAlloc_5812_, 3, v_l_5527_);
lean_ctor_set(v_reuseFailAlloc_5812_, 4, v_l_5527_);
v___x_5805_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
lean_object* v___x_5807_; 
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 4, v_l_5527_);
lean_ctor_set(v___x_5678_, 3, v_l_5527_);
lean_ctor_set(v___x_5678_, 2, v_v_5797_);
lean_ctor_set(v___x_5678_, 1, v_k_5796_);
lean_ctor_set(v___x_5678_, 0, v___x_5534_);
v___x_5807_ = v___x_5678_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v___x_5534_);
lean_ctor_set(v_reuseFailAlloc_5811_, 1, v_k_5796_);
lean_ctor_set(v_reuseFailAlloc_5811_, 2, v_v_5797_);
lean_ctor_set(v_reuseFailAlloc_5811_, 3, v_l_5527_);
lean_ctor_set(v_reuseFailAlloc_5811_, 4, v_l_5527_);
v___x_5807_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
lean_object* v___x_5809_; 
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 4, v___x_5807_);
lean_ctor_set(v___x_5794_, 3, v___x_5805_);
lean_ctor_set(v___x_5794_, 2, v_v_5799_);
lean_ctor_set(v___x_5794_, 1, v_k_5798_);
lean_ctor_set(v___x_5794_, 0, v___x_5803_);
v___x_5809_ = v___x_5794_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5810_; 
v_reuseFailAlloc_5810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5810_, 0, v___x_5803_);
lean_ctor_set(v_reuseFailAlloc_5810_, 1, v_k_5798_);
lean_ctor_set(v_reuseFailAlloc_5810_, 2, v_v_5799_);
lean_ctor_set(v_reuseFailAlloc_5810_, 3, v___x_5805_);
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
}
else
{
lean_object* v_k_5823_; lean_object* v_v_5824_; lean_object* v___x_5825_; lean_object* v___x_5827_; 
v_k_5823_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_k_5823_);
v_v_5824_ = lean_ctor_get(v___x_5680_, 1);
lean_inc(v_v_5824_);
lean_dec_ref(v___x_5680_);
v___x_5825_ = lean_unsigned_to_nat(2u);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 4, v_r_5528_);
lean_ctor_set(v___x_5678_, 3, v_l_5344_);
lean_ctor_set(v___x_5678_, 2, v_v_5824_);
lean_ctor_set(v___x_5678_, 1, v_k_5823_);
lean_ctor_set(v___x_5678_, 0, v___x_5825_);
v___x_5827_ = v___x_5678_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v___x_5825_);
lean_ctor_set(v_reuseFailAlloc_5828_, 1, v_k_5823_);
lean_ctor_set(v_reuseFailAlloc_5828_, 2, v_v_5824_);
lean_ctor_set(v_reuseFailAlloc_5828_, 3, v_l_5344_);
lean_ctor_set(v_reuseFailAlloc_5828_, 4, v_r_5528_);
v___x_5827_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5826_;
}
v_reusejp_5826_:
{
return v___x_5827_;
}
}
}
}
}
}
}
else
{
return v_l_5344_;
}
}
else
{
return v_r_5345_;
}
}
default: 
{
lean_object* v_impl_5835_; lean_object* v___x_5836_; 
v_impl_5835_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5340_, v_r_5345_);
v___x_5836_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5835_) == 0)
{
if (lean_obj_tag(v_l_5344_) == 0)
{
lean_object* v_size_5837_; lean_object* v_size_5838_; lean_object* v_k_5839_; lean_object* v_v_5840_; lean_object* v_l_5841_; lean_object* v_r_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; uint8_t v___x_5845_; 
v_size_5837_ = lean_ctor_get(v_impl_5835_, 0);
v_size_5838_ = lean_ctor_get(v_l_5344_, 0);
v_k_5839_ = lean_ctor_get(v_l_5344_, 1);
v_v_5840_ = lean_ctor_get(v_l_5344_, 2);
v_l_5841_ = lean_ctor_get(v_l_5344_, 3);
v_r_5842_ = lean_ctor_get(v_l_5344_, 4);
lean_inc(v_r_5842_);
v___x_5843_ = lean_unsigned_to_nat(3u);
v___x_5844_ = lean_nat_mul(v___x_5843_, v_size_5837_);
v___x_5845_ = lean_nat_dec_lt(v___x_5844_, v_size_5838_);
lean_dec(v___x_5844_);
if (v___x_5845_ == 0)
{
lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5849_; 
lean_dec(v_r_5842_);
v___x_5846_ = lean_nat_add(v___x_5836_, v_size_5838_);
v___x_5847_ = lean_nat_add(v___x_5846_, v_size_5837_);
lean_dec(v___x_5846_);
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v_impl_5835_);
lean_ctor_set(v___x_5347_, 0, v___x_5847_);
v___x_5849_ = v___x_5347_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v___x_5847_);
lean_ctor_set(v_reuseFailAlloc_5850_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5850_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5850_, 3, v_l_5344_);
lean_ctor_set(v_reuseFailAlloc_5850_, 4, v_impl_5835_);
v___x_5849_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
return v___x_5849_;
}
}
else
{
lean_object* v___x_5852_; uint8_t v_isShared_5853_; uint8_t v_isSharedCheck_5916_; 
lean_inc(v_l_5841_);
lean_inc(v_v_5840_);
lean_inc(v_k_5839_);
lean_inc(v_size_5838_);
v_isSharedCheck_5916_ = !lean_is_exclusive(v_l_5344_);
if (v_isSharedCheck_5916_ == 0)
{
lean_object* v_unused_5917_; lean_object* v_unused_5918_; lean_object* v_unused_5919_; lean_object* v_unused_5920_; lean_object* v_unused_5921_; 
v_unused_5917_ = lean_ctor_get(v_l_5344_, 4);
lean_dec(v_unused_5917_);
v_unused_5918_ = lean_ctor_get(v_l_5344_, 3);
lean_dec(v_unused_5918_);
v_unused_5919_ = lean_ctor_get(v_l_5344_, 2);
lean_dec(v_unused_5919_);
v_unused_5920_ = lean_ctor_get(v_l_5344_, 1);
lean_dec(v_unused_5920_);
v_unused_5921_ = lean_ctor_get(v_l_5344_, 0);
lean_dec(v_unused_5921_);
v___x_5852_ = v_l_5344_;
v_isShared_5853_ = v_isSharedCheck_5916_;
goto v_resetjp_5851_;
}
else
{
lean_dec(v_l_5344_);
v___x_5852_ = lean_box(0);
v_isShared_5853_ = v_isSharedCheck_5916_;
goto v_resetjp_5851_;
}
v_resetjp_5851_:
{
lean_object* v_size_5854_; lean_object* v_size_5855_; lean_object* v_k_5856_; lean_object* v_v_5857_; lean_object* v_l_5858_; lean_object* v_r_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; uint8_t v___x_5862_; 
v_size_5854_ = lean_ctor_get(v_l_5841_, 0);
v_size_5855_ = lean_ctor_get(v_r_5842_, 0);
v_k_5856_ = lean_ctor_get(v_r_5842_, 1);
v_v_5857_ = lean_ctor_get(v_r_5842_, 2);
v_l_5858_ = lean_ctor_get(v_r_5842_, 3);
v_r_5859_ = lean_ctor_get(v_r_5842_, 4);
v___x_5860_ = lean_unsigned_to_nat(2u);
v___x_5861_ = lean_nat_mul(v___x_5860_, v_size_5854_);
v___x_5862_ = lean_nat_dec_lt(v_size_5855_, v___x_5861_);
lean_dec(v___x_5861_);
if (v___x_5862_ == 0)
{
lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5891_; 
lean_inc(v_r_5859_);
lean_inc(v_l_5858_);
lean_inc(v_v_5857_);
lean_inc(v_k_5856_);
v_isSharedCheck_5891_ = !lean_is_exclusive(v_r_5842_);
if (v_isSharedCheck_5891_ == 0)
{
lean_object* v_unused_5892_; lean_object* v_unused_5893_; lean_object* v_unused_5894_; lean_object* v_unused_5895_; lean_object* v_unused_5896_; 
v_unused_5892_ = lean_ctor_get(v_r_5842_, 4);
lean_dec(v_unused_5892_);
v_unused_5893_ = lean_ctor_get(v_r_5842_, 3);
lean_dec(v_unused_5893_);
v_unused_5894_ = lean_ctor_get(v_r_5842_, 2);
lean_dec(v_unused_5894_);
v_unused_5895_ = lean_ctor_get(v_r_5842_, 1);
lean_dec(v_unused_5895_);
v_unused_5896_ = lean_ctor_get(v_r_5842_, 0);
lean_dec(v_unused_5896_);
v___x_5864_ = v_r_5842_;
v_isShared_5865_ = v_isSharedCheck_5891_;
goto v_resetjp_5863_;
}
else
{
lean_dec(v_r_5842_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5891_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___y_5869_; lean_object* v___y_5870_; lean_object* v___y_5871_; lean_object* v___x_5879_; lean_object* v___y_5881_; 
v___x_5866_ = lean_nat_add(v___x_5836_, v_size_5838_);
lean_dec(v_size_5838_);
v___x_5867_ = lean_nat_add(v___x_5866_, v_size_5837_);
lean_dec(v___x_5866_);
v___x_5879_ = lean_nat_add(v___x_5836_, v_size_5854_);
if (lean_obj_tag(v_l_5858_) == 0)
{
lean_object* v_size_5889_; 
v_size_5889_ = lean_ctor_get(v_l_5858_, 0);
lean_inc(v_size_5889_);
v___y_5881_ = v_size_5889_;
goto v___jp_5880_;
}
else
{
lean_object* v___x_5890_; 
v___x_5890_ = lean_unsigned_to_nat(0u);
v___y_5881_ = v___x_5890_;
goto v___jp_5880_;
}
v___jp_5868_:
{
lean_object* v___x_5872_; lean_object* v___x_5874_; 
v___x_5872_ = lean_nat_add(v___y_5869_, v___y_5871_);
lean_dec(v___y_5871_);
lean_dec(v___y_5869_);
if (v_isShared_5865_ == 0)
{
lean_ctor_set(v___x_5864_, 4, v_impl_5835_);
lean_ctor_set(v___x_5864_, 3, v_r_5859_);
lean_ctor_set(v___x_5864_, 2, v_v_5343_);
lean_ctor_set(v___x_5864_, 1, v_k_5342_);
lean_ctor_set(v___x_5864_, 0, v___x_5872_);
v___x_5874_ = v___x_5864_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5878_; 
v_reuseFailAlloc_5878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5878_, 0, v___x_5872_);
lean_ctor_set(v_reuseFailAlloc_5878_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5878_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5878_, 3, v_r_5859_);
lean_ctor_set(v_reuseFailAlloc_5878_, 4, v_impl_5835_);
v___x_5874_ = v_reuseFailAlloc_5878_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
lean_object* v___x_5876_; 
if (v_isShared_5853_ == 0)
{
lean_ctor_set(v___x_5852_, 4, v___x_5874_);
lean_ctor_set(v___x_5852_, 3, v___y_5870_);
lean_ctor_set(v___x_5852_, 2, v_v_5857_);
lean_ctor_set(v___x_5852_, 1, v_k_5856_);
lean_ctor_set(v___x_5852_, 0, v___x_5867_);
v___x_5876_ = v___x_5852_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v___x_5867_);
lean_ctor_set(v_reuseFailAlloc_5877_, 1, v_k_5856_);
lean_ctor_set(v_reuseFailAlloc_5877_, 2, v_v_5857_);
lean_ctor_set(v_reuseFailAlloc_5877_, 3, v___y_5870_);
lean_ctor_set(v_reuseFailAlloc_5877_, 4, v___x_5874_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
v___jp_5880_:
{
lean_object* v___x_5882_; lean_object* v___x_5884_; 
v___x_5882_ = lean_nat_add(v___x_5879_, v___y_5881_);
lean_dec(v___y_5881_);
lean_dec(v___x_5879_);
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v_l_5858_);
lean_ctor_set(v___x_5347_, 3, v_l_5841_);
lean_ctor_set(v___x_5347_, 2, v_v_5840_);
lean_ctor_set(v___x_5347_, 1, v_k_5839_);
lean_ctor_set(v___x_5347_, 0, v___x_5882_);
v___x_5884_ = v___x_5347_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5888_; 
v_reuseFailAlloc_5888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5888_, 0, v___x_5882_);
lean_ctor_set(v_reuseFailAlloc_5888_, 1, v_k_5839_);
lean_ctor_set(v_reuseFailAlloc_5888_, 2, v_v_5840_);
lean_ctor_set(v_reuseFailAlloc_5888_, 3, v_l_5841_);
lean_ctor_set(v_reuseFailAlloc_5888_, 4, v_l_5858_);
v___x_5884_ = v_reuseFailAlloc_5888_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
lean_object* v___x_5885_; 
v___x_5885_ = lean_nat_add(v___x_5836_, v_size_5837_);
if (lean_obj_tag(v_r_5859_) == 0)
{
lean_object* v_size_5886_; 
v_size_5886_ = lean_ctor_get(v_r_5859_, 0);
lean_inc(v_size_5886_);
v___y_5869_ = v___x_5885_;
v___y_5870_ = v___x_5884_;
v___y_5871_ = v_size_5886_;
goto v___jp_5868_;
}
else
{
lean_object* v___x_5887_; 
v___x_5887_ = lean_unsigned_to_nat(0u);
v___y_5869_ = v___x_5885_;
v___y_5870_ = v___x_5884_;
v___y_5871_ = v___x_5887_;
goto v___jp_5868_;
}
}
}
}
}
else
{
lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5902_; 
lean_del_object(v___x_5347_);
v___x_5897_ = lean_nat_add(v___x_5836_, v_size_5838_);
lean_dec(v_size_5838_);
v___x_5898_ = lean_nat_add(v___x_5897_, v_size_5837_);
lean_dec(v___x_5897_);
v___x_5899_ = lean_nat_add(v___x_5836_, v_size_5837_);
v___x_5900_ = lean_nat_add(v___x_5899_, v_size_5855_);
lean_dec(v___x_5899_);
lean_inc_ref(v_impl_5835_);
if (v_isShared_5853_ == 0)
{
lean_ctor_set(v___x_5852_, 4, v_impl_5835_);
lean_ctor_set(v___x_5852_, 3, v_r_5842_);
lean_ctor_set(v___x_5852_, 2, v_v_5343_);
lean_ctor_set(v___x_5852_, 1, v_k_5342_);
lean_ctor_set(v___x_5852_, 0, v___x_5900_);
v___x_5902_ = v___x_5852_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v___x_5900_);
lean_ctor_set(v_reuseFailAlloc_5915_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5915_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5915_, 3, v_r_5842_);
lean_ctor_set(v_reuseFailAlloc_5915_, 4, v_impl_5835_);
v___x_5902_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
lean_object* v___x_5904_; uint8_t v_isShared_5905_; uint8_t v_isSharedCheck_5909_; 
v_isSharedCheck_5909_ = !lean_is_exclusive(v_impl_5835_);
if (v_isSharedCheck_5909_ == 0)
{
lean_object* v_unused_5910_; lean_object* v_unused_5911_; lean_object* v_unused_5912_; lean_object* v_unused_5913_; lean_object* v_unused_5914_; 
v_unused_5910_ = lean_ctor_get(v_impl_5835_, 4);
lean_dec(v_unused_5910_);
v_unused_5911_ = lean_ctor_get(v_impl_5835_, 3);
lean_dec(v_unused_5911_);
v_unused_5912_ = lean_ctor_get(v_impl_5835_, 2);
lean_dec(v_unused_5912_);
v_unused_5913_ = lean_ctor_get(v_impl_5835_, 1);
lean_dec(v_unused_5913_);
v_unused_5914_ = lean_ctor_get(v_impl_5835_, 0);
lean_dec(v_unused_5914_);
v___x_5904_ = v_impl_5835_;
v_isShared_5905_ = v_isSharedCheck_5909_;
goto v_resetjp_5903_;
}
else
{
lean_dec(v_impl_5835_);
v___x_5904_ = lean_box(0);
v_isShared_5905_ = v_isSharedCheck_5909_;
goto v_resetjp_5903_;
}
v_resetjp_5903_:
{
lean_object* v___x_5907_; 
if (v_isShared_5905_ == 0)
{
lean_ctor_set(v___x_5904_, 4, v___x_5902_);
lean_ctor_set(v___x_5904_, 3, v_l_5841_);
lean_ctor_set(v___x_5904_, 2, v_v_5840_);
lean_ctor_set(v___x_5904_, 1, v_k_5839_);
lean_ctor_set(v___x_5904_, 0, v___x_5898_);
v___x_5907_ = v___x_5904_;
goto v_reusejp_5906_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v___x_5898_);
lean_ctor_set(v_reuseFailAlloc_5908_, 1, v_k_5839_);
lean_ctor_set(v_reuseFailAlloc_5908_, 2, v_v_5840_);
lean_ctor_set(v_reuseFailAlloc_5908_, 3, v_l_5841_);
lean_ctor_set(v_reuseFailAlloc_5908_, 4, v___x_5902_);
v___x_5907_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5906_;
}
v_reusejp_5906_:
{
return v___x_5907_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5922_; lean_object* v___x_5923_; lean_object* v___x_5925_; 
v_size_5922_ = lean_ctor_get(v_impl_5835_, 0);
v___x_5923_ = lean_nat_add(v___x_5836_, v_size_5922_);
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v_impl_5835_);
lean_ctor_set(v___x_5347_, 0, v___x_5923_);
v___x_5925_ = v___x_5347_;
goto v_reusejp_5924_;
}
else
{
lean_object* v_reuseFailAlloc_5926_; 
v_reuseFailAlloc_5926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5926_, 0, v___x_5923_);
lean_ctor_set(v_reuseFailAlloc_5926_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5926_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5926_, 3, v_l_5344_);
lean_ctor_set(v_reuseFailAlloc_5926_, 4, v_impl_5835_);
v___x_5925_ = v_reuseFailAlloc_5926_;
goto v_reusejp_5924_;
}
v_reusejp_5924_:
{
return v___x_5925_;
}
}
}
else
{
if (lean_obj_tag(v_l_5344_) == 0)
{
lean_object* v_l_5927_; 
v_l_5927_ = lean_ctor_get(v_l_5344_, 3);
if (lean_obj_tag(v_l_5927_) == 0)
{
lean_object* v_r_5928_; 
lean_inc_ref(v_l_5927_);
v_r_5928_ = lean_ctor_get(v_l_5344_, 4);
lean_inc(v_r_5928_);
if (lean_obj_tag(v_r_5928_) == 0)
{
lean_object* v_size_5929_; lean_object* v_k_5930_; lean_object* v_v_5931_; lean_object* v___x_5933_; uint8_t v_isShared_5934_; uint8_t v_isSharedCheck_5944_; 
v_size_5929_ = lean_ctor_get(v_l_5344_, 0);
v_k_5930_ = lean_ctor_get(v_l_5344_, 1);
v_v_5931_ = lean_ctor_get(v_l_5344_, 2);
v_isSharedCheck_5944_ = !lean_is_exclusive(v_l_5344_);
if (v_isSharedCheck_5944_ == 0)
{
lean_object* v_unused_5945_; lean_object* v_unused_5946_; 
v_unused_5945_ = lean_ctor_get(v_l_5344_, 4);
lean_dec(v_unused_5945_);
v_unused_5946_ = lean_ctor_get(v_l_5344_, 3);
lean_dec(v_unused_5946_);
v___x_5933_ = v_l_5344_;
v_isShared_5934_ = v_isSharedCheck_5944_;
goto v_resetjp_5932_;
}
else
{
lean_inc(v_v_5931_);
lean_inc(v_k_5930_);
lean_inc(v_size_5929_);
lean_dec(v_l_5344_);
v___x_5933_ = lean_box(0);
v_isShared_5934_ = v_isSharedCheck_5944_;
goto v_resetjp_5932_;
}
v_resetjp_5932_:
{
lean_object* v_size_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5939_; 
v_size_5935_ = lean_ctor_get(v_r_5928_, 0);
v___x_5936_ = lean_nat_add(v___x_5836_, v_size_5929_);
lean_dec(v_size_5929_);
v___x_5937_ = lean_nat_add(v___x_5836_, v_size_5935_);
if (v_isShared_5934_ == 0)
{
lean_ctor_set(v___x_5933_, 4, v_impl_5835_);
lean_ctor_set(v___x_5933_, 3, v_r_5928_);
lean_ctor_set(v___x_5933_, 2, v_v_5343_);
lean_ctor_set(v___x_5933_, 1, v_k_5342_);
lean_ctor_set(v___x_5933_, 0, v___x_5937_);
v___x_5939_ = v___x_5933_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5943_; 
v_reuseFailAlloc_5943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5943_, 0, v___x_5937_);
lean_ctor_set(v_reuseFailAlloc_5943_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5943_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5943_, 3, v_r_5928_);
lean_ctor_set(v_reuseFailAlloc_5943_, 4, v_impl_5835_);
v___x_5939_ = v_reuseFailAlloc_5943_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
lean_object* v___x_5941_; 
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v___x_5939_);
lean_ctor_set(v___x_5347_, 3, v_l_5927_);
lean_ctor_set(v___x_5347_, 2, v_v_5931_);
lean_ctor_set(v___x_5347_, 1, v_k_5930_);
lean_ctor_set(v___x_5347_, 0, v___x_5936_);
v___x_5941_ = v___x_5347_;
goto v_reusejp_5940_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v___x_5936_);
lean_ctor_set(v_reuseFailAlloc_5942_, 1, v_k_5930_);
lean_ctor_set(v_reuseFailAlloc_5942_, 2, v_v_5931_);
lean_ctor_set(v_reuseFailAlloc_5942_, 3, v_l_5927_);
lean_ctor_set(v_reuseFailAlloc_5942_, 4, v___x_5939_);
v___x_5941_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5940_;
}
v_reusejp_5940_:
{
return v___x_5941_;
}
}
}
}
else
{
lean_object* v_k_5947_; lean_object* v_v_5948_; lean_object* v___x_5950_; uint8_t v_isShared_5951_; uint8_t v_isSharedCheck_5959_; 
v_k_5947_ = lean_ctor_get(v_l_5344_, 1);
v_v_5948_ = lean_ctor_get(v_l_5344_, 2);
v_isSharedCheck_5959_ = !lean_is_exclusive(v_l_5344_);
if (v_isSharedCheck_5959_ == 0)
{
lean_object* v_unused_5960_; lean_object* v_unused_5961_; lean_object* v_unused_5962_; 
v_unused_5960_ = lean_ctor_get(v_l_5344_, 4);
lean_dec(v_unused_5960_);
v_unused_5961_ = lean_ctor_get(v_l_5344_, 3);
lean_dec(v_unused_5961_);
v_unused_5962_ = lean_ctor_get(v_l_5344_, 0);
lean_dec(v_unused_5962_);
v___x_5950_ = v_l_5344_;
v_isShared_5951_ = v_isSharedCheck_5959_;
goto v_resetjp_5949_;
}
else
{
lean_inc(v_v_5948_);
lean_inc(v_k_5947_);
lean_dec(v_l_5344_);
v___x_5950_ = lean_box(0);
v_isShared_5951_ = v_isSharedCheck_5959_;
goto v_resetjp_5949_;
}
v_resetjp_5949_:
{
lean_object* v___x_5952_; lean_object* v___x_5954_; 
v___x_5952_ = lean_unsigned_to_nat(3u);
if (v_isShared_5951_ == 0)
{
lean_ctor_set(v___x_5950_, 3, v_r_5928_);
lean_ctor_set(v___x_5950_, 2, v_v_5343_);
lean_ctor_set(v___x_5950_, 1, v_k_5342_);
lean_ctor_set(v___x_5950_, 0, v___x_5836_);
v___x_5954_ = v___x_5950_;
goto v_reusejp_5953_;
}
else
{
lean_object* v_reuseFailAlloc_5958_; 
v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5958_, 0, v___x_5836_);
lean_ctor_set(v_reuseFailAlloc_5958_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5958_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5958_, 3, v_r_5928_);
lean_ctor_set(v_reuseFailAlloc_5958_, 4, v_r_5928_);
v___x_5954_ = v_reuseFailAlloc_5958_;
goto v_reusejp_5953_;
}
v_reusejp_5953_:
{
lean_object* v___x_5956_; 
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v___x_5954_);
lean_ctor_set(v___x_5347_, 3, v_l_5927_);
lean_ctor_set(v___x_5347_, 2, v_v_5948_);
lean_ctor_set(v___x_5347_, 1, v_k_5947_);
lean_ctor_set(v___x_5347_, 0, v___x_5952_);
v___x_5956_ = v___x_5347_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v___x_5952_);
lean_ctor_set(v_reuseFailAlloc_5957_, 1, v_k_5947_);
lean_ctor_set(v_reuseFailAlloc_5957_, 2, v_v_5948_);
lean_ctor_set(v_reuseFailAlloc_5957_, 3, v_l_5927_);
lean_ctor_set(v_reuseFailAlloc_5957_, 4, v___x_5954_);
v___x_5956_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
return v___x_5956_;
}
}
}
}
}
else
{
lean_object* v_r_5963_; 
v_r_5963_ = lean_ctor_get(v_l_5344_, 4);
lean_inc(v_r_5963_);
if (lean_obj_tag(v_r_5963_) == 0)
{
lean_object* v_k_5964_; lean_object* v_v_5965_; lean_object* v___x_5967_; uint8_t v_isShared_5968_; uint8_t v_isSharedCheck_5988_; 
lean_inc(v_l_5927_);
v_k_5964_ = lean_ctor_get(v_l_5344_, 1);
v_v_5965_ = lean_ctor_get(v_l_5344_, 2);
v_isSharedCheck_5988_ = !lean_is_exclusive(v_l_5344_);
if (v_isSharedCheck_5988_ == 0)
{
lean_object* v_unused_5989_; lean_object* v_unused_5990_; lean_object* v_unused_5991_; 
v_unused_5989_ = lean_ctor_get(v_l_5344_, 4);
lean_dec(v_unused_5989_);
v_unused_5990_ = lean_ctor_get(v_l_5344_, 3);
lean_dec(v_unused_5990_);
v_unused_5991_ = lean_ctor_get(v_l_5344_, 0);
lean_dec(v_unused_5991_);
v___x_5967_ = v_l_5344_;
v_isShared_5968_ = v_isSharedCheck_5988_;
goto v_resetjp_5966_;
}
else
{
lean_inc(v_v_5965_);
lean_inc(v_k_5964_);
lean_dec(v_l_5344_);
v___x_5967_ = lean_box(0);
v_isShared_5968_ = v_isSharedCheck_5988_;
goto v_resetjp_5966_;
}
v_resetjp_5966_:
{
lean_object* v_k_5969_; lean_object* v_v_5970_; lean_object* v___x_5972_; uint8_t v_isShared_5973_; uint8_t v_isSharedCheck_5984_; 
v_k_5969_ = lean_ctor_get(v_r_5963_, 1);
v_v_5970_ = lean_ctor_get(v_r_5963_, 2);
v_isSharedCheck_5984_ = !lean_is_exclusive(v_r_5963_);
if (v_isSharedCheck_5984_ == 0)
{
lean_object* v_unused_5985_; lean_object* v_unused_5986_; lean_object* v_unused_5987_; 
v_unused_5985_ = lean_ctor_get(v_r_5963_, 4);
lean_dec(v_unused_5985_);
v_unused_5986_ = lean_ctor_get(v_r_5963_, 3);
lean_dec(v_unused_5986_);
v_unused_5987_ = lean_ctor_get(v_r_5963_, 0);
lean_dec(v_unused_5987_);
v___x_5972_ = v_r_5963_;
v_isShared_5973_ = v_isSharedCheck_5984_;
goto v_resetjp_5971_;
}
else
{
lean_inc(v_v_5970_);
lean_inc(v_k_5969_);
lean_dec(v_r_5963_);
v___x_5972_ = lean_box(0);
v_isShared_5973_ = v_isSharedCheck_5984_;
goto v_resetjp_5971_;
}
v_resetjp_5971_:
{
lean_object* v___x_5974_; lean_object* v___x_5976_; 
v___x_5974_ = lean_unsigned_to_nat(3u);
if (v_isShared_5973_ == 0)
{
lean_ctor_set(v___x_5972_, 4, v_l_5927_);
lean_ctor_set(v___x_5972_, 3, v_l_5927_);
lean_ctor_set(v___x_5972_, 2, v_v_5965_);
lean_ctor_set(v___x_5972_, 1, v_k_5964_);
lean_ctor_set(v___x_5972_, 0, v___x_5836_);
v___x_5976_ = v___x_5972_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v___x_5836_);
lean_ctor_set(v_reuseFailAlloc_5983_, 1, v_k_5964_);
lean_ctor_set(v_reuseFailAlloc_5983_, 2, v_v_5965_);
lean_ctor_set(v_reuseFailAlloc_5983_, 3, v_l_5927_);
lean_ctor_set(v_reuseFailAlloc_5983_, 4, v_l_5927_);
v___x_5976_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
lean_object* v___x_5978_; 
if (v_isShared_5968_ == 0)
{
lean_ctor_set(v___x_5967_, 4, v_l_5927_);
lean_ctor_set(v___x_5967_, 2, v_v_5343_);
lean_ctor_set(v___x_5967_, 1, v_k_5342_);
lean_ctor_set(v___x_5967_, 0, v___x_5836_);
v___x_5978_ = v___x_5967_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v___x_5836_);
lean_ctor_set(v_reuseFailAlloc_5982_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5982_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5982_, 3, v_l_5927_);
lean_ctor_set(v_reuseFailAlloc_5982_, 4, v_l_5927_);
v___x_5978_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
lean_object* v___x_5980_; 
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v___x_5978_);
lean_ctor_set(v___x_5347_, 3, v___x_5976_);
lean_ctor_set(v___x_5347_, 2, v_v_5970_);
lean_ctor_set(v___x_5347_, 1, v_k_5969_);
lean_ctor_set(v___x_5347_, 0, v___x_5974_);
v___x_5980_ = v___x_5347_;
goto v_reusejp_5979_;
}
else
{
lean_object* v_reuseFailAlloc_5981_; 
v_reuseFailAlloc_5981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5981_, 0, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5981_, 1, v_k_5969_);
lean_ctor_set(v_reuseFailAlloc_5981_, 2, v_v_5970_);
lean_ctor_set(v_reuseFailAlloc_5981_, 3, v___x_5976_);
lean_ctor_set(v_reuseFailAlloc_5981_, 4, v___x_5978_);
v___x_5980_ = v_reuseFailAlloc_5981_;
goto v_reusejp_5979_;
}
v_reusejp_5979_:
{
return v___x_5980_;
}
}
}
}
}
}
else
{
lean_object* v___x_5992_; lean_object* v___x_5994_; 
v___x_5992_ = lean_unsigned_to_nat(2u);
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v_r_5963_);
lean_ctor_set(v___x_5347_, 0, v___x_5992_);
v___x_5994_ = v___x_5347_;
goto v_reusejp_5993_;
}
else
{
lean_object* v_reuseFailAlloc_5995_; 
v_reuseFailAlloc_5995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5995_, 0, v___x_5992_);
lean_ctor_set(v_reuseFailAlloc_5995_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5995_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5995_, 3, v_l_5344_);
lean_ctor_set(v_reuseFailAlloc_5995_, 4, v_r_5963_);
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
else
{
lean_object* v___x_5997_; 
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 4, v_l_5344_);
lean_ctor_set(v___x_5347_, 0, v___x_5836_);
v___x_5997_ = v___x_5347_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_5998_; 
v_reuseFailAlloc_5998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5998_, 0, v___x_5836_);
lean_ctor_set(v_reuseFailAlloc_5998_, 1, v_k_5342_);
lean_ctor_set(v_reuseFailAlloc_5998_, 2, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5998_, 3, v_l_5344_);
lean_ctor_set(v_reuseFailAlloc_5998_, 4, v_l_5344_);
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
}
}
}
else
{
return v_t_5341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_6001_, lean_object* v_t_6002_){
_start:
{
lean_object* v_res_6003_; 
v_res_6003_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6001_, v_t_6002_);
lean_dec(v_k_6001_);
return v_res_6003_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_6004_, lean_object* v_x_6005_){
_start:
{
if (lean_obj_tag(v_x_6005_) == 0)
{
lean_object* v_k_6006_; lean_object* v_l_6007_; lean_object* v_r_6008_; lean_object* v___x_6009_; lean_object* v_ileans_6010_; lean_object* v_workers_6011_; lean_object* v___x_6013_; uint8_t v_isShared_6014_; uint8_t v_isSharedCheck_6020_; 
v_k_6006_ = lean_ctor_get(v_x_6005_, 1);
v_l_6007_ = lean_ctor_get(v_x_6005_, 3);
v_r_6008_ = lean_ctor_get(v_x_6005_, 4);
v___x_6009_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6004_, v_l_6007_);
v_ileans_6010_ = lean_ctor_get(v___x_6009_, 0);
v_workers_6011_ = lean_ctor_get(v___x_6009_, 1);
v_isSharedCheck_6020_ = !lean_is_exclusive(v___x_6009_);
if (v_isSharedCheck_6020_ == 0)
{
v___x_6013_ = v___x_6009_;
v_isShared_6014_ = v_isSharedCheck_6020_;
goto v_resetjp_6012_;
}
else
{
lean_inc(v_workers_6011_);
lean_inc(v_ileans_6010_);
lean_dec(v___x_6009_);
v___x_6013_ = lean_box(0);
v_isShared_6014_ = v_isSharedCheck_6020_;
goto v_resetjp_6012_;
}
v_resetjp_6012_:
{
lean_object* v___x_6015_; lean_object* v___x_6017_; 
v___x_6015_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6006_, v_ileans_6010_);
if (v_isShared_6014_ == 0)
{
lean_ctor_set(v___x_6013_, 0, v___x_6015_);
v___x_6017_ = v___x_6013_;
goto v_reusejp_6016_;
}
else
{
lean_object* v_reuseFailAlloc_6019_; 
v_reuseFailAlloc_6019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6019_, 0, v___x_6015_);
lean_ctor_set(v_reuseFailAlloc_6019_, 1, v_workers_6011_);
v___x_6017_ = v_reuseFailAlloc_6019_;
goto v_reusejp_6016_;
}
v_reusejp_6016_:
{
v_init_6004_ = v___x_6017_;
v_x_6005_ = v_r_6008_;
goto _start;
}
}
}
else
{
return v_init_6004_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_6021_, lean_object* v_x_6022_){
_start:
{
lean_object* v_res_6023_; 
v_res_6023_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6021_, v_x_6022_);
lean_dec(v_x_6022_);
return v_res_6023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_6024_, lean_object* v_path_6025_){
_start:
{
lean_object* v_ileans_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; 
v_ileans_6026_ = lean_ctor_get(v_self_6024_, 0);
lean_inc(v_ileans_6026_);
v___x_6027_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6025_, v_ileans_6026_);
v___x_6028_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_6024_, v___x_6027_);
lean_dec(v___x_6027_);
return v___x_6028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_6029_, lean_object* v_path_6030_){
_start:
{
lean_object* v_res_6031_; 
v_res_6031_ = l_Lean_Server_References_removeIlean(v_self_6029_, v_path_6030_);
lean_dec_ref(v_path_6030_);
return v_res_6031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_6032_, lean_object* v_k_6033_, lean_object* v_t_6034_, lean_object* v_h_6035_){
_start:
{
lean_object* v___x_6036_; 
v___x_6036_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6033_, v_t_6034_);
return v___x_6036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_6037_, lean_object* v_k_6038_, lean_object* v_t_6039_, lean_object* v_h_6040_){
_start:
{
lean_object* v_res_6041_; 
v_res_6041_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_6037_, v_k_6038_, v_t_6039_, v_h_6040_);
lean_dec(v_k_6038_);
return v_res_6041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_6042_, lean_object* v_t_6043_, lean_object* v_hl_6044_){
_start:
{
lean_object* v___x_6045_; 
v___x_6045_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6042_, v_t_6043_);
return v___x_6045_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_6046_, lean_object* v_t_6047_, lean_object* v_hl_6048_){
_start:
{
lean_object* v_res_6049_; 
v_res_6049_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_6046_, v_t_6047_, v_hl_6048_);
lean_dec_ref(v_path_6046_);
return v_res_6049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_6050_, lean_object* v_t_6051_){
_start:
{
lean_object* v___x_6052_; 
v___x_6052_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6050_, v_t_6051_);
return v___x_6052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_6053_, lean_object* v_t_6054_){
_start:
{
lean_object* v_res_6055_; 
v_res_6055_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_6053_, v_t_6054_);
lean_dec(v_t_6054_);
return v_res_6055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_6056_, lean_object* v_k_6057_){
_start:
{
if (lean_obj_tag(v_t_6056_) == 0)
{
lean_object* v_k_6058_; lean_object* v_v_6059_; lean_object* v_l_6060_; lean_object* v_r_6061_; uint8_t v___x_6062_; 
v_k_6058_ = lean_ctor_get(v_t_6056_, 1);
v_v_6059_ = lean_ctor_get(v_t_6056_, 2);
v_l_6060_ = lean_ctor_get(v_t_6056_, 3);
v_r_6061_ = lean_ctor_get(v_t_6056_, 4);
v___x_6062_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6057_, v_k_6058_);
switch(v___x_6062_)
{
case 0:
{
v_t_6056_ = v_l_6060_;
goto _start;
}
case 1:
{
lean_object* v___x_6064_; 
lean_inc(v_v_6059_);
v___x_6064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6064_, 0, v_v_6059_);
return v___x_6064_;
}
default: 
{
v_t_6056_ = v_r_6061_;
goto _start;
}
}
}
else
{
lean_object* v___x_6066_; 
v___x_6066_ = lean_box(0);
return v___x_6066_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_6067_, lean_object* v_k_6068_){
_start:
{
lean_object* v_res_6069_; 
v_res_6069_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6067_, v_k_6068_);
lean_dec(v_k_6068_);
lean_dec(v_t_6067_);
return v_res_6069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_6070_, lean_object* v_name_6071_, lean_object* v_moduleUri_6072_, lean_object* v_version_6073_, lean_object* v_directImports_6074_, uint8_t v_isSetupFailure_6075_){
_start:
{
lean_object* v___x_6077_; lean_object* v___x_6078_; 
v___x_6077_ = lean_box(1);
v___x_6078_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_6074_);
if (lean_obj_tag(v___x_6078_) == 0)
{
lean_object* v_a_6079_; lean_object* v___x_6081_; uint8_t v_isShared_6082_; uint8_t v_isSharedCheck_6144_; 
v_a_6079_ = lean_ctor_get(v___x_6078_, 0);
v_isSharedCheck_6144_ = !lean_is_exclusive(v___x_6078_);
if (v_isSharedCheck_6144_ == 0)
{
v___x_6081_ = v___x_6078_;
v_isShared_6082_ = v_isSharedCheck_6144_;
goto v_resetjp_6080_;
}
else
{
lean_inc(v_a_6079_);
lean_dec(v___x_6078_);
v___x_6081_ = lean_box(0);
v_isShared_6082_ = v_isSharedCheck_6144_;
goto v_resetjp_6080_;
}
v_resetjp_6080_:
{
lean_object* v_ileans_6083_; lean_object* v_workers_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; 
v_ileans_6083_ = lean_ctor_get(v_self_6070_, 0);
v_workers_6084_ = lean_ctor_get(v_self_6070_, 1);
v___x_6085_ = lean_box(v_isSetupFailure_6075_);
v___x_6086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
v___x_6087_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6084_, v_name_6071_);
if (lean_obj_tag(v___x_6087_) == 1)
{
lean_object* v_val_6088_; lean_object* v_version_6089_; lean_object* v_refs_6090_; lean_object* v_decls_6091_; lean_object* v___x_6093_; uint8_t v_isShared_6094_; uint8_t v_isSharedCheck_6126_; 
v_val_6088_ = lean_ctor_get(v___x_6087_, 0);
lean_inc(v_val_6088_);
lean_dec_ref_known(v___x_6087_, 1);
v_version_6089_ = lean_ctor_get(v_val_6088_, 1);
v_refs_6090_ = lean_ctor_get(v_val_6088_, 4);
v_decls_6091_ = lean_ctor_get(v_val_6088_, 5);
v_isSharedCheck_6126_ = !lean_is_exclusive(v_val_6088_);
if (v_isSharedCheck_6126_ == 0)
{
lean_object* v_unused_6127_; lean_object* v_unused_6128_; lean_object* v_unused_6129_; 
v_unused_6127_ = lean_ctor_get(v_val_6088_, 3);
lean_dec(v_unused_6127_);
v_unused_6128_ = lean_ctor_get(v_val_6088_, 2);
lean_dec(v_unused_6128_);
v_unused_6129_ = lean_ctor_get(v_val_6088_, 0);
lean_dec(v_unused_6129_);
v___x_6093_ = v_val_6088_;
v_isShared_6094_ = v_isSharedCheck_6126_;
goto v_resetjp_6092_;
}
else
{
lean_inc(v_decls_6091_);
lean_inc(v_refs_6090_);
lean_inc(v_version_6089_);
lean_dec(v_val_6088_);
v___x_6093_ = lean_box(0);
v_isShared_6094_ = v_isSharedCheck_6126_;
goto v_resetjp_6092_;
}
v_resetjp_6092_:
{
uint8_t v___x_6095_; 
v___x_6095_ = lean_nat_dec_lt(v_version_6073_, v_version_6089_);
if (v___x_6095_ == 0)
{
lean_object* v___x_6097_; uint8_t v_isShared_6098_; uint8_t v_isSharedCheck_6120_; 
lean_inc(v_workers_6084_);
lean_inc(v_ileans_6083_);
v_isSharedCheck_6120_ = !lean_is_exclusive(v_self_6070_);
if (v_isSharedCheck_6120_ == 0)
{
lean_object* v_unused_6121_; lean_object* v_unused_6122_; 
v_unused_6121_ = lean_ctor_get(v_self_6070_, 1);
lean_dec(v_unused_6121_);
v_unused_6122_ = lean_ctor_get(v_self_6070_, 0);
lean_dec(v_unused_6122_);
v___x_6097_ = v_self_6070_;
v_isShared_6098_ = v_isSharedCheck_6120_;
goto v_resetjp_6096_;
}
else
{
lean_dec(v_self_6070_);
v___x_6097_ = lean_box(0);
v_isShared_6098_ = v_isSharedCheck_6120_;
goto v_resetjp_6096_;
}
v_resetjp_6096_:
{
uint8_t v___x_6099_; 
v___x_6099_ = lean_nat_dec_eq(v_version_6073_, v_version_6089_);
lean_dec(v_version_6089_);
if (v___x_6099_ == 0)
{
lean_object* v___x_6101_; 
lean_dec(v_decls_6091_);
lean_dec(v_refs_6090_);
if (v_isShared_6094_ == 0)
{
lean_ctor_set(v___x_6093_, 5, v___x_6077_);
lean_ctor_set(v___x_6093_, 4, v___x_6077_);
lean_ctor_set(v___x_6093_, 3, v___x_6086_);
lean_ctor_set(v___x_6093_, 2, v_a_6079_);
lean_ctor_set(v___x_6093_, 1, v_version_6073_);
lean_ctor_set(v___x_6093_, 0, v_moduleUri_6072_);
v___x_6101_ = v___x_6093_;
goto v_reusejp_6100_;
}
else
{
lean_object* v_reuseFailAlloc_6109_; 
v_reuseFailAlloc_6109_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6109_, 0, v_moduleUri_6072_);
lean_ctor_set(v_reuseFailAlloc_6109_, 1, v_version_6073_);
lean_ctor_set(v_reuseFailAlloc_6109_, 2, v_a_6079_);
lean_ctor_set(v_reuseFailAlloc_6109_, 3, v___x_6086_);
lean_ctor_set(v_reuseFailAlloc_6109_, 4, v___x_6077_);
lean_ctor_set(v_reuseFailAlloc_6109_, 5, v___x_6077_);
v___x_6101_ = v_reuseFailAlloc_6109_;
goto v_reusejp_6100_;
}
v_reusejp_6100_:
{
lean_object* v___x_6102_; lean_object* v___x_6104_; 
v___x_6102_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6071_, v___x_6101_, v_workers_6084_);
if (v_isShared_6098_ == 0)
{
lean_ctor_set(v___x_6097_, 1, v___x_6102_);
v___x_6104_ = v___x_6097_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6108_; 
v_reuseFailAlloc_6108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6108_, 0, v_ileans_6083_);
lean_ctor_set(v_reuseFailAlloc_6108_, 1, v___x_6102_);
v___x_6104_ = v_reuseFailAlloc_6108_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
lean_object* v___x_6106_; 
if (v_isShared_6082_ == 0)
{
lean_ctor_set(v___x_6081_, 0, v___x_6104_);
v___x_6106_ = v___x_6081_;
goto v_reusejp_6105_;
}
else
{
lean_object* v_reuseFailAlloc_6107_; 
v_reuseFailAlloc_6107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6107_, 0, v___x_6104_);
v___x_6106_ = v_reuseFailAlloc_6107_;
goto v_reusejp_6105_;
}
v_reusejp_6105_:
{
return v___x_6106_;
}
}
}
}
else
{
lean_object* v___x_6111_; 
if (v_isShared_6094_ == 0)
{
lean_ctor_set(v___x_6093_, 3, v___x_6086_);
lean_ctor_set(v___x_6093_, 2, v_a_6079_);
lean_ctor_set(v___x_6093_, 1, v_version_6073_);
lean_ctor_set(v___x_6093_, 0, v_moduleUri_6072_);
v___x_6111_ = v___x_6093_;
goto v_reusejp_6110_;
}
else
{
lean_object* v_reuseFailAlloc_6119_; 
v_reuseFailAlloc_6119_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_moduleUri_6072_);
lean_ctor_set(v_reuseFailAlloc_6119_, 1, v_version_6073_);
lean_ctor_set(v_reuseFailAlloc_6119_, 2, v_a_6079_);
lean_ctor_set(v_reuseFailAlloc_6119_, 3, v___x_6086_);
lean_ctor_set(v_reuseFailAlloc_6119_, 4, v_refs_6090_);
lean_ctor_set(v_reuseFailAlloc_6119_, 5, v_decls_6091_);
v___x_6111_ = v_reuseFailAlloc_6119_;
goto v_reusejp_6110_;
}
v_reusejp_6110_:
{
lean_object* v___x_6112_; lean_object* v___x_6114_; 
v___x_6112_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6071_, v___x_6111_, v_workers_6084_);
if (v_isShared_6098_ == 0)
{
lean_ctor_set(v___x_6097_, 1, v___x_6112_);
v___x_6114_ = v___x_6097_;
goto v_reusejp_6113_;
}
else
{
lean_object* v_reuseFailAlloc_6118_; 
v_reuseFailAlloc_6118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6118_, 0, v_ileans_6083_);
lean_ctor_set(v_reuseFailAlloc_6118_, 1, v___x_6112_);
v___x_6114_ = v_reuseFailAlloc_6118_;
goto v_reusejp_6113_;
}
v_reusejp_6113_:
{
lean_object* v___x_6116_; 
if (v_isShared_6082_ == 0)
{
lean_ctor_set(v___x_6081_, 0, v___x_6114_);
v___x_6116_ = v___x_6081_;
goto v_reusejp_6115_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v___x_6114_);
v___x_6116_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6115_;
}
v_reusejp_6115_:
{
return v___x_6116_;
}
}
}
}
}
}
else
{
lean_object* v___x_6124_; 
lean_del_object(v___x_6093_);
lean_dec(v_decls_6091_);
lean_dec(v_refs_6090_);
lean_dec(v_version_6089_);
lean_dec_ref_known(v___x_6086_, 1);
lean_dec(v_a_6079_);
lean_dec(v_version_6073_);
lean_dec_ref(v_moduleUri_6072_);
lean_dec(v_name_6071_);
if (v_isShared_6082_ == 0)
{
lean_ctor_set(v___x_6081_, 0, v_self_6070_);
v___x_6124_ = v___x_6081_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_self_6070_);
v___x_6124_ = v_reuseFailAlloc_6125_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
return v___x_6124_;
}
}
}
}
else
{
lean_object* v___x_6131_; uint8_t v_isShared_6132_; uint8_t v_isSharedCheck_6141_; 
lean_inc(v_workers_6084_);
lean_inc(v_ileans_6083_);
lean_dec(v___x_6087_);
v_isSharedCheck_6141_ = !lean_is_exclusive(v_self_6070_);
if (v_isSharedCheck_6141_ == 0)
{
lean_object* v_unused_6142_; lean_object* v_unused_6143_; 
v_unused_6142_ = lean_ctor_get(v_self_6070_, 1);
lean_dec(v_unused_6142_);
v_unused_6143_ = lean_ctor_get(v_self_6070_, 0);
lean_dec(v_unused_6143_);
v___x_6131_ = v_self_6070_;
v_isShared_6132_ = v_isSharedCheck_6141_;
goto v_resetjp_6130_;
}
else
{
lean_dec(v_self_6070_);
v___x_6131_ = lean_box(0);
v_isShared_6132_ = v_isSharedCheck_6141_;
goto v_resetjp_6130_;
}
v_resetjp_6130_:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6136_; 
v___x_6133_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6133_, 0, v_moduleUri_6072_);
lean_ctor_set(v___x_6133_, 1, v_version_6073_);
lean_ctor_set(v___x_6133_, 2, v_a_6079_);
lean_ctor_set(v___x_6133_, 3, v___x_6086_);
lean_ctor_set(v___x_6133_, 4, v___x_6077_);
lean_ctor_set(v___x_6133_, 5, v___x_6077_);
v___x_6134_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6071_, v___x_6133_, v_workers_6084_);
if (v_isShared_6132_ == 0)
{
lean_ctor_set(v___x_6131_, 1, v___x_6134_);
v___x_6136_ = v___x_6131_;
goto v_reusejp_6135_;
}
else
{
lean_object* v_reuseFailAlloc_6140_; 
v_reuseFailAlloc_6140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6140_, 0, v_ileans_6083_);
lean_ctor_set(v_reuseFailAlloc_6140_, 1, v___x_6134_);
v___x_6136_ = v_reuseFailAlloc_6140_;
goto v_reusejp_6135_;
}
v_reusejp_6135_:
{
lean_object* v___x_6138_; 
if (v_isShared_6082_ == 0)
{
lean_ctor_set(v___x_6081_, 0, v___x_6136_);
v___x_6138_ = v___x_6081_;
goto v_reusejp_6137_;
}
else
{
lean_object* v_reuseFailAlloc_6139_; 
v_reuseFailAlloc_6139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6139_, 0, v___x_6136_);
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
}
}
else
{
lean_object* v_a_6145_; lean_object* v___x_6147_; uint8_t v_isShared_6148_; uint8_t v_isSharedCheck_6152_; 
lean_dec(v_version_6073_);
lean_dec_ref(v_moduleUri_6072_);
lean_dec(v_name_6071_);
lean_dec_ref(v_self_6070_);
v_a_6145_ = lean_ctor_get(v___x_6078_, 0);
v_isSharedCheck_6152_ = !lean_is_exclusive(v___x_6078_);
if (v_isSharedCheck_6152_ == 0)
{
v___x_6147_ = v___x_6078_;
v_isShared_6148_ = v_isSharedCheck_6152_;
goto v_resetjp_6146_;
}
else
{
lean_inc(v_a_6145_);
lean_dec(v___x_6078_);
v___x_6147_ = lean_box(0);
v_isShared_6148_ = v_isSharedCheck_6152_;
goto v_resetjp_6146_;
}
v_resetjp_6146_:
{
lean_object* v___x_6150_; 
if (v_isShared_6148_ == 0)
{
v___x_6150_ = v___x_6147_;
goto v_reusejp_6149_;
}
else
{
lean_object* v_reuseFailAlloc_6151_; 
v_reuseFailAlloc_6151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6151_, 0, v_a_6145_);
v___x_6150_ = v_reuseFailAlloc_6151_;
goto v_reusejp_6149_;
}
v_reusejp_6149_:
{
return v___x_6150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6153_, lean_object* v_name_6154_, lean_object* v_moduleUri_6155_, lean_object* v_version_6156_, lean_object* v_directImports_6157_, lean_object* v_isSetupFailure_6158_, lean_object* v_a_6159_){
_start:
{
uint8_t v_isSetupFailure_boxed_6160_; lean_object* v_res_6161_; 
v_isSetupFailure_boxed_6160_ = lean_unbox(v_isSetupFailure_6158_);
v_res_6161_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6153_, v_name_6154_, v_moduleUri_6155_, v_version_6156_, v_directImports_6157_, v_isSetupFailure_boxed_6160_);
lean_dec_ref(v_directImports_6157_);
return v_res_6161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6162_, lean_object* v_t_6163_, lean_object* v_k_6164_){
_start:
{
lean_object* v___x_6165_; 
v___x_6165_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6163_, v_k_6164_);
return v___x_6165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6166_, lean_object* v_t_6167_, lean_object* v_k_6168_){
_start:
{
lean_object* v_res_6169_; 
v_res_6169_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6166_, v_t_6167_, v_k_6168_);
lean_dec(v_k_6168_);
lean_dec(v_t_6167_);
return v_res_6169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6170_, lean_object* v_____s_6171_){
_start:
{
lean_object* v_fst_6172_; lean_object* v_snd_6173_; lean_object* v_r_6174_; lean_object* v___x_6175_; 
v_fst_6172_ = lean_ctor_get(v_x_6170_, 0);
lean_inc(v_fst_6172_);
v_snd_6173_ = lean_ctor_get(v_x_6170_, 1);
lean_inc(v_snd_6173_);
lean_dec_ref(v_x_6170_);
v_r_6174_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6172_, v_snd_6173_, v_____s_6171_);
v___x_6175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6175_, 0, v_r_6174_);
return v___x_6175_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6176_, lean_object* v_k_6177_, lean_object* v_fallback_6178_){
_start:
{
if (lean_obj_tag(v_t_6176_) == 0)
{
lean_object* v_k_6179_; lean_object* v_v_6180_; lean_object* v_l_6181_; lean_object* v_r_6182_; uint8_t v___x_6183_; 
v_k_6179_ = lean_ctor_get(v_t_6176_, 1);
v_v_6180_ = lean_ctor_get(v_t_6176_, 2);
v_l_6181_ = lean_ctor_get(v_t_6176_, 3);
v_r_6182_ = lean_ctor_get(v_t_6176_, 4);
v___x_6183_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6177_, v_k_6179_);
switch(v___x_6183_)
{
case 0:
{
v_t_6176_ = v_l_6181_;
goto _start;
}
case 1:
{
lean_inc(v_v_6180_);
return v_v_6180_;
}
default: 
{
v_t_6176_ = v_r_6182_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6178_);
return v_fallback_6178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6186_, lean_object* v_k_6187_, lean_object* v_fallback_6188_){
_start:
{
lean_object* v_res_6189_; 
v_res_6189_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6186_, v_k_6187_, v_fallback_6188_);
lean_dec(v_fallback_6188_);
lean_dec_ref(v_k_6187_);
lean_dec(v_t_6186_);
return v_res_6189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6190_, lean_object* v_x_6191_){
_start:
{
if (lean_obj_tag(v_x_6191_) == 0)
{
lean_object* v_k_6192_; lean_object* v_v_6193_; lean_object* v_l_6194_; lean_object* v_r_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; 
v_k_6192_ = lean_ctor_get(v_x_6191_, 1);
lean_inc(v_k_6192_);
v_v_6193_ = lean_ctor_get(v_x_6191_, 2);
lean_inc(v_v_6193_);
v_l_6194_ = lean_ctor_get(v_x_6191_, 3);
lean_inc(v_l_6194_);
v_r_6195_ = lean_ctor_get(v_x_6191_, 4);
lean_inc(v_r_6195_);
lean_dec_ref_known(v_x_6191_, 5);
v___x_6196_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6190_, v_l_6194_);
v___x_6197_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6198_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6196_, v_k_6192_, v___x_6197_);
v___x_6199_ = l_Lean_Lsp_RefInfo_merge(v___x_6198_, v_v_6193_);
v___x_6200_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6192_, v___x_6199_, v___x_6196_);
v_init_6190_ = v___x_6200_;
v_x_6191_ = v_r_6195_;
goto _start;
}
else
{
return v_init_6190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6203_, lean_object* v_name_6204_, lean_object* v_moduleUri_6205_, lean_object* v_version_6206_, lean_object* v_refs_6207_, lean_object* v_decls_6208_){
_start:
{
lean_object* v_ileans_6210_; lean_object* v_workers_6211_; lean_object* v___x_6212_; 
v_ileans_6210_ = lean_ctor_get(v_self_6203_, 0);
v_workers_6211_ = lean_ctor_get(v_self_6203_, 1);
v___x_6212_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6211_, v_name_6204_);
if (lean_obj_tag(v___x_6212_) == 1)
{
lean_object* v_val_6213_; lean_object* v___x_6215_; uint8_t v_isShared_6216_; uint8_t v_isSharedCheck_6261_; 
v_val_6213_ = lean_ctor_get(v___x_6212_, 0);
v_isSharedCheck_6261_ = !lean_is_exclusive(v___x_6212_);
if (v_isSharedCheck_6261_ == 0)
{
v___x_6215_ = v___x_6212_;
v_isShared_6216_ = v_isSharedCheck_6261_;
goto v_resetjp_6214_;
}
else
{
lean_inc(v_val_6213_);
lean_dec(v___x_6212_);
v___x_6215_ = lean_box(0);
v_isShared_6216_ = v_isSharedCheck_6261_;
goto v_resetjp_6214_;
}
v_resetjp_6214_:
{
lean_object* v_version_6217_; lean_object* v_directImports_6218_; lean_object* v_isSetupFailure_x3f_6219_; lean_object* v_refs_6220_; lean_object* v_decls_6221_; lean_object* v___x_6223_; uint8_t v_isShared_6224_; uint8_t v_isSharedCheck_6259_; 
v_version_6217_ = lean_ctor_get(v_val_6213_, 1);
v_directImports_6218_ = lean_ctor_get(v_val_6213_, 2);
v_isSetupFailure_x3f_6219_ = lean_ctor_get(v_val_6213_, 3);
v_refs_6220_ = lean_ctor_get(v_val_6213_, 4);
v_decls_6221_ = lean_ctor_get(v_val_6213_, 5);
v_isSharedCheck_6259_ = !lean_is_exclusive(v_val_6213_);
if (v_isSharedCheck_6259_ == 0)
{
lean_object* v_unused_6260_; 
v_unused_6260_ = lean_ctor_get(v_val_6213_, 0);
lean_dec(v_unused_6260_);
v___x_6223_ = v_val_6213_;
v_isShared_6224_ = v_isSharedCheck_6259_;
goto v_resetjp_6222_;
}
else
{
lean_inc(v_decls_6221_);
lean_inc(v_refs_6220_);
lean_inc(v_isSetupFailure_x3f_6219_);
lean_inc(v_directImports_6218_);
lean_inc(v_version_6217_);
lean_dec(v_val_6213_);
v___x_6223_ = lean_box(0);
v_isShared_6224_ = v_isSharedCheck_6259_;
goto v_resetjp_6222_;
}
v_resetjp_6222_:
{
uint8_t v___x_6225_; 
v___x_6225_ = lean_nat_dec_lt(v_version_6206_, v_version_6217_);
if (v___x_6225_ == 0)
{
lean_object* v___x_6227_; uint8_t v_isShared_6228_; uint8_t v_isSharedCheck_6253_; 
lean_inc(v_workers_6211_);
lean_inc(v_ileans_6210_);
v_isSharedCheck_6253_ = !lean_is_exclusive(v_self_6203_);
if (v_isSharedCheck_6253_ == 0)
{
lean_object* v_unused_6254_; lean_object* v_unused_6255_; 
v_unused_6254_ = lean_ctor_get(v_self_6203_, 1);
lean_dec(v_unused_6254_);
v_unused_6255_ = lean_ctor_get(v_self_6203_, 0);
lean_dec(v_unused_6255_);
v___x_6227_ = v_self_6203_;
v_isShared_6228_ = v_isSharedCheck_6253_;
goto v_resetjp_6226_;
}
else
{
lean_dec(v_self_6203_);
v___x_6227_ = lean_box(0);
v_isShared_6228_ = v_isSharedCheck_6253_;
goto v_resetjp_6226_;
}
v_resetjp_6226_:
{
uint8_t v___x_6229_; 
v___x_6229_ = lean_nat_dec_eq(v_version_6206_, v_version_6217_);
lean_dec(v_version_6217_);
if (v___x_6229_ == 0)
{
lean_object* v___x_6231_; 
lean_dec(v_decls_6221_);
lean_dec(v_refs_6220_);
if (v_isShared_6224_ == 0)
{
lean_ctor_set(v___x_6223_, 5, v_decls_6208_);
lean_ctor_set(v___x_6223_, 4, v_refs_6207_);
lean_ctor_set(v___x_6223_, 1, v_version_6206_);
lean_ctor_set(v___x_6223_, 0, v_moduleUri_6205_);
v___x_6231_ = v___x_6223_;
goto v_reusejp_6230_;
}
else
{
lean_object* v_reuseFailAlloc_6239_; 
v_reuseFailAlloc_6239_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6239_, 0, v_moduleUri_6205_);
lean_ctor_set(v_reuseFailAlloc_6239_, 1, v_version_6206_);
lean_ctor_set(v_reuseFailAlloc_6239_, 2, v_directImports_6218_);
lean_ctor_set(v_reuseFailAlloc_6239_, 3, v_isSetupFailure_x3f_6219_);
lean_ctor_set(v_reuseFailAlloc_6239_, 4, v_refs_6207_);
lean_ctor_set(v_reuseFailAlloc_6239_, 5, v_decls_6208_);
v___x_6231_ = v_reuseFailAlloc_6239_;
goto v_reusejp_6230_;
}
v_reusejp_6230_:
{
lean_object* v___x_6232_; lean_object* v___x_6234_; 
v___x_6232_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6204_, v___x_6231_, v_workers_6211_);
if (v_isShared_6228_ == 0)
{
lean_ctor_set(v___x_6227_, 1, v___x_6232_);
v___x_6234_ = v___x_6227_;
goto v_reusejp_6233_;
}
else
{
lean_object* v_reuseFailAlloc_6238_; 
v_reuseFailAlloc_6238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_ileans_6210_);
lean_ctor_set(v_reuseFailAlloc_6238_, 1, v___x_6232_);
v___x_6234_ = v_reuseFailAlloc_6238_;
goto v_reusejp_6233_;
}
v_reusejp_6233_:
{
lean_object* v___x_6236_; 
if (v_isShared_6216_ == 0)
{
lean_ctor_set_tag(v___x_6215_, 0);
lean_ctor_set(v___x_6215_, 0, v___x_6234_);
v___x_6236_ = v___x_6215_;
goto v_reusejp_6235_;
}
else
{
lean_object* v_reuseFailAlloc_6237_; 
v_reuseFailAlloc_6237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6237_, 0, v___x_6234_);
v___x_6236_ = v_reuseFailAlloc_6237_;
goto v_reusejp_6235_;
}
v_reusejp_6235_:
{
return v___x_6236_;
}
}
}
}
else
{
lean_object* v___f_6240_; lean_object* v_mergedRefs_6241_; lean_object* v_mergedDecls_6242_; lean_object* v___x_6244_; 
v___f_6240_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6241_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6220_, v_refs_6207_);
v_mergedDecls_6242_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6208_, v_decls_6221_, v___f_6240_);
lean_dec(v_decls_6208_);
if (v_isShared_6224_ == 0)
{
lean_ctor_set(v___x_6223_, 5, v_mergedDecls_6242_);
lean_ctor_set(v___x_6223_, 4, v_mergedRefs_6241_);
lean_ctor_set(v___x_6223_, 1, v_version_6206_);
lean_ctor_set(v___x_6223_, 0, v_moduleUri_6205_);
v___x_6244_ = v___x_6223_;
goto v_reusejp_6243_;
}
else
{
lean_object* v_reuseFailAlloc_6252_; 
v_reuseFailAlloc_6252_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6252_, 0, v_moduleUri_6205_);
lean_ctor_set(v_reuseFailAlloc_6252_, 1, v_version_6206_);
lean_ctor_set(v_reuseFailAlloc_6252_, 2, v_directImports_6218_);
lean_ctor_set(v_reuseFailAlloc_6252_, 3, v_isSetupFailure_x3f_6219_);
lean_ctor_set(v_reuseFailAlloc_6252_, 4, v_mergedRefs_6241_);
lean_ctor_set(v_reuseFailAlloc_6252_, 5, v_mergedDecls_6242_);
v___x_6244_ = v_reuseFailAlloc_6252_;
goto v_reusejp_6243_;
}
v_reusejp_6243_:
{
lean_object* v___x_6245_; lean_object* v___x_6247_; 
v___x_6245_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6204_, v___x_6244_, v_workers_6211_);
if (v_isShared_6228_ == 0)
{
lean_ctor_set(v___x_6227_, 1, v___x_6245_);
v___x_6247_ = v___x_6227_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6251_; 
v_reuseFailAlloc_6251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6251_, 0, v_ileans_6210_);
lean_ctor_set(v_reuseFailAlloc_6251_, 1, v___x_6245_);
v___x_6247_ = v_reuseFailAlloc_6251_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
lean_object* v___x_6249_; 
if (v_isShared_6216_ == 0)
{
lean_ctor_set_tag(v___x_6215_, 0);
lean_ctor_set(v___x_6215_, 0, v___x_6247_);
v___x_6249_ = v___x_6215_;
goto v_reusejp_6248_;
}
else
{
lean_object* v_reuseFailAlloc_6250_; 
v_reuseFailAlloc_6250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6250_, 0, v___x_6247_);
v___x_6249_ = v_reuseFailAlloc_6250_;
goto v_reusejp_6248_;
}
v_reusejp_6248_:
{
return v___x_6249_;
}
}
}
}
}
}
else
{
lean_object* v___x_6257_; 
lean_del_object(v___x_6223_);
lean_dec(v_decls_6221_);
lean_dec(v_refs_6220_);
lean_dec(v_isSetupFailure_x3f_6219_);
lean_dec_ref(v_directImports_6218_);
lean_dec(v_version_6217_);
lean_dec(v_decls_6208_);
lean_dec(v_refs_6207_);
lean_dec(v_version_6206_);
lean_dec_ref(v_moduleUri_6205_);
lean_dec(v_name_6204_);
if (v_isShared_6216_ == 0)
{
lean_ctor_set_tag(v___x_6215_, 0);
lean_ctor_set(v___x_6215_, 0, v_self_6203_);
v___x_6257_ = v___x_6215_;
goto v_reusejp_6256_;
}
else
{
lean_object* v_reuseFailAlloc_6258_; 
v_reuseFailAlloc_6258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6258_, 0, v_self_6203_);
v___x_6257_ = v_reuseFailAlloc_6258_;
goto v_reusejp_6256_;
}
v_reusejp_6256_:
{
return v___x_6257_;
}
}
}
}
}
else
{
lean_object* v___x_6263_; uint8_t v_isShared_6264_; uint8_t v_isSharedCheck_6273_; 
lean_inc(v_workers_6211_);
lean_inc(v_ileans_6210_);
lean_dec(v___x_6212_);
v_isSharedCheck_6273_ = !lean_is_exclusive(v_self_6203_);
if (v_isSharedCheck_6273_ == 0)
{
lean_object* v_unused_6274_; lean_object* v_unused_6275_; 
v_unused_6274_ = lean_ctor_get(v_self_6203_, 1);
lean_dec(v_unused_6274_);
v_unused_6275_ = lean_ctor_get(v_self_6203_, 0);
lean_dec(v_unused_6275_);
v___x_6263_ = v_self_6203_;
v_isShared_6264_ = v_isSharedCheck_6273_;
goto v_resetjp_6262_;
}
else
{
lean_dec(v_self_6203_);
v___x_6263_ = lean_box(0);
v_isShared_6264_ = v_isSharedCheck_6273_;
goto v_resetjp_6262_;
}
v_resetjp_6262_:
{
lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6270_; 
v___x_6265_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6266_ = lean_box(0);
v___x_6267_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6267_, 0, v_moduleUri_6205_);
lean_ctor_set(v___x_6267_, 1, v_version_6206_);
lean_ctor_set(v___x_6267_, 2, v___x_6265_);
lean_ctor_set(v___x_6267_, 3, v___x_6266_);
lean_ctor_set(v___x_6267_, 4, v_refs_6207_);
lean_ctor_set(v___x_6267_, 5, v_decls_6208_);
v___x_6268_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6204_, v___x_6267_, v_workers_6211_);
if (v_isShared_6264_ == 0)
{
lean_ctor_set(v___x_6263_, 1, v___x_6268_);
v___x_6270_ = v___x_6263_;
goto v_reusejp_6269_;
}
else
{
lean_object* v_reuseFailAlloc_6272_; 
v_reuseFailAlloc_6272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6272_, 0, v_ileans_6210_);
lean_ctor_set(v_reuseFailAlloc_6272_, 1, v___x_6268_);
v___x_6270_ = v_reuseFailAlloc_6272_;
goto v_reusejp_6269_;
}
v_reusejp_6269_:
{
lean_object* v___x_6271_; 
v___x_6271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6271_, 0, v___x_6270_);
return v___x_6271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6276_, lean_object* v_name_6277_, lean_object* v_moduleUri_6278_, lean_object* v_version_6279_, lean_object* v_refs_6280_, lean_object* v_decls_6281_, lean_object* v_a_6282_){
_start:
{
lean_object* v_res_6283_; 
v_res_6283_ = l_Lean_Server_References_updateWorkerRefs(v_self_6276_, v_name_6277_, v_moduleUri_6278_, v_version_6279_, v_refs_6280_, v_decls_6281_);
return v_res_6283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6284_, lean_object* v_t_6285_, lean_object* v_k_6286_, lean_object* v_fallback_6287_){
_start:
{
lean_object* v___x_6288_; 
v___x_6288_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6285_, v_k_6286_, v_fallback_6287_);
return v___x_6288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6289_, lean_object* v_t_6290_, lean_object* v_k_6291_, lean_object* v_fallback_6292_){
_start:
{
lean_object* v_res_6293_; 
v_res_6293_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6289_, v_t_6290_, v_k_6291_, v_fallback_6292_);
lean_dec(v_fallback_6292_);
lean_dec_ref(v_k_6291_);
lean_dec(v_t_6290_);
return v_res_6293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6294_, lean_object* v_t_6295_){
_start:
{
lean_object* v___x_6296_; 
v___x_6296_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6294_, v_t_6295_);
return v___x_6296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6297_, lean_object* v_name_6298_, lean_object* v_moduleUri_6299_, lean_object* v_version_6300_, lean_object* v_refs_6301_, lean_object* v_decls_6302_){
_start:
{
lean_object* v_ileans_6304_; lean_object* v_workers_6305_; lean_object* v___x_6306_; 
v_ileans_6304_ = lean_ctor_get(v_self_6297_, 0);
v_workers_6305_ = lean_ctor_get(v_self_6297_, 1);
v___x_6306_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6305_, v_name_6298_);
if (lean_obj_tag(v___x_6306_) == 1)
{
lean_object* v_val_6307_; lean_object* v___x_6309_; uint8_t v_isShared_6310_; uint8_t v_isSharedCheck_6341_; 
v_val_6307_ = lean_ctor_get(v___x_6306_, 0);
v_isSharedCheck_6341_ = !lean_is_exclusive(v___x_6306_);
if (v_isSharedCheck_6341_ == 0)
{
v___x_6309_ = v___x_6306_;
v_isShared_6310_ = v_isSharedCheck_6341_;
goto v_resetjp_6308_;
}
else
{
lean_inc(v_val_6307_);
lean_dec(v___x_6306_);
v___x_6309_ = lean_box(0);
v_isShared_6310_ = v_isSharedCheck_6341_;
goto v_resetjp_6308_;
}
v_resetjp_6308_:
{
lean_object* v_version_6311_; lean_object* v_directImports_6312_; lean_object* v_isSetupFailure_x3f_6313_; lean_object* v___x_6315_; uint8_t v_isShared_6316_; uint8_t v_isSharedCheck_6337_; 
v_version_6311_ = lean_ctor_get(v_val_6307_, 1);
v_directImports_6312_ = lean_ctor_get(v_val_6307_, 2);
v_isSetupFailure_x3f_6313_ = lean_ctor_get(v_val_6307_, 3);
v_isSharedCheck_6337_ = !lean_is_exclusive(v_val_6307_);
if (v_isSharedCheck_6337_ == 0)
{
lean_object* v_unused_6338_; lean_object* v_unused_6339_; lean_object* v_unused_6340_; 
v_unused_6338_ = lean_ctor_get(v_val_6307_, 5);
lean_dec(v_unused_6338_);
v_unused_6339_ = lean_ctor_get(v_val_6307_, 4);
lean_dec(v_unused_6339_);
v_unused_6340_ = lean_ctor_get(v_val_6307_, 0);
lean_dec(v_unused_6340_);
v___x_6315_ = v_val_6307_;
v_isShared_6316_ = v_isSharedCheck_6337_;
goto v_resetjp_6314_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6313_);
lean_inc(v_directImports_6312_);
lean_inc(v_version_6311_);
lean_dec(v_val_6307_);
v___x_6315_ = lean_box(0);
v_isShared_6316_ = v_isSharedCheck_6337_;
goto v_resetjp_6314_;
}
v_resetjp_6314_:
{
uint8_t v___x_6317_; 
v___x_6317_ = lean_nat_dec_lt(v_version_6300_, v_version_6311_);
lean_dec(v_version_6311_);
if (v___x_6317_ == 0)
{
lean_object* v___x_6319_; uint8_t v_isShared_6320_; uint8_t v_isSharedCheck_6331_; 
lean_inc(v_workers_6305_);
lean_inc(v_ileans_6304_);
v_isSharedCheck_6331_ = !lean_is_exclusive(v_self_6297_);
if (v_isSharedCheck_6331_ == 0)
{
lean_object* v_unused_6332_; lean_object* v_unused_6333_; 
v_unused_6332_ = lean_ctor_get(v_self_6297_, 1);
lean_dec(v_unused_6332_);
v_unused_6333_ = lean_ctor_get(v_self_6297_, 0);
lean_dec(v_unused_6333_);
v___x_6319_ = v_self_6297_;
v_isShared_6320_ = v_isSharedCheck_6331_;
goto v_resetjp_6318_;
}
else
{
lean_dec(v_self_6297_);
v___x_6319_ = lean_box(0);
v_isShared_6320_ = v_isSharedCheck_6331_;
goto v_resetjp_6318_;
}
v_resetjp_6318_:
{
lean_object* v___x_6322_; 
if (v_isShared_6316_ == 0)
{
lean_ctor_set(v___x_6315_, 5, v_decls_6302_);
lean_ctor_set(v___x_6315_, 4, v_refs_6301_);
lean_ctor_set(v___x_6315_, 1, v_version_6300_);
lean_ctor_set(v___x_6315_, 0, v_moduleUri_6299_);
v___x_6322_ = v___x_6315_;
goto v_reusejp_6321_;
}
else
{
lean_object* v_reuseFailAlloc_6330_; 
v_reuseFailAlloc_6330_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6330_, 0, v_moduleUri_6299_);
lean_ctor_set(v_reuseFailAlloc_6330_, 1, v_version_6300_);
lean_ctor_set(v_reuseFailAlloc_6330_, 2, v_directImports_6312_);
lean_ctor_set(v_reuseFailAlloc_6330_, 3, v_isSetupFailure_x3f_6313_);
lean_ctor_set(v_reuseFailAlloc_6330_, 4, v_refs_6301_);
lean_ctor_set(v_reuseFailAlloc_6330_, 5, v_decls_6302_);
v___x_6322_ = v_reuseFailAlloc_6330_;
goto v_reusejp_6321_;
}
v_reusejp_6321_:
{
lean_object* v___x_6323_; lean_object* v___x_6325_; 
v___x_6323_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6298_, v___x_6322_, v_workers_6305_);
if (v_isShared_6320_ == 0)
{
lean_ctor_set(v___x_6319_, 1, v___x_6323_);
v___x_6325_ = v___x_6319_;
goto v_reusejp_6324_;
}
else
{
lean_object* v_reuseFailAlloc_6329_; 
v_reuseFailAlloc_6329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6329_, 0, v_ileans_6304_);
lean_ctor_set(v_reuseFailAlloc_6329_, 1, v___x_6323_);
v___x_6325_ = v_reuseFailAlloc_6329_;
goto v_reusejp_6324_;
}
v_reusejp_6324_:
{
lean_object* v___x_6327_; 
if (v_isShared_6310_ == 0)
{
lean_ctor_set_tag(v___x_6309_, 0);
lean_ctor_set(v___x_6309_, 0, v___x_6325_);
v___x_6327_ = v___x_6309_;
goto v_reusejp_6326_;
}
else
{
lean_object* v_reuseFailAlloc_6328_; 
v_reuseFailAlloc_6328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6328_, 0, v___x_6325_);
v___x_6327_ = v_reuseFailAlloc_6328_;
goto v_reusejp_6326_;
}
v_reusejp_6326_:
{
return v___x_6327_;
}
}
}
}
}
else
{
lean_object* v___x_6335_; 
lean_del_object(v___x_6315_);
lean_dec(v_isSetupFailure_x3f_6313_);
lean_dec_ref(v_directImports_6312_);
lean_dec(v_decls_6302_);
lean_dec(v_refs_6301_);
lean_dec(v_version_6300_);
lean_dec_ref(v_moduleUri_6299_);
lean_dec(v_name_6298_);
if (v_isShared_6310_ == 0)
{
lean_ctor_set_tag(v___x_6309_, 0);
lean_ctor_set(v___x_6309_, 0, v_self_6297_);
v___x_6335_ = v___x_6309_;
goto v_reusejp_6334_;
}
else
{
lean_object* v_reuseFailAlloc_6336_; 
v_reuseFailAlloc_6336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6336_, 0, v_self_6297_);
v___x_6335_ = v_reuseFailAlloc_6336_;
goto v_reusejp_6334_;
}
v_reusejp_6334_:
{
return v___x_6335_;
}
}
}
}
}
else
{
lean_object* v___x_6343_; uint8_t v_isShared_6344_; uint8_t v_isSharedCheck_6353_; 
lean_inc(v_workers_6305_);
lean_inc(v_ileans_6304_);
lean_dec(v___x_6306_);
v_isSharedCheck_6353_ = !lean_is_exclusive(v_self_6297_);
if (v_isSharedCheck_6353_ == 0)
{
lean_object* v_unused_6354_; lean_object* v_unused_6355_; 
v_unused_6354_ = lean_ctor_get(v_self_6297_, 1);
lean_dec(v_unused_6354_);
v_unused_6355_ = lean_ctor_get(v_self_6297_, 0);
lean_dec(v_unused_6355_);
v___x_6343_ = v_self_6297_;
v_isShared_6344_ = v_isSharedCheck_6353_;
goto v_resetjp_6342_;
}
else
{
lean_dec(v_self_6297_);
v___x_6343_ = lean_box(0);
v_isShared_6344_ = v_isSharedCheck_6353_;
goto v_resetjp_6342_;
}
v_resetjp_6342_:
{
lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___x_6350_; 
v___x_6345_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6346_ = lean_box(0);
v___x_6347_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6347_, 0, v_moduleUri_6299_);
lean_ctor_set(v___x_6347_, 1, v_version_6300_);
lean_ctor_set(v___x_6347_, 2, v___x_6345_);
lean_ctor_set(v___x_6347_, 3, v___x_6346_);
lean_ctor_set(v___x_6347_, 4, v_refs_6301_);
lean_ctor_set(v___x_6347_, 5, v_decls_6302_);
v___x_6348_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6298_, v___x_6347_, v_workers_6305_);
if (v_isShared_6344_ == 0)
{
lean_ctor_set(v___x_6343_, 1, v___x_6348_);
v___x_6350_ = v___x_6343_;
goto v_reusejp_6349_;
}
else
{
lean_object* v_reuseFailAlloc_6352_; 
v_reuseFailAlloc_6352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6352_, 0, v_ileans_6304_);
lean_ctor_set(v_reuseFailAlloc_6352_, 1, v___x_6348_);
v___x_6350_ = v_reuseFailAlloc_6352_;
goto v_reusejp_6349_;
}
v_reusejp_6349_:
{
lean_object* v___x_6351_; 
v___x_6351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6351_, 0, v___x_6350_);
return v___x_6351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6356_, lean_object* v_name_6357_, lean_object* v_moduleUri_6358_, lean_object* v_version_6359_, lean_object* v_refs_6360_, lean_object* v_decls_6361_, lean_object* v_a_6362_){
_start:
{
lean_object* v_res_6363_; 
v_res_6363_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6356_, v_name_6357_, v_moduleUri_6358_, v_version_6359_, v_refs_6360_, v_decls_6361_);
return v_res_6363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6364_, lean_object* v_name_6365_){
_start:
{
lean_object* v_ileans_6366_; lean_object* v_workers_6367_; lean_object* v___x_6369_; uint8_t v_isShared_6370_; uint8_t v_isSharedCheck_6375_; 
v_ileans_6366_ = lean_ctor_get(v_self_6364_, 0);
v_workers_6367_ = lean_ctor_get(v_self_6364_, 1);
v_isSharedCheck_6375_ = !lean_is_exclusive(v_self_6364_);
if (v_isSharedCheck_6375_ == 0)
{
v___x_6369_ = v_self_6364_;
v_isShared_6370_ = v_isSharedCheck_6375_;
goto v_resetjp_6368_;
}
else
{
lean_inc(v_workers_6367_);
lean_inc(v_ileans_6366_);
lean_dec(v_self_6364_);
v___x_6369_ = lean_box(0);
v_isShared_6370_ = v_isSharedCheck_6375_;
goto v_resetjp_6368_;
}
v_resetjp_6368_:
{
lean_object* v___x_6371_; lean_object* v___x_6373_; 
v___x_6371_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6365_, v_workers_6367_);
if (v_isShared_6370_ == 0)
{
lean_ctor_set(v___x_6369_, 1, v___x_6371_);
v___x_6373_ = v___x_6369_;
goto v_reusejp_6372_;
}
else
{
lean_object* v_reuseFailAlloc_6374_; 
v_reuseFailAlloc_6374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6374_, 0, v_ileans_6366_);
lean_ctor_set(v_reuseFailAlloc_6374_, 1, v___x_6371_);
v___x_6373_ = v_reuseFailAlloc_6374_;
goto v_reusejp_6372_;
}
v_reusejp_6372_:
{
return v___x_6373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6376_, lean_object* v_name_6377_){
_start:
{
lean_object* v_res_6378_; 
v_res_6378_ = l_Lean_Server_References_removeWorkerRefs(v_self_6376_, v_name_6377_);
lean_dec(v_name_6377_);
return v_res_6378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6379_, lean_object* v_x_6380_){
_start:
{
if (lean_obj_tag(v_x_6380_) == 0)
{
lean_object* v_v_6381_; lean_object* v_k_6382_; lean_object* v_l_6383_; lean_object* v_r_6384_; lean_object* v_moduleUri_6385_; lean_object* v_refs_6386_; lean_object* v_decls_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; 
v_v_6381_ = lean_ctor_get(v_x_6380_, 2);
lean_inc(v_v_6381_);
v_k_6382_ = lean_ctor_get(v_x_6380_, 1);
lean_inc(v_k_6382_);
v_l_6383_ = lean_ctor_get(v_x_6380_, 3);
lean_inc(v_l_6383_);
v_r_6384_ = lean_ctor_get(v_x_6380_, 4);
lean_inc(v_r_6384_);
lean_dec_ref_known(v_x_6380_, 5);
v_moduleUri_6385_ = lean_ctor_get(v_v_6381_, 0);
lean_inc_ref(v_moduleUri_6385_);
v_refs_6386_ = lean_ctor_get(v_v_6381_, 3);
lean_inc(v_refs_6386_);
v_decls_6387_ = lean_ctor_get(v_v_6381_, 4);
lean_inc(v_decls_6387_);
lean_dec(v_v_6381_);
v___x_6388_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6379_, v_l_6383_);
v___x_6389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6389_, 0, v_refs_6386_);
lean_ctor_set(v___x_6389_, 1, v_decls_6387_);
v___x_6390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6390_, 0, v_moduleUri_6385_);
lean_ctor_set(v___x_6390_, 1, v___x_6389_);
v___x_6391_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6382_, v___x_6390_, v___x_6388_);
v_init_6379_ = v___x_6391_;
v_x_6380_ = v_r_6384_;
goto _start;
}
else
{
return v_init_6379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6393_, lean_object* v_x_6394_){
_start:
{
if (lean_obj_tag(v_x_6394_) == 0)
{
lean_object* v_v_6395_; lean_object* v_k_6396_; lean_object* v_l_6397_; lean_object* v_r_6398_; lean_object* v_moduleUri_6399_; lean_object* v_refs_6400_; lean_object* v_decls_6401_; lean_object* v___x_6402_; uint8_t v___x_6403_; 
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
v_refs_6400_ = lean_ctor_get(v_v_6395_, 4);
lean_inc(v_refs_6400_);
v_decls_6401_ = lean_ctor_get(v_v_6395_, 5);
lean_inc(v_decls_6401_);
v___x_6402_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6393_, v_l_6397_);
v___x_6403_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6395_);
lean_dec(v_v_6395_);
if (v___x_6403_ == 0)
{
lean_dec(v_decls_6401_);
lean_dec(v_refs_6400_);
lean_dec_ref(v_moduleUri_6399_);
lean_dec(v_k_6396_);
v_init_6393_ = v___x_6402_;
v_x_6394_ = v_r_6398_;
goto _start;
}
else
{
lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; 
v___x_6405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6405_, 0, v_refs_6400_);
lean_ctor_set(v___x_6405_, 1, v_decls_6401_);
v___x_6406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6406_, 0, v_moduleUri_6399_);
lean_ctor_set(v___x_6406_, 1, v___x_6405_);
v___x_6407_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6396_, v___x_6406_, v___x_6402_);
v_init_6393_ = v___x_6407_;
v_x_6394_ = v_r_6398_;
goto _start;
}
}
else
{
return v_init_6393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6409_){
_start:
{
lean_object* v_ileans_6410_; lean_object* v_workers_6411_; lean_object* v___x_6412_; lean_object* v_ileanRefs_6413_; lean_object* v___x_6414_; 
v_ileans_6410_ = lean_ctor_get(v_self_6409_, 0);
lean_inc(v_ileans_6410_);
v_workers_6411_ = lean_ctor_get(v_self_6409_, 1);
lean_inc(v_workers_6411_);
lean_dec_ref(v_self_6409_);
v___x_6412_ = lean_box(1);
v_ileanRefs_6413_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6412_, v_ileans_6410_);
v___x_6414_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6413_, v_workers_6411_);
return v___x_6414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6415_, lean_object* v_t_6416_){
_start:
{
lean_object* v___x_6417_; 
v___x_6417_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6415_, v_t_6416_);
return v___x_6417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6418_, lean_object* v_t_6419_){
_start:
{
lean_object* v___x_6420_; 
v___x_6420_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6418_, v_t_6419_);
return v___x_6420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6421_, lean_object* v_x_6422_){
_start:
{
if (lean_obj_tag(v_x_6422_) == 0)
{
lean_object* v_k_6423_; lean_object* v_v_6424_; lean_object* v_l_6425_; lean_object* v_r_6426_; lean_object* v___x_6427_; lean_object* v_a_6428_; uint8_t v___x_6429_; 
v_k_6423_ = lean_ctor_get(v_x_6422_, 1);
lean_inc(v_k_6423_);
v_v_6424_ = lean_ctor_get(v_x_6422_, 2);
lean_inc(v_v_6424_);
v_l_6425_ = lean_ctor_get(v_x_6422_, 3);
lean_inc(v_l_6425_);
v_r_6426_ = lean_ctor_get(v_x_6422_, 4);
lean_inc(v_r_6426_);
lean_dec_ref_known(v_x_6422_, 5);
v___x_6427_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6421_, v_l_6425_);
v_a_6428_ = lean_ctor_get(v___x_6427_, 0);
v___x_6429_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6424_);
if (v___x_6429_ == 0)
{
lean_object* v_a_6430_; 
lean_dec(v_v_6424_);
lean_dec(v_k_6423_);
v_a_6430_ = lean_ctor_get(v___x_6427_, 0);
lean_inc(v_a_6430_);
lean_dec_ref(v___x_6427_);
v_init_6421_ = v_a_6430_;
v_x_6422_ = v_r_6426_;
goto _start;
}
else
{
lean_object* v_moduleUri_6432_; lean_object* v_directImports_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; 
lean_inc(v_a_6428_);
lean_dec_ref(v___x_6427_);
v_moduleUri_6432_ = lean_ctor_get(v_v_6424_, 0);
lean_inc_ref(v_moduleUri_6432_);
v_directImports_6433_ = lean_ctor_get(v_v_6424_, 2);
lean_inc_ref(v_directImports_6433_);
lean_dec(v_v_6424_);
v___x_6434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6434_, 0, v_moduleUri_6432_);
lean_ctor_set(v___x_6434_, 1, v_directImports_6433_);
v___x_6435_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6423_, v___x_6434_, v_a_6428_);
v_init_6421_ = v___x_6435_;
v_x_6422_ = v_r_6426_;
goto _start;
}
}
else
{
lean_object* v___x_6437_; 
v___x_6437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6437_, 0, v_init_6421_);
return v___x_6437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6438_, lean_object* v_x_6439_){
_start:
{
if (lean_obj_tag(v_x_6439_) == 0)
{
lean_object* v_k_6440_; lean_object* v_v_6441_; lean_object* v_l_6442_; lean_object* v_r_6443_; lean_object* v___x_6444_; lean_object* v_a_6445_; lean_object* v_moduleUri_6446_; lean_object* v_directImports_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; 
v_k_6440_ = lean_ctor_get(v_x_6439_, 1);
lean_inc(v_k_6440_);
v_v_6441_ = lean_ctor_get(v_x_6439_, 2);
lean_inc(v_v_6441_);
v_l_6442_ = lean_ctor_get(v_x_6439_, 3);
lean_inc(v_l_6442_);
v_r_6443_ = lean_ctor_get(v_x_6439_, 4);
lean_inc(v_r_6443_);
lean_dec_ref_known(v_x_6439_, 5);
v___x_6444_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6438_, v_l_6442_);
v_a_6445_ = lean_ctor_get(v___x_6444_, 0);
lean_inc(v_a_6445_);
lean_dec_ref(v___x_6444_);
v_moduleUri_6446_ = lean_ctor_get(v_v_6441_, 0);
lean_inc_ref(v_moduleUri_6446_);
v_directImports_6447_ = lean_ctor_get(v_v_6441_, 2);
lean_inc_ref(v_directImports_6447_);
lean_dec(v_v_6441_);
v___x_6448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6448_, 0, v_moduleUri_6446_);
lean_ctor_set(v___x_6448_, 1, v_directImports_6447_);
v___x_6449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6440_, v___x_6448_, v_a_6445_);
v_init_6438_ = v___x_6449_;
v_x_6439_ = v_r_6443_;
goto _start;
}
else
{
lean_object* v___x_6451_; 
v___x_6451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6451_, 0, v_init_6438_);
return v___x_6451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6452_){
_start:
{
lean_object* v_ileans_6453_; lean_object* v_workers_6454_; lean_object* v___y_6456_; lean_object* v_allDirectImports_6459_; lean_object* v___x_6460_; lean_object* v_a_6461_; 
v_ileans_6453_ = lean_ctor_get(v_self_6452_, 0);
lean_inc(v_ileans_6453_);
v_workers_6454_ = lean_ctor_get(v_self_6452_, 1);
lean_inc(v_workers_6454_);
lean_dec_ref(v_self_6452_);
v_allDirectImports_6459_ = lean_box(1);
v___x_6460_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6459_, v_ileans_6453_);
v_a_6461_ = lean_ctor_get(v___x_6460_, 0);
lean_inc(v_a_6461_);
lean_dec_ref(v___x_6460_);
v___y_6456_ = v_a_6461_;
goto v___jp_6455_;
v___jp_6455_:
{
lean_object* v___x_6457_; lean_object* v_a_6458_; 
v___x_6457_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6456_, v_workers_6454_);
v_a_6458_ = lean_ctor_get(v___x_6457_, 0);
lean_inc(v_a_6458_);
lean_dec_ref(v___x_6457_);
return v_a_6458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6462_, lean_object* v_mod_6463_){
_start:
{
lean_object* v_ileans_6464_; lean_object* v_workers_6465_; lean_object* v___x_6467_; uint8_t v_isShared_6468_; uint8_t v_isSharedCheck_6502_; 
v_ileans_6464_ = lean_ctor_get(v_self_6462_, 0);
v_workers_6465_ = lean_ctor_get(v_self_6462_, 1);
v_isSharedCheck_6502_ = !lean_is_exclusive(v_self_6462_);
if (v_isSharedCheck_6502_ == 0)
{
v___x_6467_ = v_self_6462_;
v_isShared_6468_ = v_isSharedCheck_6502_;
goto v_resetjp_6466_;
}
else
{
lean_inc(v_workers_6465_);
lean_inc(v_ileans_6464_);
lean_dec(v_self_6462_);
v___x_6467_ = lean_box(0);
v_isShared_6468_ = v_isSharedCheck_6502_;
goto v_resetjp_6466_;
}
v_resetjp_6466_:
{
lean_object* v___x_6487_; 
v___x_6487_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6465_, v_mod_6463_);
lean_dec(v_workers_6465_);
if (lean_obj_tag(v___x_6487_) == 1)
{
lean_object* v_val_6488_; lean_object* v___x_6490_; uint8_t v_isShared_6491_; uint8_t v_isSharedCheck_6501_; 
v_val_6488_ = lean_ctor_get(v___x_6487_, 0);
v_isSharedCheck_6501_ = !lean_is_exclusive(v___x_6487_);
if (v_isSharedCheck_6501_ == 0)
{
v___x_6490_ = v___x_6487_;
v_isShared_6491_ = v_isSharedCheck_6501_;
goto v_resetjp_6489_;
}
else
{
lean_inc(v_val_6488_);
lean_dec(v___x_6487_);
v___x_6490_ = lean_box(0);
v_isShared_6491_ = v_isSharedCheck_6501_;
goto v_resetjp_6489_;
}
v_resetjp_6489_:
{
uint8_t v___x_6492_; 
v___x_6492_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6488_);
if (v___x_6492_ == 0)
{
lean_del_object(v___x_6490_);
lean_dec(v_val_6488_);
goto v___jp_6469_;
}
else
{
lean_object* v_moduleUri_6493_; lean_object* v_refs_6494_; lean_object* v_decls_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; lean_object* v___x_6499_; 
lean_del_object(v___x_6467_);
lean_dec(v_ileans_6464_);
v_moduleUri_6493_ = lean_ctor_get(v_val_6488_, 0);
lean_inc_ref(v_moduleUri_6493_);
v_refs_6494_ = lean_ctor_get(v_val_6488_, 4);
lean_inc(v_refs_6494_);
v_decls_6495_ = lean_ctor_get(v_val_6488_, 5);
lean_inc(v_decls_6495_);
lean_dec(v_val_6488_);
v___x_6496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6496_, 0, v_refs_6494_);
lean_ctor_set(v___x_6496_, 1, v_decls_6495_);
v___x_6497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6497_, 0, v_moduleUri_6493_);
lean_ctor_set(v___x_6497_, 1, v___x_6496_);
if (v_isShared_6491_ == 0)
{
lean_ctor_set(v___x_6490_, 0, v___x_6497_);
v___x_6499_ = v___x_6490_;
goto v_reusejp_6498_;
}
else
{
lean_object* v_reuseFailAlloc_6500_; 
v_reuseFailAlloc_6500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6500_, 0, v___x_6497_);
v___x_6499_ = v_reuseFailAlloc_6500_;
goto v_reusejp_6498_;
}
v_reusejp_6498_:
{
return v___x_6499_;
}
}
}
}
else
{
lean_dec(v___x_6487_);
goto v___jp_6469_;
}
v___jp_6469_:
{
lean_object* v___x_6470_; 
v___x_6470_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6464_, v_mod_6463_);
lean_dec(v_ileans_6464_);
if (lean_obj_tag(v___x_6470_) == 1)
{
lean_object* v_val_6471_; lean_object* v___x_6473_; uint8_t v_isShared_6474_; uint8_t v_isSharedCheck_6485_; 
v_val_6471_ = lean_ctor_get(v___x_6470_, 0);
v_isSharedCheck_6485_ = !lean_is_exclusive(v___x_6470_);
if (v_isSharedCheck_6485_ == 0)
{
v___x_6473_ = v___x_6470_;
v_isShared_6474_ = v_isSharedCheck_6485_;
goto v_resetjp_6472_;
}
else
{
lean_inc(v_val_6471_);
lean_dec(v___x_6470_);
v___x_6473_ = lean_box(0);
v_isShared_6474_ = v_isSharedCheck_6485_;
goto v_resetjp_6472_;
}
v_resetjp_6472_:
{
lean_object* v_moduleUri_6475_; lean_object* v_refs_6476_; lean_object* v_decls_6477_; lean_object* v___x_6479_; 
v_moduleUri_6475_ = lean_ctor_get(v_val_6471_, 0);
lean_inc_ref(v_moduleUri_6475_);
v_refs_6476_ = lean_ctor_get(v_val_6471_, 3);
lean_inc(v_refs_6476_);
v_decls_6477_ = lean_ctor_get(v_val_6471_, 4);
lean_inc(v_decls_6477_);
lean_dec(v_val_6471_);
if (v_isShared_6468_ == 0)
{
lean_ctor_set(v___x_6467_, 1, v_decls_6477_);
lean_ctor_set(v___x_6467_, 0, v_refs_6476_);
v___x_6479_ = v___x_6467_;
goto v_reusejp_6478_;
}
else
{
lean_object* v_reuseFailAlloc_6484_; 
v_reuseFailAlloc_6484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6484_, 0, v_refs_6476_);
lean_ctor_set(v_reuseFailAlloc_6484_, 1, v_decls_6477_);
v___x_6479_ = v_reuseFailAlloc_6484_;
goto v_reusejp_6478_;
}
v_reusejp_6478_:
{
lean_object* v___x_6480_; lean_object* v___x_6482_; 
v___x_6480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6480_, 0, v_moduleUri_6475_);
lean_ctor_set(v___x_6480_, 1, v___x_6479_);
if (v_isShared_6474_ == 0)
{
lean_ctor_set(v___x_6473_, 0, v___x_6480_);
v___x_6482_ = v___x_6473_;
goto v_reusejp_6481_;
}
else
{
lean_object* v_reuseFailAlloc_6483_; 
v_reuseFailAlloc_6483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6483_, 0, v___x_6480_);
v___x_6482_ = v_reuseFailAlloc_6483_;
goto v_reusejp_6481_;
}
v_reusejp_6481_:
{
return v___x_6482_;
}
}
}
}
else
{
lean_object* v___x_6486_; 
lean_dec(v___x_6470_);
lean_del_object(v___x_6467_);
v___x_6486_ = lean_box(0);
return v___x_6486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6503_, lean_object* v_mod_6504_){
_start:
{
lean_object* v_res_6505_; 
v_res_6505_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6503_, v_mod_6504_);
lean_dec(v_mod_6504_);
return v_res_6505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6506_, lean_object* v_mod_6507_){
_start:
{
lean_object* v_ileans_6508_; lean_object* v_workers_6509_; lean_object* v___x_6522_; 
v_ileans_6508_ = lean_ctor_get(v_self_6506_, 0);
v_workers_6509_ = lean_ctor_get(v_self_6506_, 1);
v___x_6522_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6509_, v_mod_6507_);
if (lean_obj_tag(v___x_6522_) == 1)
{
lean_object* v_val_6523_; lean_object* v___x_6525_; uint8_t v_isShared_6526_; uint8_t v_isSharedCheck_6532_; 
v_val_6523_ = lean_ctor_get(v___x_6522_, 0);
v_isSharedCheck_6532_ = !lean_is_exclusive(v___x_6522_);
if (v_isSharedCheck_6532_ == 0)
{
v___x_6525_ = v___x_6522_;
v_isShared_6526_ = v_isSharedCheck_6532_;
goto v_resetjp_6524_;
}
else
{
lean_inc(v_val_6523_);
lean_dec(v___x_6522_);
v___x_6525_ = lean_box(0);
v_isShared_6526_ = v_isSharedCheck_6532_;
goto v_resetjp_6524_;
}
v_resetjp_6524_:
{
uint8_t v___x_6527_; 
v___x_6527_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6523_);
if (v___x_6527_ == 0)
{
lean_del_object(v___x_6525_);
lean_dec(v_val_6523_);
goto v___jp_6510_;
}
else
{
lean_object* v_directImports_6528_; lean_object* v___x_6530_; 
v_directImports_6528_ = lean_ctor_get(v_val_6523_, 2);
lean_inc_ref(v_directImports_6528_);
lean_dec(v_val_6523_);
if (v_isShared_6526_ == 0)
{
lean_ctor_set(v___x_6525_, 0, v_directImports_6528_);
v___x_6530_ = v___x_6525_;
goto v_reusejp_6529_;
}
else
{
lean_object* v_reuseFailAlloc_6531_; 
v_reuseFailAlloc_6531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6531_, 0, v_directImports_6528_);
v___x_6530_ = v_reuseFailAlloc_6531_;
goto v_reusejp_6529_;
}
v_reusejp_6529_:
{
return v___x_6530_;
}
}
}
}
else
{
lean_dec(v___x_6522_);
goto v___jp_6510_;
}
v___jp_6510_:
{
lean_object* v___x_6511_; 
v___x_6511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6508_, v_mod_6507_);
if (lean_obj_tag(v___x_6511_) == 1)
{
lean_object* v_val_6512_; lean_object* v___x_6514_; uint8_t v_isShared_6515_; uint8_t v_isSharedCheck_6520_; 
v_val_6512_ = lean_ctor_get(v___x_6511_, 0);
v_isSharedCheck_6520_ = !lean_is_exclusive(v___x_6511_);
if (v_isSharedCheck_6520_ == 0)
{
v___x_6514_ = v___x_6511_;
v_isShared_6515_ = v_isSharedCheck_6520_;
goto v_resetjp_6513_;
}
else
{
lean_inc(v_val_6512_);
lean_dec(v___x_6511_);
v___x_6514_ = lean_box(0);
v_isShared_6515_ = v_isSharedCheck_6520_;
goto v_resetjp_6513_;
}
v_resetjp_6513_:
{
lean_object* v_directImports_6516_; lean_object* v___x_6518_; 
v_directImports_6516_ = lean_ctor_get(v_val_6512_, 2);
lean_inc_ref(v_directImports_6516_);
lean_dec(v_val_6512_);
if (v_isShared_6515_ == 0)
{
lean_ctor_set(v___x_6514_, 0, v_directImports_6516_);
v___x_6518_ = v___x_6514_;
goto v_reusejp_6517_;
}
else
{
lean_object* v_reuseFailAlloc_6519_; 
v_reuseFailAlloc_6519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6519_, 0, v_directImports_6516_);
v___x_6518_ = v_reuseFailAlloc_6519_;
goto v_reusejp_6517_;
}
v_reusejp_6517_:
{
return v___x_6518_;
}
}
}
else
{
lean_object* v___x_6521_; 
lean_dec(v___x_6511_);
v___x_6521_ = lean_box(0);
return v___x_6521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6533_, lean_object* v_mod_6534_){
_start:
{
lean_object* v_res_6535_; 
v_res_6535_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6533_, v_mod_6534_);
lean_dec(v_mod_6534_);
lean_dec_ref(v_self_6533_);
return v_res_6535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6536_, lean_object* v_mod_6537_){
_start:
{
lean_object* v_ileans_6538_; lean_object* v_workers_6539_; lean_object* v___x_6552_; 
v_ileans_6538_ = lean_ctor_get(v_self_6536_, 0);
v_workers_6539_ = lean_ctor_get(v_self_6536_, 1);
v___x_6552_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6539_, v_mod_6537_);
if (lean_obj_tag(v___x_6552_) == 1)
{
lean_object* v_val_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6562_; 
v_val_6553_ = lean_ctor_get(v___x_6552_, 0);
v_isSharedCheck_6562_ = !lean_is_exclusive(v___x_6552_);
if (v_isSharedCheck_6562_ == 0)
{
v___x_6555_ = v___x_6552_;
v_isShared_6556_ = v_isSharedCheck_6562_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_val_6553_);
lean_dec(v___x_6552_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6562_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
uint8_t v___x_6557_; 
v___x_6557_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6553_);
if (v___x_6557_ == 0)
{
lean_del_object(v___x_6555_);
lean_dec(v_val_6553_);
goto v___jp_6540_;
}
else
{
lean_object* v_decls_6558_; lean_object* v___x_6560_; 
v_decls_6558_ = lean_ctor_get(v_val_6553_, 5);
lean_inc(v_decls_6558_);
lean_dec(v_val_6553_);
if (v_isShared_6556_ == 0)
{
lean_ctor_set(v___x_6555_, 0, v_decls_6558_);
v___x_6560_ = v___x_6555_;
goto v_reusejp_6559_;
}
else
{
lean_object* v_reuseFailAlloc_6561_; 
v_reuseFailAlloc_6561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6561_, 0, v_decls_6558_);
v___x_6560_ = v_reuseFailAlloc_6561_;
goto v_reusejp_6559_;
}
v_reusejp_6559_:
{
return v___x_6560_;
}
}
}
}
else
{
lean_dec(v___x_6552_);
goto v___jp_6540_;
}
v___jp_6540_:
{
lean_object* v___x_6541_; 
v___x_6541_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6538_, v_mod_6537_);
if (lean_obj_tag(v___x_6541_) == 1)
{
lean_object* v_val_6542_; lean_object* v___x_6544_; uint8_t v_isShared_6545_; uint8_t v_isSharedCheck_6550_; 
v_val_6542_ = lean_ctor_get(v___x_6541_, 0);
v_isSharedCheck_6550_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6550_ == 0)
{
v___x_6544_ = v___x_6541_;
v_isShared_6545_ = v_isSharedCheck_6550_;
goto v_resetjp_6543_;
}
else
{
lean_inc(v_val_6542_);
lean_dec(v___x_6541_);
v___x_6544_ = lean_box(0);
v_isShared_6545_ = v_isSharedCheck_6550_;
goto v_resetjp_6543_;
}
v_resetjp_6543_:
{
lean_object* v_decls_6546_; lean_object* v___x_6548_; 
v_decls_6546_ = lean_ctor_get(v_val_6542_, 4);
lean_inc(v_decls_6546_);
lean_dec(v_val_6542_);
if (v_isShared_6545_ == 0)
{
lean_ctor_set(v___x_6544_, 0, v_decls_6546_);
v___x_6548_ = v___x_6544_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_decls_6546_);
v___x_6548_ = v_reuseFailAlloc_6549_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
return v___x_6548_;
}
}
}
else
{
lean_object* v___x_6551_; 
lean_dec(v___x_6541_);
v___x_6551_ = lean_box(0);
return v___x_6551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6563_, lean_object* v_mod_6564_){
_start:
{
lean_object* v_res_6565_; 
v_res_6565_ = l_Lean_Server_References_getDecls_x3f(v_self_6563_, v_mod_6564_);
lean_dec(v_mod_6564_);
lean_dec_ref(v_self_6563_);
return v_res_6565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6566_, lean_object* v_x_6567_){
_start:
{
if (lean_obj_tag(v_x_6567_) == 0)
{
lean_object* v_k_6568_; lean_object* v_v_6569_; lean_object* v_l_6570_; lean_object* v_r_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; lean_object* v___x_6574_; 
v_k_6568_ = lean_ctor_get(v_x_6567_, 1);
v_v_6569_ = lean_ctor_get(v_x_6567_, 2);
v_l_6570_ = lean_ctor_get(v_x_6567_, 3);
v_r_6571_ = lean_ctor_get(v_x_6567_, 4);
v___x_6572_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6566_, v_l_6570_);
lean_inc(v_v_6569_);
lean_inc(v_k_6568_);
v___x_6573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6573_, 0, v_k_6568_);
lean_ctor_set(v___x_6573_, 1, v_v_6569_);
v___x_6574_ = lean_array_push(v___x_6572_, v___x_6573_);
v_init_6566_ = v___x_6574_;
v_x_6567_ = v_r_6571_;
goto _start;
}
else
{
return v_init_6566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6576_, lean_object* v_x_6577_){
_start:
{
lean_object* v_res_6578_; 
v_res_6578_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6576_, v_x_6577_);
lean_dec(v_x_6577_);
return v_res_6578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6579_, lean_object* v_k_6580_){
_start:
{
if (lean_obj_tag(v_t_6579_) == 0)
{
lean_object* v_k_6581_; lean_object* v_v_6582_; lean_object* v_l_6583_; lean_object* v_r_6584_; uint8_t v___x_6585_; 
v_k_6581_ = lean_ctor_get(v_t_6579_, 1);
v_v_6582_ = lean_ctor_get(v_t_6579_, 2);
v_l_6583_ = lean_ctor_get(v_t_6579_, 3);
v_r_6584_ = lean_ctor_get(v_t_6579_, 4);
v___x_6585_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6580_, v_k_6581_);
switch(v___x_6585_)
{
case 0:
{
v_t_6579_ = v_l_6583_;
goto _start;
}
case 1:
{
lean_object* v___x_6587_; 
lean_inc(v_v_6582_);
v___x_6587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6587_, 0, v_v_6582_);
return v___x_6587_;
}
default: 
{
v_t_6579_ = v_r_6584_;
goto _start;
}
}
}
else
{
lean_object* v___x_6589_; 
v___x_6589_ = lean_box(0);
return v___x_6589_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6590_, lean_object* v_k_6591_){
_start:
{
lean_object* v_res_6592_; 
v_res_6592_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6590_, v_k_6591_);
lean_dec_ref(v_k_6591_);
lean_dec(v_t_6590_);
return v_res_6592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6593_, lean_object* v_as_6594_, size_t v_sz_6595_, size_t v_i_6596_, lean_object* v_b_6597_){
_start:
{
lean_object* v_a_6599_; uint8_t v___x_6603_; 
v___x_6603_ = lean_usize_dec_lt(v_i_6596_, v_sz_6595_);
if (v___x_6603_ == 0)
{
return v_b_6597_;
}
else
{
lean_object* v_a_6604_; lean_object* v_snd_6605_; lean_object* v_snd_6606_; lean_object* v_fst_6607_; lean_object* v___x_6609_; uint8_t v_isShared_6610_; uint8_t v_isSharedCheck_6635_; 
v_a_6604_ = lean_array_uget(v_as_6594_, v_i_6596_);
v_snd_6605_ = lean_ctor_get(v_a_6604_, 1);
lean_inc(v_snd_6605_);
v_snd_6606_ = lean_ctor_get(v_snd_6605_, 1);
lean_inc(v_snd_6606_);
v_fst_6607_ = lean_ctor_get(v_a_6604_, 0);
v_isSharedCheck_6635_ = !lean_is_exclusive(v_a_6604_);
if (v_isSharedCheck_6635_ == 0)
{
lean_object* v_unused_6636_; 
v_unused_6636_ = lean_ctor_get(v_a_6604_, 1);
lean_dec(v_unused_6636_);
v___x_6609_ = v_a_6604_;
v_isShared_6610_ = v_isSharedCheck_6635_;
goto v_resetjp_6608_;
}
else
{
lean_inc(v_fst_6607_);
lean_dec(v_a_6604_);
v___x_6609_ = lean_box(0);
v_isShared_6610_ = v_isSharedCheck_6635_;
goto v_resetjp_6608_;
}
v_resetjp_6608_:
{
lean_object* v_fst_6611_; lean_object* v___x_6613_; uint8_t v_isShared_6614_; uint8_t v_isSharedCheck_6633_; 
v_fst_6611_ = lean_ctor_get(v_snd_6605_, 0);
v_isSharedCheck_6633_ = !lean_is_exclusive(v_snd_6605_);
if (v_isSharedCheck_6633_ == 0)
{
lean_object* v_unused_6634_; 
v_unused_6634_ = lean_ctor_get(v_snd_6605_, 1);
lean_dec(v_unused_6634_);
v___x_6613_ = v_snd_6605_;
v_isShared_6614_ = v_isSharedCheck_6633_;
goto v_resetjp_6612_;
}
else
{
lean_inc(v_fst_6611_);
lean_dec(v_snd_6605_);
v___x_6613_ = lean_box(0);
v_isShared_6614_ = v_isSharedCheck_6633_;
goto v_resetjp_6612_;
}
v_resetjp_6612_:
{
lean_object* v_fst_6615_; lean_object* v_snd_6616_; lean_object* v___x_6618_; uint8_t v_isShared_6619_; uint8_t v_isSharedCheck_6632_; 
v_fst_6615_ = lean_ctor_get(v_snd_6606_, 0);
v_snd_6616_ = lean_ctor_get(v_snd_6606_, 1);
v_isSharedCheck_6632_ = !lean_is_exclusive(v_snd_6606_);
if (v_isSharedCheck_6632_ == 0)
{
v___x_6618_ = v_snd_6606_;
v_isShared_6619_ = v_isSharedCheck_6632_;
goto v_resetjp_6617_;
}
else
{
lean_inc(v_snd_6616_);
lean_inc(v_fst_6615_);
lean_dec(v_snd_6606_);
v___x_6618_ = lean_box(0);
v_isShared_6619_ = v_isSharedCheck_6632_;
goto v_resetjp_6617_;
}
v_resetjp_6617_:
{
lean_object* v___x_6620_; 
v___x_6620_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6615_, v_ident_6593_);
lean_dec(v_fst_6615_);
if (lean_obj_tag(v___x_6620_) == 1)
{
lean_object* v_val_6621_; lean_object* v___x_6623_; 
v_val_6621_ = lean_ctor_get(v___x_6620_, 0);
lean_inc(v_val_6621_);
lean_dec_ref_known(v___x_6620_, 1);
if (v_isShared_6619_ == 0)
{
lean_ctor_set(v___x_6618_, 0, v_val_6621_);
v___x_6623_ = v___x_6618_;
goto v_reusejp_6622_;
}
else
{
lean_object* v_reuseFailAlloc_6631_; 
v_reuseFailAlloc_6631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6631_, 0, v_val_6621_);
lean_ctor_set(v_reuseFailAlloc_6631_, 1, v_snd_6616_);
v___x_6623_ = v_reuseFailAlloc_6631_;
goto v_reusejp_6622_;
}
v_reusejp_6622_:
{
lean_object* v___x_6625_; 
if (v_isShared_6614_ == 0)
{
lean_ctor_set(v___x_6613_, 1, v___x_6623_);
lean_ctor_set(v___x_6613_, 0, v_fst_6607_);
v___x_6625_ = v___x_6613_;
goto v_reusejp_6624_;
}
else
{
lean_object* v_reuseFailAlloc_6630_; 
v_reuseFailAlloc_6630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6630_, 0, v_fst_6607_);
lean_ctor_set(v_reuseFailAlloc_6630_, 1, v___x_6623_);
v___x_6625_ = v_reuseFailAlloc_6630_;
goto v_reusejp_6624_;
}
v_reusejp_6624_:
{
lean_object* v___x_6627_; 
if (v_isShared_6610_ == 0)
{
lean_ctor_set(v___x_6609_, 1, v___x_6625_);
lean_ctor_set(v___x_6609_, 0, v_fst_6611_);
v___x_6627_ = v___x_6609_;
goto v_reusejp_6626_;
}
else
{
lean_object* v_reuseFailAlloc_6629_; 
v_reuseFailAlloc_6629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6629_, 0, v_fst_6611_);
lean_ctor_set(v_reuseFailAlloc_6629_, 1, v___x_6625_);
v___x_6627_ = v_reuseFailAlloc_6629_;
goto v_reusejp_6626_;
}
v_reusejp_6626_:
{
lean_object* v___x_6628_; 
v___x_6628_ = lean_array_push(v_b_6597_, v___x_6627_);
v_a_6599_ = v___x_6628_;
goto v___jp_6598_;
}
}
}
}
else
{
lean_dec(v___x_6620_);
lean_del_object(v___x_6618_);
lean_dec(v_snd_6616_);
lean_del_object(v___x_6613_);
lean_dec(v_fst_6611_);
lean_del_object(v___x_6609_);
lean_dec(v_fst_6607_);
v_a_6599_ = v_b_6597_;
goto v___jp_6598_;
}
}
}
}
}
v___jp_6598_:
{
size_t v___x_6600_; size_t v___x_6601_; 
v___x_6600_ = ((size_t)1ULL);
v___x_6601_ = lean_usize_add(v_i_6596_, v___x_6600_);
v_i_6596_ = v___x_6601_;
v_b_6597_ = v_a_6599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6637_, lean_object* v_as_6638_, lean_object* v_sz_6639_, lean_object* v_i_6640_, lean_object* v_b_6641_){
_start:
{
size_t v_sz_boxed_6642_; size_t v_i_boxed_6643_; lean_object* v_res_6644_; 
v_sz_boxed_6642_ = lean_unbox_usize(v_sz_6639_);
lean_dec(v_sz_6639_);
v_i_boxed_6643_ = lean_unbox_usize(v_i_6640_);
lean_dec(v_i_6640_);
v_res_6644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6637_, v_as_6638_, v_sz_boxed_6642_, v_i_boxed_6643_, v_b_6641_);
lean_dec_ref(v_as_6638_);
lean_dec_ref(v_ident_6637_);
return v_res_6644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6651_, lean_object* v_ident_6652_){
_start:
{
lean_object* v___y_6654_; 
if (lean_obj_tag(v_ident_6652_) == 0)
{
lean_object* v___x_6659_; lean_object* v___x_6660_; lean_object* v___x_6661_; 
v___x_6659_ = l_Lean_Server_References_allRefs(v_self_6651_);
v___x_6660_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6661_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6660_, v___x_6659_);
lean_dec(v___x_6659_);
v___y_6654_ = v___x_6661_;
goto v___jp_6653_;
}
else
{
lean_object* v_moduleName_6662_; lean_object* v_identModuleName_6663_; lean_object* v___x_6664_; 
v_moduleName_6662_ = lean_ctor_get(v_ident_6652_, 0);
lean_inc_ref(v_moduleName_6662_);
v_identModuleName_6663_ = l_String_toName(v_moduleName_6662_);
v___x_6664_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6651_, v_identModuleName_6663_);
if (lean_obj_tag(v___x_6664_) == 0)
{
lean_object* v___x_6665_; 
lean_dec(v_identModuleName_6663_);
v___x_6665_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6654_ = v___x_6665_;
goto v___jp_6653_;
}
else
{
lean_object* v_val_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; lean_object* v___x_6670_; 
v_val_6666_ = lean_ctor_get(v___x_6664_, 0);
lean_inc(v_val_6666_);
lean_dec_ref_known(v___x_6664_, 1);
v___x_6667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6667_, 0, v_identModuleName_6663_);
lean_ctor_set(v___x_6667_, 1, v_val_6666_);
v___x_6668_ = lean_unsigned_to_nat(1u);
v___x_6669_ = lean_mk_empty_array_with_capacity(v___x_6668_);
v___x_6670_ = lean_array_push(v___x_6669_, v___x_6667_);
v___y_6654_ = v___x_6670_;
goto v___jp_6653_;
}
}
v___jp_6653_:
{
lean_object* v_result_6655_; size_t v_sz_6656_; size_t v___x_6657_; lean_object* v___x_6658_; 
v_result_6655_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6656_ = lean_array_size(v___y_6654_);
v___x_6657_ = ((size_t)0ULL);
v___x_6658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6652_, v___y_6654_, v_sz_6656_, v___x_6657_, v_result_6655_);
lean_dec_ref(v___y_6654_);
lean_dec_ref(v_ident_6652_);
return v___x_6658_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6671_, lean_object* v_t_6672_, lean_object* v_k_6673_){
_start:
{
lean_object* v___x_6674_; 
v___x_6674_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6672_, v_k_6673_);
return v___x_6674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6675_, lean_object* v_t_6676_, lean_object* v_k_6677_){
_start:
{
lean_object* v_res_6678_; 
v_res_6678_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6675_, v_t_6676_, v_k_6677_);
lean_dec_ref(v_k_6677_);
lean_dec(v_t_6676_);
return v_res_6678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6679_, lean_object* v_t_6680_){
_start:
{
lean_object* v___x_6681_; 
v___x_6681_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6679_, v_t_6680_);
return v___x_6681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6682_, lean_object* v_t_6683_){
_start:
{
lean_object* v_res_6684_; 
v_res_6684_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6682_, v_t_6683_);
lean_dec(v_t_6683_);
return v_res_6684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6685_, lean_object* v_module_6686_, lean_object* v_pos_6687_, uint8_t v_includeStop_6688_){
_start:
{
lean_object* v___x_6689_; 
v___x_6689_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6685_, v_module_6686_);
if (lean_obj_tag(v___x_6689_) == 1)
{
lean_object* v_val_6690_; lean_object* v_snd_6691_; lean_object* v_fst_6692_; lean_object* v___x_6693_; 
v_val_6690_ = lean_ctor_get(v___x_6689_, 0);
lean_inc(v_val_6690_);
lean_dec_ref_known(v___x_6689_, 1);
v_snd_6691_ = lean_ctor_get(v_val_6690_, 1);
lean_inc(v_snd_6691_);
lean_dec(v_val_6690_);
v_fst_6692_ = lean_ctor_get(v_snd_6691_, 0);
lean_inc(v_fst_6692_);
lean_dec(v_snd_6691_);
v___x_6693_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6692_, v_pos_6687_, v_includeStop_6688_);
return v___x_6693_;
}
else
{
lean_object* v___x_6694_; 
lean_dec(v___x_6689_);
v___x_6694_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6695_, lean_object* v_module_6696_, lean_object* v_pos_6697_, lean_object* v_includeStop_6698_){
_start:
{
uint8_t v_includeStop_boxed_6699_; lean_object* v_res_6700_; 
v_includeStop_boxed_6699_ = lean_unbox(v_includeStop_6698_);
v_res_6700_ = l_Lean_Server_References_findAt(v_self_6695_, v_module_6696_, v_pos_6697_, v_includeStop_boxed_6699_);
lean_dec_ref(v_pos_6697_);
lean_dec(v_module_6696_);
return v_res_6700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6701_, lean_object* v_module_6702_, lean_object* v_pos_6703_, uint8_t v_includeStop_6704_){
_start:
{
lean_object* v___x_6705_; 
v___x_6705_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6701_, v_module_6702_);
if (lean_obj_tag(v___x_6705_) == 0)
{
lean_object* v___x_6706_; 
v___x_6706_ = lean_box(0);
return v___x_6706_;
}
else
{
lean_object* v_val_6707_; lean_object* v_snd_6708_; lean_object* v_fst_6709_; lean_object* v___x_6710_; 
v_val_6707_ = lean_ctor_get(v___x_6705_, 0);
lean_inc(v_val_6707_);
lean_dec_ref_known(v___x_6705_, 1);
v_snd_6708_ = lean_ctor_get(v_val_6707_, 1);
lean_inc(v_snd_6708_);
lean_dec(v_val_6707_);
v_fst_6709_ = lean_ctor_get(v_snd_6708_, 0);
lean_inc(v_fst_6709_);
lean_dec(v_snd_6708_);
v___x_6710_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6709_, v_pos_6703_, v_includeStop_6704_);
lean_dec(v_fst_6709_);
return v___x_6710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6711_, lean_object* v_module_6712_, lean_object* v_pos_6713_, lean_object* v_includeStop_6714_){
_start:
{
uint8_t v_includeStop_boxed_6715_; lean_object* v_res_6716_; 
v_includeStop_boxed_6715_ = lean_unbox(v_includeStop_6714_);
v_res_6716_ = l_Lean_Server_References_findRange_x3f(v_self_6711_, v_module_6712_, v_pos_6713_, v_includeStop_boxed_6715_);
lean_dec_ref(v_pos_6713_);
lean_dec(v_module_6712_);
return v_res_6716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6717_, lean_object* v_k_6718_){
_start:
{
if (lean_obj_tag(v_t_6717_) == 0)
{
lean_object* v_k_6719_; lean_object* v_v_6720_; lean_object* v_l_6721_; lean_object* v_r_6722_; uint8_t v___x_6723_; 
v_k_6719_ = lean_ctor_get(v_t_6717_, 1);
v_v_6720_ = lean_ctor_get(v_t_6717_, 2);
v_l_6721_ = lean_ctor_get(v_t_6717_, 3);
v_r_6722_ = lean_ctor_get(v_t_6717_, 4);
v___x_6723_ = lean_string_compare(v_k_6718_, v_k_6719_);
switch(v___x_6723_)
{
case 0:
{
v_t_6717_ = v_l_6721_;
goto _start;
}
case 1:
{
lean_object* v___x_6725_; 
lean_inc(v_v_6720_);
v___x_6725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6725_, 0, v_v_6720_);
return v___x_6725_;
}
default: 
{
v_t_6717_ = v_r_6722_;
goto _start;
}
}
}
else
{
lean_object* v___x_6727_; 
v___x_6727_ = lean_box(0);
return v___x_6727_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6728_, lean_object* v_k_6729_){
_start:
{
lean_object* v_res_6730_; 
v_res_6730_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6728_, v_k_6729_);
lean_dec_ref(v_k_6729_);
lean_dec(v_t_6728_);
return v_res_6730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6731_, lean_object* v_name_6732_){
_start:
{
lean_object* v___x_6733_; 
v___x_6733_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6731_, v_name_6732_);
if (lean_obj_tag(v___x_6733_) == 0)
{
lean_object* v___x_6734_; 
lean_dec_ref(v_name_6732_);
v___x_6734_ = lean_box(0);
return v___x_6734_;
}
else
{
lean_object* v_val_6735_; lean_object* v___x_6737_; uint8_t v_isShared_6738_; uint8_t v_isSharedCheck_6745_; 
v_val_6735_ = lean_ctor_get(v___x_6733_, 0);
v_isSharedCheck_6745_ = !lean_is_exclusive(v___x_6733_);
if (v_isSharedCheck_6745_ == 0)
{
v___x_6737_ = v___x_6733_;
v_isShared_6738_ = v_isSharedCheck_6745_;
goto v_resetjp_6736_;
}
else
{
lean_inc(v_val_6735_);
lean_dec(v___x_6733_);
v___x_6737_ = lean_box(0);
v_isShared_6738_ = v_isSharedCheck_6745_;
goto v_resetjp_6736_;
}
v_resetjp_6736_:
{
lean_object* v___x_6739_; lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6743_; 
v___x_6739_ = l_Lean_Lsp_DeclInfo_range(v_val_6735_);
v___x_6740_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6735_);
lean_dec(v_val_6735_);
v___x_6741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6741_, 0, v_name_6732_);
lean_ctor_set(v___x_6741_, 1, v___x_6739_);
lean_ctor_set(v___x_6741_, 2, v___x_6740_);
if (v_isShared_6738_ == 0)
{
lean_ctor_set(v___x_6737_, 0, v___x_6741_);
v___x_6743_ = v___x_6737_;
goto v_reusejp_6742_;
}
else
{
lean_object* v_reuseFailAlloc_6744_; 
v_reuseFailAlloc_6744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6744_, 0, v___x_6741_);
v___x_6743_ = v_reuseFailAlloc_6744_;
goto v_reusejp_6742_;
}
v_reusejp_6742_:
{
return v___x_6743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6746_, lean_object* v_name_6747_){
_start:
{
lean_object* v_res_6748_; 
v_res_6748_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6746_, v_name_6747_);
lean_dec(v_ds_6746_);
return v_res_6748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6749_, lean_object* v_t_6750_, lean_object* v_k_6751_){
_start:
{
lean_object* v___x_6752_; 
v___x_6752_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6750_, v_k_6751_);
return v___x_6752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6753_, lean_object* v_t_6754_, lean_object* v_k_6755_){
_start:
{
lean_object* v_res_6756_; 
v_res_6756_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6753_, v_t_6754_, v_k_6755_);
lean_dec_ref(v_k_6755_);
lean_dec(v_t_6754_);
return v_res_6756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6757_, lean_object* v_fst_6758_, lean_object* v_snd_6759_, lean_object* v_as_6760_, size_t v_sz_6761_, size_t v_i_6762_, lean_object* v_b_6763_){
_start:
{
uint8_t v___x_6764_; 
v___x_6764_ = lean_usize_dec_lt(v_i_6762_, v_sz_6761_);
if (v___x_6764_ == 0)
{
lean_dec(v_fst_6758_);
lean_dec_ref(v_fst_6757_);
return v_b_6763_;
}
else
{
lean_object* v_a_6765_; lean_object* v___y_6767_; lean_object* v___x_6775_; 
v_a_6765_ = lean_array_uget_borrowed(v_as_6760_, v_i_6762_);
v___x_6775_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6765_);
if (lean_obj_tag(v___x_6775_) == 0)
{
lean_object* v___x_6776_; 
v___x_6776_ = lean_box(0);
v___y_6767_ = v___x_6776_;
goto v___jp_6766_;
}
else
{
lean_object* v_val_6777_; lean_object* v___x_6778_; 
v_val_6777_ = lean_ctor_get(v___x_6775_, 0);
lean_inc(v_val_6777_);
lean_dec_ref_known(v___x_6775_, 1);
v___x_6778_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6759_, v_val_6777_);
v___y_6767_ = v___x_6778_;
goto v___jp_6766_;
}
v___jp_6766_:
{
lean_object* v___x_6768_; lean_object* v___x_6769_; lean_object* v___x_6770_; lean_object* v___x_6771_; size_t v___x_6772_; size_t v___x_6773_; 
v___x_6768_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6765_);
lean_inc_ref(v_fst_6757_);
v___x_6769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6769_, 0, v_fst_6757_);
lean_ctor_set(v___x_6769_, 1, v___x_6768_);
lean_inc(v_fst_6758_);
v___x_6770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6770_, 0, v___x_6769_);
lean_ctor_set(v___x_6770_, 1, v_fst_6758_);
lean_ctor_set(v___x_6770_, 2, v___y_6767_);
v___x_6771_ = lean_array_push(v_b_6763_, v___x_6770_);
v___x_6772_ = ((size_t)1ULL);
v___x_6773_ = lean_usize_add(v_i_6762_, v___x_6772_);
v_i_6762_ = v___x_6773_;
v_b_6763_ = v___x_6771_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6779_, lean_object* v_fst_6780_, lean_object* v_snd_6781_, lean_object* v_as_6782_, lean_object* v_sz_6783_, lean_object* v_i_6784_, lean_object* v_b_6785_){
_start:
{
size_t v_sz_boxed_6786_; size_t v_i_boxed_6787_; lean_object* v_res_6788_; 
v_sz_boxed_6786_ = lean_unbox_usize(v_sz_6783_);
lean_dec(v_sz_6783_);
v_i_boxed_6787_ = lean_unbox_usize(v_i_6784_);
lean_dec(v_i_6784_);
v_res_6788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6779_, v_fst_6780_, v_snd_6781_, v_as_6782_, v_sz_boxed_6786_, v_i_boxed_6787_, v_b_6785_);
lean_dec_ref(v_as_6782_);
lean_dec(v_snd_6781_);
return v_res_6788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6789_, lean_object* v_as_6790_, size_t v_sz_6791_, size_t v_i_6792_, lean_object* v_b_6793_){
_start:
{
uint8_t v___x_6794_; 
v___x_6794_ = lean_usize_dec_lt(v_i_6792_, v_sz_6791_);
if (v___x_6794_ == 0)
{
return v_b_6793_;
}
else
{
lean_object* v_a_6795_; lean_object* v_snd_6796_; lean_object* v_snd_6797_; lean_object* v_fst_6798_; lean_object* v_fst_6799_; lean_object* v_fst_6800_; lean_object* v_snd_6801_; lean_object* v___x_6803_; uint8_t v_isShared_6804_; uint8_t v_isSharedCheck_6828_; 
v_a_6795_ = lean_array_uget_borrowed(v_as_6790_, v_i_6792_);
v_snd_6796_ = lean_ctor_get(v_a_6795_, 1);
v_snd_6797_ = lean_ctor_get(v_snd_6796_, 1);
lean_inc(v_snd_6797_);
v_fst_6798_ = lean_ctor_get(v_a_6795_, 0);
v_fst_6799_ = lean_ctor_get(v_snd_6796_, 0);
v_fst_6800_ = lean_ctor_get(v_snd_6797_, 0);
v_snd_6801_ = lean_ctor_get(v_snd_6797_, 1);
v_isSharedCheck_6828_ = !lean_is_exclusive(v_snd_6797_);
if (v_isSharedCheck_6828_ == 0)
{
v___x_6803_ = v_snd_6797_;
v_isShared_6804_ = v_isSharedCheck_6828_;
goto v_resetjp_6802_;
}
else
{
lean_inc(v_snd_6801_);
lean_inc(v_fst_6800_);
lean_dec(v_snd_6797_);
v___x_6803_ = lean_box(0);
v_isShared_6804_ = v_isSharedCheck_6828_;
goto v_resetjp_6802_;
}
v_resetjp_6802_:
{
lean_object* v_result_6806_; 
if (v_includeDefinition_6789_ == 0)
{
lean_del_object(v___x_6803_);
v_result_6806_ = v_b_6793_;
goto v___jp_6805_;
}
else
{
lean_object* v_definition_x3f_6814_; 
v_definition_x3f_6814_ = lean_ctor_get(v_fst_6800_, 0);
if (lean_obj_tag(v_definition_x3f_6814_) == 1)
{
lean_object* v_val_6815_; lean_object* v___y_6817_; lean_object* v___x_6824_; 
v_val_6815_ = lean_ctor_get(v_definition_x3f_6814_, 0);
v___x_6824_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6815_);
if (lean_obj_tag(v___x_6824_) == 0)
{
lean_object* v___x_6825_; 
v___x_6825_ = lean_box(0);
v___y_6817_ = v___x_6825_;
goto v___jp_6816_;
}
else
{
lean_object* v_val_6826_; lean_object* v___x_6827_; 
v_val_6826_ = lean_ctor_get(v___x_6824_, 0);
lean_inc(v_val_6826_);
lean_dec_ref_known(v___x_6824_, 1);
v___x_6827_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6801_, v_val_6826_);
v___y_6817_ = v___x_6827_;
goto v___jp_6816_;
}
v___jp_6816_:
{
lean_object* v___x_6818_; lean_object* v___x_6820_; 
v___x_6818_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6815_);
lean_inc(v_fst_6798_);
if (v_isShared_6804_ == 0)
{
lean_ctor_set(v___x_6803_, 1, v___x_6818_);
lean_ctor_set(v___x_6803_, 0, v_fst_6798_);
v___x_6820_ = v___x_6803_;
goto v_reusejp_6819_;
}
else
{
lean_object* v_reuseFailAlloc_6823_; 
v_reuseFailAlloc_6823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6823_, 0, v_fst_6798_);
lean_ctor_set(v_reuseFailAlloc_6823_, 1, v___x_6818_);
v___x_6820_ = v_reuseFailAlloc_6823_;
goto v_reusejp_6819_;
}
v_reusejp_6819_:
{
lean_object* v___x_6821_; lean_object* v___x_6822_; 
lean_inc(v_fst_6799_);
v___x_6821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6821_, 0, v___x_6820_);
lean_ctor_set(v___x_6821_, 1, v_fst_6799_);
lean_ctor_set(v___x_6821_, 2, v___y_6817_);
v___x_6822_ = lean_array_push(v_b_6793_, v___x_6821_);
v_result_6806_ = v___x_6822_;
goto v___jp_6805_;
}
}
}
else
{
lean_del_object(v___x_6803_);
v_result_6806_ = v_b_6793_;
goto v___jp_6805_;
}
}
v___jp_6805_:
{
lean_object* v_usages_6807_; size_t v_sz_6808_; size_t v___x_6809_; lean_object* v___x_6810_; size_t v___x_6811_; size_t v___x_6812_; 
v_usages_6807_ = lean_ctor_get(v_fst_6800_, 1);
lean_inc_ref(v_usages_6807_);
lean_dec(v_fst_6800_);
v_sz_6808_ = lean_array_size(v_usages_6807_);
v___x_6809_ = ((size_t)0ULL);
lean_inc(v_fst_6799_);
lean_inc(v_fst_6798_);
v___x_6810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6798_, v_fst_6799_, v_snd_6801_, v_usages_6807_, v_sz_6808_, v___x_6809_, v_result_6806_);
lean_dec_ref(v_usages_6807_);
lean_dec(v_snd_6801_);
v___x_6811_ = ((size_t)1ULL);
v___x_6812_ = lean_usize_add(v_i_6792_, v___x_6811_);
v_i_6792_ = v___x_6812_;
v_b_6793_ = v___x_6810_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6829_, lean_object* v_as_6830_, lean_object* v_sz_6831_, lean_object* v_i_6832_, lean_object* v_b_6833_){
_start:
{
uint8_t v_includeDefinition_boxed_6834_; size_t v_sz_boxed_6835_; size_t v_i_boxed_6836_; lean_object* v_res_6837_; 
v_includeDefinition_boxed_6834_ = lean_unbox(v_includeDefinition_6829_);
v_sz_boxed_6835_ = lean_unbox_usize(v_sz_6831_);
lean_dec(v_sz_6831_);
v_i_boxed_6836_ = lean_unbox_usize(v_i_6832_);
lean_dec(v_i_6832_);
v_res_6837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6834_, v_as_6830_, v_sz_boxed_6835_, v_i_boxed_6836_, v_b_6833_);
lean_dec_ref(v_as_6830_);
return v_res_6837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6840_, lean_object* v_ident_6841_, uint8_t v_includeDefinition_6842_){
_start:
{
lean_object* v_result_6843_; lean_object* v___x_6844_; size_t v_sz_6845_; size_t v___x_6846_; lean_object* v___x_6847_; 
v_result_6843_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6844_ = l_Lean_Server_References_allRefsFor(v_self_6840_, v_ident_6841_);
v_sz_6845_ = lean_array_size(v___x_6844_);
v___x_6846_ = ((size_t)0ULL);
v___x_6847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6842_, v___x_6844_, v_sz_6845_, v___x_6846_, v_result_6843_);
lean_dec_ref(v___x_6844_);
return v___x_6847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6848_, lean_object* v_ident_6849_, lean_object* v_includeDefinition_6850_){
_start:
{
uint8_t v_includeDefinition_boxed_6851_; lean_object* v_res_6852_; 
v_includeDefinition_boxed_6851_ = lean_unbox(v_includeDefinition_6850_);
v_res_6852_ = l_Lean_Server_References_referringTo(v_self_6848_, v_ident_6849_, v_includeDefinition_boxed_6851_);
return v_res_6852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6856_, size_t v_sz_6857_, size_t v_i_6858_, lean_object* v_b_6859_){
_start:
{
uint8_t v___x_6860_; 
v___x_6860_ = lean_usize_dec_lt(v_i_6858_, v_sz_6857_);
if (v___x_6860_ == 0)
{
lean_inc_ref(v_b_6859_);
return v_b_6859_;
}
else
{
lean_object* v_a_6861_; lean_object* v_snd_6862_; lean_object* v_snd_6863_; lean_object* v_fst_6864_; lean_object* v_fst_6865_; lean_object* v_fst_6866_; lean_object* v_snd_6867_; lean_object* v___x_6869_; uint8_t v_isShared_6870_; uint8_t v_isSharedCheck_6905_; 
v_a_6861_ = lean_array_uget_borrowed(v_as_6856_, v_i_6858_);
v_snd_6862_ = lean_ctor_get(v_a_6861_, 1);
v_snd_6863_ = lean_ctor_get(v_snd_6862_, 1);
lean_inc(v_snd_6863_);
v_fst_6864_ = lean_ctor_get(v_snd_6863_, 0);
lean_inc(v_fst_6864_);
v_fst_6865_ = lean_ctor_get(v_a_6861_, 0);
v_fst_6866_ = lean_ctor_get(v_snd_6862_, 0);
v_snd_6867_ = lean_ctor_get(v_snd_6863_, 1);
v_isSharedCheck_6905_ = !lean_is_exclusive(v_snd_6863_);
if (v_isSharedCheck_6905_ == 0)
{
lean_object* v_unused_6906_; 
v_unused_6906_ = lean_ctor_get(v_snd_6863_, 0);
lean_dec(v_unused_6906_);
v___x_6869_ = v_snd_6863_;
v_isShared_6870_ = v_isSharedCheck_6905_;
goto v_resetjp_6868_;
}
else
{
lean_inc(v_snd_6867_);
lean_dec(v_snd_6863_);
v___x_6869_ = lean_box(0);
v_isShared_6870_ = v_isSharedCheck_6905_;
goto v_resetjp_6868_;
}
v_resetjp_6868_:
{
lean_object* v_definition_x3f_6871_; lean_object* v___x_6873_; uint8_t v_isShared_6874_; uint8_t v_isSharedCheck_6903_; 
v_definition_x3f_6871_ = lean_ctor_get(v_fst_6864_, 0);
v_isSharedCheck_6903_ = !lean_is_exclusive(v_fst_6864_);
if (v_isSharedCheck_6903_ == 0)
{
lean_object* v_unused_6904_; 
v_unused_6904_ = lean_ctor_get(v_fst_6864_, 1);
lean_dec(v_unused_6904_);
v___x_6873_ = v_fst_6864_;
v_isShared_6874_ = v_isSharedCheck_6903_;
goto v_resetjp_6872_;
}
else
{
lean_inc(v_definition_x3f_6871_);
lean_dec(v_fst_6864_);
v___x_6873_ = lean_box(0);
v_isShared_6874_ = v_isSharedCheck_6903_;
goto v_resetjp_6872_;
}
v_resetjp_6872_:
{
lean_object* v___x_6875_; 
v___x_6875_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6871_) == 1)
{
lean_object* v_val_6876_; lean_object* v___x_6878_; uint8_t v_isShared_6879_; uint8_t v_isSharedCheck_6898_; 
v_val_6876_ = lean_ctor_get(v_definition_x3f_6871_, 0);
v_isSharedCheck_6898_ = !lean_is_exclusive(v_definition_x3f_6871_);
if (v_isSharedCheck_6898_ == 0)
{
v___x_6878_ = v_definition_x3f_6871_;
v_isShared_6879_ = v_isSharedCheck_6898_;
goto v_resetjp_6877_;
}
else
{
lean_inc(v_val_6876_);
lean_dec(v_definition_x3f_6871_);
v___x_6878_ = lean_box(0);
v_isShared_6879_ = v_isSharedCheck_6898_;
goto v_resetjp_6877_;
}
v_resetjp_6877_:
{
lean_object* v___y_6881_; lean_object* v___x_6894_; 
v___x_6894_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6876_);
if (lean_obj_tag(v___x_6894_) == 0)
{
lean_object* v___x_6895_; 
lean_dec(v_snd_6867_);
v___x_6895_ = lean_box(0);
v___y_6881_ = v___x_6895_;
goto v___jp_6880_;
}
else
{
lean_object* v_val_6896_; lean_object* v___x_6897_; 
v_val_6896_ = lean_ctor_get(v___x_6894_, 0);
lean_inc(v_val_6896_);
lean_dec_ref_known(v___x_6894_, 1);
v___x_6897_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6867_, v_val_6896_);
lean_dec(v_snd_6867_);
v___y_6881_ = v___x_6897_;
goto v___jp_6880_;
}
v___jp_6880_:
{
lean_object* v___x_6882_; lean_object* v___x_6884_; 
v___x_6882_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6876_);
lean_dec(v_val_6876_);
lean_inc(v_fst_6865_);
if (v_isShared_6874_ == 0)
{
lean_ctor_set(v___x_6873_, 1, v___x_6882_);
lean_ctor_set(v___x_6873_, 0, v_fst_6865_);
v___x_6884_ = v___x_6873_;
goto v_reusejp_6883_;
}
else
{
lean_object* v_reuseFailAlloc_6893_; 
v_reuseFailAlloc_6893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6893_, 0, v_fst_6865_);
lean_ctor_set(v_reuseFailAlloc_6893_, 1, v___x_6882_);
v___x_6884_ = v_reuseFailAlloc_6893_;
goto v_reusejp_6883_;
}
v_reusejp_6883_:
{
lean_object* v___x_6885_; lean_object* v___x_6887_; 
lean_inc(v_fst_6866_);
v___x_6885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6885_, 0, v___x_6884_);
lean_ctor_set(v___x_6885_, 1, v_fst_6866_);
lean_ctor_set(v___x_6885_, 2, v___y_6881_);
if (v_isShared_6879_ == 0)
{
lean_ctor_set(v___x_6878_, 0, v___x_6885_);
v___x_6887_ = v___x_6878_;
goto v_reusejp_6886_;
}
else
{
lean_object* v_reuseFailAlloc_6892_; 
v_reuseFailAlloc_6892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6892_, 0, v___x_6885_);
v___x_6887_ = v_reuseFailAlloc_6892_;
goto v_reusejp_6886_;
}
v_reusejp_6886_:
{
lean_object* v___x_6888_; lean_object* v___x_6890_; 
v___x_6888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6888_, 0, v___x_6887_);
if (v_isShared_6870_ == 0)
{
lean_ctor_set(v___x_6869_, 1, v___x_6875_);
lean_ctor_set(v___x_6869_, 0, v___x_6888_);
v___x_6890_ = v___x_6869_;
goto v_reusejp_6889_;
}
else
{
lean_object* v_reuseFailAlloc_6891_; 
v_reuseFailAlloc_6891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6891_, 0, v___x_6888_);
lean_ctor_set(v_reuseFailAlloc_6891_, 1, v___x_6875_);
v___x_6890_ = v_reuseFailAlloc_6891_;
goto v_reusejp_6889_;
}
v_reusejp_6889_:
{
return v___x_6890_;
}
}
}
}
}
}
else
{
lean_object* v___x_6899_; size_t v___x_6900_; size_t v___x_6901_; 
lean_del_object(v___x_6873_);
lean_dec(v_definition_x3f_6871_);
lean_del_object(v___x_6869_);
lean_dec(v_snd_6867_);
v___x_6899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6900_ = ((size_t)1ULL);
v___x_6901_ = lean_usize_add(v_i_6858_, v___x_6900_);
v_i_6858_ = v___x_6901_;
v_b_6859_ = v___x_6899_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6907_, lean_object* v_sz_6908_, lean_object* v_i_6909_, lean_object* v_b_6910_){
_start:
{
size_t v_sz_boxed_6911_; size_t v_i_boxed_6912_; lean_object* v_res_6913_; 
v_sz_boxed_6911_ = lean_unbox_usize(v_sz_6908_);
lean_dec(v_sz_6908_);
v_i_boxed_6912_ = lean_unbox_usize(v_i_6909_);
lean_dec(v_i_6909_);
v_res_6913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6907_, v_sz_boxed_6911_, v_i_boxed_6912_, v_b_6910_);
lean_dec_ref(v_b_6910_);
lean_dec_ref(v_as_6907_);
return v_res_6913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6914_, lean_object* v_ident_6915_){
_start:
{
lean_object* v___x_6916_; lean_object* v___x_6917_; lean_object* v___x_6918_; size_t v_sz_6919_; size_t v___x_6920_; lean_object* v___x_6921_; lean_object* v_fst_6922_; 
v___x_6916_ = l_Lean_Server_References_allRefsFor(v_self_6914_, v_ident_6915_);
v___x_6917_ = lean_box(0);
v___x_6918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6919_ = lean_array_size(v___x_6916_);
v___x_6920_ = ((size_t)0ULL);
v___x_6921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6916_, v_sz_6919_, v___x_6920_, v___x_6918_);
lean_dec_ref(v___x_6916_);
v_fst_6922_ = lean_ctor_get(v___x_6921_, 0);
lean_inc(v_fst_6922_);
lean_dec_ref(v___x_6921_);
if (lean_obj_tag(v_fst_6922_) == 0)
{
return v___x_6917_;
}
else
{
lean_object* v_val_6923_; 
v_val_6923_ = lean_ctor_get(v_fst_6922_, 0);
lean_inc(v_val_6923_);
lean_dec_ref_known(v_fst_6922_, 1);
return v_val_6923_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6924_, lean_object* v_a_6925_, lean_object* v_fst_6926_, lean_object* v_init_6927_, lean_object* v_x_6928_){
_start:
{
lean_object* v_d_6931_; 
if (lean_obj_tag(v_x_6928_) == 0)
{
lean_object* v_k_6933_; lean_object* v_v_6934_; lean_object* v_l_6935_; lean_object* v_r_6936_; lean_object* v___y_6938_; lean_object* v___x_6942_; 
v_k_6933_ = lean_ctor_get(v_x_6928_, 1);
lean_inc(v_k_6933_);
v_v_6934_ = lean_ctor_get(v_x_6928_, 2);
lean_inc(v_v_6934_);
v_l_6935_ = lean_ctor_get(v_x_6928_, 3);
lean_inc(v_l_6935_);
v_r_6936_ = lean_ctor_get(v_x_6928_, 4);
lean_inc(v_r_6936_);
lean_dec_ref_known(v_x_6928_, 5);
lean_inc_ref(v_fst_6926_);
lean_inc(v_a_6925_);
lean_inc_ref(v_filterMapIdent_6924_);
v___x_6942_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6924_, v_a_6925_, v_fst_6926_, v_init_6927_, v_l_6935_);
if (lean_obj_tag(v___x_6942_) == 0)
{
lean_object* v_a_6943_; 
lean_dec(v_r_6936_);
lean_dec(v_v_6934_);
lean_dec(v_k_6933_);
lean_dec_ref(v_fst_6926_);
lean_dec(v_a_6925_);
lean_dec_ref(v_filterMapIdent_6924_);
v_a_6943_ = lean_ctor_get(v___x_6942_, 0);
lean_inc(v_a_6943_);
lean_dec_ref_known(v___x_6942_, 1);
v_d_6931_ = v_a_6943_;
goto v___jp_6930_;
}
else
{
if (lean_obj_tag(v_k_6933_) == 0)
{
lean_object* v_definition_x3f_6944_; 
v_definition_x3f_6944_ = lean_ctor_get(v_v_6934_, 0);
lean_inc(v_definition_x3f_6944_);
lean_dec(v_v_6934_);
if (lean_obj_tag(v_definition_x3f_6944_) == 1)
{
lean_object* v_a_6945_; lean_object* v_identName_6946_; lean_object* v_val_6947_; lean_object* v___x_6948_; lean_object* v___x_6949_; 
v_a_6945_ = lean_ctor_get(v___x_6942_, 0);
v_identName_6946_ = lean_ctor_get(v_k_6933_, 1);
lean_inc_ref(v_identName_6946_);
lean_dec_ref_known(v_k_6933_, 2);
v_val_6947_ = lean_ctor_get(v_definition_x3f_6944_, 0);
lean_inc(v_val_6947_);
lean_dec_ref_known(v_definition_x3f_6944_, 1);
v___x_6948_ = l_String_toName(v_identName_6946_);
lean_inc_ref(v_filterMapIdent_6924_);
v___x_6949_ = lean_apply_1(v_filterMapIdent_6924_, v___x_6948_);
if (lean_obj_tag(v___x_6949_) == 1)
{
lean_object* v_val_6950_; lean_object* v___x_6951_; lean_object* v___x_6952_; lean_object* v___x_6953_; 
lean_inc(v_a_6945_);
lean_dec_ref_known(v___x_6942_, 1);
v_val_6950_ = lean_ctor_get(v___x_6949_, 0);
lean_inc(v_val_6950_);
lean_dec_ref_known(v___x_6949_, 1);
v___x_6951_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6947_);
lean_dec(v_val_6947_);
lean_inc_ref(v_fst_6926_);
lean_inc(v_a_6925_);
v___x_6952_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6952_, 0, v_a_6925_);
lean_ctor_set(v___x_6952_, 1, v_fst_6926_);
lean_ctor_set(v___x_6952_, 2, v_val_6950_);
lean_ctor_set(v___x_6952_, 3, v___x_6951_);
v___x_6953_ = lean_array_push(v_a_6945_, v___x_6952_);
v_init_6927_ = v___x_6953_;
v_x_6928_ = v_r_6936_;
goto _start;
}
else
{
lean_dec(v___x_6949_);
lean_dec(v_val_6947_);
v___y_6938_ = v___x_6942_;
goto v___jp_6937_;
}
}
else
{
lean_dec(v_definition_x3f_6944_);
lean_dec_ref_known(v_k_6933_, 2);
v___y_6938_ = v___x_6942_;
goto v___jp_6937_;
}
}
else
{
lean_dec(v_v_6934_);
lean_dec(v_k_6933_);
v___y_6938_ = v___x_6942_;
goto v___jp_6937_;
}
}
v___jp_6937_:
{
if (lean_obj_tag(v___y_6938_) == 0)
{
lean_object* v_a_6939_; 
lean_dec(v_r_6936_);
lean_dec_ref(v_fst_6926_);
lean_dec(v_a_6925_);
lean_dec_ref(v_filterMapIdent_6924_);
v_a_6939_ = lean_ctor_get(v___y_6938_, 0);
lean_inc(v_a_6939_);
lean_dec_ref_known(v___y_6938_, 1);
v_d_6931_ = v_a_6939_;
goto v___jp_6930_;
}
else
{
lean_object* v_a_6940_; 
v_a_6940_ = lean_ctor_get(v___y_6938_, 0);
lean_inc(v_a_6940_);
lean_dec_ref_known(v___y_6938_, 1);
v_init_6927_ = v_a_6940_;
v_x_6928_ = v_r_6936_;
goto _start;
}
}
}
else
{
lean_object* v___x_6955_; 
lean_dec_ref(v_fst_6926_);
lean_dec(v_a_6925_);
lean_dec_ref(v_filterMapIdent_6924_);
v___x_6955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6955_, 0, v_init_6927_);
return v___x_6955_;
}
v___jp_6930_:
{
lean_object* v___x_6932_; 
v___x_6932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6932_, 0, v_d_6931_);
return v___x_6932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6956_, lean_object* v_a_6957_, lean_object* v_fst_6958_, lean_object* v_init_6959_, lean_object* v_x_6960_, lean_object* v___y_6961_){
_start:
{
lean_object* v_res_6962_; 
v_res_6962_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6956_, v_a_6957_, v_fst_6958_, v_init_6959_, v_x_6960_);
return v_res_6962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6963_, lean_object* v_cancelTk_x3f_6964_, lean_object* v_init_6965_, lean_object* v_x_6966_){
_start:
{
lean_object* v_d_6969_; 
if (lean_obj_tag(v_x_6966_) == 0)
{
lean_object* v_k_6971_; lean_object* v_v_6972_; lean_object* v_l_6973_; lean_object* v_r_6974_; lean_object* v___x_6975_; lean_object* v_val_6977_; lean_object* v___x_6980_; 
v_k_6971_ = lean_ctor_get(v_x_6966_, 1);
lean_inc(v_k_6971_);
v_v_6972_ = lean_ctor_get(v_x_6966_, 2);
lean_inc(v_v_6972_);
v_l_6973_ = lean_ctor_get(v_x_6966_, 3);
lean_inc(v_l_6973_);
v_r_6974_ = lean_ctor_get(v_x_6966_, 4);
lean_inc(v_r_6974_);
lean_dec_ref_known(v_x_6966_, 5);
v___x_6975_ = lean_box(0);
lean_inc(v_cancelTk_x3f_6964_);
lean_inc_ref(v_filterMapIdent_6963_);
v___x_6980_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6963_, v_cancelTk_x3f_6964_, v_init_6965_, v_l_6973_);
if (lean_obj_tag(v___x_6980_) == 0)
{
lean_object* v_a_6981_; 
lean_dec(v_r_6974_);
lean_dec(v_v_6972_);
lean_dec(v_k_6971_);
lean_dec(v_cancelTk_x3f_6964_);
lean_dec_ref(v_filterMapIdent_6963_);
v_a_6981_ = lean_ctor_get(v___x_6980_, 0);
lean_inc(v_a_6981_);
lean_dec_ref_known(v___x_6980_, 1);
v_d_6969_ = v_a_6981_;
goto v___jp_6968_;
}
else
{
lean_object* v_snd_6982_; lean_object* v_a_6983_; lean_object* v_fst_6984_; lean_object* v_fst_6985_; lean_object* v_snd_6986_; lean_object* v___x_6988_; uint8_t v_isShared_6989_; uint8_t v_isSharedCheck_7006_; 
v_snd_6982_ = lean_ctor_get(v_v_6972_, 1);
lean_inc(v_snd_6982_);
v_a_6983_ = lean_ctor_get(v___x_6980_, 0);
lean_inc(v_a_6983_);
lean_dec_ref_known(v___x_6980_, 1);
v_fst_6984_ = lean_ctor_get(v_v_6972_, 0);
lean_inc(v_fst_6984_);
lean_dec(v_v_6972_);
v_fst_6985_ = lean_ctor_get(v_snd_6982_, 0);
lean_inc(v_fst_6985_);
lean_dec(v_snd_6982_);
v_snd_6986_ = lean_ctor_get(v_a_6983_, 1);
v_isSharedCheck_7006_ = !lean_is_exclusive(v_a_6983_);
if (v_isSharedCheck_7006_ == 0)
{
lean_object* v_unused_7007_; 
v_unused_7007_ = lean_ctor_get(v_a_6983_, 0);
lean_dec(v_unused_7007_);
v___x_6988_ = v_a_6983_;
v_isShared_6989_ = v_isSharedCheck_7006_;
goto v_resetjp_6987_;
}
else
{
lean_inc(v_snd_6986_);
lean_dec(v_a_6983_);
v___x_6988_ = lean_box(0);
v_isShared_6989_ = v_isSharedCheck_7006_;
goto v_resetjp_6987_;
}
v_resetjp_6987_:
{
if (lean_obj_tag(v_cancelTk_x3f_6964_) == 1)
{
lean_object* v_val_6993_; uint8_t v___x_6994_; 
v_val_6993_ = lean_ctor_get(v_cancelTk_x3f_6964_, 0);
v___x_6994_ = l_IO_CancelToken_isSet(v_val_6993_);
if (v___x_6994_ == 0)
{
lean_del_object(v___x_6988_);
goto v___jp_6990_;
}
else
{
lean_object* v___x_6996_; uint8_t v_isShared_6997_; uint8_t v_isSharedCheck_7004_; 
lean_dec(v_fst_6985_);
lean_dec(v_fst_6984_);
lean_dec(v_r_6974_);
lean_dec(v_k_6971_);
lean_dec_ref(v_filterMapIdent_6963_);
v_isSharedCheck_7004_ = !lean_is_exclusive(v_cancelTk_x3f_6964_);
if (v_isSharedCheck_7004_ == 0)
{
lean_object* v_unused_7005_; 
v_unused_7005_ = lean_ctor_get(v_cancelTk_x3f_6964_, 0);
lean_dec(v_unused_7005_);
v___x_6996_ = v_cancelTk_x3f_6964_;
v_isShared_6997_ = v_isSharedCheck_7004_;
goto v_resetjp_6995_;
}
else
{
lean_dec(v_cancelTk_x3f_6964_);
v___x_6996_ = lean_box(0);
v_isShared_6997_ = v_isSharedCheck_7004_;
goto v_resetjp_6995_;
}
v_resetjp_6995_:
{
lean_object* v___x_6999_; 
lean_inc(v_snd_6986_);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 0, v_snd_6986_);
v___x_6999_ = v___x_6996_;
goto v_reusejp_6998_;
}
else
{
lean_object* v_reuseFailAlloc_7003_; 
v_reuseFailAlloc_7003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7003_, 0, v_snd_6986_);
v___x_6999_ = v_reuseFailAlloc_7003_;
goto v_reusejp_6998_;
}
v_reusejp_6998_:
{
lean_object* v___x_7001_; 
if (v_isShared_6989_ == 0)
{
lean_ctor_set(v___x_6988_, 0, v___x_6999_);
v___x_7001_ = v___x_6988_;
goto v_reusejp_7000_;
}
else
{
lean_object* v_reuseFailAlloc_7002_; 
v_reuseFailAlloc_7002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7002_, 0, v___x_6999_);
lean_ctor_set(v_reuseFailAlloc_7002_, 1, v_snd_6986_);
v___x_7001_ = v_reuseFailAlloc_7002_;
goto v_reusejp_7000_;
}
v_reusejp_7000_:
{
v_d_6969_ = v___x_7001_;
goto v___jp_6968_;
}
}
}
}
}
else
{
lean_del_object(v___x_6988_);
goto v___jp_6990_;
}
v___jp_6990_:
{
lean_object* v___x_6991_; lean_object* v_a_6992_; 
lean_inc_ref(v_filterMapIdent_6963_);
v___x_6991_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6963_, v_k_6971_, v_fst_6984_, v_snd_6986_, v_fst_6985_);
v_a_6992_ = lean_ctor_get(v___x_6991_, 0);
lean_inc(v_a_6992_);
lean_dec_ref(v___x_6991_);
v_val_6977_ = v_a_6992_;
goto v___jp_6976_;
}
}
}
v___jp_6976_:
{
lean_object* v___x_6978_; 
v___x_6978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6978_, 0, v___x_6975_);
lean_ctor_set(v___x_6978_, 1, v_val_6977_);
v_init_6965_ = v___x_6978_;
v_x_6966_ = v_r_6974_;
goto _start;
}
}
else
{
lean_object* v___x_7008_; 
lean_dec(v_cancelTk_x3f_6964_);
lean_dec_ref(v_filterMapIdent_6963_);
v___x_7008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7008_, 0, v_init_6965_);
return v___x_7008_;
}
v___jp_6968_:
{
lean_object* v___x_6970_; 
v___x_6970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6970_, 0, v_d_6969_);
return v___x_6970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_7009_, lean_object* v_cancelTk_x3f_7010_, lean_object* v_init_7011_, lean_object* v_x_7012_, lean_object* v___y_7013_){
_start:
{
lean_object* v_res_7014_; 
v_res_7014_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7009_, v_cancelTk_x3f_7010_, v_init_7011_, v_x_7012_);
return v_res_7014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_7020_, lean_object* v_filterMapIdent_7021_, lean_object* v_cancelTk_x3f_7022_){
_start:
{
lean_object* v_val_7025_; lean_object* v___x_7029_; lean_object* v___x_7030_; lean_object* v___x_7031_; lean_object* v_a_7032_; 
v___x_7029_ = l_Lean_Server_References_allRefs(v_self_7020_);
v___x_7030_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_7031_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7021_, v_cancelTk_x3f_7022_, v___x_7030_, v___x_7029_);
v_a_7032_ = lean_ctor_get(v___x_7031_, 0);
lean_inc(v_a_7032_);
lean_dec_ref(v___x_7031_);
v_val_7025_ = v_a_7032_;
goto v___jp_7024_;
v___jp_7024_:
{
lean_object* v_fst_7026_; 
v_fst_7026_ = lean_ctor_get(v_val_7025_, 0);
if (lean_obj_tag(v_fst_7026_) == 0)
{
lean_object* v_snd_7027_; 
v_snd_7027_ = lean_ctor_get(v_val_7025_, 1);
lean_inc(v_snd_7027_);
lean_dec_ref(v_val_7025_);
return v_snd_7027_;
}
else
{
lean_object* v_val_7028_; 
lean_inc_ref(v_fst_7026_);
lean_dec_ref(v_val_7025_);
v_val_7028_ = lean_ctor_get(v_fst_7026_, 0);
lean_inc(v_val_7028_);
lean_dec_ref_known(v_fst_7026_, 1);
return v_val_7028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_7033_, lean_object* v_filterMapIdent_7034_, lean_object* v_cancelTk_x3f_7035_, lean_object* v_a_7036_){
_start:
{
lean_object* v_res_7037_; 
v_res_7037_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7033_, v_filterMapIdent_7034_, v_cancelTk_x3f_7035_);
return v_res_7037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_7038_, lean_object* v_self_7039_, lean_object* v_filterMapIdent_7040_, lean_object* v_cancelTk_x3f_7041_){
_start:
{
lean_object* v___x_7043_; 
v___x_7043_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7039_, v_filterMapIdent_7040_, v_cancelTk_x3f_7041_);
return v___x_7043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_7044_, lean_object* v_self_7045_, lean_object* v_filterMapIdent_7046_, lean_object* v_cancelTk_x3f_7047_, lean_object* v_a_7048_){
_start:
{
lean_object* v_res_7049_; 
v_res_7049_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_7044_, v_self_7045_, v_filterMapIdent_7046_, v_cancelTk_x3f_7047_);
return v_res_7049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_7050_, lean_object* v_filterMapIdent_7051_, lean_object* v_a_7052_, lean_object* v_fst_7053_, lean_object* v_init_7054_, lean_object* v_x_7055_){
_start:
{
lean_object* v___x_7057_; 
v___x_7057_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_7051_, v_a_7052_, v_fst_7053_, v_init_7054_, v_x_7055_);
return v___x_7057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_7058_, lean_object* v_filterMapIdent_7059_, lean_object* v_a_7060_, lean_object* v_fst_7061_, lean_object* v_init_7062_, lean_object* v_x_7063_, lean_object* v___y_7064_){
_start:
{
lean_object* v_res_7065_; 
v_res_7065_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_7058_, v_filterMapIdent_7059_, v_a_7060_, v_fst_7061_, v_init_7062_, v_x_7063_);
return v_res_7065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_7066_, lean_object* v_filterMapIdent_7067_, lean_object* v_cancelTk_x3f_7068_, lean_object* v_init_7069_, lean_object* v_x_7070_){
_start:
{
lean_object* v___x_7072_; 
v___x_7072_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7067_, v_cancelTk_x3f_7068_, v_init_7069_, v_x_7070_);
return v___x_7072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7073_, lean_object* v_filterMapIdent_7074_, lean_object* v_cancelTk_x3f_7075_, lean_object* v_init_7076_, lean_object* v_x_7077_, lean_object* v___y_7078_){
_start:
{
lean_object* v_res_7079_; 
v_res_7079_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7073_, v_filterMapIdent_7074_, v_cancelTk_x3f_7075_, v_init_7076_, v_x_7077_);
return v_res_7079_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7080_){
_start:
{
lean_object* v___x_7081_; lean_object* v___x_7082_; 
v___x_7081_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7082_ = lean_panic_fn_borrowed(v___x_7081_, v_msg_7080_);
return v___x_7082_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7086_; lean_object* v___x_7087_; lean_object* v___x_7088_; lean_object* v___x_7089_; lean_object* v___x_7090_; lean_object* v___x_7091_; 
v___x_7086_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7087_ = lean_unsigned_to_nat(14u);
v___x_7088_ = lean_unsigned_to_nat(22u);
v___x_7089_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7090_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7091_ = l_mkPanicMessageWithDecl(v___x_7090_, v___x_7089_, v___x_7088_, v___x_7087_, v___x_7086_);
return v___x_7091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7092_, lean_object* v_init_7093_, lean_object* v_x_7094_){
_start:
{
if (lean_obj_tag(v_x_7094_) == 0)
{
lean_object* v_k_7095_; lean_object* v_v_7096_; lean_object* v_l_7097_; lean_object* v_r_7098_; lean_object* v___x_7099_; lean_object* v_a_7100_; lean_object* v_fst_7101_; lean_object* v_snd_7102_; lean_object* v___y_7104_; lean_object* v_index_7119_; lean_object* v___x_7120_; 
v_k_7095_ = lean_ctor_get(v_x_7094_, 1);
v_v_7096_ = lean_ctor_get(v_x_7094_, 2);
v_l_7097_ = lean_ctor_get(v_x_7094_, 3);
v_r_7098_ = lean_ctor_get(v_x_7094_, 4);
v___x_7099_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7092_, v_init_7093_, v_l_7097_);
v_a_7100_ = lean_ctor_get(v___x_7099_, 0);
v_fst_7101_ = lean_ctor_get(v_v_7096_, 0);
v_snd_7102_ = lean_ctor_get(v_v_7096_, 1);
v_index_7119_ = lean_ctor_get(v_snd_7102_, 1);
v___x_7120_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7119_, v_requestedMod_7092_);
if (lean_obj_tag(v___x_7120_) == 1)
{
lean_object* v_val_7121_; lean_object* v___x_7122_; 
lean_inc(v_a_7100_);
lean_dec_ref(v___x_7099_);
v_val_7121_ = lean_ctor_get(v___x_7120_, 0);
lean_inc(v_val_7121_);
lean_dec_ref_known(v___x_7120_, 1);
v___x_7122_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7121_);
lean_dec(v_val_7121_);
if (lean_obj_tag(v___x_7122_) == 0)
{
lean_object* v___x_7123_; lean_object* v___x_7124_; 
v___x_7123_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7124_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7123_);
v___y_7104_ = v___x_7124_;
goto v___jp_7103_;
}
else
{
lean_object* v_val_7125_; 
v_val_7125_ = lean_ctor_get(v___x_7122_, 0);
lean_inc(v_val_7125_);
lean_dec_ref_known(v___x_7122_, 1);
v___y_7104_ = v_val_7125_;
goto v___jp_7103_;
}
}
else
{
lean_object* v_a_7126_; 
lean_dec(v___x_7120_);
v_a_7126_ = lean_ctor_get(v___x_7099_, 0);
lean_inc(v_a_7126_);
lean_dec_ref(v___x_7099_);
v_init_7093_ = v_a_7126_;
v_x_7094_ = v_r_7098_;
goto _start;
}
v___jp_7103_:
{
uint8_t v_isAll_7105_; uint8_t v_isPrivate_7106_; uint8_t v_metaKind_7107_; lean_object* v___x_7109_; uint8_t v_isShared_7110_; uint8_t v_isSharedCheck_7116_; 
v_isAll_7105_ = lean_ctor_get_uint8(v___y_7104_, sizeof(void*)*2);
v_isPrivate_7106_ = lean_ctor_get_uint8(v___y_7104_, sizeof(void*)*2 + 1);
v_metaKind_7107_ = lean_ctor_get_uint8(v___y_7104_, sizeof(void*)*2 + 2);
v_isSharedCheck_7116_ = !lean_is_exclusive(v___y_7104_);
if (v_isSharedCheck_7116_ == 0)
{
lean_object* v_unused_7117_; lean_object* v_unused_7118_; 
v_unused_7117_ = lean_ctor_get(v___y_7104_, 1);
lean_dec(v_unused_7117_);
v_unused_7118_ = lean_ctor_get(v___y_7104_, 0);
lean_dec(v_unused_7118_);
v___x_7109_ = v___y_7104_;
v_isShared_7110_ = v_isSharedCheck_7116_;
goto v_resetjp_7108_;
}
else
{
lean_dec(v___y_7104_);
v___x_7109_ = lean_box(0);
v_isShared_7110_ = v_isSharedCheck_7116_;
goto v_resetjp_7108_;
}
v_resetjp_7108_:
{
lean_object* v___x_7112_; 
lean_inc(v_fst_7101_);
lean_inc(v_k_7095_);
if (v_isShared_7110_ == 0)
{
lean_ctor_set(v___x_7109_, 1, v_fst_7101_);
lean_ctor_set(v___x_7109_, 0, v_k_7095_);
v___x_7112_ = v___x_7109_;
goto v_reusejp_7111_;
}
else
{
lean_object* v_reuseFailAlloc_7115_; 
v_reuseFailAlloc_7115_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7115_, 0, v_k_7095_);
lean_ctor_set(v_reuseFailAlloc_7115_, 1, v_fst_7101_);
lean_ctor_set_uint8(v_reuseFailAlloc_7115_, sizeof(void*)*2, v_isAll_7105_);
lean_ctor_set_uint8(v_reuseFailAlloc_7115_, sizeof(void*)*2 + 1, v_isPrivate_7106_);
lean_ctor_set_uint8(v_reuseFailAlloc_7115_, sizeof(void*)*2 + 2, v_metaKind_7107_);
v___x_7112_ = v_reuseFailAlloc_7115_;
goto v_reusejp_7111_;
}
v_reusejp_7111_:
{
lean_object* v___x_7113_; 
v___x_7113_ = lean_array_push(v_a_7100_, v___x_7112_);
v_init_7093_ = v___x_7113_;
v_x_7094_ = v_r_7098_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7128_; 
v___x_7128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7128_, 0, v_init_7093_);
return v___x_7128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object* v_requestedMod_7129_, lean_object* v_init_7130_, lean_object* v_x_7131_){
_start:
{
lean_object* v_res_7132_; 
v_res_7132_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7129_, v_init_7130_, v_x_7131_);
lean_dec(v_x_7131_);
lean_dec(v_requestedMod_7129_);
return v_res_7132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object* v_self_7133_, lean_object* v_requestedMod_7134_){
_start:
{
lean_object* v_result_7135_; lean_object* v___x_7136_; lean_object* v___x_7137_; lean_object* v_a_7138_; 
v_result_7135_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_7136_ = l_Lean_Server_References_allDirectImports(v_self_7133_);
v___x_7137_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7134_, v_result_7135_, v___x_7136_);
lean_dec(v___x_7136_);
v_a_7138_ = lean_ctor_get(v___x_7137_, 0);
lean_inc(v_a_7138_);
lean_dec_ref(v___x_7137_);
return v_a_7138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object* v_self_7139_, lean_object* v_requestedMod_7140_){
_start:
{
lean_object* v_res_7141_; 
v_res_7141_ = l_Lean_Server_References_importedBy(v_self_7139_, v_requestedMod_7140_);
lean_dec(v_requestedMod_7140_);
return v_res_7141_;
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

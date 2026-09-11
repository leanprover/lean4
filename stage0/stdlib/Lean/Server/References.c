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
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_nbuckets_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2955_ = lean_array_get_size(v_data_2954_);
v___x_2956_ = lean_unsigned_to_nat(2u);
v_nbuckets_2957_ = lean_nat_mul(v___x_2955_, v___x_2956_);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_mk_array(v_nbuckets_2957_, v___x_2959_);
v___x_2961_ = lean_array_propagate_mark(v_data_2954_, v___x_2960_);
v___x_2962_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v___x_2958_, v_data_2954_, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(lean_object* v_m_2963_, lean_object* v_a_2964_, lean_object* v_b_2965_){
_start:
{
lean_object* v_size_2966_; lean_object* v_buckets_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3010_; 
v_size_2966_ = lean_ctor_get(v_m_2963_, 0);
v_buckets_2967_ = lean_ctor_get(v_m_2963_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_m_2963_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2969_ = v_m_2963_;
v_isShared_2970_ = v_isSharedCheck_3010_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_buckets_2967_);
lean_inc(v_size_2966_);
lean_dec(v_m_2963_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3010_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; uint64_t v___x_2972_; uint64_t v___x_2973_; uint64_t v___x_2974_; uint64_t v_fold_2975_; uint64_t v___x_2976_; uint64_t v___x_2977_; uint64_t v___x_2978_; size_t v___x_2979_; size_t v___x_2980_; size_t v___x_2981_; size_t v___x_2982_; size_t v___x_2983_; lean_object* v_bkt_2984_; uint8_t v___x_2985_; 
v___x_2971_ = lean_array_get_size(v_buckets_2967_);
v___x_2972_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_2964_);
v___x_2973_ = 32ULL;
v___x_2974_ = lean_uint64_shift_right(v___x_2972_, v___x_2973_);
v_fold_2975_ = lean_uint64_xor(v___x_2972_, v___x_2974_);
v___x_2976_ = 16ULL;
v___x_2977_ = lean_uint64_shift_right(v_fold_2975_, v___x_2976_);
v___x_2978_ = lean_uint64_xor(v_fold_2975_, v___x_2977_);
v___x_2979_ = lean_uint64_to_usize(v___x_2978_);
v___x_2980_ = lean_usize_of_nat(v___x_2971_);
v___x_2981_ = ((size_t)1ULL);
v___x_2982_ = lean_usize_sub(v___x_2980_, v___x_2981_);
v___x_2983_ = lean_usize_land(v___x_2979_, v___x_2982_);
v_bkt_2984_ = lean_array_uget_borrowed(v_buckets_2967_, v___x_2983_);
v___x_2985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_2964_, v_bkt_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v_size_x27_2987_; lean_object* v___x_2988_; lean_object* v_buckets_x27_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2986_ = lean_unsigned_to_nat(1u);
v_size_x27_2987_ = lean_nat_add(v_size_2966_, v___x_2986_);
lean_dec(v_size_2966_);
lean_inc(v_bkt_2984_);
v___x_2988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2988_, 0, v_a_2964_);
lean_ctor_set(v___x_2988_, 1, v_b_2965_);
lean_ctor_set(v___x_2988_, 2, v_bkt_2984_);
v_buckets_x27_2989_ = lean_array_uset(v_buckets_2967_, v___x_2983_, v___x_2988_);
v___x_2990_ = lean_unsigned_to_nat(4u);
v___x_2991_ = lean_nat_mul(v_size_x27_2987_, v___x_2990_);
v___x_2992_ = lean_unsigned_to_nat(3u);
v___x_2993_ = lean_nat_div(v___x_2991_, v___x_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_array_get_size(v_buckets_x27_2989_);
v___x_2995_ = lean_nat_dec_le(v___x_2993_, v___x_2994_);
lean_dec(v___x_2993_);
if (v___x_2995_ == 0)
{
lean_object* v_val_2996_; lean_object* v___x_2998_; 
v_val_2996_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_2989_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v_val_2996_);
lean_ctor_set(v___x_2969_, 0, v_size_x27_2987_);
v___x_2998_ = v___x_2969_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_size_x27_2987_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_val_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
else
{
lean_object* v___x_3001_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v_buckets_x27_2989_);
lean_ctor_set(v___x_2969_, 0, v_size_x27_2987_);
v___x_3001_ = v___x_2969_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_size_x27_2987_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_buckets_x27_2989_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
else
{
lean_object* v___x_3003_; lean_object* v_buckets_x27_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
lean_inc(v_bkt_2984_);
v___x_3003_ = lean_box(0);
v_buckets_x27_3004_ = lean_array_uset(v_buckets_2967_, v___x_2983_, v___x_3003_);
v___x_3005_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_2964_, v_b_2965_, v_bkt_2984_);
v___x_3006_ = lean_array_uset(v_buckets_x27_3004_, v___x_2983_, v___x_3005_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v___x_3006_);
v___x_3008_ = v___x_2969_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_size_2966_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(lean_object* v___x_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
if (lean_obj_tag(v_a_3012_) == 0)
{
lean_object* v___x_3014_; 
lean_dec_ref(v___x_3011_);
v___x_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_a_3013_);
return v___x_3014_;
}
else
{
lean_object* v_key_3015_; lean_object* v_tail_3016_; uint8_t v___x_3017_; 
v_key_3015_ = lean_ctor_get(v_a_3012_, 0);
lean_inc(v_key_3015_);
v_tail_3016_ = lean_ctor_get(v_a_3012_, 2);
lean_inc(v_tail_3016_);
lean_dec_ref_known(v_a_3012_, 3);
v___x_3017_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3015_, v___x_3011_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; 
lean_inc_ref(v___x_3011_);
v___x_3018_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3013_, v_key_3015_, v___x_3011_);
v_a_3012_ = v_tail_3016_;
v_a_3013_ = v___x_3018_;
goto _start;
}
else
{
lean_dec(v_key_3015_);
v_a_3012_ = v_tail_3016_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(lean_object* v___x_3021_, lean_object* v_as_3022_, size_t v_sz_3023_, size_t v_i_3024_, lean_object* v_b_3025_){
_start:
{
uint8_t v___x_3026_; 
v___x_3026_ = lean_usize_dec_lt(v_i_3024_, v_sz_3023_);
if (v___x_3026_ == 0)
{
lean_dec_ref(v___x_3021_);
return v_b_3025_;
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3028_; 
v_a_3027_ = lean_array_uget_borrowed(v_as_3022_, v_i_3024_);
lean_inc(v_a_3027_);
lean_inc_ref(v___x_3021_);
v___x_3028_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__6(v___x_3021_, v_a_3027_, v_b_3025_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; 
lean_dec_ref(v___x_3021_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
return v_a_3029_;
}
else
{
lean_object* v_a_3030_; size_t v___x_3031_; size_t v___x_3032_; 
v_a_3030_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3028_, 1);
v___x_3031_ = ((size_t)1ULL);
v___x_3032_ = lean_usize_add(v_i_3024_, v___x_3031_);
v_i_3024_ = v___x_3032_;
v_b_3025_ = v_a_3030_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7___boxed(lean_object* v___x_3034_, lean_object* v_as_3035_, lean_object* v_sz_3036_, lean_object* v_i_3037_, lean_object* v_b_3038_){
_start:
{
size_t v_sz_boxed_3039_; size_t v_i_boxed_3040_; lean_object* v_res_3041_; 
v_sz_boxed_3039_ = lean_unbox_usize(v_sz_3036_);
lean_dec(v_sz_3036_);
v_i_boxed_3040_ = lean_unbox_usize(v_i_3037_);
lean_dec(v_i_3037_);
v_res_3041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3034_, v_as_3035_, v_sz_boxed_3039_, v_i_boxed_3040_, v_b_3038_);
lean_dec_ref(v_as_3035_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
if (lean_obj_tag(v_a_3042_) == 0)
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3044_, 0, v_a_3043_);
return v___x_3044_;
}
else
{
lean_object* v_value_3045_; lean_object* v_key_3046_; lean_object* v_tail_3047_; lean_object* v_buckets_3048_; size_t v_sz_3049_; size_t v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v_value_3045_ = lean_ctor_get(v_a_3042_, 1);
lean_inc(v_value_3045_);
v_key_3046_ = lean_ctor_get(v_a_3042_, 0);
lean_inc(v_key_3046_);
v_tail_3047_ = lean_ctor_get(v_a_3042_, 2);
lean_inc(v_tail_3047_);
lean_dec_ref_known(v_a_3042_, 3);
v_buckets_3048_ = lean_ctor_get(v_value_3045_, 1);
lean_inc_ref(v_buckets_3048_);
lean_dec(v_value_3045_);
v_sz_3049_ = lean_array_size(v_buckets_3048_);
v___x_3050_ = ((size_t)0ULL);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__5(v_buckets_3048_, v_sz_3049_, v___x_3050_, v_key_3046_);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__7(v___x_3051_, v_buckets_3048_, v_sz_3049_, v___x_3050_, v_a_3043_);
lean_dec_ref(v_buckets_3048_);
v_a_3042_ = v_tail_3047_;
v_a_3043_ = v___x_3052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(lean_object* v_as_3054_, size_t v_sz_3055_, size_t v_i_3056_, lean_object* v_b_3057_){
_start:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_usize_dec_lt(v_i_3056_, v_sz_3055_);
if (v___x_3058_ == 0)
{
return v_b_3057_;
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3060_; 
v_a_3059_ = lean_array_uget_borrowed(v_as_3054_, v_i_3056_);
lean_inc(v_a_3059_);
v___x_3060_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__8(v_a_3059_, v_b_3057_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
return v_a_3061_;
}
else
{
lean_object* v_a_3062_; size_t v___x_3063_; size_t v___x_3064_; 
v_a_3062_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3062_);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3063_ = ((size_t)1ULL);
v___x_3064_ = lean_usize_add(v_i_3056_, v___x_3063_);
v_i_3056_ = v___x_3064_;
v_b_3057_ = v_a_3062_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11___boxed(lean_object* v_as_3066_, lean_object* v_sz_3067_, lean_object* v_i_3068_, lean_object* v_b_3069_){
_start:
{
size_t v_sz_boxed_3070_; size_t v_i_boxed_3071_; lean_object* v_res_3072_; 
v_sz_boxed_3070_ = lean_unbox_usize(v_sz_3067_);
lean_dec(v_sz_3067_);
v_i_boxed_3071_ = lean_unbox_usize(v_i_3068_);
lean_dec(v_i_3068_);
v_res_3072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_as_3066_, v_sz_boxed_3070_, v_i_boxed_3071_, v_b_3069_);
lean_dec_ref(v_as_3066_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(lean_object* v_a_3073_, lean_object* v_x_3074_){
_start:
{
if (lean_obj_tag(v_x_3074_) == 0)
{
return v_x_3074_;
}
else
{
lean_object* v_key_3075_; lean_object* v_value_3076_; lean_object* v_tail_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3086_; 
v_key_3075_ = lean_ctor_get(v_x_3074_, 0);
v_value_3076_ = lean_ctor_get(v_x_3074_, 1);
v_tail_3077_ = lean_ctor_get(v_x_3074_, 2);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_x_3074_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3079_ = v_x_3074_;
v_isShared_3080_ = v_isSharedCheck_3086_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_tail_3077_);
lean_inc(v_value_3076_);
lean_inc(v_key_3075_);
lean_dec(v_x_3074_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3086_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
uint8_t v___x_3081_; 
v___x_3081_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3075_, v_a_3073_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3073_, v_tail_3077_);
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 2, v___x_3082_);
v___x_3084_ = v___x_3079_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_key_3075_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_value_3076_);
lean_ctor_set(v_reuseFailAlloc_3085_, 2, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
else
{
lean_del_object(v___x_3079_);
lean_dec(v_value_3076_);
lean_dec(v_key_3075_);
return v_tail_3077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg___boxed(lean_object* v_a_3087_, lean_object* v_x_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3087_, v_x_3088_);
lean_dec_ref(v_a_3087_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(lean_object* v_m_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_size_3092_; lean_object* v_buckets_3093_; lean_object* v___x_3094_; uint64_t v___x_3095_; uint64_t v___x_3096_; uint64_t v___x_3097_; uint64_t v_fold_3098_; uint64_t v___x_3099_; uint64_t v___x_3100_; uint64_t v___x_3101_; size_t v___x_3102_; size_t v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; size_t v___x_3106_; lean_object* v_bkt_3107_; uint8_t v___x_3108_; 
v_size_3092_ = lean_ctor_get(v_m_3090_, 0);
v_buckets_3093_ = lean_ctor_get(v_m_3090_, 1);
v___x_3094_ = lean_array_get_size(v_buckets_3093_);
v___x_3095_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3091_);
v___x_3096_ = 32ULL;
v___x_3097_ = lean_uint64_shift_right(v___x_3095_, v___x_3096_);
v_fold_3098_ = lean_uint64_xor(v___x_3095_, v___x_3097_);
v___x_3099_ = 16ULL;
v___x_3100_ = lean_uint64_shift_right(v_fold_3098_, v___x_3099_);
v___x_3101_ = lean_uint64_xor(v_fold_3098_, v___x_3100_);
v___x_3102_ = lean_uint64_to_usize(v___x_3101_);
v___x_3103_ = lean_usize_of_nat(v___x_3094_);
v___x_3104_ = ((size_t)1ULL);
v___x_3105_ = lean_usize_sub(v___x_3103_, v___x_3104_);
v___x_3106_ = lean_usize_land(v___x_3102_, v___x_3105_);
v_bkt_3107_ = lean_array_uget_borrowed(v_buckets_3093_, v___x_3106_);
v___x_3108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3091_, v_bkt_3107_);
if (v___x_3108_ == 0)
{
return v_m_3090_;
}
else
{
lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3121_; 
lean_inc(v_bkt_3107_);
lean_inc_ref(v_buckets_3093_);
lean_inc(v_size_3092_);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_m_3090_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; lean_object* v_unused_3123_; 
v_unused_3122_ = lean_ctor_get(v_m_3090_, 1);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_m_3090_, 0);
lean_dec(v_unused_3123_);
v___x_3110_ = v_m_3090_;
v_isShared_3111_ = v_isSharedCheck_3121_;
goto v_resetjp_3109_;
}
else
{
lean_dec(v_m_3090_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3121_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v_buckets_x27_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3112_ = lean_box(0);
v_buckets_x27_3113_ = lean_array_uset(v_buckets_3093_, v___x_3106_, v___x_3112_);
v___x_3114_ = lean_unsigned_to_nat(1u);
v___x_3115_ = lean_nat_sub(v_size_3092_, v___x_3114_);
lean_dec(v_size_3092_);
v___x_3116_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3091_, v_bkt_3107_);
v___x_3117_ = lean_array_uset(v_buckets_x27_3113_, v___x_3106_, v___x_3116_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 1, v___x_3117_);
lean_ctor_set(v___x_3110_, 0, v___x_3115_);
v___x_3119_ = v___x_3110_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg___boxed(lean_object* v_m_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3124_, v_a_3125_);
lean_dec_ref(v_a_3125_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(lean_object* v_m_3127_, lean_object* v_a_3128_, lean_object* v_b_3129_){
_start:
{
lean_object* v_size_3130_; lean_object* v_buckets_3131_; lean_object* v___x_3132_; uint64_t v___x_3133_; uint64_t v___x_3134_; uint64_t v___x_3135_; uint64_t v_fold_3136_; uint64_t v___x_3137_; uint64_t v___x_3138_; uint64_t v___x_3139_; size_t v___x_3140_; size_t v___x_3141_; size_t v___x_3142_; size_t v___x_3143_; size_t v___x_3144_; lean_object* v_bkt_3145_; uint8_t v___x_3146_; 
v_size_3130_ = lean_ctor_get(v_m_3127_, 0);
v_buckets_3131_ = lean_ctor_get(v_m_3127_, 1);
v___x_3132_ = lean_array_get_size(v_buckets_3131_);
v___x_3133_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3128_);
v___x_3134_ = 32ULL;
v___x_3135_ = lean_uint64_shift_right(v___x_3133_, v___x_3134_);
v_fold_3136_ = lean_uint64_xor(v___x_3133_, v___x_3135_);
v___x_3137_ = 16ULL;
v___x_3138_ = lean_uint64_shift_right(v_fold_3136_, v___x_3137_);
v___x_3139_ = lean_uint64_xor(v_fold_3136_, v___x_3138_);
v___x_3140_ = lean_uint64_to_usize(v___x_3139_);
v___x_3141_ = lean_usize_of_nat(v___x_3132_);
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_sub(v___x_3141_, v___x_3142_);
v___x_3144_ = lean_usize_land(v___x_3140_, v___x_3143_);
v_bkt_3145_ = lean_array_uget_borrowed(v_buckets_3131_, v___x_3144_);
v___x_3146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0_spec__0___redArg(v_a_3128_, v_bkt_3145_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3167_; 
lean_inc_ref(v_buckets_3131_);
lean_inc(v_size_3130_);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_m_3127_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; lean_object* v_unused_3169_; 
v_unused_3168_ = lean_ctor_get(v_m_3127_, 1);
lean_dec(v_unused_3168_);
v_unused_3169_ = lean_ctor_get(v_m_3127_, 0);
lean_dec(v_unused_3169_);
v___x_3148_ = v_m_3127_;
v_isShared_3149_ = v_isSharedCheck_3167_;
goto v_resetjp_3147_;
}
else
{
lean_dec(v_m_3127_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3167_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v_size_x27_3151_; lean_object* v___x_3152_; lean_object* v_buckets_x27_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3150_ = lean_unsigned_to_nat(1u);
v_size_x27_3151_ = lean_nat_add(v_size_3130_, v___x_3150_);
lean_dec(v_size_3130_);
lean_inc(v_bkt_3145_);
v___x_3152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3152_, 0, v_a_3128_);
lean_ctor_set(v___x_3152_, 1, v_b_3129_);
lean_ctor_set(v___x_3152_, 2, v_bkt_3145_);
v_buckets_x27_3153_ = lean_array_uset(v_buckets_3131_, v___x_3144_, v___x_3152_);
v___x_3154_ = lean_unsigned_to_nat(4u);
v___x_3155_ = lean_nat_mul(v_size_x27_3151_, v___x_3154_);
v___x_3156_ = lean_unsigned_to_nat(3u);
v___x_3157_ = lean_nat_div(v___x_3155_, v___x_3156_);
lean_dec(v___x_3155_);
v___x_3158_ = lean_array_get_size(v_buckets_x27_3153_);
v___x_3159_ = lean_nat_dec_le(v___x_3157_, v___x_3158_);
lean_dec(v___x_3157_);
if (v___x_3159_ == 0)
{
lean_object* v_val_3160_; lean_object* v___x_3162_; 
v_val_3160_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_buckets_x27_3153_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v_val_3160_);
lean_ctor_set(v___x_3148_, 0, v_size_x27_3151_);
v___x_3162_ = v___x_3148_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_size_x27_3151_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_val_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
else
{
lean_object* v___x_3165_; 
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v_buckets_x27_3153_);
lean_ctor_set(v___x_3148_, 0, v_size_x27_3151_);
v___x_3165_ = v___x_3148_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_size_x27_3151_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_buckets_x27_3153_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_dec(v_b_3129_);
lean_dec_ref(v_a_3128_);
return v_m_3127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(lean_object* v_a_3170_, lean_object* v_fallback_3171_, lean_object* v_x_3172_){
_start:
{
if (lean_obj_tag(v_x_3172_) == 0)
{
lean_inc(v_fallback_3171_);
return v_fallback_3171_;
}
else
{
lean_object* v_key_3173_; lean_object* v_value_3174_; lean_object* v_tail_3175_; uint8_t v___x_3176_; 
v_key_3173_ = lean_ctor_get(v_x_3172_, 0);
v_value_3174_ = lean_ctor_get(v_x_3172_, 1);
v_tail_3175_ = lean_ctor_get(v_x_3172_, 2);
v___x_3176_ = l_Lean_Lsp_instBEqRefIdent_beq(v_key_3173_, v_a_3170_);
if (v___x_3176_ == 0)
{
v_x_3172_ = v_tail_3175_;
goto _start;
}
else
{
lean_inc(v_value_3174_);
return v_value_3174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg___boxed(lean_object* v_a_3178_, lean_object* v_fallback_3179_, lean_object* v_x_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3178_, v_fallback_3179_, v_x_3180_);
lean_dec(v_x_3180_);
lean_dec(v_fallback_3179_);
lean_dec_ref(v_a_3178_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(lean_object* v_m_3182_, lean_object* v_a_3183_, lean_object* v_fallback_3184_){
_start:
{
lean_object* v_buckets_3185_; lean_object* v___x_3186_; uint64_t v___x_3187_; uint64_t v___x_3188_; uint64_t v___x_3189_; uint64_t v_fold_3190_; uint64_t v___x_3191_; uint64_t v___x_3192_; uint64_t v___x_3193_; size_t v___x_3194_; size_t v___x_3195_; size_t v___x_3196_; size_t v___x_3197_; size_t v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_buckets_3185_ = lean_ctor_get(v_m_3182_, 1);
v___x_3186_ = lean_array_get_size(v_buckets_3185_);
v___x_3187_ = l_Lean_Lsp_instHashableRefIdent_hash(v_a_3183_);
v___x_3188_ = 32ULL;
v___x_3189_ = lean_uint64_shift_right(v___x_3187_, v___x_3188_);
v_fold_3190_ = lean_uint64_xor(v___x_3187_, v___x_3189_);
v___x_3191_ = 16ULL;
v___x_3192_ = lean_uint64_shift_right(v_fold_3190_, v___x_3191_);
v___x_3193_ = lean_uint64_xor(v_fold_3190_, v___x_3192_);
v___x_3194_ = lean_uint64_to_usize(v___x_3193_);
v___x_3195_ = lean_usize_of_nat(v___x_3186_);
v___x_3196_ = ((size_t)1ULL);
v___x_3197_ = lean_usize_sub(v___x_3195_, v___x_3196_);
v___x_3198_ = lean_usize_land(v___x_3194_, v___x_3197_);
v___x_3199_ = lean_array_uget_borrowed(v_buckets_3185_, v___x_3198_);
v___x_3200_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3183_, v_fallback_3184_, v___x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg___boxed(lean_object* v_m_3201_, lean_object* v_a_3202_, lean_object* v_fallback_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3201_, v_a_3202_, v_fallback_3203_);
lean_dec(v_fallback_3203_);
lean_dec_ref(v_a_3202_);
lean_dec_ref(v_m_3201_);
return v_res_3204_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_box(0);
v___x_3206_ = lean_unsigned_to_nat(16u);
v___x_3207_ = lean_mk_array(v___x_3206_, v___x_3205_);
return v___x_3207_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3208_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__0);
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v___x_3208_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(lean_object* v_idMap_3211_, lean_object* v_classesById_3212_, lean_object* v_id_3213_){
_start:
{
lean_object* v_representative_3214_; lean_object* v___x_3215_; lean_object* v_class_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v_class_3219_; lean_object* v___x_3220_; 
lean_inc_ref(v_id_3213_);
v_representative_3214_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_idMap_3211_, v_id_3213_);
v___x_3215_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_class_3216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_classesById_3212_, v_representative_3214_, v___x_3215_);
v___x_3217_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_classesById_3212_, v_representative_3214_);
v___x_3218_ = lean_box(0);
v_class_3219_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_class_3216_, v_id_3213_, v___x_3218_);
v___x_3220_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v___x_3217_, v_representative_3214_, v_class_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___boxed(lean_object* v_idMap_3221_, lean_object* v_classesById_3222_, lean_object* v_id_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3221_, v_classesById_3222_, v_id_3223_);
lean_dec_ref(v_idMap_3221_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(lean_object* v_idMap_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
if (lean_obj_tag(v_a_3226_) == 0)
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v_a_3227_);
return v___x_3228_;
}
else
{
lean_object* v_key_3229_; lean_object* v_value_3230_; lean_object* v_tail_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_key_3229_ = lean_ctor_get(v_a_3226_, 0);
lean_inc(v_key_3229_);
v_value_3230_ = lean_ctor_get(v_a_3226_, 1);
lean_inc(v_value_3230_);
v_tail_3231_ = lean_ctor_get(v_a_3226_, 2);
lean_inc(v_tail_3231_);
lean_dec_ref_known(v_a_3226_, 3);
v___x_3232_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3225_, v_a_3227_, v_key_3229_);
v___x_3233_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0(v_idMap_3225_, v___x_3232_, v_value_3230_);
v_a_3226_ = v_tail_3231_;
v_a_3227_ = v___x_3233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___boxed(lean_object* v_idMap_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3235_, v_a_3236_, v_a_3237_);
lean_dec_ref(v_idMap_3235_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(lean_object* v_idMap_3239_, lean_object* v_as_3240_, size_t v_sz_3241_, size_t v_i_3242_, lean_object* v_b_3243_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_lt(v_i_3242_, v_sz_3241_);
if (v___x_3244_ == 0)
{
return v_b_3243_;
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3246_; 
v_a_3245_ = lean_array_uget_borrowed(v_as_3240_, v_i_3242_);
lean_inc(v_a_3245_);
v___x_3246_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9(v_idMap_3239_, v_a_3245_, v_b_3243_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
return v_a_3247_;
}
else
{
lean_object* v_a_3248_; size_t v___x_3249_; size_t v___x_3250_; 
v_a_3248_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3246_, 1);
v___x_3249_ = ((size_t)1ULL);
v___x_3250_ = lean_usize_add(v_i_3242_, v___x_3249_);
v_i_3242_ = v___x_3250_;
v_b_3243_ = v_a_3248_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10___boxed(lean_object* v_idMap_3252_, lean_object* v_as_3253_, lean_object* v_sz_3254_, lean_object* v_i_3255_, lean_object* v_b_3256_){
_start:
{
size_t v_sz_boxed_3257_; size_t v_i_boxed_3258_; lean_object* v_res_3259_; 
v_sz_boxed_3257_ = lean_unbox_usize(v_sz_3254_);
lean_dec(v_sz_3254_);
v_i_boxed_3258_ = lean_unbox_usize(v_i_3255_);
lean_dec(v_i_3255_);
v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3252_, v_as_3253_, v_sz_boxed_3257_, v_i_boxed_3258_, v_b_3256_);
lean_dec_ref(v_as_3253_);
lean_dec_ref(v_idMap_3252_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(lean_object* v_idMap_3260_){
_start:
{
lean_object* v_buckets_3261_; lean_object* v_classesById_3262_; size_t v_sz_3263_; size_t v___x_3264_; lean_object* v___x_3265_; lean_object* v_buckets_3266_; size_t v_sz_3267_; lean_object* v___x_3268_; 
v_buckets_3261_ = lean_ctor_get(v_idMap_3260_, 1);
v_classesById_3262_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v_sz_3263_ = lean_array_size(v_buckets_3261_);
v___x_3264_ = ((size_t)0ULL);
v___x_3265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__10(v_idMap_3260_, v_buckets_3261_, v_sz_3263_, v___x_3264_, v_classesById_3262_);
v_buckets_3266_ = lean_ctor_get(v___x_3265_, 1);
lean_inc_ref(v_buckets_3266_);
lean_dec_ref(v___x_3265_);
v_sz_3267_ = lean_array_size(v_buckets_3266_);
v___x_3268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__11(v_buckets_3266_, v_sz_3267_, v___x_3264_, v_classesById_3262_);
lean_dec_ref(v_buckets_3266_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives___boxed(lean_object* v_idMap_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v_idMap_3269_);
lean_dec_ref(v_idMap_3269_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(lean_object* v_00_u03b2_3271_, lean_object* v_m_3272_, lean_object* v_a_3273_, lean_object* v_fallback_3274_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___redArg(v_m_3272_, v_a_3273_, v_fallback_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0___boxed(lean_object* v_00_u03b2_3276_, lean_object* v_m_3277_, lean_object* v_a_3278_, lean_object* v_fallback_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0(v_00_u03b2_3276_, v_m_3277_, v_a_3278_, v_fallback_3279_);
lean_dec(v_fallback_3279_);
lean_dec_ref(v_a_3278_);
lean_dec_ref(v_m_3277_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(lean_object* v_00_u03b2_3281_, lean_object* v_m_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___redArg(v_m_3282_, v_a_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1___boxed(lean_object* v_00_u03b2_3285_, lean_object* v_m_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1(v_00_u03b2_3285_, v_m_3286_, v_a_3287_);
lean_dec_ref(v_a_3287_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2(lean_object* v_00_u03b2_3289_, lean_object* v_m_3290_, lean_object* v_a_3291_, lean_object* v_b_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2___redArg(v_m_3290_, v_a_3291_, v_b_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3(lean_object* v_00_u03b2_3294_, lean_object* v_m_3295_, lean_object* v_a_3296_, lean_object* v_b_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_m_3295_, v_a_3296_, v_b_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(lean_object* v_00_u03b2_3299_, lean_object* v_a_3300_, lean_object* v_fallback_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___redArg(v_a_3300_, v_fallback_3301_, v_x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3304_, lean_object* v_a_3305_, lean_object* v_fallback_3306_, lean_object* v_x_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__0_spec__0(v_00_u03b2_3304_, v_a_3305_, v_fallback_3306_, v_x_3307_);
lean_dec(v_x_3307_);
lean_dec(v_fallback_3306_);
lean_dec_ref(v_a_3305_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(lean_object* v_00_u03b2_3309_, lean_object* v_a_3310_, lean_object* v_x_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___redArg(v_a_3310_, v_x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3313_, lean_object* v_a_3314_, lean_object* v_x_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__1_spec__2(v_00_u03b2_3313_, v_a_3314_, v_x_3315_);
lean_dec_ref(v_a_3314_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4(lean_object* v_00_u03b2_3317_, lean_object* v_data_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4___redArg(v_data_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6(lean_object* v_00_u03b2_3320_, lean_object* v_a_3321_, lean_object* v_b_3322_, lean_object* v_x_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3_spec__6___redArg(v_a_3321_, v_b_3322_, v_x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3325_, lean_object* v_i_3326_, lean_object* v_source_3327_, lean_object* v_target_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5___redArg(v_i_3326_, v_source_3327_, v_target_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15(lean_object* v_00_u03b2_3330_, lean_object* v_x_3331_, lean_object* v_x_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__2_spec__4_spec__5_spec__15___redArg(v_x_3331_, v_x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(lean_object* v_id_3334_, lean_object* v_baseId_3335_, lean_object* v_a_3336_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v___x_3337_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3336_, v_id_3334_);
v___x_3338_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v_a_3336_, v_baseId_3335_);
v___x_3339_ = l_Lean_Lsp_instBEqRefIdent_beq(v___x_3338_, v___x_3337_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__3___redArg(v_a_3336_, v___x_3337_, v___x_3338_);
v___x_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
return v___x_3342_;
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec_ref(v___x_3338_);
lean_dec_ref(v___x_3337_);
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
lean_ctor_set(v___x_3344_, 1, v_a_3336_);
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(lean_object* v_ci_3345_, lean_object* v_info_3346_, lean_object* v_x_3347_, lean_object* v___y_3348_){
_start:
{
if (lean_obj_tag(v_info_3346_) == 11)
{
lean_object* v_toCommandContextInfo_3349_; lean_object* v_i_3350_; lean_object* v_env_3351_; lean_object* v___x_3352_; lean_object* v_mainModule_3353_; lean_object* v_id_3354_; lean_object* v_baseId_3355_; uint8_t v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_toCommandContextInfo_3349_ = lean_ctor_get(v_ci_3345_, 0);
v_i_3350_ = lean_ctor_get(v_info_3346_, 0);
lean_inc_ref(v_i_3350_);
lean_dec_ref_known(v_info_3346_, 1);
v_env_3351_ = lean_ctor_get(v_toCommandContextInfo_3349_, 0);
v___x_3352_ = l_Lean_Environment_header(v_env_3351_);
v_mainModule_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_mainModule_3353_);
lean_dec_ref(v___x_3352_);
v_id_3354_ = lean_ctor_get(v_i_3350_, 1);
lean_inc(v_id_3354_);
v_baseId_3355_ = lean_ctor_get(v_i_3350_, 2);
lean_inc(v_baseId_3355_);
lean_dec_ref(v_i_3350_);
v___x_3356_ = 1;
v___x_3357_ = l_Lean_Name_toString(v_mainModule_3353_, v___x_3356_);
v___x_3358_ = l_Lean_Name_toString(v_id_3354_, v___x_3356_);
lean_inc_ref(v___x_3357_);
v___x_3359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_Name_toString(v_baseId_3355_, v___x_3356_);
v___x_3361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3357_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v___x_3359_, v___x_3361_, v___y_3348_);
return v___x_3362_;
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec_ref(v_info_3346_);
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___y_3348_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1___boxed(lean_object* v_ci_3365_, lean_object* v_info_3366_, lean_object* v_x_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__1(v_ci_3365_, v_info_3366_, v_x_3367_, v___y_3368_);
lean_dec_ref(v_x_3367_);
lean_dec_ref(v_ci_3365_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(lean_object* v_x_3370_, lean_object* v_x_3371_, lean_object* v_x_3372_, lean_object* v___y_3373_){
_start:
{
uint8_t v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = 1;
v___x_3375_ = lean_box(v___x_3374_);
v___x_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
lean_ctor_set(v___x_3376_, 1, v___y_3373_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0___boxed(lean_object* v_x_3377_, lean_object* v_x_3378_, lean_object* v_x_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___lam__0(v_x_3377_, v_x_3378_, v_x_3379_, v___y_3380_);
lean_dec_ref(v_x_3379_);
lean_dec_ref(v_x_3378_);
lean_dec_ref(v_x_3377_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(lean_object* v_postNode_3382_, lean_object* v_ci_3383_, lean_object* v_i_3384_, lean_object* v_cs_3385_, lean_object* v_x_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_apply_4(v_postNode_3382_, v_ci_3383_, v_i_3384_, v_cs_3385_, v___y_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed(lean_object* v_postNode_3389_, lean_object* v_ci_3390_, lean_object* v_i_3391_, lean_object* v_cs_3392_, lean_object* v_x_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0(v_postNode_3389_, v_ci_3390_, v_i_3391_, v_cs_3392_, v_x_3393_, v___y_3394_);
lean_dec(v_x_3393_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___f_3398_; lean_object* v___f_3399_; lean_object* v___f_3400_; lean_object* v___f_3401_; lean_object* v___f_3402_; lean_object* v___f_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___f_3408_; lean_object* v___f_3409_; lean_object* v___f_3410_; lean_object* v___f_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3750__overap_3420_; lean_object* v___x_3421_; 
v___f_3398_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__0));
v___f_3399_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__1));
v___f_3400_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__2));
v___f_3401_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__3));
v___f_3402_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__4));
v___f_3403_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__5));
v___f_3404_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0_spec__1___redArg___closed__6));
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___f_3398_);
lean_ctor_set(v___x_3405_, 1, v___f_3399_);
v___x_3406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v___f_3400_);
lean_ctor_set(v___x_3406_, 2, v___f_3401_);
lean_ctor_set(v___x_3406_, 3, v___f_3402_);
lean_ctor_set(v___x_3406_, 4, v___f_3403_);
v___x_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
lean_ctor_set(v___x_3407_, 1, v___f_3404_);
lean_inc_ref_n(v___x_3407_, 6);
v___f_3408_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3408_, 0, v___x_3407_);
v___f_3409_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3409_, 0, v___x_3407_);
v___f_3410_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3410_, 0, v___x_3407_);
v___f_3411_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3411_, 0, v___x_3407_);
v___x_3412_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3412_, 0, lean_box(0));
lean_closure_set(v___x_3412_, 1, lean_box(0));
lean_closure_set(v___x_3412_, 2, v___x_3407_);
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v___f_3408_);
v___x_3414_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3414_, 0, lean_box(0));
lean_closure_set(v___x_3414_, 1, lean_box(0));
lean_closure_set(v___x_3414_, 2, v___x_3407_);
v___x_3415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
lean_ctor_set(v___x_3415_, 2, v___f_3409_);
lean_ctor_set(v___x_3415_, 3, v___f_3410_);
lean_ctor_set(v___x_3415_, 4, v___f_3411_);
v___x_3416_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3416_, 0, lean_box(0));
lean_closure_set(v___x_3416_, 1, lean_box(0));
lean_closure_set(v___x_3416_, 2, v___x_3407_);
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = lean_box(0);
v___x_3419_ = l_instInhabitedOfMonad___redArg(v___x_3417_, v___x_3418_);
v___x_3750__overap_3420_ = lean_panic_fn_borrowed(v___x_3419_, v_msg_3396_);
lean_dec(v___x_3419_);
v___x_3421_ = lean_apply_1(v___x_3750__overap_3420_, v___y_3397_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(lean_object* v_preNode_3422_, lean_object* v_postNode_3423_, lean_object* v_x_3424_, lean_object* v_x_3425_, lean_object* v___y_3426_){
_start:
{
switch(lean_obj_tag(v_x_3425_))
{
case 0:
{
lean_object* v_i_3427_; lean_object* v_t_3428_; lean_object* v___x_3429_; 
v_i_3427_ = lean_ctor_get(v_x_3425_, 0);
lean_inc_ref(v_i_3427_);
v_t_3428_ = lean_ctor_get(v_x_3425_, 1);
lean_inc_ref(v_t_3428_);
lean_dec_ref_known(v_x_3425_, 2);
v___x_3429_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_3427_, v_x_3424_);
v_x_3424_ = v___x_3429_;
v_x_3425_ = v_t_3428_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_3424_) == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
lean_dec_ref_known(v_x_3425_, 2);
lean_dec_ref(v_postNode_3423_);
lean_dec_ref(v_preNode_3422_);
v___x_3431_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_findReferences_spec__0_spec__0___redArg___closed__3);
v___x_3432_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v___x_3431_, v___y_3426_);
return v___x_3432_;
}
else
{
lean_object* v_i_3433_; lean_object* v_children_3434_; lean_object* v_val_3435_; lean_object* v___x_3436_; lean_object* v_fst_3437_; uint8_t v___x_3438_; 
v_i_3433_ = lean_ctor_get(v_x_3425_, 0);
lean_inc_ref_n(v_i_3433_, 2);
v_children_3434_ = lean_ctor_get(v_x_3425_, 1);
lean_inc_ref_n(v_children_3434_, 2);
lean_dec_ref_known(v_x_3425_, 2);
v_val_3435_ = lean_ctor_get(v_x_3424_, 0);
lean_inc_n(v_val_3435_, 2);
lean_inc_ref(v_preNode_3422_);
v___x_3436_ = lean_apply_4(v_preNode_3422_, v_val_3435_, v_i_3433_, v_children_3434_, v___y_3426_);
v_fst_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_fst_3437_);
v___x_3438_ = lean_unbox(v_fst_3437_);
lean_dec(v_fst_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3457_; 
lean_dec_ref(v_preNode_3422_);
v_isSharedCheck_3457_ = !lean_is_exclusive(v_x_3424_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; 
v_unused_3458_ = lean_ctor_get(v_x_3424_, 0);
lean_dec(v_unused_3458_);
v___x_3440_ = v_x_3424_;
v_isShared_3441_ = v_isSharedCheck_3457_;
goto v_resetjp_3439_;
}
else
{
lean_dec(v_x_3424_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3457_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_snd_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v_fst_3445_; lean_object* v_snd_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3456_; 
v_snd_3442_ = lean_ctor_get(v___x_3436_, 1);
lean_inc(v_snd_3442_);
lean_dec_ref(v___x_3436_);
v___x_3443_ = lean_box(0);
v___x_3444_ = lean_apply_5(v_postNode_3423_, v_val_3435_, v_i_3433_, v_children_3434_, v___x_3443_, v_snd_3442_);
v_fst_3445_ = lean_ctor_get(v___x_3444_, 0);
v_snd_3446_ = lean_ctor_get(v___x_3444_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3448_ = v___x_3444_;
v_isShared_3449_ = v_isSharedCheck_3456_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_snd_3446_);
lean_inc(v_fst_3445_);
lean_dec(v___x_3444_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3456_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v_fst_3445_);
v___x_3451_ = v___x_3440_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_fst_3445_);
v___x_3451_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3451_);
v___x_3453_ = v___x_3448_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_snd_3446_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
else
{
lean_object* v_snd_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v_fst_3464_; lean_object* v_snd_3465_; lean_object* v___x_3466_; lean_object* v_fst_3467_; lean_object* v_snd_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3476_; 
v_snd_3459_ = lean_ctor_get(v___x_3436_, 1);
lean_inc(v_snd_3459_);
lean_dec_ref(v___x_3436_);
v___x_3460_ = l_Lean_Elab_Info_updateContext_x3f(v_x_3424_, v_i_3433_);
v___x_3461_ = l_Lean_PersistentArray_toList___redArg(v_children_3434_);
v___x_3462_ = lean_box(0);
lean_inc_ref(v_postNode_3423_);
v___x_3463_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3422_, v_postNode_3423_, v___x_3460_, v___x_3461_, v___x_3462_, v_snd_3459_);
v_fst_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_fst_3464_);
v_snd_3465_ = lean_ctor_get(v___x_3463_, 1);
lean_inc(v_snd_3465_);
lean_dec_ref(v___x_3463_);
v___x_3466_ = lean_apply_5(v_postNode_3423_, v_val_3435_, v_i_3433_, v_children_3434_, v_fst_3464_, v_snd_3465_);
v_fst_3467_ = lean_ctor_get(v___x_3466_, 0);
v_snd_3468_ = lean_ctor_get(v___x_3466_, 1);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3470_ = v___x_3466_;
v_isShared_3471_ = v_isSharedCheck_3476_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_snd_3468_);
lean_inc(v_fst_3467_);
lean_dec(v___x_3466_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3476_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3474_; 
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v_fst_3467_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3472_);
v___x_3474_ = v___x_3470_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_snd_3468_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
}
default: 
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
lean_dec_ref_known(v_x_3425_, 1);
lean_dec(v_x_3424_);
lean_dec_ref(v_postNode_3423_);
lean_dec_ref(v_preNode_3422_);
v___x_3477_ = lean_box(0);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v___y_3426_);
return v___x_3478_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(lean_object* v_preNode_3479_, lean_object* v_postNode_3480_, lean_object* v___x_3481_, lean_object* v_x_3482_, lean_object* v_x_3483_, lean_object* v___y_3484_){
_start:
{
if (lean_obj_tag(v_x_3482_) == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_dec(v___x_3481_);
lean_dec_ref(v_postNode_3480_);
lean_dec_ref(v_preNode_3479_);
v___x_3485_ = l_List_reverse___redArg(v_x_3483_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v___y_3484_);
return v___x_3486_;
}
else
{
lean_object* v_head_3487_; lean_object* v_tail_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3499_; 
v_head_3487_ = lean_ctor_get(v_x_3482_, 0);
v_tail_3488_ = lean_ctor_get(v_x_3482_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_x_3482_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3490_ = v_x_3482_;
v_isShared_3491_ = v_isSharedCheck_3499_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_tail_3488_);
lean_inc(v_head_3487_);
lean_dec(v_x_3482_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3499_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; lean_object* v_fst_3493_; lean_object* v_snd_3494_; lean_object* v___x_3496_; 
lean_inc(v___x_3481_);
lean_inc_ref(v_postNode_3480_);
lean_inc_ref(v_preNode_3479_);
v___x_3492_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3479_, v_postNode_3480_, v___x_3481_, v_head_3487_, v___y_3484_);
v_fst_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_fst_3493_);
v_snd_3494_ = lean_ctor_get(v___x_3492_, 1);
lean_inc(v_snd_3494_);
lean_dec_ref(v___x_3492_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 1, v_x_3483_);
lean_ctor_set(v___x_3490_, 0, v_fst_3493_);
v___x_3496_ = v___x_3490_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_fst_3493_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_x_3483_);
v___x_3496_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
v_x_3482_ = v_tail_3488_;
v_x_3483_ = v___x_3496_;
v___y_3484_ = v_snd_3494_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(lean_object* v_preNode_3500_, lean_object* v_postNode_3501_, lean_object* v_ctx_x3f_3502_, lean_object* v_t_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___f_3505_; lean_object* v___x_3506_; lean_object* v_snd_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3515_; 
v___f_3505_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3505_, 0, v_postNode_3501_);
v___x_3506_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3500_, v___f_3505_, v_ctx_x3f_3502_, v_t_3503_, v___y_3504_);
v_snd_3507_ = lean_ctor_get(v___x_3506_, 1);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3515_ == 0)
{
lean_object* v_unused_3516_; 
v_unused_3516_ = lean_ctor_get(v___x_3506_, 0);
lean_dec(v_unused_3516_);
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3515_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_snd_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3515_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3511_ = lean_box(0);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3511_);
v___x_3513_ = v___x_3509_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_snd_3507_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(lean_object* v_as_3519_, size_t v_i_3520_, size_t v_stop_3521_, lean_object* v_b_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v___x_3524_; 
v___x_3524_ = lean_usize_dec_eq(v_i_3520_, v_stop_3521_);
if (v___x_3524_ == 0)
{
lean_object* v___f_3525_; lean_object* v___f_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_fst_3530_; lean_object* v_snd_3531_; size_t v___x_3532_; size_t v___x_3533_; 
v___f_3525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__0));
v___f_3526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___closed__1));
v___x_3527_ = lean_array_uget_borrowed(v_as_3519_, v_i_3520_);
v___x_3528_ = lean_box(0);
lean_inc(v___x_3527_);
v___x_3529_ = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0(v___f_3525_, v___f_3526_, v___x_3528_, v___x_3527_, v___y_3523_);
v_fst_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_fst_3530_);
v_snd_3531_ = lean_ctor_get(v___x_3529_, 1);
lean_inc(v_snd_3531_);
lean_dec_ref(v___x_3529_);
v___x_3532_ = ((size_t)1ULL);
v___x_3533_ = lean_usize_add(v_i_3520_, v___x_3532_);
v_i_3520_ = v___x_3533_;
v_b_3522_ = v_fst_3530_;
v___y_3523_ = v_snd_3531_;
goto _start;
}
else
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v_b_3522_);
lean_ctor_set(v___x_3535_, 1, v___y_3523_);
return v___x_3535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3___boxed(lean_object* v_as_3536_, lean_object* v_i_3537_, lean_object* v_stop_3538_, lean_object* v_b_3539_, lean_object* v___y_3540_){
_start:
{
size_t v_i_boxed_3541_; size_t v_stop_boxed_3542_; lean_object* v_res_3543_; 
v_i_boxed_3541_ = lean_unbox_usize(v_i_3537_);
lean_dec(v_i_3537_);
v_stop_boxed_3542_ = lean_unbox_usize(v_stop_3538_);
lean_dec(v_stop_3538_);
v_res_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_as_3536_, v_i_boxed_3541_, v_stop_boxed_3542_, v_b_3539_, v___y_3540_);
lean_dec_ref(v_as_3536_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(lean_object* v_a_3544_, lean_object* v_x_3545_){
_start:
{
if (lean_obj_tag(v_x_3545_) == 0)
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_box(0);
return v___x_3546_;
}
else
{
lean_object* v_key_3547_; lean_object* v_value_3548_; lean_object* v_tail_3549_; uint8_t v___x_3550_; 
v_key_3547_ = lean_ctor_get(v_x_3545_, 0);
v_value_3548_ = lean_ctor_get(v_x_3545_, 1);
v_tail_3549_ = lean_ctor_get(v_x_3545_, 2);
v___x_3550_ = l_Lean_Lsp_instBEqRange_beq(v_key_3547_, v_a_3544_);
if (v___x_3550_ == 0)
{
v_x_3545_ = v_tail_3549_;
goto _start;
}
else
{
lean_object* v___x_3552_; 
lean_inc(v_value_3548_);
v___x_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3552_, 0, v_value_3548_);
return v___x_3552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg___boxed(lean_object* v_a_3553_, lean_object* v_x_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3553_, v_x_3554_);
lean_dec(v_x_3554_);
lean_dec_ref(v_a_3553_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(lean_object* v_m_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v_buckets_3558_; lean_object* v___x_3559_; uint64_t v___x_3560_; uint64_t v___x_3561_; uint64_t v___x_3562_; uint64_t v_fold_3563_; uint64_t v___x_3564_; uint64_t v___x_3565_; uint64_t v___x_3566_; size_t v___x_3567_; size_t v___x_3568_; size_t v___x_3569_; size_t v___x_3570_; size_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_buckets_3558_ = lean_ctor_get(v_m_3556_, 1);
v___x_3559_ = lean_array_get_size(v_buckets_3558_);
v___x_3560_ = l_Lean_Lsp_instHashableRange_hash(v_a_3557_);
v___x_3561_ = 32ULL;
v___x_3562_ = lean_uint64_shift_right(v___x_3560_, v___x_3561_);
v_fold_3563_ = lean_uint64_xor(v___x_3560_, v___x_3562_);
v___x_3564_ = 16ULL;
v___x_3565_ = lean_uint64_shift_right(v_fold_3563_, v___x_3564_);
v___x_3566_ = lean_uint64_xor(v_fold_3563_, v___x_3565_);
v___x_3567_ = lean_uint64_to_usize(v___x_3566_);
v___x_3568_ = lean_usize_of_nat(v___x_3559_);
v___x_3569_ = ((size_t)1ULL);
v___x_3570_ = lean_usize_sub(v___x_3568_, v___x_3569_);
v___x_3571_ = lean_usize_land(v___x_3567_, v___x_3570_);
v___x_3572_ = lean_array_uget_borrowed(v_buckets_3558_, v___x_3571_);
v___x_3573_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3557_, v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg___boxed(lean_object* v_m_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3574_, v_a_3575_);
lean_dec_ref(v_a_3575_);
lean_dec_ref(v_m_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(lean_object* v_posMap_3577_, lean_object* v_as_3578_, size_t v_sz_3579_, size_t v_i_3580_, lean_object* v_b_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_a_3584_; lean_object* v_snd_3585_; uint8_t v___x_3589_; 
v___x_3589_ = lean_usize_dec_lt(v_i_3580_, v_sz_3579_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v_b_3581_);
lean_ctor_set(v___x_3590_, 1, v___y_3582_);
return v___x_3590_;
}
else
{
lean_object* v_a_3591_; lean_object* v_ident_3592_; lean_object* v_range_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_a_3591_ = lean_array_uget_borrowed(v_as_3578_, v_i_3580_);
v_ident_3592_ = lean_ctor_get(v_a_3591_, 0);
v_range_3593_ = lean_ctor_get(v_a_3591_, 2);
v___x_3594_ = lean_box(0);
v___x_3595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_posMap_3577_, v_range_3593_);
if (lean_obj_tag(v___x_3595_) == 1)
{
lean_object* v_val_3596_; lean_object* v___x_3597_; lean_object* v_snd_3598_; 
v_val_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_val_3596_);
lean_dec_ref_known(v___x_3595_, 1);
lean_inc_ref(v_ident_3592_);
v___x_3597_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_insertIdMap(v_val_3596_, v_ident_3592_, v___y_3582_);
v_snd_3598_ = lean_ctor_get(v___x_3597_, 1);
lean_inc(v_snd_3598_);
lean_dec_ref(v___x_3597_);
v_a_3584_ = v___x_3594_;
v_snd_3585_ = v_snd_3598_;
goto v___jp_3583_;
}
else
{
lean_dec(v___x_3595_);
v_a_3584_ = v___x_3594_;
v_snd_3585_ = v___y_3582_;
goto v___jp_3583_;
}
}
v___jp_3583_:
{
size_t v___x_3586_; size_t v___x_3587_; 
v___x_3586_ = ((size_t)1ULL);
v___x_3587_ = lean_usize_add(v_i_3580_, v___x_3586_);
v_i_3580_ = v___x_3587_;
v_b_3581_ = v_a_3584_;
v___y_3582_ = v_snd_3585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2___boxed(lean_object* v_posMap_3599_, lean_object* v_as_3600_, lean_object* v_sz_3601_, lean_object* v_i_3602_, lean_object* v_b_3603_, lean_object* v___y_3604_){
_start:
{
size_t v_sz_boxed_3605_; size_t v_i_boxed_3606_; lean_object* v_res_3607_; 
v_sz_boxed_3605_ = lean_unbox_usize(v_sz_3601_);
lean_dec(v_sz_3601_);
v_i_boxed_3606_ = lean_unbox_usize(v_i_3602_);
lean_dec(v_i_3602_);
v_res_3607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3599_, v_as_3600_, v_sz_boxed_3605_, v_i_boxed_3606_, v_b_3603_, v___y_3604_);
lean_dec_ref(v_as_3600_);
lean_dec_ref(v_posMap_3599_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(lean_object* v_trees_3608_, lean_object* v_refs_3609_, lean_object* v_posMap_3610_){
_start:
{
lean_object* v___x_3611_; size_t v_sz_3612_; size_t v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v_snd_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3611_ = lean_box(0);
v_sz_3612_ = lean_array_size(v_refs_3609_);
v___x_3613_ = ((size_t)0ULL);
v___x_3614_ = lean_unsigned_to_nat(0u);
v___x_3615_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives_spec__9___lam__0___closed__1);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__2(v_posMap_3610_, v_refs_3609_, v_sz_3612_, v___x_3613_, v___x_3611_, v___x_3615_);
v_snd_3617_ = lean_ctor_get(v___x_3616_, 1);
lean_inc(v_snd_3617_);
lean_dec_ref(v___x_3616_);
v___x_3618_ = lean_array_get_size(v_trees_3608_);
v___x_3619_ = lean_nat_dec_lt(v___x_3614_, v___x_3618_);
if (v___x_3619_ == 0)
{
return v_snd_3617_;
}
else
{
uint8_t v___x_3620_; 
v___x_3620_ = lean_nat_dec_le(v___x_3618_, v___x_3618_);
if (v___x_3620_ == 0)
{
if (v___x_3619_ == 0)
{
return v_snd_3617_;
}
else
{
size_t v___x_3621_; lean_object* v___x_3622_; lean_object* v_snd_3623_; 
v___x_3621_ = lean_usize_of_nat(v___x_3618_);
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3608_, v___x_3613_, v___x_3621_, v___x_3611_, v_snd_3617_);
v_snd_3623_ = lean_ctor_get(v___x_3622_, 1);
lean_inc(v_snd_3623_);
lean_dec_ref(v___x_3622_);
return v_snd_3623_;
}
}
else
{
size_t v___x_3624_; lean_object* v___x_3625_; lean_object* v_snd_3626_; 
v___x_3624_ = lean_usize_of_nat(v___x_3618_);
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__3(v_trees_3608_, v___x_3613_, v___x_3624_, v___x_3611_, v_snd_3617_);
v_snd_3626_ = lean_ctor_get(v___x_3625_, 1);
lean_inc(v_snd_3626_);
lean_dec_ref(v___x_3625_);
return v_snd_3626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap___boxed(lean_object* v_trees_3627_, lean_object* v_refs_3628_, lean_object* v_posMap_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3627_, v_refs_3628_, v_posMap_3629_);
lean_dec_ref(v_posMap_3629_);
lean_dec_ref(v_refs_3628_);
lean_dec_ref(v_trees_3627_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(lean_object* v_00_u03b2_3631_, lean_object* v_m_3632_, lean_object* v_a_3633_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___redArg(v_m_3632_, v_a_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1___boxed(lean_object* v_00_u03b2_3635_, lean_object* v_m_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1(v_00_u03b2_3635_, v_m_3636_, v_a_3637_);
lean_dec_ref(v_a_3637_);
lean_dec_ref(v_m_3636_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3639_, lean_object* v_msg_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__1___redArg(v_msg_3640_, v___y_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0(lean_object* v_00_u03b1_3643_, lean_object* v_preNode_3644_, lean_object* v_postNode_3645_, lean_object* v_x_3646_, lean_object* v_x_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0___redArg(v_preNode_3644_, v_postNode_3645_, v_x_3646_, v_x_3647_, v___y_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(lean_object* v_00_u03b2_3650_, lean_object* v_a_3651_, lean_object* v_x_3652_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___redArg(v_a_3651_, v_x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3654_, lean_object* v_a_3655_, lean_object* v_x_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__1_spec__2(v_00_u03b2_3654_, v_a_3655_, v_x_3656_);
lean_dec(v_x_3656_);
lean_dec_ref(v_a_3655_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3658_, lean_object* v_preNode_3659_, lean_object* v_postNode_3660_, lean_object* v___x_3661_, lean_object* v_x_3662_, lean_object* v_x_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap_spec__0_spec__0_spec__2___redArg(v_preNode_3659_, v_postNode_3660_, v___x_3661_, v_x_3662_, v_x_3663_, v___y_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(lean_object* v_a_3666_, lean_object* v_b_3667_, lean_object* v_x_3668_){
_start:
{
if (lean_obj_tag(v_x_3668_) == 0)
{
lean_dec(v_b_3667_);
lean_dec_ref(v_a_3666_);
return v_x_3668_;
}
else
{
lean_object* v_key_3669_; lean_object* v_value_3670_; lean_object* v_tail_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3683_; 
v_key_3669_ = lean_ctor_get(v_x_3668_, 0);
v_value_3670_ = lean_ctor_get(v_x_3668_, 1);
v_tail_3671_ = lean_ctor_get(v_x_3668_, 2);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_x_3668_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3673_ = v_x_3668_;
v_isShared_3674_ = v_isSharedCheck_3683_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_tail_3671_);
lean_inc(v_value_3670_);
lean_inc(v_key_3669_);
lean_dec(v_x_3668_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3683_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
uint8_t v___x_3675_; 
v___x_3675_ = l_Lean_Lsp_instBEqRange_beq(v_key_3669_, v_a_3666_);
if (v___x_3675_ == 0)
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3676_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3666_, v_b_3667_, v_tail_3671_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 2, v___x_3676_);
v___x_3678_ = v___x_3673_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_key_3669_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_value_3670_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
else
{
lean_object* v___x_3681_; 
lean_dec(v_value_3670_);
lean_dec(v_key_3669_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 1, v_b_3667_);
lean_ctor_set(v___x_3673_, 0, v_a_3666_);
v___x_3681_ = v___x_3673_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3666_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_b_3667_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v_tail_3671_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_3684_, lean_object* v_x_3685_){
_start:
{
if (lean_obj_tag(v_x_3685_) == 0)
{
return v_x_3684_;
}
else
{
lean_object* v_key_3686_; lean_object* v_value_3687_; lean_object* v_tail_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3711_; 
v_key_3686_ = lean_ctor_get(v_x_3685_, 0);
v_value_3687_ = lean_ctor_get(v_x_3685_, 1);
v_tail_3688_ = lean_ctor_get(v_x_3685_, 2);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_x_3685_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3690_ = v_x_3685_;
v_isShared_3691_ = v_isSharedCheck_3711_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_tail_3688_);
lean_inc(v_value_3687_);
lean_inc(v_key_3686_);
lean_dec(v_x_3685_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3711_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3692_; uint64_t v___x_3693_; uint64_t v___x_3694_; uint64_t v___x_3695_; uint64_t v_fold_3696_; uint64_t v___x_3697_; uint64_t v___x_3698_; uint64_t v___x_3699_; size_t v___x_3700_; size_t v___x_3701_; size_t v___x_3702_; size_t v___x_3703_; size_t v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
v___x_3692_ = lean_array_get_size(v_x_3684_);
v___x_3693_ = l_Lean_Lsp_instHashableRange_hash(v_key_3686_);
v___x_3694_ = 32ULL;
v___x_3695_ = lean_uint64_shift_right(v___x_3693_, v___x_3694_);
v_fold_3696_ = lean_uint64_xor(v___x_3693_, v___x_3695_);
v___x_3697_ = 16ULL;
v___x_3698_ = lean_uint64_shift_right(v_fold_3696_, v___x_3697_);
v___x_3699_ = lean_uint64_xor(v_fold_3696_, v___x_3698_);
v___x_3700_ = lean_uint64_to_usize(v___x_3699_);
v___x_3701_ = lean_usize_of_nat(v___x_3692_);
v___x_3702_ = ((size_t)1ULL);
v___x_3703_ = lean_usize_sub(v___x_3701_, v___x_3702_);
v___x_3704_ = lean_usize_land(v___x_3700_, v___x_3703_);
v___x_3705_ = lean_array_uget_borrowed(v_x_3684_, v___x_3704_);
lean_inc(v___x_3705_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 2, v___x_3705_);
v___x_3707_ = v___x_3690_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_key_3686_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_value_3687_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_array_uset(v_x_3684_, v___x_3704_, v___x_3707_);
v_x_3684_ = v___x_3708_;
v_x_3685_ = v_tail_3688_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3712_, lean_object* v_source_3713_, lean_object* v_target_3714_){
_start:
{
lean_object* v___x_3715_; uint8_t v___x_3716_; 
v___x_3715_ = lean_array_get_size(v_source_3713_);
v___x_3716_ = lean_nat_dec_lt(v_i_3712_, v___x_3715_);
if (v___x_3716_ == 0)
{
lean_dec_ref(v_source_3713_);
lean_dec(v_i_3712_);
return v_target_3714_;
}
else
{
lean_object* v_es_3717_; lean_object* v___x_3718_; lean_object* v_source_3719_; lean_object* v_target_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_es_3717_ = lean_array_fget(v_source_3713_, v_i_3712_);
v___x_3718_ = lean_box(0);
v_source_3719_ = lean_array_fset(v_source_3713_, v_i_3712_, v___x_3718_);
v_target_3720_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3714_, v_es_3717_);
v___x_3721_ = lean_unsigned_to_nat(1u);
v___x_3722_ = lean_nat_add(v_i_3712_, v___x_3721_);
lean_dec(v_i_3712_);
v_i_3712_ = v___x_3722_;
v_source_3713_ = v_source_3719_;
v_target_3714_ = v_target_3720_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(lean_object* v_data_3724_){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v_nbuckets_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3725_ = lean_array_get_size(v_data_3724_);
v___x_3726_ = lean_unsigned_to_nat(2u);
v_nbuckets_3727_ = lean_nat_mul(v___x_3725_, v___x_3726_);
v___x_3728_ = lean_unsigned_to_nat(0u);
v___x_3729_ = lean_box(0);
v___x_3730_ = lean_mk_array(v_nbuckets_3727_, v___x_3729_);
v___x_3731_ = lean_array_propagate_mark(v_data_3724_, v___x_3730_);
v___x_3732_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v___x_3728_, v_data_3724_, v___x_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(lean_object* v_a_3733_, lean_object* v_x_3734_){
_start:
{
if (lean_obj_tag(v_x_3734_) == 0)
{
uint8_t v___x_3735_; 
v___x_3735_ = 0;
return v___x_3735_;
}
else
{
lean_object* v_key_3736_; lean_object* v_tail_3737_; uint8_t v___x_3738_; 
v_key_3736_ = lean_ctor_get(v_x_3734_, 0);
v_tail_3737_ = lean_ctor_get(v_x_3734_, 2);
v___x_3738_ = l_Lean_Lsp_instBEqRange_beq(v_key_3736_, v_a_3733_);
if (v___x_3738_ == 0)
{
v_x_3734_ = v_tail_3737_;
goto _start;
}
else
{
return v___x_3738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg___boxed(lean_object* v_a_3740_, lean_object* v_x_3741_){
_start:
{
uint8_t v_res_3742_; lean_object* v_r_3743_; 
v_res_3742_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3740_, v_x_3741_);
lean_dec(v_x_3741_);
lean_dec_ref(v_a_3740_);
v_r_3743_ = lean_box(v_res_3742_);
return v_r_3743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(lean_object* v_m_3744_, lean_object* v_a_3745_, lean_object* v_b_3746_){
_start:
{
lean_object* v_size_3747_; lean_object* v_buckets_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3791_; 
v_size_3747_ = lean_ctor_get(v_m_3744_, 0);
v_buckets_3748_ = lean_ctor_get(v_m_3744_, 1);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_m_3744_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3750_ = v_m_3744_;
v_isShared_3751_ = v_isSharedCheck_3791_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_buckets_3748_);
lean_inc(v_size_3747_);
lean_dec(v_m_3744_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3791_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; uint64_t v___x_3753_; uint64_t v___x_3754_; uint64_t v___x_3755_; uint64_t v_fold_3756_; uint64_t v___x_3757_; uint64_t v___x_3758_; uint64_t v___x_3759_; size_t v___x_3760_; size_t v___x_3761_; size_t v___x_3762_; size_t v___x_3763_; size_t v___x_3764_; lean_object* v_bkt_3765_; uint8_t v___x_3766_; 
v___x_3752_ = lean_array_get_size(v_buckets_3748_);
v___x_3753_ = l_Lean_Lsp_instHashableRange_hash(v_a_3745_);
v___x_3754_ = 32ULL;
v___x_3755_ = lean_uint64_shift_right(v___x_3753_, v___x_3754_);
v_fold_3756_ = lean_uint64_xor(v___x_3753_, v___x_3755_);
v___x_3757_ = 16ULL;
v___x_3758_ = lean_uint64_shift_right(v_fold_3756_, v___x_3757_);
v___x_3759_ = lean_uint64_xor(v_fold_3756_, v___x_3758_);
v___x_3760_ = lean_uint64_to_usize(v___x_3759_);
v___x_3761_ = lean_usize_of_nat(v___x_3752_);
v___x_3762_ = ((size_t)1ULL);
v___x_3763_ = lean_usize_sub(v___x_3761_, v___x_3762_);
v___x_3764_ = lean_usize_land(v___x_3760_, v___x_3763_);
v_bkt_3765_ = lean_array_uget_borrowed(v_buckets_3748_, v___x_3764_);
v___x_3766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3745_, v_bkt_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v_size_x27_3768_; lean_object* v___x_3769_; lean_object* v_buckets_x27_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v___x_3767_ = lean_unsigned_to_nat(1u);
v_size_x27_3768_ = lean_nat_add(v_size_3747_, v___x_3767_);
lean_dec(v_size_3747_);
lean_inc(v_bkt_3765_);
v___x_3769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3769_, 0, v_a_3745_);
lean_ctor_set(v___x_3769_, 1, v_b_3746_);
lean_ctor_set(v___x_3769_, 2, v_bkt_3765_);
v_buckets_x27_3770_ = lean_array_uset(v_buckets_3748_, v___x_3764_, v___x_3769_);
v___x_3771_ = lean_unsigned_to_nat(4u);
v___x_3772_ = lean_nat_mul(v_size_x27_3768_, v___x_3771_);
v___x_3773_ = lean_unsigned_to_nat(3u);
v___x_3774_ = lean_nat_div(v___x_3772_, v___x_3773_);
lean_dec(v___x_3772_);
v___x_3775_ = lean_array_get_size(v_buckets_x27_3770_);
v___x_3776_ = lean_nat_dec_le(v___x_3774_, v___x_3775_);
lean_dec(v___x_3774_);
if (v___x_3776_ == 0)
{
lean_object* v_val_3777_; lean_object* v___x_3779_; 
v_val_3777_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_buckets_x27_3770_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v_val_3777_);
lean_ctor_set(v___x_3750_, 0, v_size_x27_3768_);
v___x_3779_ = v___x_3750_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_size_x27_3768_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_val_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
else
{
lean_object* v___x_3782_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v_buckets_x27_3770_);
lean_ctor_set(v___x_3750_, 0, v_size_x27_3768_);
v___x_3782_ = v___x_3750_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_size_x27_3768_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_buckets_x27_3770_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
else
{
lean_object* v___x_3784_; lean_object* v_buckets_x27_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
lean_inc(v_bkt_3765_);
v___x_3784_ = lean_box(0);
v_buckets_x27_3785_ = lean_array_uset(v_buckets_3748_, v___x_3764_, v___x_3784_);
v___x_3786_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3745_, v_b_3746_, v_bkt_3765_);
v___x_3787_ = lean_array_uset(v_buckets_x27_3785_, v___x_3764_, v___x_3786_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v___x_3787_);
v___x_3789_ = v___x_3750_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_size_3747_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(lean_object* v_as_3792_, size_t v_sz_3793_, size_t v_i_3794_, lean_object* v_b_3795_){
_start:
{
lean_object* v_a_3797_; uint8_t v___x_3801_; 
v___x_3801_ = lean_usize_dec_lt(v_i_3794_, v_sz_3793_);
if (v___x_3801_ == 0)
{
return v_b_3795_;
}
else
{
lean_object* v_a_3802_; uint8_t v_isBinder_3803_; 
v_a_3802_ = lean_array_uget_borrowed(v_as_3792_, v_i_3794_);
v_isBinder_3803_ = lean_ctor_get_uint8(v_a_3802_, sizeof(void*)*6);
if (v_isBinder_3803_ == 1)
{
lean_object* v_ident_3804_; lean_object* v_range_3805_; lean_object* v___x_3806_; 
v_ident_3804_ = lean_ctor_get(v_a_3802_, 0);
v_range_3805_ = lean_ctor_get(v_a_3802_, 2);
lean_inc_ref(v_ident_3804_);
lean_inc_ref(v_range_3805_);
v___x_3806_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_b_3795_, v_range_3805_, v_ident_3804_);
v_a_3797_ = v___x_3806_;
goto v___jp_3796_;
}
else
{
v_a_3797_ = v_b_3795_;
goto v___jp_3796_;
}
}
v___jp_3796_:
{
size_t v___x_3798_; size_t v___x_3799_; 
v___x_3798_ = ((size_t)1ULL);
v___x_3799_ = lean_usize_add(v_i_3794_, v___x_3798_);
v_i_3794_ = v___x_3799_;
v_b_3795_ = v_a_3797_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1___boxed(lean_object* v_as_3807_, lean_object* v_sz_3808_, lean_object* v_i_3809_, lean_object* v_b_3810_){
_start:
{
size_t v_sz_boxed_3811_; size_t v_i_boxed_3812_; lean_object* v_res_3813_; 
v_sz_boxed_3811_ = lean_unbox_usize(v_sz_3808_);
lean_dec(v_sz_3808_);
v_i_boxed_3812_ = lean_unbox_usize(v_i_3809_);
lean_dec(v_i_3809_);
v_res_3813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_as_3807_, v_sz_boxed_3811_, v_i_boxed_3812_, v_b_3810_);
lean_dec_ref(v_as_3807_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(lean_object* v___x_3814_, lean_object* v_as_3815_, size_t v_sz_3816_, size_t v_i_3817_, lean_object* v_b_3818_){
_start:
{
lean_object* v_a_3820_; uint8_t v___x_3824_; 
v___x_3824_ = lean_usize_dec_lt(v_i_3817_, v_sz_3816_);
if (v___x_3824_ == 0)
{
return v_b_3818_;
}
else
{
lean_object* v_a_3825_; lean_object* v_ident_3828_; lean_object* v_range_3829_; lean_object* v_stx_3830_; lean_object* v_ci_3831_; lean_object* v_info_3832_; uint8_t v_isBinder_3833_; uint8_t v___x_3834_; 
v_a_3825_ = lean_array_uget(v_as_3815_, v_i_3817_);
v_ident_3828_ = lean_ctor_get(v_a_3825_, 0);
v_range_3829_ = lean_ctor_get(v_a_3825_, 2);
v_stx_3830_ = lean_ctor_get(v_a_3825_, 3);
v_ci_3831_ = lean_ctor_get(v_a_3825_, 4);
v_info_3832_ = lean_ctor_get(v_a_3825_, 5);
v_isBinder_3833_ = lean_ctor_get_uint8(v_a_3825_, sizeof(void*)*6);
v___x_3834_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__0___redArg(v___x_3814_, v_ident_3828_);
if (v___x_3834_ == 0)
{
if (v___x_3834_ == 0)
{
goto v___jp_3826_;
}
else
{
if (v___x_3834_ == 0)
{
lean_dec(v_a_3825_);
v_a_3820_ = v_b_3818_;
goto v___jp_3819_;
}
else
{
goto v___jp_3826_;
}
}
}
else
{
lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3846_; 
lean_inc_ref(v_info_3832_);
lean_inc_ref(v_ci_3831_);
lean_inc(v_stx_3830_);
lean_inc_ref(v_range_3829_);
lean_inc_ref(v_ident_3828_);
v_isSharedCheck_3846_ = !lean_is_exclusive(v_a_3825_);
if (v_isSharedCheck_3846_ == 0)
{
lean_object* v_unused_3847_; lean_object* v_unused_3848_; lean_object* v_unused_3849_; lean_object* v_unused_3850_; lean_object* v_unused_3851_; lean_object* v_unused_3852_; 
v_unused_3847_ = lean_ctor_get(v_a_3825_, 5);
lean_dec(v_unused_3847_);
v_unused_3848_ = lean_ctor_get(v_a_3825_, 4);
lean_dec(v_unused_3848_);
v_unused_3849_ = lean_ctor_get(v_a_3825_, 3);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_a_3825_, 2);
lean_dec(v_unused_3850_);
v_unused_3851_ = lean_ctor_get(v_a_3825_, 1);
lean_dec(v_unused_3851_);
v_unused_3852_ = lean_ctor_get(v_a_3825_, 0);
lean_dec(v_unused_3852_);
v___x_3836_ = v_a_3825_;
v_isShared_3837_ = v_isSharedCheck_3846_;
goto v_resetjp_3835_;
}
else
{
lean_dec(v_a_3825_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3846_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
lean_inc_ref(v_ident_3828_);
v___x_3838_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_References_0__Lean_Server_combineIdents_findCanonicalRepresentative_spec__2___redArg(v___x_3814_, v_ident_3828_);
v___x_3839_ = lean_unsigned_to_nat(1u);
v___x_3840_ = lean_mk_empty_array_with_capacity(v___x_3839_);
v___x_3841_ = lean_array_push(v___x_3840_, v_ident_3828_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 1, v___x_3841_);
lean_ctor_set(v___x_3836_, 0, v___x_3838_);
v___x_3843_ = v___x_3836_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3845_, 2, v_range_3829_);
lean_ctor_set(v_reuseFailAlloc_3845_, 3, v_stx_3830_);
lean_ctor_set(v_reuseFailAlloc_3845_, 4, v_ci_3831_);
lean_ctor_set(v_reuseFailAlloc_3845_, 5, v_info_3832_);
lean_ctor_set_uint8(v_reuseFailAlloc_3845_, sizeof(void*)*6, v_isBinder_3833_);
v___x_3843_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_array_push(v_b_3818_, v___x_3843_);
v_a_3820_ = v___x_3844_;
goto v___jp_3819_;
}
}
}
v___jp_3826_:
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_array_push(v_b_3818_, v_a_3825_);
v_a_3820_ = v___x_3827_;
goto v___jp_3819_;
}
}
v___jp_3819_:
{
size_t v___x_3821_; size_t v___x_3822_; 
v___x_3821_ = ((size_t)1ULL);
v___x_3822_ = lean_usize_add(v_i_3817_, v___x_3821_);
v_i_3817_ = v___x_3822_;
v_b_3818_ = v_a_3820_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2___boxed(lean_object* v___x_3853_, lean_object* v_as_3854_, lean_object* v_sz_3855_, lean_object* v_i_3856_, lean_object* v_b_3857_){
_start:
{
size_t v_sz_boxed_3858_; size_t v_i_boxed_3859_; lean_object* v_res_3860_; 
v_sz_boxed_3858_ = lean_unbox_usize(v_sz_3855_);
lean_dec(v_sz_3855_);
v_i_boxed_3859_ = lean_unbox_usize(v_i_3856_);
lean_dec(v_i_3856_);
v_res_3860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3853_, v_as_3854_, v_sz_boxed_3858_, v_i_boxed_3859_, v_b_3857_);
lean_dec_ref(v_as_3854_);
lean_dec_ref(v___x_3853_);
return v_res_3860_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__0(void){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = lean_box(0);
v___x_3862_ = lean_unsigned_to_nat(16u);
v___x_3863_ = lean_mk_array(v___x_3862_, v___x_3861_);
return v___x_3863_;
}
}
static lean_object* _init_l_Lean_Server_combineIdents___closed__1(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v_posMap_3866_; 
v___x_3864_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__0, &l_Lean_Server_combineIdents___closed__0_once, _init_l_Lean_Server_combineIdents___closed__0);
v___x_3865_ = lean_unsigned_to_nat(0u);
v_posMap_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_posMap_3866_, 0, v___x_3865_);
lean_ctor_set(v_posMap_3866_, 1, v___x_3864_);
return v_posMap_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents(lean_object* v_trees_3867_, lean_object* v_refs_3868_){
_start:
{
lean_object* v_posMap_3869_; size_t v_sz_3870_; size_t v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_posMap_3869_ = lean_obj_once(&l_Lean_Server_combineIdents___closed__1, &l_Lean_Server_combineIdents___closed__1_once, _init_l_Lean_Server_combineIdents___closed__1);
v_sz_3870_ = lean_array_size(v_refs_3868_);
v___x_3871_ = ((size_t)0ULL);
v___x_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__1(v_refs_3868_, v_sz_3870_, v___x_3871_, v_posMap_3869_);
v___x_3873_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_buildIdMap(v_trees_3867_, v_refs_3868_, v___x_3872_);
lean_dec_ref(v___x_3872_);
v___x_3874_ = l___private_Lean_Server_References_0__Lean_Server_combineIdents_useConstRepresentatives(v___x_3873_);
lean_dec_ref(v___x_3873_);
v___x_3875_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_3876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_combineIdents_spec__2(v___x_3874_, v_refs_3868_, v_sz_3870_, v___x_3871_, v___x_3875_);
lean_dec_ref(v___x_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_combineIdents___boxed(lean_object* v_trees_3877_, lean_object* v_refs_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Lean_Server_combineIdents(v_trees_3877_, v_refs_3878_);
lean_dec_ref(v_refs_3878_);
lean_dec_ref(v_trees_3877_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0(lean_object* v_00_u03b2_3880_, lean_object* v_m_3881_, lean_object* v_a_3882_, lean_object* v_b_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0___redArg(v_m_3881_, v_a_3882_, v_b_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(lean_object* v_00_u03b2_3885_, lean_object* v_a_3886_, lean_object* v_x_3887_){
_start:
{
uint8_t v___x_3888_; 
v___x_3888_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___redArg(v_a_3886_, v_x_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3889_, lean_object* v_a_3890_, lean_object* v_x_3891_){
_start:
{
uint8_t v_res_3892_; lean_object* v_r_3893_; 
v_res_3892_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__0(v_00_u03b2_3889_, v_a_3890_, v_x_3891_);
lean_dec(v_x_3891_);
lean_dec_ref(v_a_3890_);
v_r_3893_ = lean_box(v_res_3892_);
return v_r_3893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1(lean_object* v_00_u03b2_3894_, lean_object* v_data_3895_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1___redArg(v_data_3895_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2(lean_object* v_00_u03b2_3897_, lean_object* v_a_3898_, lean_object* v_b_3899_, lean_object* v_x_3900_){
_start:
{
lean_object* v___x_3901_; 
v___x_3901_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__2___redArg(v_a_3898_, v_b_3899_, v_x_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3902_, lean_object* v_i_3903_, lean_object* v_source_3904_, lean_object* v_target_3905_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2___redArg(v_i_3903_, v_source_3904_, v_target_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3907_, lean_object* v_x_3908_, lean_object* v_x_3909_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_combineIdents_spec__0_spec__1_spec__2_spec__5___redArg(v_x_3908_, v_x_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(lean_object* v_hi_3911_, lean_object* v_pivot_3912_, lean_object* v_as_3913_, lean_object* v_i_3914_, lean_object* v_k_3915_){
_start:
{
uint8_t v___x_3920_; 
v___x_3920_ = lean_nat_dec_lt(v_k_3915_, v_hi_3911_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_dec(v_k_3915_);
v___x_3921_ = lean_array_fswap(v_as_3913_, v_i_3914_, v_hi_3911_);
v___x_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3922_, 0, v_i_3914_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
return v___x_3922_;
}
else
{
lean_object* v___x_3923_; lean_object* v_range_3924_; lean_object* v_range_3925_; uint8_t v___x_3926_; 
v___x_3923_ = lean_array_fget_borrowed(v_as_3913_, v_k_3915_);
v_range_3924_ = lean_ctor_get(v___x_3923_, 2);
v_range_3925_ = lean_ctor_get(v_pivot_3912_, 2);
v___x_3926_ = l_Lean_Lsp_instOrdRange_ord(v_range_3924_, v_range_3925_);
if (v___x_3926_ == 0)
{
if (v___x_3920_ == 0)
{
goto v___jp_3916_;
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3927_ = lean_array_fswap(v_as_3913_, v_i_3914_, v_k_3915_);
v___x_3928_ = lean_unsigned_to_nat(1u);
v___x_3929_ = lean_nat_add(v_i_3914_, v___x_3928_);
lean_dec(v_i_3914_);
v___x_3930_ = lean_nat_add(v_k_3915_, v___x_3928_);
lean_dec(v_k_3915_);
v_as_3913_ = v___x_3927_;
v_i_3914_ = v___x_3929_;
v_k_3915_ = v___x_3930_;
goto _start;
}
}
else
{
goto v___jp_3916_;
}
}
v___jp_3916_:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = lean_unsigned_to_nat(1u);
v___x_3918_ = lean_nat_add(v_k_3915_, v___x_3917_);
lean_dec(v_k_3915_);
v_k_3915_ = v___x_3918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg___boxed(lean_object* v_hi_3932_, lean_object* v_pivot_3933_, lean_object* v_as_3934_, lean_object* v_i_3935_, lean_object* v_k_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3932_, v_pivot_3933_, v_as_3934_, v_i_3935_, v_k_3936_);
lean_dec_ref(v_pivot_3933_);
lean_dec(v_hi_3932_);
return v_res_3937_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(uint8_t v___x_3938_, lean_object* v_x1_3939_, lean_object* v_x2_3940_){
_start:
{
lean_object* v_range_3941_; lean_object* v_range_3942_; uint8_t v___x_3943_; 
v_range_3941_ = lean_ctor_get(v_x1_3939_, 2);
v_range_3942_ = lean_ctor_get(v_x2_3940_, 2);
v___x_3943_ = l_Lean_Lsp_instOrdRange_ord(v_range_3941_, v_range_3942_);
if (v___x_3943_ == 0)
{
return v___x_3938_;
}
else
{
uint8_t v___x_3944_; 
v___x_3944_ = 0;
return v___x_3944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0___boxed(lean_object* v___x_3945_, lean_object* v_x1_3946_, lean_object* v_x2_3947_){
_start:
{
uint8_t v___x_2119__boxed_3948_; uint8_t v_res_3949_; lean_object* v_r_3950_; 
v___x_2119__boxed_3948_ = lean_unbox(v___x_3945_);
v_res_3949_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_2119__boxed_3948_, v_x1_3946_, v_x2_3947_);
lean_dec_ref(v_x2_3947_);
lean_dec_ref(v_x1_3946_);
v_r_3950_ = lean_box(v_res_3949_);
return v_r_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(lean_object* v_n_3951_, lean_object* v_as_3952_, lean_object* v_lo_3953_, lean_object* v_hi_3954_){
_start:
{
lean_object* v___y_3956_; uint8_t v___x_3966_; 
v___x_3966_ = lean_nat_dec_lt(v_lo_3953_, v_hi_3954_);
if (v___x_3966_ == 0)
{
lean_dec(v_lo_3953_);
return v_as_3952_;
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v_mid_3969_; lean_object* v___y_3971_; lean_object* v___y_3977_; lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; 
v___x_3967_ = lean_nat_add(v_lo_3953_, v_hi_3954_);
v___x_3968_ = lean_unsigned_to_nat(1u);
v_mid_3969_ = lean_nat_shiftr(v___x_3967_, v___x_3968_);
lean_dec(v___x_3967_);
v___x_3982_ = lean_array_fget_borrowed(v_as_3952_, v_mid_3969_);
v___x_3983_ = lean_array_fget_borrowed(v_as_3952_, v_lo_3953_);
v___x_3984_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3966_, v___x_3982_, v___x_3983_);
if (v___x_3984_ == 0)
{
v___y_3977_ = v_as_3952_;
goto v___jp_3976_;
}
else
{
lean_object* v___x_3985_; 
v___x_3985_ = lean_array_fswap(v_as_3952_, v_lo_3953_, v_mid_3969_);
v___y_3977_ = v___x_3985_;
goto v___jp_3976_;
}
v___jp_3970_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3972_ = lean_array_fget_borrowed(v___y_3971_, v_mid_3969_);
v___x_3973_ = lean_array_fget_borrowed(v___y_3971_, v_hi_3954_);
v___x_3974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3966_, v___x_3972_, v___x_3973_);
if (v___x_3974_ == 0)
{
lean_dec(v_mid_3969_);
v___y_3956_ = v___y_3971_;
goto v___jp_3955_;
}
else
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_array_fswap(v___y_3971_, v_mid_3969_, v_hi_3954_);
lean_dec(v_mid_3969_);
v___y_3956_ = v___x_3975_;
goto v___jp_3955_;
}
}
v___jp_3976_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; 
v___x_3978_ = lean_array_fget_borrowed(v___y_3977_, v_hi_3954_);
v___x_3979_ = lean_array_fget_borrowed(v___y_3977_, v_lo_3953_);
v___x_3980_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___lam__0(v___x_3966_, v___x_3978_, v___x_3979_);
if (v___x_3980_ == 0)
{
v___y_3971_ = v___y_3977_;
goto v___jp_3970_;
}
else
{
lean_object* v___x_3981_; 
v___x_3981_ = lean_array_fswap(v___y_3977_, v_lo_3953_, v_hi_3954_);
v___y_3971_ = v___x_3981_;
goto v___jp_3970_;
}
}
}
v___jp_3955_:
{
lean_object* v_pivot_3957_; lean_object* v___x_3958_; lean_object* v_fst_3959_; lean_object* v_snd_3960_; uint8_t v___x_3961_; 
v_pivot_3957_ = lean_array_fget(v___y_3956_, v_hi_3954_);
lean_inc_n(v_lo_3953_, 2);
v___x_3958_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_3954_, v_pivot_3957_, v___y_3956_, v_lo_3953_, v_lo_3953_);
lean_dec(v_pivot_3957_);
v_fst_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_fst_3959_);
v_snd_3960_ = lean_ctor_get(v___x_3958_, 1);
lean_inc(v_snd_3960_);
lean_dec_ref(v___x_3958_);
v___x_3961_ = lean_nat_dec_le(v_hi_3954_, v_fst_3959_);
if (v___x_3961_ == 0)
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3951_, v_snd_3960_, v_lo_3953_, v_fst_3959_);
v___x_3963_ = lean_unsigned_to_nat(1u);
v___x_3964_ = lean_nat_add(v_fst_3959_, v___x_3963_);
lean_dec(v_fst_3959_);
v_as_3952_ = v___x_3962_;
v_lo_3953_ = v___x_3964_;
goto _start;
}
else
{
lean_dec(v_fst_3959_);
lean_dec(v_lo_3953_);
return v_snd_3960_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg___boxed(lean_object* v_n_3986_, lean_object* v_as_3987_, lean_object* v_lo_3988_, lean_object* v_hi_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_3986_, v_as_3987_, v_lo_3988_, v_hi_3989_);
lean_dec(v_hi_3989_);
lean_dec(v_n_3986_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(lean_object* v_x_3991_, lean_object* v_x_3992_){
_start:
{
if (lean_obj_tag(v_x_3992_) == 0)
{
return v_x_3991_;
}
else
{
lean_object* v_key_3993_; lean_object* v_snd_3994_; lean_object* v_value_3995_; lean_object* v_tail_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4036_; 
v_key_3993_ = lean_ctor_get(v_x_3992_, 0);
lean_inc(v_key_3993_);
v_snd_3994_ = lean_ctor_get(v_key_3993_, 1);
v_value_3995_ = lean_ctor_get(v_x_3992_, 1);
v_tail_3996_ = lean_ctor_get(v_x_3992_, 2);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_x_3992_);
if (v_isSharedCheck_4036_ == 0)
{
lean_object* v_unused_4037_; 
v_unused_4037_ = lean_ctor_get(v_x_3992_, 0);
lean_dec(v_unused_4037_);
v___x_3998_ = v_x_3992_;
v_isShared_3999_ = v_isSharedCheck_4036_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_tail_3996_);
lean_inc(v_value_3995_);
lean_dec(v_x_3992_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4036_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v_fst_4000_; lean_object* v_fst_4001_; lean_object* v_snd_4002_; lean_object* v___x_4003_; uint64_t v___x_4004_; uint64_t v___y_4006_; uint64_t v___y_4028_; 
v_fst_4000_ = lean_ctor_get(v_key_3993_, 0);
v_fst_4001_ = lean_ctor_get(v_snd_3994_, 0);
v_snd_4002_ = lean_ctor_get(v_snd_3994_, 1);
v___x_4003_ = lean_array_get_size(v_x_3991_);
v___x_4004_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4000_);
if (lean_obj_tag(v_fst_4001_) == 0)
{
uint64_t v___x_4031_; 
v___x_4031_ = 11ULL;
v___y_4006_ = v___x_4031_;
goto v___jp_4005_;
}
else
{
lean_object* v_val_4032_; uint8_t v___x_4033_; 
v_val_4032_ = lean_ctor_get(v_fst_4001_, 0);
v___x_4033_ = lean_unbox(v_val_4032_);
if (v___x_4033_ == 0)
{
uint64_t v___x_4034_; 
v___x_4034_ = 13ULL;
v___y_4028_ = v___x_4034_;
goto v___jp_4027_;
}
else
{
uint64_t v___x_4035_; 
v___x_4035_ = 11ULL;
v___y_4028_ = v___x_4035_;
goto v___jp_4027_;
}
}
v___jp_4005_:
{
uint64_t v___x_4007_; uint64_t v___x_4008_; uint64_t v___x_4009_; uint64_t v___x_4010_; uint64_t v___x_4011_; uint64_t v_fold_4012_; uint64_t v___x_4013_; uint64_t v___x_4014_; uint64_t v___x_4015_; size_t v___x_4016_; size_t v___x_4017_; size_t v___x_4018_; size_t v___x_4019_; size_t v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4007_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4002_);
v___x_4008_ = lean_uint64_mix_hash(v___y_4006_, v___x_4007_);
v___x_4009_ = lean_uint64_mix_hash(v___x_4004_, v___x_4008_);
v___x_4010_ = 32ULL;
v___x_4011_ = lean_uint64_shift_right(v___x_4009_, v___x_4010_);
v_fold_4012_ = lean_uint64_xor(v___x_4009_, v___x_4011_);
v___x_4013_ = 16ULL;
v___x_4014_ = lean_uint64_shift_right(v_fold_4012_, v___x_4013_);
v___x_4015_ = lean_uint64_xor(v_fold_4012_, v___x_4014_);
v___x_4016_ = lean_uint64_to_usize(v___x_4015_);
v___x_4017_ = lean_usize_of_nat(v___x_4003_);
v___x_4018_ = ((size_t)1ULL);
v___x_4019_ = lean_usize_sub(v___x_4017_, v___x_4018_);
v___x_4020_ = lean_usize_land(v___x_4016_, v___x_4019_);
v___x_4021_ = lean_array_uget_borrowed(v_x_3991_, v___x_4020_);
lean_inc(v___x_4021_);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 2, v___x_4021_);
v___x_4023_ = v___x_3998_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_key_3993_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v_value_3995_);
lean_ctor_set(v_reuseFailAlloc_4026_, 2, v___x_4021_);
v___x_4023_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_array_uset(v_x_3991_, v___x_4020_, v___x_4023_);
v_x_3991_ = v___x_4024_;
v_x_3992_ = v_tail_3996_;
goto _start;
}
}
v___jp_4027_:
{
uint64_t v___x_4029_; uint64_t v___x_4030_; 
v___x_4029_ = 13ULL;
v___x_4030_ = lean_uint64_mix_hash(v___y_4028_, v___x_4029_);
v___y_4006_ = v___x_4030_;
goto v___jp_4005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(lean_object* v_i_4038_, lean_object* v_source_4039_, lean_object* v_target_4040_){
_start:
{
lean_object* v___x_4041_; uint8_t v___x_4042_; 
v___x_4041_ = lean_array_get_size(v_source_4039_);
v___x_4042_ = lean_nat_dec_lt(v_i_4038_, v___x_4041_);
if (v___x_4042_ == 0)
{
lean_dec_ref(v_source_4039_);
lean_dec(v_i_4038_);
return v_target_4040_;
}
else
{
lean_object* v_es_4043_; lean_object* v___x_4044_; lean_object* v_source_4045_; lean_object* v_target_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v_es_4043_ = lean_array_fget(v_source_4039_, v_i_4038_);
v___x_4044_ = lean_box(0);
v_source_4045_ = lean_array_fset(v_source_4039_, v_i_4038_, v___x_4044_);
v_target_4046_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_target_4040_, v_es_4043_);
v___x_4047_ = lean_unsigned_to_nat(1u);
v___x_4048_ = lean_nat_add(v_i_4038_, v___x_4047_);
lean_dec(v_i_4038_);
v_i_4038_ = v___x_4048_;
v_source_4039_ = v_source_4045_;
v_target_4040_ = v_target_4046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(lean_object* v_data_4050_){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v_nbuckets_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4051_ = lean_array_get_size(v_data_4050_);
v___x_4052_ = lean_unsigned_to_nat(2u);
v_nbuckets_4053_ = lean_nat_mul(v___x_4051_, v___x_4052_);
v___x_4054_ = lean_unsigned_to_nat(0u);
v___x_4055_ = lean_box(0);
v___x_4056_ = lean_mk_array(v_nbuckets_4053_, v___x_4055_);
v___x_4057_ = lean_array_propagate_mark(v_data_4050_, v___x_4056_);
v___x_4058_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v___x_4054_, v_data_4050_, v___x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(lean_object* v_x_4059_, lean_object* v_x_4060_){
_start:
{
if (lean_obj_tag(v_x_4059_) == 0)
{
if (lean_obj_tag(v_x_4060_) == 0)
{
uint8_t v___x_4061_; 
v___x_4061_ = 1;
return v___x_4061_;
}
else
{
uint8_t v___x_4062_; 
v___x_4062_ = 0;
return v___x_4062_;
}
}
else
{
if (lean_obj_tag(v_x_4060_) == 0)
{
uint8_t v___x_4063_; 
v___x_4063_ = 0;
return v___x_4063_;
}
else
{
lean_object* v_val_4064_; uint8_t v___x_4065_; 
v_val_4064_ = lean_ctor_get(v_x_4060_, 0);
v___x_4065_ = lean_unbox(v_val_4064_);
if (v___x_4065_ == 0)
{
lean_object* v_val_4066_; uint8_t v___x_4067_; 
v_val_4066_ = lean_ctor_get(v_x_4059_, 0);
v___x_4067_ = lean_unbox(v_val_4066_);
if (v___x_4067_ == 0)
{
uint8_t v___x_4068_; 
v___x_4068_ = 1;
return v___x_4068_;
}
else
{
uint8_t v___x_4069_; 
v___x_4069_ = lean_unbox(v_val_4064_);
return v___x_4069_;
}
}
else
{
lean_object* v_val_4070_; uint8_t v___x_4071_; 
v_val_4070_ = lean_ctor_get(v_x_4059_, 0);
v___x_4071_ = lean_unbox(v_val_4070_);
return v___x_4071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3___boxed(lean_object* v_x_4072_, lean_object* v_x_4073_){
_start:
{
uint8_t v_res_4074_; lean_object* v_r_4075_; 
v_res_4074_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_x_4072_, v_x_4073_);
lean_dec(v_x_4073_);
lean_dec(v_x_4072_);
v_r_4075_ = lean_box(v_res_4074_);
return v_r_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(lean_object* v_a_4076_, lean_object* v_x_4077_){
_start:
{
if (lean_obj_tag(v_x_4077_) == 0)
{
lean_object* v___x_4078_; 
v___x_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4078_, 0, v_a_4076_);
return v___x_4078_;
}
else
{
lean_object* v_val_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4107_; 
v_val_4079_ = lean_ctor_get(v_x_4077_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v_x_4077_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4081_ = v_x_4077_;
v_isShared_4082_ = v_isSharedCheck_4107_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_val_4079_);
lean_dec(v_x_4077_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4107_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v_ident_4083_; lean_object* v_aliases_4084_; lean_object* v_range_4085_; lean_object* v_stx_4086_; lean_object* v_ci_4087_; lean_object* v_info_4088_; uint8_t v_isBinder_4089_; lean_object* v_aliases_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4101_; 
v_ident_4083_ = lean_ctor_get(v_val_4079_, 0);
lean_inc_ref(v_ident_4083_);
v_aliases_4084_ = lean_ctor_get(v_val_4079_, 1);
lean_inc_ref(v_aliases_4084_);
v_range_4085_ = lean_ctor_get(v_val_4079_, 2);
lean_inc_ref(v_range_4085_);
v_stx_4086_ = lean_ctor_get(v_val_4079_, 3);
lean_inc(v_stx_4086_);
v_ci_4087_ = lean_ctor_get(v_val_4079_, 4);
lean_inc_ref(v_ci_4087_);
v_info_4088_ = lean_ctor_get(v_val_4079_, 5);
lean_inc_ref(v_info_4088_);
v_isBinder_4089_ = lean_ctor_get_uint8(v_val_4079_, sizeof(void*)*6);
lean_dec(v_val_4079_);
v_aliases_4090_ = lean_ctor_get(v_a_4076_, 1);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_a_4076_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; lean_object* v_unused_4103_; lean_object* v_unused_4104_; lean_object* v_unused_4105_; lean_object* v_unused_4106_; 
v_unused_4102_ = lean_ctor_get(v_a_4076_, 5);
lean_dec(v_unused_4102_);
v_unused_4103_ = lean_ctor_get(v_a_4076_, 4);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_a_4076_, 3);
lean_dec(v_unused_4104_);
v_unused_4105_ = lean_ctor_get(v_a_4076_, 2);
lean_dec(v_unused_4105_);
v_unused_4106_ = lean_ctor_get(v_a_4076_, 0);
lean_dec(v_unused_4106_);
v___x_4092_ = v_a_4076_;
v_isShared_4093_ = v_isSharedCheck_4101_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_aliases_4090_);
lean_dec(v_a_4076_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4101_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4094_; lean_object* v___x_4096_; 
v___x_4094_ = l_Array_append___redArg(v_aliases_4084_, v_aliases_4090_);
lean_dec_ref(v_aliases_4090_);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 5, v_info_4088_);
lean_ctor_set(v___x_4092_, 4, v_ci_4087_);
lean_ctor_set(v___x_4092_, 3, v_stx_4086_);
lean_ctor_set(v___x_4092_, 2, v_range_4085_);
lean_ctor_set(v___x_4092_, 1, v___x_4094_);
lean_ctor_set(v___x_4092_, 0, v_ident_4083_);
v___x_4096_ = v___x_4092_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_ident_4083_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v___x_4094_);
lean_ctor_set(v_reuseFailAlloc_4100_, 2, v_range_4085_);
lean_ctor_set(v_reuseFailAlloc_4100_, 3, v_stx_4086_);
lean_ctor_set(v_reuseFailAlloc_4100_, 4, v_ci_4087_);
lean_ctor_set(v_reuseFailAlloc_4100_, 5, v_info_4088_);
v___x_4096_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
lean_object* v___x_4098_; 
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*6, v_isBinder_4089_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 0, v___x_4096_);
v___x_4098_ = v___x_4081_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4096_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_x_4110_){
_start:
{
if (lean_obj_tag(v_x_4110_) == 0)
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v_val_4113_; lean_object* v___x_4114_; 
v___x_4111_ = lean_box(0);
v___x_4112_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4108_, v___x_4111_);
v_val_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_val_4113_);
lean_dec(v___x_4112_);
v___x_4114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4114_, 0, v_a_4109_);
lean_ctor_set(v___x_4114_, 1, v_val_4113_);
lean_ctor_set(v___x_4114_, 2, v_x_4110_);
return v___x_4114_;
}
else
{
lean_object* v_key_4115_; lean_object* v_value_4116_; lean_object* v_tail_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4144_; 
v_key_4115_ = lean_ctor_get(v_x_4110_, 0);
v_value_4116_ = lean_ctor_get(v_x_4110_, 1);
v_tail_4117_ = lean_ctor_get(v_x_4110_, 2);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_x_4110_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4119_ = v_x_4110_;
v_isShared_4120_ = v_isSharedCheck_4144_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_tail_4117_);
lean_inc(v_value_4116_);
lean_inc(v_key_4115_);
lean_dec(v_x_4110_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4144_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
uint8_t v___y_4122_; lean_object* v_fst_4133_; lean_object* v_snd_4134_; lean_object* v_fst_4135_; lean_object* v_snd_4136_; uint8_t v___x_4137_; 
v_fst_4133_ = lean_ctor_get(v_key_4115_, 0);
v_snd_4134_ = lean_ctor_get(v_key_4115_, 1);
v_fst_4135_ = lean_ctor_get(v_a_4109_, 0);
v_snd_4136_ = lean_ctor_get(v_a_4109_, 1);
v___x_4137_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4133_, v_fst_4135_);
if (v___x_4137_ == 0)
{
v___y_4122_ = v___x_4137_;
goto v___jp_4121_;
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
v___y_4122_ = v___x_4142_;
goto v___jp_4121_;
}
else
{
uint8_t v___x_4143_; 
v___x_4143_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4139_, v_snd_4141_);
v___y_4122_ = v___x_4143_;
goto v___jp_4121_;
}
}
v___jp_4121_:
{
if (v___y_4122_ == 0)
{
lean_object* v_tail_4123_; lean_object* v___x_4125_; 
v_tail_4123_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4108_, v_a_4109_, v_tail_4117_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 2, v_tail_4123_);
v___x_4125_ = v___x_4119_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_key_4115_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_value_4116_);
lean_ctor_set(v_reuseFailAlloc_4126_, 2, v_tail_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
else
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v_val_4129_; lean_object* v___x_4131_; 
lean_dec(v_key_4115_);
v___x_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4127_, 0, v_value_4116_);
v___x_4128_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4___lam__0(v_a_4108_, v___x_4127_);
v_val_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_val_4129_);
lean_dec(v___x_4128_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 1, v_val_4129_);
lean_ctor_set(v___x_4119_, 0, v_a_4109_);
v___x_4131_ = v___x_4119_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4109_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_val_4129_);
lean_ctor_set(v_reuseFailAlloc_4132_, 2, v_tail_4117_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(lean_object* v_a_4145_, lean_object* v_x_4146_){
_start:
{
if (lean_obj_tag(v_x_4146_) == 0)
{
uint8_t v___x_4147_; 
v___x_4147_ = 0;
return v___x_4147_;
}
else
{
lean_object* v_key_4148_; lean_object* v_tail_4149_; uint8_t v___y_4151_; lean_object* v_fst_4153_; lean_object* v_snd_4154_; lean_object* v_fst_4155_; lean_object* v_snd_4156_; uint8_t v___x_4157_; 
v_key_4148_ = lean_ctor_get(v_x_4146_, 0);
v_tail_4149_ = lean_ctor_get(v_x_4146_, 2);
v_fst_4153_ = lean_ctor_get(v_key_4148_, 0);
v_snd_4154_ = lean_ctor_get(v_key_4148_, 1);
v_fst_4155_ = lean_ctor_get(v_a_4145_, 0);
v_snd_4156_ = lean_ctor_get(v_a_4145_, 1);
v___x_4157_ = l_Lean_Lsp_instBEqRefIdent_beq(v_fst_4153_, v_fst_4155_);
if (v___x_4157_ == 0)
{
v___y_4151_ = v___x_4157_;
goto v___jp_4150_;
}
else
{
lean_object* v_fst_4158_; lean_object* v_snd_4159_; lean_object* v_fst_4160_; lean_object* v_snd_4161_; uint8_t v___x_4162_; 
v_fst_4158_ = lean_ctor_get(v_snd_4154_, 0);
v_snd_4159_ = lean_ctor_get(v_snd_4154_, 1);
v_fst_4160_ = lean_ctor_get(v_snd_4156_, 0);
v_snd_4161_ = lean_ctor_get(v_snd_4156_, 1);
v___x_4162_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2_spec__3(v_fst_4158_, v_fst_4160_);
if (v___x_4162_ == 0)
{
v___y_4151_ = v___x_4162_;
goto v___jp_4150_;
}
else
{
uint8_t v___x_4163_; 
v___x_4163_ = l_Lean_Lsp_instBEqRange_beq(v_snd_4159_, v_snd_4161_);
v___y_4151_ = v___x_4163_;
goto v___jp_4150_;
}
}
v___jp_4150_:
{
if (v___y_4151_ == 0)
{
v_x_4146_ = v_tail_4149_;
goto _start;
}
else
{
return v___y_4151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg___boxed(lean_object* v_a_4164_, lean_object* v_x_4165_){
_start:
{
uint8_t v_res_4166_; lean_object* v_r_4167_; 
v_res_4166_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4164_, v_x_4165_);
lean_dec(v_x_4165_);
lean_dec_ref(v_a_4164_);
v_r_4167_ = lean_box(v_res_4166_);
return v_r_4167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(lean_object* v_a_4168_, lean_object* v_m_4169_, lean_object* v_a_4170_){
_start:
{
size_t v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v_snd_4178_; lean_object* v_size_4179_; lean_object* v_buckets_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4239_; 
v_snd_4178_ = lean_ctor_get(v_a_4170_, 1);
v_size_4179_ = lean_ctor_get(v_m_4169_, 0);
v_buckets_4180_ = lean_ctor_get(v_m_4169_, 1);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_m_4169_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4182_ = v_m_4169_;
v_isShared_4183_ = v_isSharedCheck_4239_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_buckets_4180_);
lean_inc(v_size_4179_);
lean_dec(v_m_4169_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4239_;
goto v_resetjp_4181_;
}
v___jp_4171_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4176_ = lean_array_uset(v___y_4173_, v___y_4172_, v___y_4174_);
v___x_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___y_4175_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
return v___x_4177_;
}
v_resetjp_4181_:
{
lean_object* v_fst_4184_; lean_object* v_fst_4185_; lean_object* v_snd_4186_; lean_object* v___x_4187_; uint64_t v___x_4188_; uint64_t v___y_4190_; uint64_t v___y_4231_; 
v_fst_4184_ = lean_ctor_get(v_a_4170_, 0);
v_fst_4185_ = lean_ctor_get(v_snd_4178_, 0);
v_snd_4186_ = lean_ctor_get(v_snd_4178_, 1);
v___x_4187_ = lean_array_get_size(v_buckets_4180_);
v___x_4188_ = l_Lean_Lsp_instHashableRefIdent_hash(v_fst_4184_);
if (lean_obj_tag(v_fst_4185_) == 0)
{
uint64_t v___x_4234_; 
v___x_4234_ = 11ULL;
v___y_4190_ = v___x_4234_;
goto v___jp_4189_;
}
else
{
lean_object* v_val_4235_; uint8_t v___x_4236_; 
v_val_4235_ = lean_ctor_get(v_fst_4185_, 0);
v___x_4236_ = lean_unbox(v_val_4235_);
if (v___x_4236_ == 0)
{
uint64_t v___x_4237_; 
v___x_4237_ = 13ULL;
v___y_4231_ = v___x_4237_;
goto v___jp_4230_;
}
else
{
uint64_t v___x_4238_; 
v___x_4238_ = 11ULL;
v___y_4231_ = v___x_4238_;
goto v___jp_4230_;
}
}
v___jp_4189_:
{
uint64_t v___x_4191_; uint64_t v___x_4192_; uint64_t v___x_4193_; uint64_t v___x_4194_; uint64_t v___x_4195_; uint64_t v_fold_4196_; uint64_t v___x_4197_; uint64_t v___x_4198_; uint64_t v___x_4199_; size_t v___x_4200_; size_t v___x_4201_; size_t v___x_4202_; size_t v___x_4203_; size_t v___x_4204_; lean_object* v_bkt_4205_; uint8_t v___x_4206_; 
v___x_4191_ = l_Lean_Lsp_instHashableRange_hash(v_snd_4186_);
v___x_4192_ = lean_uint64_mix_hash(v___y_4190_, v___x_4191_);
v___x_4193_ = lean_uint64_mix_hash(v___x_4188_, v___x_4192_);
v___x_4194_ = 32ULL;
v___x_4195_ = lean_uint64_shift_right(v___x_4193_, v___x_4194_);
v_fold_4196_ = lean_uint64_xor(v___x_4193_, v___x_4195_);
v___x_4197_ = 16ULL;
v___x_4198_ = lean_uint64_shift_right(v_fold_4196_, v___x_4197_);
v___x_4199_ = lean_uint64_xor(v_fold_4196_, v___x_4198_);
v___x_4200_ = lean_uint64_to_usize(v___x_4199_);
v___x_4201_ = lean_usize_of_nat(v___x_4187_);
v___x_4202_ = ((size_t)1ULL);
v___x_4203_ = lean_usize_sub(v___x_4201_, v___x_4202_);
v___x_4204_ = lean_usize_land(v___x_4200_, v___x_4203_);
v_bkt_4205_ = lean_array_uget_borrowed(v_buckets_4180_, v___x_4204_);
v___x_4206_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4170_, v_bkt_4205_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; lean_object* v_size_x27_4208_; lean_object* v___x_4209_; lean_object* v_buckets_x27_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; 
v___x_4207_ = lean_unsigned_to_nat(1u);
v_size_x27_4208_ = lean_nat_add(v_size_4179_, v___x_4207_);
lean_dec(v_size_4179_);
lean_inc(v_bkt_4205_);
v___x_4209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4209_, 0, v_a_4170_);
lean_ctor_set(v___x_4209_, 1, v_a_4168_);
lean_ctor_set(v___x_4209_, 2, v_bkt_4205_);
v_buckets_x27_4210_ = lean_array_uset(v_buckets_4180_, v___x_4204_, v___x_4209_);
v___x_4211_ = lean_unsigned_to_nat(4u);
v___x_4212_ = lean_nat_mul(v_size_x27_4208_, v___x_4211_);
v___x_4213_ = lean_unsigned_to_nat(3u);
v___x_4214_ = lean_nat_div(v___x_4212_, v___x_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_array_get_size(v_buckets_x27_4210_);
v___x_4216_ = lean_nat_dec_le(v___x_4214_, v___x_4215_);
lean_dec(v___x_4214_);
if (v___x_4216_ == 0)
{
lean_object* v_val_4217_; lean_object* v___x_4219_; 
v_val_4217_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_buckets_x27_4210_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 1, v_val_4217_);
lean_ctor_set(v___x_4182_, 0, v_size_x27_4208_);
v___x_4219_ = v___x_4182_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_size_x27_4208_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_val_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
else
{
lean_object* v___x_4222_; 
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 1, v_buckets_x27_4210_);
lean_ctor_set(v___x_4182_, 0, v_size_x27_4208_);
v___x_4222_ = v___x_4182_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_size_x27_4208_);
lean_ctor_set(v_reuseFailAlloc_4223_, 1, v_buckets_x27_4210_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
else
{
lean_object* v___x_4224_; lean_object* v_buckets_x27_4225_; lean_object* v_bkt_x27_4226_; uint8_t v___x_4227_; 
lean_inc(v_bkt_4205_);
lean_del_object(v___x_4182_);
v___x_4224_ = lean_box(0);
v_buckets_x27_4225_ = lean_array_uset(v_buckets_4180_, v___x_4204_, v___x_4224_);
lean_inc_ref(v_a_4170_);
v_bkt_x27_4226_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__4(v_a_4168_, v_a_4170_, v_bkt_4205_);
v___x_4227_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4170_, v_bkt_x27_4226_);
lean_dec_ref(v_a_4170_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = lean_unsigned_to_nat(1u);
v___x_4229_ = lean_nat_sub(v_size_4179_, v___x_4228_);
lean_dec(v_size_4179_);
v___y_4172_ = v___x_4204_;
v___y_4173_ = v_buckets_x27_4225_;
v___y_4174_ = v_bkt_x27_4226_;
v___y_4175_ = v___x_4229_;
goto v___jp_4171_;
}
else
{
v___y_4172_ = v___x_4204_;
v___y_4173_ = v_buckets_x27_4225_;
v___y_4174_ = v_bkt_x27_4226_;
v___y_4175_ = v_size_4179_;
goto v___jp_4171_;
}
}
}
v___jp_4230_:
{
uint64_t v___x_4232_; uint64_t v___x_4233_; 
v___x_4232_ = 13ULL;
v___x_4233_ = lean_uint64_mix_hash(v___y_4231_, v___x_4232_);
v___y_4190_ = v___x_4233_;
goto v___jp_4189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(uint8_t v_allowSimultaneousBinderUse_4240_, lean_object* v_as_4241_, size_t v_sz_4242_, size_t v_i_4243_, lean_object* v_b_4244_){
_start:
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_usize_dec_lt(v_i_4243_, v_sz_4242_);
if (v___x_4245_ == 0)
{
return v_b_4244_;
}
else
{
lean_object* v_a_4246_; lean_object* v___y_4248_; 
v_a_4246_ = lean_array_uget_borrowed(v_as_4241_, v_i_4243_);
if (v_allowSimultaneousBinderUse_4240_ == 0)
{
lean_object* v___x_4257_; 
v___x_4257_ = lean_box(0);
v___y_4248_ = v___x_4257_;
goto v___jp_4247_;
}
else
{
uint8_t v_isBinder_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_isBinder_4258_ = lean_ctor_get_uint8(v_a_4246_, sizeof(void*)*6);
v___x_4259_ = lean_box(v_isBinder_4258_);
v___x_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4259_);
v___y_4248_ = v___x_4260_;
goto v___jp_4247_;
}
v___jp_4247_:
{
lean_object* v_ident_4249_; lean_object* v_range_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; size_t v___x_4254_; size_t v___x_4255_; 
v_ident_4249_ = lean_ctor_get(v_a_4246_, 0);
v_range_4250_ = lean_ctor_get(v_a_4246_, 2);
lean_inc_ref(v_range_4250_);
v___x_4251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___y_4248_);
lean_ctor_set(v___x_4251_, 1, v_range_4250_);
lean_inc_ref(v_ident_4249_);
v___x_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4252_, 0, v_ident_4249_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
lean_inc(v_a_4246_);
v___x_4253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1(v_a_4246_, v_b_4244_, v___x_4252_);
v___x_4254_ = ((size_t)1ULL);
v___x_4255_ = lean_usize_add(v_i_4243_, v___x_4254_);
v_i_4243_ = v___x_4255_;
v_b_4244_ = v___x_4253_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2___boxed(lean_object* v_allowSimultaneousBinderUse_4261_, lean_object* v_as_4262_, lean_object* v_sz_4263_, lean_object* v_i_4264_, lean_object* v_b_4265_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4266_; size_t v_sz_boxed_4267_; size_t v_i_boxed_4268_; lean_object* v_res_4269_; 
v_allowSimultaneousBinderUse_boxed_4266_ = lean_unbox(v_allowSimultaneousBinderUse_4261_);
v_sz_boxed_4267_ = lean_unbox_usize(v_sz_4263_);
lean_dec(v_sz_4263_);
v_i_boxed_4268_ = lean_unbox_usize(v_i_4264_);
lean_dec(v_i_4264_);
v_res_4269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_boxed_4266_, v_as_4262_, v_sz_boxed_4267_, v_i_boxed_4268_, v_b_4265_);
lean_dec_ref(v_as_4262_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(lean_object* v_x_4270_, lean_object* v_x_4271_){
_start:
{
if (lean_obj_tag(v_x_4271_) == 0)
{
return v_x_4270_;
}
else
{
lean_object* v_value_4272_; lean_object* v_tail_4273_; lean_object* v___x_4274_; 
v_value_4272_ = lean_ctor_get(v_x_4271_, 1);
lean_inc(v_value_4272_);
v_tail_4273_ = lean_ctor_get(v_x_4271_, 2);
lean_inc(v_tail_4273_);
lean_dec_ref_known(v_x_4271_, 3);
v___x_4274_ = lean_array_push(v_x_4270_, v_value_4272_);
v_x_4270_ = v___x_4274_;
v_x_4271_ = v_tail_4273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(lean_object* v_as_4276_, size_t v_i_4277_, size_t v_stop_4278_, lean_object* v_b_4279_){
_start:
{
uint8_t v___x_4280_; 
v___x_4280_ = lean_usize_dec_eq(v_i_4277_, v_stop_4278_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4282_; size_t v___x_4283_; size_t v___x_4284_; 
v___x_4281_ = lean_array_uget_borrowed(v_as_4276_, v_i_4277_);
lean_inc(v___x_4281_);
v___x_4282_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_dedupReferences_spec__3(v_b_4279_, v___x_4281_);
v___x_4283_ = ((size_t)1ULL);
v___x_4284_ = lean_usize_add(v_i_4277_, v___x_4283_);
v_i_4277_ = v___x_4284_;
v_b_4279_ = v___x_4282_;
goto _start;
}
else
{
return v_b_4279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4___boxed(lean_object* v_as_4286_, lean_object* v_i_4287_, lean_object* v_stop_4288_, lean_object* v_b_4289_){
_start:
{
size_t v_i_boxed_4290_; size_t v_stop_boxed_4291_; lean_object* v_res_4292_; 
v_i_boxed_4290_ = lean_unbox_usize(v_i_4287_);
lean_dec(v_i_4287_);
v_stop_boxed_4291_ = lean_unbox_usize(v_stop_4288_);
lean_dec(v_stop_4288_);
v_res_4292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_as_4286_, v_i_boxed_4290_, v_stop_boxed_4291_, v_b_4289_);
lean_dec_ref(v_as_4286_);
return v_res_4292_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__0(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4293_ = lean_box(0);
v___x_4294_ = lean_unsigned_to_nat(16u);
v___x_4295_ = lean_mk_array(v___x_4294_, v___x_4293_);
return v___x_4295_;
}
}
static lean_object* _init_l_Lean_Server_dedupReferences___closed__1(void){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v_refsByIdAndRange_4298_; 
v___x_4296_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__0, &l_Lean_Server_dedupReferences___closed__0_once, _init_l_Lean_Server_dedupReferences___closed__0);
v___x_4297_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_refsByIdAndRange_4298_, 0, v___x_4297_);
lean_ctor_set(v_refsByIdAndRange_4298_, 1, v___x_4296_);
return v_refsByIdAndRange_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences(lean_object* v_refs_4299_, uint8_t v_allowSimultaneousBinderUse_4300_){
_start:
{
lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4310_; lean_object* v___x_4317_; lean_object* v_refsByIdAndRange_4318_; size_t v_sz_4319_; size_t v___x_4320_; lean_object* v___x_4321_; lean_object* v_buckets_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4317_ = lean_unsigned_to_nat(0u);
v_refsByIdAndRange_4318_ = lean_obj_once(&l_Lean_Server_dedupReferences___closed__1, &l_Lean_Server_dedupReferences___closed__1_once, _init_l_Lean_Server_dedupReferences___closed__1);
v_sz_4319_ = lean_array_size(v_refs_4299_);
v___x_4320_ = ((size_t)0ULL);
v___x_4321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_dedupReferences_spec__2(v_allowSimultaneousBinderUse_4300_, v_refs_4299_, v_sz_4319_, v___x_4320_, v_refsByIdAndRange_4318_);
v_buckets_4322_ = lean_ctor_get(v___x_4321_, 1);
lean_inc_ref(v_buckets_4322_);
lean_dec_ref(v___x_4321_);
v___x_4323_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4324_ = lean_array_get_size(v_buckets_4322_);
v___x_4325_ = lean_nat_dec_lt(v___x_4317_, v___x_4324_);
if (v___x_4325_ == 0)
{
lean_dec_ref(v_buckets_4322_);
v___y_4310_ = v___x_4323_;
goto v___jp_4309_;
}
else
{
size_t v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = lean_usize_of_nat(v___x_4324_);
v___x_4327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_dedupReferences_spec__4(v_buckets_4322_, v___x_4320_, v___x_4326_, v___x_4323_);
lean_dec_ref(v_buckets_4322_);
v___y_4310_ = v___x_4327_;
goto v___jp_4309_;
}
v___jp_4301_:
{
uint8_t v___x_4306_; 
v___x_4306_ = lean_nat_dec_le(v___y_4305_, v___y_4304_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; 
lean_dec(v___y_4304_);
lean_inc(v___y_4305_);
v___x_4307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4302_, v___y_4303_, v___y_4305_, v___y_4305_);
lean_dec(v___y_4305_);
lean_dec(v___y_4302_);
return v___x_4307_;
}
else
{
lean_object* v___x_4308_; 
v___x_4308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v___y_4302_, v___y_4303_, v___y_4305_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec(v___y_4302_);
return v___x_4308_;
}
}
v___jp_4309_:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4311_ = lean_array_get_size(v___y_4310_);
v___x_4312_ = lean_unsigned_to_nat(0u);
v___x_4313_ = lean_nat_dec_eq(v___x_4311_, v___x_4312_);
if (v___x_4313_ == 0)
{
lean_object* v___x_4314_; lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4314_ = lean_unsigned_to_nat(1u);
v___x_4315_ = lean_nat_sub(v___x_4311_, v___x_4314_);
v___x_4316_ = lean_nat_dec_le(v___x_4312_, v___x_4315_);
if (v___x_4316_ == 0)
{
lean_inc(v___x_4315_);
v___y_4302_ = v___x_4311_;
v___y_4303_ = v___y_4310_;
v___y_4304_ = v___x_4315_;
v___y_4305_ = v___x_4315_;
goto v___jp_4301_;
}
else
{
v___y_4302_ = v___x_4311_;
v___y_4303_ = v___y_4310_;
v___y_4304_ = v___x_4315_;
v___y_4305_ = v___x_4312_;
goto v___jp_4301_;
}
}
else
{
return v___y_4310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_dedupReferences___boxed(lean_object* v_refs_4328_, lean_object* v_allowSimultaneousBinderUse_4329_){
_start:
{
uint8_t v_allowSimultaneousBinderUse_boxed_4330_; lean_object* v_res_4331_; 
v_allowSimultaneousBinderUse_boxed_4330_ = lean_unbox(v_allowSimultaneousBinderUse_4329_);
v_res_4331_ = l_Lean_Server_dedupReferences(v_refs_4328_, v_allowSimultaneousBinderUse_boxed_4330_);
lean_dec_ref(v_refs_4328_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(lean_object* v_n_4332_, lean_object* v_as_4333_, lean_object* v_lo_4334_, lean_object* v_hi_4335_, lean_object* v_w_4336_, lean_object* v_hlo_4337_, lean_object* v_hhi_4338_){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___redArg(v_n_4332_, v_as_4333_, v_lo_4334_, v_hi_4335_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0___boxed(lean_object* v_n_4340_, lean_object* v_as_4341_, lean_object* v_lo_4342_, lean_object* v_hi_4343_, lean_object* v_w_4344_, lean_object* v_hlo_4345_, lean_object* v_hhi_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0(v_n_4340_, v_as_4341_, v_lo_4342_, v_hi_4343_, v_w_4344_, v_hlo_4345_, v_hhi_4346_);
lean_dec(v_hi_4343_);
lean_dec(v_n_4340_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(lean_object* v_n_4348_, lean_object* v_lo_4349_, lean_object* v_hi_4350_, lean_object* v_hhi_4351_, lean_object* v_pivot_4352_, lean_object* v_as_4353_, lean_object* v_i_4354_, lean_object* v_k_4355_, lean_object* v_ilo_4356_, lean_object* v_ik_4357_, lean_object* v_w_4358_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___redArg(v_hi_4350_, v_pivot_4352_, v_as_4353_, v_i_4354_, v_k_4355_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0___boxed(lean_object* v_n_4360_, lean_object* v_lo_4361_, lean_object* v_hi_4362_, lean_object* v_hhi_4363_, lean_object* v_pivot_4364_, lean_object* v_as_4365_, lean_object* v_i_4366_, lean_object* v_k_4367_, lean_object* v_ilo_4368_, lean_object* v_ik_4369_, lean_object* v_w_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_dedupReferences_spec__0_spec__0(v_n_4360_, v_lo_4361_, v_hi_4362_, v_hhi_4363_, v_pivot_4364_, v_as_4365_, v_i_4366_, v_k_4367_, v_ilo_4368_, v_ik_4369_, v_w_4370_);
lean_dec_ref(v_pivot_4364_);
lean_dec(v_hi_4362_);
lean_dec(v_lo_4361_);
lean_dec(v_n_4360_);
return v_res_4371_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(lean_object* v_00_u03b2_4372_, lean_object* v_a_4373_, lean_object* v_x_4374_){
_start:
{
uint8_t v___x_4375_; 
v___x_4375_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___redArg(v_a_4373_, v_x_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4376_, lean_object* v_a_4377_, lean_object* v_x_4378_){
_start:
{
uint8_t v_res_4379_; lean_object* v_r_4380_; 
v_res_4379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__2(v_00_u03b2_4376_, v_a_4377_, v_x_4378_);
lean_dec(v_x_4378_);
lean_dec_ref(v_a_4377_);
v_r_4380_ = lean_box(v_res_4379_);
return v_r_4380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3(lean_object* v_00_u03b2_4381_, lean_object* v_data_4382_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3___redArg(v_data_4382_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4384_, lean_object* v_i_4385_, lean_object* v_source_4386_, lean_object* v_target_4387_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5___redArg(v_i_4385_, v_source_4386_, v_target_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4389_, lean_object* v_x_4390_, lean_object* v_x_4391_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_dedupReferences_spec__1_spec__3_spec__5_spec__9___redArg(v_x_4390_, v_x_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(lean_object* v_as_4393_, size_t v_i_4394_, size_t v_stop_4395_, lean_object* v_b_4396_){
_start:
{
uint8_t v___x_4397_; 
v___x_4397_ = lean_usize_dec_eq(v_i_4394_, v_stop_4395_);
if (v___x_4397_ == 0)
{
lean_object* v___x_4398_; lean_object* v___x_4399_; size_t v___x_4400_; size_t v___x_4401_; 
v___x_4398_ = lean_array_uget_borrowed(v_as_4393_, v_i_4394_);
lean_inc(v___x_4398_);
v___x_4399_ = l_Lean_Server_ModuleRefs_addRef(v_b_4396_, v___x_4398_);
v___x_4400_ = ((size_t)1ULL);
v___x_4401_ = lean_usize_add(v_i_4394_, v___x_4400_);
v_i_4394_ = v___x_4401_;
v_b_4396_ = v___x_4399_;
goto _start;
}
else
{
return v_b_4396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0___boxed(lean_object* v_as_4403_, lean_object* v_i_4404_, lean_object* v_stop_4405_, lean_object* v_b_4406_){
_start:
{
size_t v_i_boxed_4407_; size_t v_stop_boxed_4408_; lean_object* v_res_4409_; 
v_i_boxed_4407_ = lean_unbox_usize(v_i_4404_);
lean_dec(v_i_4404_);
v_stop_boxed_4408_ = lean_unbox_usize(v_stop_4405_);
lean_dec(v_stop_4405_);
v_res_4409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_as_4403_, v_i_boxed_4407_, v_stop_boxed_4408_, v_b_4406_);
lean_dec_ref(v_as_4403_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(lean_object* v_as_4410_, size_t v_i_4411_, size_t v_stop_4412_, lean_object* v_b_4413_){
_start:
{
lean_object* v___y_4415_; uint8_t v___x_4419_; 
v___x_4419_ = lean_usize_dec_eq(v_i_4411_, v_stop_4412_);
if (v___x_4419_ == 0)
{
lean_object* v___x_4420_; lean_object* v_ident_4421_; 
v___x_4420_ = lean_array_uget_borrowed(v_as_4410_, v_i_4411_);
v_ident_4421_ = lean_ctor_get(v___x_4420_, 0);
if (lean_obj_tag(v_ident_4421_) == 1)
{
v___y_4415_ = v_b_4413_;
goto v___jp_4414_;
}
else
{
lean_object* v___x_4422_; 
lean_inc(v___x_4420_);
v___x_4422_ = lean_array_push(v_b_4413_, v___x_4420_);
v___y_4415_ = v___x_4422_;
goto v___jp_4414_;
}
}
else
{
return v_b_4413_;
}
v___jp_4414_:
{
size_t v___x_4416_; size_t v___x_4417_; 
v___x_4416_ = ((size_t)1ULL);
v___x_4417_ = lean_usize_add(v_i_4411_, v___x_4416_);
v_i_4411_ = v___x_4417_;
v_b_4413_ = v___y_4415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1___boxed(lean_object* v_as_4423_, lean_object* v_i_4424_, lean_object* v_stop_4425_, lean_object* v_b_4426_){
_start:
{
size_t v_i_boxed_4427_; size_t v_stop_boxed_4428_; lean_object* v_res_4429_; 
v_i_boxed_4427_ = lean_unbox_usize(v_i_4424_);
lean_dec(v_i_4424_);
v_stop_boxed_4428_ = lean_unbox_usize(v_stop_4425_);
lean_dec(v_stop_4425_);
v_res_4429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_as_4423_, v_i_boxed_4427_, v_stop_boxed_4428_, v_b_4426_);
lean_dec_ref(v_as_4423_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs(lean_object* v_text_4430_, lean_object* v_trees_4431_, uint8_t v_localVars_4432_, uint8_t v_allowSimultaneousBinderUse_4433_){
_start:
{
lean_object* v_refs_4435_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v_refs_4449_; 
v___x_4447_ = l_Lean_Server_findReferences(v_text_4430_, v_trees_4431_);
v___x_4448_ = l_Lean_Server_combineIdents(v_trees_4431_, v___x_4447_);
lean_dec_ref(v___x_4447_);
v_refs_4449_ = l_Lean_Server_dedupReferences(v___x_4448_, v_allowSimultaneousBinderUse_4433_);
lean_dec_ref(v___x_4448_);
if (v_localVars_4432_ == 0)
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; uint8_t v___x_4453_; 
v___x_4450_ = lean_unsigned_to_nat(0u);
v___x_4451_ = lean_array_get_size(v_refs_4449_);
v___x_4452_ = ((lean_object*)(l_Lean_Server_RefInfo_empty___closed__0));
v___x_4453_ = lean_nat_dec_lt(v___x_4450_, v___x_4451_);
if (v___x_4453_ == 0)
{
lean_dec_ref(v_refs_4449_);
v_refs_4435_ = v___x_4452_;
goto v___jp_4434_;
}
else
{
uint8_t v___x_4454_; 
v___x_4454_ = lean_nat_dec_le(v___x_4451_, v___x_4451_);
if (v___x_4454_ == 0)
{
if (v___x_4453_ == 0)
{
lean_dec_ref(v_refs_4449_);
v_refs_4435_ = v___x_4452_;
goto v___jp_4434_;
}
else
{
size_t v___x_4455_; size_t v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = ((size_t)0ULL);
v___x_4456_ = lean_usize_of_nat(v___x_4451_);
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4449_, v___x_4455_, v___x_4456_, v___x_4452_);
lean_dec_ref(v_refs_4449_);
v_refs_4435_ = v___x_4457_;
goto v___jp_4434_;
}
}
else
{
size_t v___x_4458_; size_t v___x_4459_; lean_object* v___x_4460_; 
v___x_4458_ = ((size_t)0ULL);
v___x_4459_ = lean_usize_of_nat(v___x_4451_);
v___x_4460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__1(v_refs_4449_, v___x_4458_, v___x_4459_, v___x_4452_);
lean_dec_ref(v_refs_4449_);
v_refs_4435_ = v___x_4460_;
goto v___jp_4434_;
}
}
}
else
{
v_refs_4435_ = v_refs_4449_;
goto v___jp_4434_;
}
v___jp_4434_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4436_ = lean_box(1);
v___x_4437_ = lean_unsigned_to_nat(0u);
v___x_4438_ = lean_array_get_size(v_refs_4435_);
v___x_4439_ = lean_nat_dec_lt(v___x_4437_, v___x_4438_);
if (v___x_4439_ == 0)
{
lean_dec_ref(v_refs_4435_);
return v___x_4436_;
}
else
{
uint8_t v___x_4440_; 
v___x_4440_ = lean_nat_dec_le(v___x_4438_, v___x_4438_);
if (v___x_4440_ == 0)
{
if (v___x_4439_ == 0)
{
lean_dec_ref(v_refs_4435_);
return v___x_4436_;
}
else
{
size_t v___x_4441_; size_t v___x_4442_; lean_object* v___x_4443_; 
v___x_4441_ = ((size_t)0ULL);
v___x_4442_ = lean_usize_of_nat(v___x_4438_);
v___x_4443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4435_, v___x_4441_, v___x_4442_, v___x_4436_);
lean_dec_ref(v_refs_4435_);
return v___x_4443_;
}
}
else
{
size_t v___x_4444_; size_t v___x_4445_; lean_object* v___x_4446_; 
v___x_4444_ = ((size_t)0ULL);
v___x_4445_ = lean_usize_of_nat(v___x_4438_);
v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_findModuleRefs_spec__0(v_refs_4435_, v___x_4444_, v___x_4445_, v___x_4436_);
lean_dec_ref(v_refs_4435_);
return v___x_4446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_findModuleRefs___boxed(lean_object* v_text_4461_, lean_object* v_trees_4462_, lean_object* v_localVars_4463_, lean_object* v_allowSimultaneousBinderUse_4464_){
_start:
{
uint8_t v_localVars_boxed_4465_; uint8_t v_allowSimultaneousBinderUse_boxed_4466_; lean_object* v_res_4467_; 
v_localVars_boxed_4465_ = lean_unbox(v_localVars_4463_);
v_allowSimultaneousBinderUse_boxed_4466_ = lean_unbox(v_allowSimultaneousBinderUse_4464_);
v_res_4467_ = l_Lean_Server_findModuleRefs(v_text_4461_, v_trees_4462_, v_localVars_boxed_4465_, v_allowSimultaneousBinderUse_boxed_4466_);
lean_dec_ref(v_trees_4462_);
return v_res_4467_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(uint8_t v_a_4475_, uint8_t v_a_4476_){
_start:
{
switch(v_a_4475_)
{
case 0:
{
if (v_a_4476_ == 1)
{
uint8_t v___x_4477_; 
v___x_4477_ = 2;
return v___x_4477_;
}
else
{
return v_a_4476_;
}
}
case 1:
{
if (v_a_4476_ == 0)
{
uint8_t v___x_4478_; 
v___x_4478_ = 2;
return v___x_4478_;
}
else
{
return v_a_4476_;
}
}
default: 
{
return v_a_4475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds___boxed(lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
uint8_t v_a_46__boxed_4481_; uint8_t v_a_47__boxed_4482_; uint8_t v_res_4483_; lean_object* v_r_4484_; 
v_a_46__boxed_4481_ = lean_unbox(v_a_4479_);
v_a_47__boxed_4482_ = lean_unbox(v_a_4480_);
v_res_4483_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_a_46__boxed_4481_, v_a_47__boxed_4482_);
v_r_4484_ = lean_box(v_res_4483_);
return v_r_4484_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(lean_object* v_upperBound_4485_, lean_object* v_identicalImports_4486_, lean_object* v_a_4487_, lean_object* v_b_4488_){
_start:
{
uint8_t v___x_4489_; 
v___x_4489_ = lean_nat_dec_lt(v_a_4487_, v_upperBound_4485_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; 
lean_dec(v_a_4487_);
v___x_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4490_, 0, v_b_4488_);
return v___x_4490_;
}
else
{
lean_object* v_module_4491_; lean_object* v_uri_4492_; uint8_t v_isAll_4493_; uint8_t v_isPrivate_4494_; uint8_t v_metaKind_4495_; lean_object* v___x_4496_; lean_object* v_module_4497_; lean_object* v_uri_4498_; uint8_t v_isAll_4499_; uint8_t v_isPrivate_4500_; uint8_t v_metaKind_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4521_; 
v_module_4491_ = lean_ctor_get(v_b_4488_, 0);
lean_inc(v_module_4491_);
v_uri_4492_ = lean_ctor_get(v_b_4488_, 1);
lean_inc_ref(v_uri_4492_);
v_isAll_4493_ = lean_ctor_get_uint8(v_b_4488_, sizeof(void*)*2);
v_isPrivate_4494_ = lean_ctor_get_uint8(v_b_4488_, sizeof(void*)*2 + 1);
v_metaKind_4495_ = lean_ctor_get_uint8(v_b_4488_, sizeof(void*)*2 + 2);
lean_dec_ref(v_b_4488_);
v___x_4496_ = lean_array_fget(v_identicalImports_4486_, v_a_4487_);
v_module_4497_ = lean_ctor_get(v___x_4496_, 0);
v_uri_4498_ = lean_ctor_get(v___x_4496_, 1);
v_isAll_4499_ = lean_ctor_get_uint8(v___x_4496_, sizeof(void*)*2);
v_isPrivate_4500_ = lean_ctor_get_uint8(v___x_4496_, sizeof(void*)*2 + 1);
v_metaKind_4501_ = lean_ctor_get_uint8(v___x_4496_, sizeof(void*)*2 + 2);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4503_ = v___x_4496_;
v_isShared_4504_ = v_isSharedCheck_4521_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_uri_4498_);
lean_inc(v_module_4497_);
lean_dec(v___x_4496_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4521_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
uint8_t v___y_4506_; uint8_t v___y_4507_; uint8_t v___y_4516_; uint8_t v___x_4517_; 
v___x_4517_ = lean_name_eq(v_module_4491_, v_module_4497_);
lean_dec(v_module_4497_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; 
lean_del_object(v___x_4503_);
lean_dec_ref(v_uri_4498_);
lean_dec_ref(v_uri_4492_);
lean_dec(v_module_4491_);
lean_dec(v_a_4487_);
v___x_4518_ = lean_box(0);
return v___x_4518_;
}
else
{
uint8_t v___x_4519_; 
v___x_4519_ = lean_string_dec_eq(v_uri_4492_, v_uri_4498_);
lean_dec_ref(v_uri_4498_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; 
lean_del_object(v___x_4503_);
lean_dec_ref(v_uri_4492_);
lean_dec(v_module_4491_);
lean_dec(v_a_4487_);
v___x_4520_ = lean_box(0);
return v___x_4520_;
}
else
{
if (v_isAll_4493_ == 0)
{
v___y_4516_ = v_isAll_4499_;
goto v___jp_4515_;
}
else
{
v___y_4516_ = v___x_4489_;
goto v___jp_4515_;
}
}
}
v___jp_4505_:
{
uint8_t v___x_4508_; lean_object* v___x_4510_; 
v___x_4508_ = l___private_Lean_Server_References_0__Lean_Server_ModuleImport_collapseIdenticalImports_x3f_collapseMetaKinds(v_metaKind_4495_, v_metaKind_4501_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 1, v_uri_4492_);
lean_ctor_set(v___x_4503_, 0, v_module_4491_);
v___x_4510_ = v___x_4503_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_module_4491_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_uri_4492_);
v___x_4510_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
lean_ctor_set_uint8(v___x_4510_, sizeof(void*)*2, v___y_4506_);
lean_ctor_set_uint8(v___x_4510_, sizeof(void*)*2 + 1, v___y_4507_);
lean_ctor_set_uint8(v___x_4510_, sizeof(void*)*2 + 2, v___x_4508_);
v___x_4511_ = lean_unsigned_to_nat(1u);
v___x_4512_ = lean_nat_add(v_a_4487_, v___x_4511_);
lean_dec(v_a_4487_);
v_a_4487_ = v___x_4512_;
v_b_4488_ = v___x_4510_;
goto _start;
}
}
v___jp_4515_:
{
if (v_isPrivate_4494_ == 0)
{
v___y_4506_ = v___y_4516_;
v___y_4507_ = v_isPrivate_4494_;
goto v___jp_4505_;
}
else
{
v___y_4506_ = v___y_4516_;
v___y_4507_ = v_isPrivate_4500_;
goto v___jp_4505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg___boxed(lean_object* v_upperBound_4522_, lean_object* v_identicalImports_4523_, lean_object* v_a_4524_, lean_object* v_b_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4522_, v_identicalImports_4523_, v_a_4524_, v_b_4525_);
lean_dec_ref(v_identicalImports_4523_);
lean_dec(v_upperBound_4522_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(lean_object* v_identicalImports_4527_){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4528_ = lean_unsigned_to_nat(0u);
v___x_4529_ = lean_array_get_size(v_identicalImports_4527_);
v___x_4530_ = lean_nat_dec_lt(v___x_4528_, v___x_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; 
v___x_4531_ = lean_box(0);
return v___x_4531_;
}
else
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = lean_unsigned_to_nat(1u);
v___x_4533_ = lean_array_fget_borrowed(v_identicalImports_4527_, v___x_4528_);
lean_inc(v___x_4533_);
v___x_4534_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v___x_4529_, v_identicalImports_4527_, v___x_4532_, v___x_4533_);
return v___x_4534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f___boxed(lean_object* v_identicalImports_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_identicalImports_4535_);
lean_dec_ref(v_identicalImports_4535_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(lean_object* v_upperBound_4537_, lean_object* v_identicalImports_4538_, lean_object* v_inst_4539_, lean_object* v_R_4540_, lean_object* v_a_4541_, lean_object* v_b_4542_, lean_object* v_c_4543_){
_start:
{
lean_object* v___x_4544_; 
v___x_4544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___redArg(v_upperBound_4537_, v_identicalImports_4538_, v_a_4541_, v_b_4542_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0___boxed(lean_object* v_upperBound_4545_, lean_object* v_identicalImports_4546_, lean_object* v_inst_4547_, lean_object* v_R_4548_, lean_object* v_a_4549_, lean_object* v_b_4550_, lean_object* v_c_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_ModuleImport_collapseIdenticalImports_x3f_spec__0(v_upperBound_4545_, v_identicalImports_4546_, v_inst_4547_, v_R_4548_, v_a_4549_, v_b_4550_, v_c_4551_);
lean_dec_ref(v_identicalImports_4546_);
lean_dec(v_upperBound_4545_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0(lean_object* v_x_4559_){
_start:
{
lean_object* v_module_4560_; 
v_module_4560_ = lean_ctor_get(v_x_4559_, 0);
lean_inc(v_module_4560_);
return v_module_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___lam__0___boxed(lean_object* v_x_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_Lean_Server_DirectImports_convertImportInfos___lam__0(v_x_4561_);
lean_dec_ref(v_x_4561_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(lean_object* v_x_4563_, lean_object* v_x_4564_){
_start:
{
if (lean_obj_tag(v_x_4564_) == 0)
{
return v_x_4563_;
}
else
{
lean_object* v_key_4565_; lean_object* v_value_4566_; lean_object* v_tail_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_key_4565_ = lean_ctor_get(v_x_4564_, 0);
v_value_4566_ = lean_ctor_get(v_x_4564_, 1);
v_tail_4567_ = lean_ctor_get(v_x_4564_, 2);
lean_inc(v_value_4566_);
lean_inc(v_key_4565_);
v___x_4568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4568_, 0, v_key_4565_);
lean_ctor_set(v___x_4568_, 1, v_value_4566_);
v___x_4569_ = lean_array_push(v_x_4563_, v___x_4568_);
v_x_4563_ = v___x_4569_;
v_x_4564_ = v_tail_4567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4___boxed(lean_object* v_x_4571_, lean_object* v_x_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_x_4571_, v_x_4572_);
lean_dec(v_x_4572_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(lean_object* v_as_4574_, size_t v_i_4575_, size_t v_stop_4576_, lean_object* v_b_4577_){
_start:
{
uint8_t v___x_4578_; 
v___x_4578_ = lean_usize_dec_eq(v_i_4575_, v_stop_4576_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; lean_object* v___x_4580_; size_t v___x_4581_; size_t v___x_4582_; 
v___x_4579_ = lean_array_uget_borrowed(v_as_4574_, v_i_4575_);
v___x_4580_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Server_DirectImports_convertImportInfos_spec__4(v_b_4577_, v___x_4579_);
v___x_4581_ = ((size_t)1ULL);
v___x_4582_ = lean_usize_add(v_i_4575_, v___x_4581_);
v_i_4575_ = v___x_4582_;
v_b_4577_ = v___x_4580_;
goto _start;
}
else
{
return v_b_4577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5___boxed(lean_object* v_as_4584_, lean_object* v_i_4585_, lean_object* v_stop_4586_, lean_object* v_b_4587_){
_start:
{
size_t v_i_boxed_4588_; size_t v_stop_boxed_4589_; lean_object* v_res_4590_; 
v_i_boxed_4588_ = lean_unbox_usize(v_i_4585_);
lean_dec(v_i_4585_);
v_stop_boxed_4589_ = lean_unbox_usize(v_stop_4586_);
lean_dec(v_stop_4586_);
v_res_4590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_as_4584_, v_i_boxed_4588_, v_stop_boxed_4589_, v_b_4587_);
lean_dec_ref(v_as_4584_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(lean_object* v_as_4591_, size_t v_i_4592_, size_t v_stop_4593_, lean_object* v_b_4594_){
_start:
{
uint8_t v___x_4596_; 
v___x_4596_ = lean_usize_dec_eq(v_i_4592_, v_stop_4593_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; lean_object* v_module_4598_; uint8_t v_isPrivate_4599_; uint8_t v_isAll_4600_; uint8_t v_isMeta_4601_; lean_object* v_module_4602_; lean_object* v___x_4603_; 
v___x_4597_ = lean_array_uget_borrowed(v_as_4591_, v_i_4592_);
v_module_4598_ = lean_ctor_get(v___x_4597_, 0);
v_isPrivate_4599_ = lean_ctor_get_uint8(v___x_4597_, sizeof(void*)*1);
v_isAll_4600_ = lean_ctor_get_uint8(v___x_4597_, sizeof(void*)*1 + 1);
v_isMeta_4601_ = lean_ctor_get_uint8(v___x_4597_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_4598_);
v_module_4602_ = l_String_toName(v_module_4598_);
lean_inc(v_module_4602_);
v___x_4603_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4602_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v_a_4604_; lean_object* v_a_4606_; 
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
lean_inc(v_a_4604_);
lean_dec_ref_known(v___x_4603_, 1);
if (lean_obj_tag(v_a_4604_) == 1)
{
lean_object* v_val_4610_; uint8_t v___y_4612_; 
v_val_4610_ = lean_ctor_get(v_a_4604_, 0);
lean_inc(v_val_4610_);
lean_dec_ref_known(v_a_4604_, 1);
if (v_isMeta_4601_ == 0)
{
uint8_t v___x_4615_; 
v___x_4615_ = 0;
v___y_4612_ = v___x_4615_;
goto v___jp_4611_;
}
else
{
uint8_t v___x_4616_; 
v___x_4616_ = 1;
v___y_4612_ = v___x_4616_;
goto v___jp_4611_;
}
v___jp_4611_:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4613_, 0, v_module_4602_);
lean_ctor_set(v___x_4613_, 1, v_val_4610_);
lean_ctor_set_uint8(v___x_4613_, sizeof(void*)*2, v_isAll_4600_);
lean_ctor_set_uint8(v___x_4613_, sizeof(void*)*2 + 1, v_isPrivate_4599_);
lean_ctor_set_uint8(v___x_4613_, sizeof(void*)*2 + 2, v___y_4612_);
v___x_4614_ = lean_array_push(v_b_4594_, v___x_4613_);
v_a_4606_ = v___x_4614_;
goto v___jp_4605_;
}
}
else
{
lean_dec(v_a_4604_);
lean_dec(v_module_4602_);
v_a_4606_ = v_b_4594_;
goto v___jp_4605_;
}
v___jp_4605_:
{
size_t v___x_4607_; size_t v___x_4608_; 
v___x_4607_ = ((size_t)1ULL);
v___x_4608_ = lean_usize_add(v_i_4592_, v___x_4607_);
v_i_4592_ = v___x_4608_;
v_b_4594_ = v_a_4606_;
goto _start;
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_dec(v_module_4602_);
lean_dec_ref(v_b_4594_);
v_a_4617_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4603_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4603_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
else
{
lean_object* v___x_4625_; 
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v_b_4594_);
return v___x_4625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0___boxed(lean_object* v_as_4626_, lean_object* v_i_4627_, lean_object* v_stop_4628_, lean_object* v_b_4629_, lean_object* v___y_4630_){
_start:
{
size_t v_i_boxed_4631_; size_t v_stop_boxed_4632_; lean_object* v_res_4633_; 
v_i_boxed_4631_ = lean_unbox_usize(v_i_4627_);
lean_dec(v_i_4627_);
v_stop_boxed_4632_ = lean_unbox_usize(v_stop_4628_);
lean_dec(v_stop_4628_);
v_res_4633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4626_, v_i_boxed_4631_, v_stop_boxed_4632_, v_b_4629_);
lean_dec_ref(v_as_4626_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(lean_object* v_as_4634_, lean_object* v_start_4635_, lean_object* v_stop_4636_){
_start:
{
lean_object* v___x_4638_; uint8_t v___x_4639_; 
v___x_4638_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_4639_ = lean_nat_dec_lt(v_start_4635_, v_stop_4636_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4640_; 
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4638_);
return v___x_4640_;
}
else
{
lean_object* v___x_4641_; uint8_t v___x_4642_; 
v___x_4641_ = lean_array_get_size(v_as_4634_);
v___x_4642_ = lean_nat_dec_le(v_stop_4636_, v___x_4641_);
if (v___x_4642_ == 0)
{
uint8_t v___x_4643_; 
v___x_4643_ = lean_nat_dec_lt(v_start_4635_, v___x_4641_);
if (v___x_4643_ == 0)
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4638_);
return v___x_4644_;
}
else
{
size_t v___x_4645_; size_t v___x_4646_; lean_object* v___x_4647_; 
v___x_4645_ = lean_usize_of_nat(v_start_4635_);
v___x_4646_ = lean_usize_of_nat(v___x_4641_);
v___x_4647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4634_, v___x_4645_, v___x_4646_, v___x_4638_);
return v___x_4647_;
}
}
else
{
size_t v___x_4648_; size_t v___x_4649_; lean_object* v___x_4650_; 
v___x_4648_ = lean_usize_of_nat(v_start_4635_);
v___x_4649_ = lean_usize_of_nat(v_stop_4636_);
v___x_4650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0_spec__0(v_as_4634_, v___x_4648_, v___x_4649_, v___x_4638_);
return v___x_4650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0___boxed(lean_object* v_as_4651_, lean_object* v_start_4652_, lean_object* v_stop_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_as_4651_, v_start_4652_, v_stop_4653_);
lean_dec(v_stop_4653_);
lean_dec(v_start_4652_);
lean_dec_ref(v_as_4651_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(lean_object* v_k_4656_, lean_object* v_v_4657_, lean_object* v_t_4658_){
_start:
{
if (lean_obj_tag(v_t_4658_) == 0)
{
lean_object* v_size_4659_; lean_object* v_k_4660_; lean_object* v_v_4661_; lean_object* v_l_4662_; lean_object* v_r_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4943_; 
v_size_4659_ = lean_ctor_get(v_t_4658_, 0);
v_k_4660_ = lean_ctor_get(v_t_4658_, 1);
v_v_4661_ = lean_ctor_get(v_t_4658_, 2);
v_l_4662_ = lean_ctor_get(v_t_4658_, 3);
v_r_4663_ = lean_ctor_get(v_t_4658_, 4);
v_isSharedCheck_4943_ = !lean_is_exclusive(v_t_4658_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4665_ = v_t_4658_;
v_isShared_4666_ = v_isSharedCheck_4943_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_r_4663_);
lean_inc(v_l_4662_);
lean_inc(v_v_4661_);
lean_inc(v_k_4660_);
lean_inc(v_size_4659_);
lean_dec(v_t_4658_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4943_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
uint8_t v___x_4667_; 
v___x_4667_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4656_, v_k_4660_);
switch(v___x_4667_)
{
case 0:
{
lean_object* v_impl_4668_; lean_object* v___x_4669_; 
lean_dec(v_size_4659_);
v_impl_4668_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4656_, v_v_4657_, v_l_4662_);
v___x_4669_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4663_) == 0)
{
lean_object* v_size_4670_; lean_object* v_size_4671_; lean_object* v_k_4672_; lean_object* v_v_4673_; lean_object* v_l_4674_; lean_object* v_r_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v_size_4670_ = lean_ctor_get(v_r_4663_, 0);
v_size_4671_ = lean_ctor_get(v_impl_4668_, 0);
lean_inc(v_size_4671_);
v_k_4672_ = lean_ctor_get(v_impl_4668_, 1);
lean_inc(v_k_4672_);
v_v_4673_ = lean_ctor_get(v_impl_4668_, 2);
lean_inc(v_v_4673_);
v_l_4674_ = lean_ctor_get(v_impl_4668_, 3);
lean_inc(v_l_4674_);
v_r_4675_ = lean_ctor_get(v_impl_4668_, 4);
lean_inc(v_r_4675_);
v___x_4676_ = lean_unsigned_to_nat(3u);
v___x_4677_ = lean_nat_mul(v___x_4676_, v_size_4670_);
v___x_4678_ = lean_nat_dec_lt(v___x_4677_, v_size_4671_);
lean_dec(v___x_4677_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4682_; 
lean_dec(v_r_4675_);
lean_dec(v_l_4674_);
lean_dec(v_v_4673_);
lean_dec(v_k_4672_);
v___x_4679_ = lean_nat_add(v___x_4669_, v_size_4671_);
lean_dec(v_size_4671_);
v___x_4680_ = lean_nat_add(v___x_4679_, v_size_4670_);
lean_dec(v___x_4679_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 3, v_impl_4668_);
lean_ctor_set(v___x_4665_, 0, v___x_4680_);
v___x_4682_ = v___x_4665_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4680_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4683_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4683_, 3, v_impl_4668_);
lean_ctor_set(v_reuseFailAlloc_4683_, 4, v_r_4663_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
else
{
lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4749_; 
v_isSharedCheck_4749_ = !lean_is_exclusive(v_impl_4668_);
if (v_isSharedCheck_4749_ == 0)
{
lean_object* v_unused_4750_; lean_object* v_unused_4751_; lean_object* v_unused_4752_; lean_object* v_unused_4753_; lean_object* v_unused_4754_; 
v_unused_4750_ = lean_ctor_get(v_impl_4668_, 4);
lean_dec(v_unused_4750_);
v_unused_4751_ = lean_ctor_get(v_impl_4668_, 3);
lean_dec(v_unused_4751_);
v_unused_4752_ = lean_ctor_get(v_impl_4668_, 2);
lean_dec(v_unused_4752_);
v_unused_4753_ = lean_ctor_get(v_impl_4668_, 1);
lean_dec(v_unused_4753_);
v_unused_4754_ = lean_ctor_get(v_impl_4668_, 0);
lean_dec(v_unused_4754_);
v___x_4685_ = v_impl_4668_;
v_isShared_4686_ = v_isSharedCheck_4749_;
goto v_resetjp_4684_;
}
else
{
lean_dec(v_impl_4668_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4749_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v_size_4687_; lean_object* v_size_4688_; lean_object* v_k_4689_; lean_object* v_v_4690_; lean_object* v_l_4691_; lean_object* v_r_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v_size_4687_ = lean_ctor_get(v_l_4674_, 0);
v_size_4688_ = lean_ctor_get(v_r_4675_, 0);
v_k_4689_ = lean_ctor_get(v_r_4675_, 1);
v_v_4690_ = lean_ctor_get(v_r_4675_, 2);
v_l_4691_ = lean_ctor_get(v_r_4675_, 3);
v_r_4692_ = lean_ctor_get(v_r_4675_, 4);
v___x_4693_ = lean_unsigned_to_nat(2u);
v___x_4694_ = lean_nat_mul(v___x_4693_, v_size_4687_);
v___x_4695_ = lean_nat_dec_lt(v_size_4688_, v___x_4694_);
lean_dec(v___x_4694_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4724_; 
lean_inc(v_r_4692_);
lean_inc(v_l_4691_);
lean_inc(v_v_4690_);
lean_inc(v_k_4689_);
v_isSharedCheck_4724_ = !lean_is_exclusive(v_r_4675_);
if (v_isSharedCheck_4724_ == 0)
{
lean_object* v_unused_4725_; lean_object* v_unused_4726_; lean_object* v_unused_4727_; lean_object* v_unused_4728_; lean_object* v_unused_4729_; 
v_unused_4725_ = lean_ctor_get(v_r_4675_, 4);
lean_dec(v_unused_4725_);
v_unused_4726_ = lean_ctor_get(v_r_4675_, 3);
lean_dec(v_unused_4726_);
v_unused_4727_ = lean_ctor_get(v_r_4675_, 2);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v_r_4675_, 1);
lean_dec(v_unused_4728_);
v_unused_4729_ = lean_ctor_get(v_r_4675_, 0);
lean_dec(v_unused_4729_);
v___x_4697_ = v_r_4675_;
v_isShared_4698_ = v_isSharedCheck_4724_;
goto v_resetjp_4696_;
}
else
{
lean_dec(v_r_4675_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4724_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___y_4702_; lean_object* v___y_4703_; lean_object* v___y_4704_; lean_object* v___x_4712_; lean_object* v___y_4714_; 
v___x_4699_ = lean_nat_add(v___x_4669_, v_size_4671_);
lean_dec(v_size_4671_);
v___x_4700_ = lean_nat_add(v___x_4699_, v_size_4670_);
lean_dec(v___x_4699_);
v___x_4712_ = lean_nat_add(v___x_4669_, v_size_4687_);
if (lean_obj_tag(v_l_4691_) == 0)
{
lean_object* v_size_4722_; 
v_size_4722_ = lean_ctor_get(v_l_4691_, 0);
lean_inc(v_size_4722_);
v___y_4714_ = v_size_4722_;
goto v___jp_4713_;
}
else
{
lean_object* v___x_4723_; 
v___x_4723_ = lean_unsigned_to_nat(0u);
v___y_4714_ = v___x_4723_;
goto v___jp_4713_;
}
v___jp_4701_:
{
lean_object* v___x_4705_; lean_object* v___x_4707_; 
v___x_4705_ = lean_nat_add(v___y_4702_, v___y_4704_);
lean_dec(v___y_4704_);
lean_dec(v___y_4702_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 4, v_r_4663_);
lean_ctor_set(v___x_4697_, 3, v_r_4692_);
lean_ctor_set(v___x_4697_, 2, v_v_4661_);
lean_ctor_set(v___x_4697_, 1, v_k_4660_);
lean_ctor_set(v___x_4697_, 0, v___x_4705_);
v___x_4707_ = v___x_4697_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v___x_4705_);
lean_ctor_set(v_reuseFailAlloc_4711_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4711_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4711_, 3, v_r_4692_);
lean_ctor_set(v_reuseFailAlloc_4711_, 4, v_r_4663_);
v___x_4707_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
lean_object* v___x_4709_; 
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 4, v___x_4707_);
lean_ctor_set(v___x_4685_, 3, v___y_4703_);
lean_ctor_set(v___x_4685_, 2, v_v_4690_);
lean_ctor_set(v___x_4685_, 1, v_k_4689_);
lean_ctor_set(v___x_4685_, 0, v___x_4700_);
v___x_4709_ = v___x_4685_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v___x_4700_);
lean_ctor_set(v_reuseFailAlloc_4710_, 1, v_k_4689_);
lean_ctor_set(v_reuseFailAlloc_4710_, 2, v_v_4690_);
lean_ctor_set(v_reuseFailAlloc_4710_, 3, v___y_4703_);
lean_ctor_set(v_reuseFailAlloc_4710_, 4, v___x_4707_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
v___jp_4713_:
{
lean_object* v___x_4715_; lean_object* v___x_4717_; 
v___x_4715_ = lean_nat_add(v___x_4712_, v___y_4714_);
lean_dec(v___y_4714_);
lean_dec(v___x_4712_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v_l_4691_);
lean_ctor_set(v___x_4665_, 3, v_l_4674_);
lean_ctor_set(v___x_4665_, 2, v_v_4673_);
lean_ctor_set(v___x_4665_, 1, v_k_4672_);
lean_ctor_set(v___x_4665_, 0, v___x_4715_);
v___x_4717_ = v___x_4665_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v___x_4715_);
lean_ctor_set(v_reuseFailAlloc_4721_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4721_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4721_, 3, v_l_4674_);
lean_ctor_set(v_reuseFailAlloc_4721_, 4, v_l_4691_);
v___x_4717_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; 
v___x_4718_ = lean_nat_add(v___x_4669_, v_size_4670_);
if (lean_obj_tag(v_r_4692_) == 0)
{
lean_object* v_size_4719_; 
v_size_4719_ = lean_ctor_get(v_r_4692_, 0);
lean_inc(v_size_4719_);
v___y_4702_ = v___x_4718_;
v___y_4703_ = v___x_4717_;
v___y_4704_ = v_size_4719_;
goto v___jp_4701_;
}
else
{
lean_object* v___x_4720_; 
v___x_4720_ = lean_unsigned_to_nat(0u);
v___y_4702_ = v___x_4718_;
v___y_4703_ = v___x_4717_;
v___y_4704_ = v___x_4720_;
goto v___jp_4701_;
}
}
}
}
}
else
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4735_; 
lean_del_object(v___x_4665_);
v___x_4730_ = lean_nat_add(v___x_4669_, v_size_4671_);
lean_dec(v_size_4671_);
v___x_4731_ = lean_nat_add(v___x_4730_, v_size_4670_);
lean_dec(v___x_4730_);
v___x_4732_ = lean_nat_add(v___x_4669_, v_size_4670_);
v___x_4733_ = lean_nat_add(v___x_4732_, v_size_4688_);
lean_dec(v___x_4732_);
lean_inc_ref(v_r_4663_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 4, v_r_4663_);
lean_ctor_set(v___x_4685_, 3, v_r_4675_);
lean_ctor_set(v___x_4685_, 2, v_v_4661_);
lean_ctor_set(v___x_4685_, 1, v_k_4660_);
lean_ctor_set(v___x_4685_, 0, v___x_4733_);
v___x_4735_ = v___x_4685_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4748_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4748_, 3, v_r_4675_);
lean_ctor_set(v_reuseFailAlloc_4748_, 4, v_r_4663_);
v___x_4735_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
v_isSharedCheck_4742_ = !lean_is_exclusive(v_r_4663_);
if (v_isSharedCheck_4742_ == 0)
{
lean_object* v_unused_4743_; lean_object* v_unused_4744_; lean_object* v_unused_4745_; lean_object* v_unused_4746_; lean_object* v_unused_4747_; 
v_unused_4743_ = lean_ctor_get(v_r_4663_, 4);
lean_dec(v_unused_4743_);
v_unused_4744_ = lean_ctor_get(v_r_4663_, 3);
lean_dec(v_unused_4744_);
v_unused_4745_ = lean_ctor_get(v_r_4663_, 2);
lean_dec(v_unused_4745_);
v_unused_4746_ = lean_ctor_get(v_r_4663_, 1);
lean_dec(v_unused_4746_);
v_unused_4747_ = lean_ctor_get(v_r_4663_, 0);
lean_dec(v_unused_4747_);
v___x_4737_ = v_r_4663_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_dec(v_r_4663_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 4, v___x_4735_);
lean_ctor_set(v___x_4737_, 3, v_l_4674_);
lean_ctor_set(v___x_4737_, 2, v_v_4673_);
lean_ctor_set(v___x_4737_, 1, v_k_4672_);
lean_ctor_set(v___x_4737_, 0, v___x_4731_);
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4731_);
lean_ctor_set(v_reuseFailAlloc_4741_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4741_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4741_, 3, v_l_4674_);
lean_ctor_set(v_reuseFailAlloc_4741_, 4, v___x_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4755_; 
v_l_4755_ = lean_ctor_get(v_impl_4668_, 3);
lean_inc(v_l_4755_);
if (lean_obj_tag(v_l_4755_) == 0)
{
lean_object* v_r_4756_; lean_object* v_k_4757_; lean_object* v_v_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4769_; 
v_r_4756_ = lean_ctor_get(v_impl_4668_, 4);
v_k_4757_ = lean_ctor_get(v_impl_4668_, 1);
v_v_4758_ = lean_ctor_get(v_impl_4668_, 2);
v_isSharedCheck_4769_ = !lean_is_exclusive(v_impl_4668_);
if (v_isSharedCheck_4769_ == 0)
{
lean_object* v_unused_4770_; lean_object* v_unused_4771_; 
v_unused_4770_ = lean_ctor_get(v_impl_4668_, 3);
lean_dec(v_unused_4770_);
v_unused_4771_ = lean_ctor_get(v_impl_4668_, 0);
lean_dec(v_unused_4771_);
v___x_4760_ = v_impl_4668_;
v_isShared_4761_ = v_isSharedCheck_4769_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_r_4756_);
lean_inc(v_v_4758_);
lean_inc(v_k_4757_);
lean_dec(v_impl_4668_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4769_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4762_; lean_object* v___x_4764_; 
v___x_4762_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4756_);
if (v_isShared_4761_ == 0)
{
lean_ctor_set(v___x_4760_, 3, v_r_4756_);
lean_ctor_set(v___x_4760_, 2, v_v_4661_);
lean_ctor_set(v___x_4760_, 1, v_k_4660_);
lean_ctor_set(v___x_4760_, 0, v___x_4669_);
v___x_4764_ = v___x_4760_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4669_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4768_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4768_, 3, v_r_4756_);
lean_ctor_set(v_reuseFailAlloc_4768_, 4, v_r_4756_);
v___x_4764_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4766_; 
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v___x_4764_);
lean_ctor_set(v___x_4665_, 3, v_l_4755_);
lean_ctor_set(v___x_4665_, 2, v_v_4758_);
lean_ctor_set(v___x_4665_, 1, v_k_4757_);
lean_ctor_set(v___x_4665_, 0, v___x_4762_);
v___x_4766_ = v___x_4665_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4762_);
lean_ctor_set(v_reuseFailAlloc_4767_, 1, v_k_4757_);
lean_ctor_set(v_reuseFailAlloc_4767_, 2, v_v_4758_);
lean_ctor_set(v_reuseFailAlloc_4767_, 3, v_l_4755_);
lean_ctor_set(v_reuseFailAlloc_4767_, 4, v___x_4764_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
else
{
lean_object* v_r_4772_; 
v_r_4772_ = lean_ctor_get(v_impl_4668_, 4);
lean_inc(v_r_4772_);
if (lean_obj_tag(v_r_4772_) == 0)
{
lean_object* v_k_4773_; lean_object* v_v_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4797_; 
v_k_4773_ = lean_ctor_get(v_impl_4668_, 1);
v_v_4774_ = lean_ctor_get(v_impl_4668_, 2);
v_isSharedCheck_4797_ = !lean_is_exclusive(v_impl_4668_);
if (v_isSharedCheck_4797_ == 0)
{
lean_object* v_unused_4798_; lean_object* v_unused_4799_; lean_object* v_unused_4800_; 
v_unused_4798_ = lean_ctor_get(v_impl_4668_, 4);
lean_dec(v_unused_4798_);
v_unused_4799_ = lean_ctor_get(v_impl_4668_, 3);
lean_dec(v_unused_4799_);
v_unused_4800_ = lean_ctor_get(v_impl_4668_, 0);
lean_dec(v_unused_4800_);
v___x_4776_ = v_impl_4668_;
v_isShared_4777_ = v_isSharedCheck_4797_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_v_4774_);
lean_inc(v_k_4773_);
lean_dec(v_impl_4668_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4797_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v_k_4778_; lean_object* v_v_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4793_; 
v_k_4778_ = lean_ctor_get(v_r_4772_, 1);
v_v_4779_ = lean_ctor_get(v_r_4772_, 2);
v_isSharedCheck_4793_ = !lean_is_exclusive(v_r_4772_);
if (v_isSharedCheck_4793_ == 0)
{
lean_object* v_unused_4794_; lean_object* v_unused_4795_; lean_object* v_unused_4796_; 
v_unused_4794_ = lean_ctor_get(v_r_4772_, 4);
lean_dec(v_unused_4794_);
v_unused_4795_ = lean_ctor_get(v_r_4772_, 3);
lean_dec(v_unused_4795_);
v_unused_4796_ = lean_ctor_get(v_r_4772_, 0);
lean_dec(v_unused_4796_);
v___x_4781_ = v_r_4772_;
v_isShared_4782_ = v_isSharedCheck_4793_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_v_4779_);
lean_inc(v_k_4778_);
lean_dec(v_r_4772_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4793_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4783_ = lean_unsigned_to_nat(3u);
if (v_isShared_4782_ == 0)
{
lean_ctor_set(v___x_4781_, 4, v_l_4755_);
lean_ctor_set(v___x_4781_, 3, v_l_4755_);
lean_ctor_set(v___x_4781_, 2, v_v_4774_);
lean_ctor_set(v___x_4781_, 1, v_k_4773_);
lean_ctor_set(v___x_4781_, 0, v___x_4669_);
v___x_4785_ = v___x_4781_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4669_);
lean_ctor_set(v_reuseFailAlloc_4792_, 1, v_k_4773_);
lean_ctor_set(v_reuseFailAlloc_4792_, 2, v_v_4774_);
lean_ctor_set(v_reuseFailAlloc_4792_, 3, v_l_4755_);
lean_ctor_set(v_reuseFailAlloc_4792_, 4, v_l_4755_);
v___x_4785_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4787_; 
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 4, v_l_4755_);
lean_ctor_set(v___x_4776_, 2, v_v_4661_);
lean_ctor_set(v___x_4776_, 1, v_k_4660_);
lean_ctor_set(v___x_4776_, 0, v___x_4669_);
v___x_4787_ = v___x_4776_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4669_);
lean_ctor_set(v_reuseFailAlloc_4791_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4791_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4791_, 3, v_l_4755_);
lean_ctor_set(v_reuseFailAlloc_4791_, 4, v_l_4755_);
v___x_4787_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
lean_object* v___x_4789_; 
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v___x_4787_);
lean_ctor_set(v___x_4665_, 3, v___x_4785_);
lean_ctor_set(v___x_4665_, 2, v_v_4779_);
lean_ctor_set(v___x_4665_, 1, v_k_4778_);
lean_ctor_set(v___x_4665_, 0, v___x_4783_);
v___x_4789_ = v___x_4665_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v___x_4783_);
lean_ctor_set(v_reuseFailAlloc_4790_, 1, v_k_4778_);
lean_ctor_set(v_reuseFailAlloc_4790_, 2, v_v_4779_);
lean_ctor_set(v_reuseFailAlloc_4790_, 3, v___x_4785_);
lean_ctor_set(v_reuseFailAlloc_4790_, 4, v___x_4787_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
}
}
}
else
{
lean_object* v___x_4801_; lean_object* v___x_4803_; 
v___x_4801_ = lean_unsigned_to_nat(2u);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v_r_4772_);
lean_ctor_set(v___x_4665_, 3, v_impl_4668_);
lean_ctor_set(v___x_4665_, 0, v___x_4801_);
v___x_4803_ = v___x_4665_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4801_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4804_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4804_, 3, v_impl_4668_);
lean_ctor_set(v_reuseFailAlloc_4804_, 4, v_r_4772_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4806_; 
lean_dec(v_v_4661_);
lean_dec(v_k_4660_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 2, v_v_4657_);
lean_ctor_set(v___x_4665_, 1, v_k_4656_);
v___x_4806_ = v___x_4665_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_size_4659_);
lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_k_4656_);
lean_ctor_set(v_reuseFailAlloc_4807_, 2, v_v_4657_);
lean_ctor_set(v_reuseFailAlloc_4807_, 3, v_l_4662_);
lean_ctor_set(v_reuseFailAlloc_4807_, 4, v_r_4663_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
default: 
{
lean_object* v_impl_4808_; lean_object* v___x_4809_; 
lean_dec(v_size_4659_);
v_impl_4808_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_4656_, v_v_4657_, v_r_4663_);
v___x_4809_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4662_) == 0)
{
lean_object* v_size_4810_; lean_object* v_size_4811_; lean_object* v_k_4812_; lean_object* v_v_4813_; lean_object* v_l_4814_; lean_object* v_r_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v_size_4810_ = lean_ctor_get(v_l_4662_, 0);
v_size_4811_ = lean_ctor_get(v_impl_4808_, 0);
lean_inc(v_size_4811_);
v_k_4812_ = lean_ctor_get(v_impl_4808_, 1);
lean_inc(v_k_4812_);
v_v_4813_ = lean_ctor_get(v_impl_4808_, 2);
lean_inc(v_v_4813_);
v_l_4814_ = lean_ctor_get(v_impl_4808_, 3);
lean_inc(v_l_4814_);
v_r_4815_ = lean_ctor_get(v_impl_4808_, 4);
lean_inc(v_r_4815_);
v___x_4816_ = lean_unsigned_to_nat(3u);
v___x_4817_ = lean_nat_mul(v___x_4816_, v_size_4810_);
v___x_4818_ = lean_nat_dec_lt(v___x_4817_, v_size_4811_);
lean_dec(v___x_4817_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4822_; 
lean_dec(v_r_4815_);
lean_dec(v_l_4814_);
lean_dec(v_v_4813_);
lean_dec(v_k_4812_);
v___x_4819_ = lean_nat_add(v___x_4809_, v_size_4810_);
v___x_4820_ = lean_nat_add(v___x_4819_, v_size_4811_);
lean_dec(v_size_4811_);
lean_dec(v___x_4819_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v_impl_4808_);
lean_ctor_set(v___x_4665_, 0, v___x_4820_);
v___x_4822_ = v___x_4665_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4823_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4823_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4823_, 3, v_l_4662_);
lean_ctor_set(v_reuseFailAlloc_4823_, 4, v_impl_4808_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
else
{
lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4887_; 
v_isSharedCheck_4887_ = !lean_is_exclusive(v_impl_4808_);
if (v_isSharedCheck_4887_ == 0)
{
lean_object* v_unused_4888_; lean_object* v_unused_4889_; lean_object* v_unused_4890_; lean_object* v_unused_4891_; lean_object* v_unused_4892_; 
v_unused_4888_ = lean_ctor_get(v_impl_4808_, 4);
lean_dec(v_unused_4888_);
v_unused_4889_ = lean_ctor_get(v_impl_4808_, 3);
lean_dec(v_unused_4889_);
v_unused_4890_ = lean_ctor_get(v_impl_4808_, 2);
lean_dec(v_unused_4890_);
v_unused_4891_ = lean_ctor_get(v_impl_4808_, 1);
lean_dec(v_unused_4891_);
v_unused_4892_ = lean_ctor_get(v_impl_4808_, 0);
lean_dec(v_unused_4892_);
v___x_4825_ = v_impl_4808_;
v_isShared_4826_ = v_isSharedCheck_4887_;
goto v_resetjp_4824_;
}
else
{
lean_dec(v_impl_4808_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4887_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v_size_4827_; lean_object* v_k_4828_; lean_object* v_v_4829_; lean_object* v_l_4830_; lean_object* v_r_4831_; lean_object* v_size_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v_size_4827_ = lean_ctor_get(v_l_4814_, 0);
v_k_4828_ = lean_ctor_get(v_l_4814_, 1);
v_v_4829_ = lean_ctor_get(v_l_4814_, 2);
v_l_4830_ = lean_ctor_get(v_l_4814_, 3);
v_r_4831_ = lean_ctor_get(v_l_4814_, 4);
v_size_4832_ = lean_ctor_get(v_r_4815_, 0);
v___x_4833_ = lean_unsigned_to_nat(2u);
v___x_4834_ = lean_nat_mul(v___x_4833_, v_size_4832_);
v___x_4835_ = lean_nat_dec_lt(v_size_4827_, v___x_4834_);
lean_dec(v___x_4834_);
if (v___x_4835_ == 0)
{
lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4863_; 
lean_inc(v_r_4831_);
lean_inc(v_l_4830_);
lean_inc(v_v_4829_);
lean_inc(v_k_4828_);
v_isSharedCheck_4863_ = !lean_is_exclusive(v_l_4814_);
if (v_isSharedCheck_4863_ == 0)
{
lean_object* v_unused_4864_; lean_object* v_unused_4865_; lean_object* v_unused_4866_; lean_object* v_unused_4867_; lean_object* v_unused_4868_; 
v_unused_4864_ = lean_ctor_get(v_l_4814_, 4);
lean_dec(v_unused_4864_);
v_unused_4865_ = lean_ctor_get(v_l_4814_, 3);
lean_dec(v_unused_4865_);
v_unused_4866_ = lean_ctor_get(v_l_4814_, 2);
lean_dec(v_unused_4866_);
v_unused_4867_ = lean_ctor_get(v_l_4814_, 1);
lean_dec(v_unused_4867_);
v_unused_4868_ = lean_ctor_get(v_l_4814_, 0);
lean_dec(v_unused_4868_);
v___x_4837_ = v_l_4814_;
v_isShared_4838_ = v_isSharedCheck_4863_;
goto v_resetjp_4836_;
}
else
{
lean_dec(v_l_4814_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4863_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4853_; 
v___x_4839_ = lean_nat_add(v___x_4809_, v_size_4810_);
v___x_4840_ = lean_nat_add(v___x_4839_, v_size_4811_);
lean_dec(v_size_4811_);
if (lean_obj_tag(v_l_4830_) == 0)
{
lean_object* v_size_4861_; 
v_size_4861_ = lean_ctor_get(v_l_4830_, 0);
lean_inc(v_size_4861_);
v___y_4853_ = v_size_4861_;
goto v___jp_4852_;
}
else
{
lean_object* v___x_4862_; 
v___x_4862_ = lean_unsigned_to_nat(0u);
v___y_4853_ = v___x_4862_;
goto v___jp_4852_;
}
v___jp_4841_:
{
lean_object* v___x_4845_; lean_object* v___x_4847_; 
v___x_4845_ = lean_nat_add(v___y_4843_, v___y_4844_);
lean_dec(v___y_4844_);
lean_dec(v___y_4843_);
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 4, v_r_4815_);
lean_ctor_set(v___x_4837_, 3, v_r_4831_);
lean_ctor_set(v___x_4837_, 2, v_v_4813_);
lean_ctor_set(v___x_4837_, 1, v_k_4812_);
lean_ctor_set(v___x_4837_, 0, v___x_4845_);
v___x_4847_ = v___x_4837_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v___x_4845_);
lean_ctor_set(v_reuseFailAlloc_4851_, 1, v_k_4812_);
lean_ctor_set(v_reuseFailAlloc_4851_, 2, v_v_4813_);
lean_ctor_set(v_reuseFailAlloc_4851_, 3, v_r_4831_);
lean_ctor_set(v_reuseFailAlloc_4851_, 4, v_r_4815_);
v___x_4847_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
lean_object* v___x_4849_; 
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 4, v___x_4847_);
lean_ctor_set(v___x_4825_, 3, v___y_4842_);
lean_ctor_set(v___x_4825_, 2, v_v_4829_);
lean_ctor_set(v___x_4825_, 1, v_k_4828_);
lean_ctor_set(v___x_4825_, 0, v___x_4840_);
v___x_4849_ = v___x_4825_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4840_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_k_4828_);
lean_ctor_set(v_reuseFailAlloc_4850_, 2, v_v_4829_);
lean_ctor_set(v_reuseFailAlloc_4850_, 3, v___y_4842_);
lean_ctor_set(v_reuseFailAlloc_4850_, 4, v___x_4847_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
v___jp_4852_:
{
lean_object* v___x_4854_; lean_object* v___x_4856_; 
v___x_4854_ = lean_nat_add(v___x_4839_, v___y_4853_);
lean_dec(v___y_4853_);
lean_dec(v___x_4839_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v_l_4830_);
lean_ctor_set(v___x_4665_, 0, v___x_4854_);
v___x_4856_ = v___x_4665_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4860_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4860_, 3, v_l_4662_);
lean_ctor_set(v_reuseFailAlloc_4860_, 4, v_l_4830_);
v___x_4856_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
lean_object* v___x_4857_; 
v___x_4857_ = lean_nat_add(v___x_4809_, v_size_4832_);
if (lean_obj_tag(v_r_4831_) == 0)
{
lean_object* v_size_4858_; 
v_size_4858_ = lean_ctor_get(v_r_4831_, 0);
lean_inc(v_size_4858_);
v___y_4842_ = v___x_4856_;
v___y_4843_ = v___x_4857_;
v___y_4844_ = v_size_4858_;
goto v___jp_4841_;
}
else
{
lean_object* v___x_4859_; 
v___x_4859_ = lean_unsigned_to_nat(0u);
v___y_4842_ = v___x_4856_;
v___y_4843_ = v___x_4857_;
v___y_4844_ = v___x_4859_;
goto v___jp_4841_;
}
}
}
}
}
else
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4873_; 
lean_del_object(v___x_4665_);
v___x_4869_ = lean_nat_add(v___x_4809_, v_size_4810_);
v___x_4870_ = lean_nat_add(v___x_4869_, v_size_4811_);
lean_dec(v_size_4811_);
v___x_4871_ = lean_nat_add(v___x_4869_, v_size_4827_);
lean_dec(v___x_4869_);
lean_inc_ref(v_l_4662_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 4, v_l_4814_);
lean_ctor_set(v___x_4825_, 3, v_l_4662_);
lean_ctor_set(v___x_4825_, 2, v_v_4661_);
lean_ctor_set(v___x_4825_, 1, v_k_4660_);
lean_ctor_set(v___x_4825_, 0, v___x_4871_);
v___x_4873_ = v___x_4825_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4871_);
lean_ctor_set(v_reuseFailAlloc_4886_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4886_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4886_, 3, v_l_4662_);
lean_ctor_set(v_reuseFailAlloc_4886_, 4, v_l_4814_);
v___x_4873_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4880_; 
v_isSharedCheck_4880_ = !lean_is_exclusive(v_l_4662_);
if (v_isSharedCheck_4880_ == 0)
{
lean_object* v_unused_4881_; lean_object* v_unused_4882_; lean_object* v_unused_4883_; lean_object* v_unused_4884_; lean_object* v_unused_4885_; 
v_unused_4881_ = lean_ctor_get(v_l_4662_, 4);
lean_dec(v_unused_4881_);
v_unused_4882_ = lean_ctor_get(v_l_4662_, 3);
lean_dec(v_unused_4882_);
v_unused_4883_ = lean_ctor_get(v_l_4662_, 2);
lean_dec(v_unused_4883_);
v_unused_4884_ = lean_ctor_get(v_l_4662_, 1);
lean_dec(v_unused_4884_);
v_unused_4885_ = lean_ctor_get(v_l_4662_, 0);
lean_dec(v_unused_4885_);
v___x_4875_ = v_l_4662_;
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
else
{
lean_dec(v_l_4662_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4878_; 
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 4, v_r_4815_);
lean_ctor_set(v___x_4875_, 3, v___x_4873_);
lean_ctor_set(v___x_4875_, 2, v_v_4813_);
lean_ctor_set(v___x_4875_, 1, v_k_4812_);
lean_ctor_set(v___x_4875_, 0, v___x_4870_);
v___x_4878_ = v___x_4875_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v___x_4870_);
lean_ctor_set(v_reuseFailAlloc_4879_, 1, v_k_4812_);
lean_ctor_set(v_reuseFailAlloc_4879_, 2, v_v_4813_);
lean_ctor_set(v_reuseFailAlloc_4879_, 3, v___x_4873_);
lean_ctor_set(v_reuseFailAlloc_4879_, 4, v_r_4815_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4893_; 
v_l_4893_ = lean_ctor_get(v_impl_4808_, 3);
lean_inc(v_l_4893_);
if (lean_obj_tag(v_l_4893_) == 0)
{
lean_object* v_r_4894_; lean_object* v_k_4895_; lean_object* v_v_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4919_; 
v_r_4894_ = lean_ctor_get(v_impl_4808_, 4);
v_k_4895_ = lean_ctor_get(v_impl_4808_, 1);
v_v_4896_ = lean_ctor_get(v_impl_4808_, 2);
v_isSharedCheck_4919_ = !lean_is_exclusive(v_impl_4808_);
if (v_isSharedCheck_4919_ == 0)
{
lean_object* v_unused_4920_; lean_object* v_unused_4921_; 
v_unused_4920_ = lean_ctor_get(v_impl_4808_, 3);
lean_dec(v_unused_4920_);
v_unused_4921_ = lean_ctor_get(v_impl_4808_, 0);
lean_dec(v_unused_4921_);
v___x_4898_ = v_impl_4808_;
v_isShared_4899_ = v_isSharedCheck_4919_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_r_4894_);
lean_inc(v_v_4896_);
lean_inc(v_k_4895_);
lean_dec(v_impl_4808_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4919_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v_k_4900_; lean_object* v_v_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4915_; 
v_k_4900_ = lean_ctor_get(v_l_4893_, 1);
v_v_4901_ = lean_ctor_get(v_l_4893_, 2);
v_isSharedCheck_4915_ = !lean_is_exclusive(v_l_4893_);
if (v_isSharedCheck_4915_ == 0)
{
lean_object* v_unused_4916_; lean_object* v_unused_4917_; lean_object* v_unused_4918_; 
v_unused_4916_ = lean_ctor_get(v_l_4893_, 4);
lean_dec(v_unused_4916_);
v_unused_4917_ = lean_ctor_get(v_l_4893_, 3);
lean_dec(v_unused_4917_);
v_unused_4918_ = lean_ctor_get(v_l_4893_, 0);
lean_dec(v_unused_4918_);
v___x_4903_ = v_l_4893_;
v_isShared_4904_ = v_isSharedCheck_4915_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_v_4901_);
lean_inc(v_k_4900_);
lean_dec(v_l_4893_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4915_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4905_; lean_object* v___x_4907_; 
v___x_4905_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4894_, 2);
if (v_isShared_4904_ == 0)
{
lean_ctor_set(v___x_4903_, 4, v_r_4894_);
lean_ctor_set(v___x_4903_, 3, v_r_4894_);
lean_ctor_set(v___x_4903_, 2, v_v_4661_);
lean_ctor_set(v___x_4903_, 1, v_k_4660_);
lean_ctor_set(v___x_4903_, 0, v___x_4809_);
v___x_4907_ = v___x_4903_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4914_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4914_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4914_, 3, v_r_4894_);
lean_ctor_set(v_reuseFailAlloc_4914_, 4, v_r_4894_);
v___x_4907_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4909_; 
lean_inc(v_r_4894_);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 3, v_r_4894_);
lean_ctor_set(v___x_4898_, 0, v___x_4809_);
v___x_4909_ = v___x_4898_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4913_, 1, v_k_4895_);
lean_ctor_set(v_reuseFailAlloc_4913_, 2, v_v_4896_);
lean_ctor_set(v_reuseFailAlloc_4913_, 3, v_r_4894_);
lean_ctor_set(v_reuseFailAlloc_4913_, 4, v_r_4894_);
v___x_4909_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
lean_object* v___x_4911_; 
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v___x_4909_);
lean_ctor_set(v___x_4665_, 3, v___x_4907_);
lean_ctor_set(v___x_4665_, 2, v_v_4901_);
lean_ctor_set(v___x_4665_, 1, v_k_4900_);
lean_ctor_set(v___x_4665_, 0, v___x_4905_);
v___x_4911_ = v___x_4665_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4905_);
lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_k_4900_);
lean_ctor_set(v_reuseFailAlloc_4912_, 2, v_v_4901_);
lean_ctor_set(v_reuseFailAlloc_4912_, 3, v___x_4907_);
lean_ctor_set(v_reuseFailAlloc_4912_, 4, v___x_4909_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
}
}
}
else
{
lean_object* v_r_4922_; 
v_r_4922_ = lean_ctor_get(v_impl_4808_, 4);
lean_inc(v_r_4922_);
if (lean_obj_tag(v_r_4922_) == 0)
{
lean_object* v_k_4923_; lean_object* v_v_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4935_; 
v_k_4923_ = lean_ctor_get(v_impl_4808_, 1);
v_v_4924_ = lean_ctor_get(v_impl_4808_, 2);
v_isSharedCheck_4935_ = !lean_is_exclusive(v_impl_4808_);
if (v_isSharedCheck_4935_ == 0)
{
lean_object* v_unused_4936_; lean_object* v_unused_4937_; lean_object* v_unused_4938_; 
v_unused_4936_ = lean_ctor_get(v_impl_4808_, 4);
lean_dec(v_unused_4936_);
v_unused_4937_ = lean_ctor_get(v_impl_4808_, 3);
lean_dec(v_unused_4937_);
v_unused_4938_ = lean_ctor_get(v_impl_4808_, 0);
lean_dec(v_unused_4938_);
v___x_4926_ = v_impl_4808_;
v_isShared_4927_ = v_isSharedCheck_4935_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_v_4924_);
lean_inc(v_k_4923_);
lean_dec(v_impl_4808_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4935_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v___x_4930_; 
v___x_4928_ = lean_unsigned_to_nat(3u);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 4, v_l_4893_);
lean_ctor_set(v___x_4926_, 2, v_v_4661_);
lean_ctor_set(v___x_4926_, 1, v_k_4660_);
lean_ctor_set(v___x_4926_, 0, v___x_4809_);
v___x_4930_ = v___x_4926_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4934_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4934_, 3, v_l_4893_);
lean_ctor_set(v_reuseFailAlloc_4934_, 4, v_l_4893_);
v___x_4930_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v___x_4932_; 
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v_r_4922_);
lean_ctor_set(v___x_4665_, 3, v___x_4930_);
lean_ctor_set(v___x_4665_, 2, v_v_4924_);
lean_ctor_set(v___x_4665_, 1, v_k_4923_);
lean_ctor_set(v___x_4665_, 0, v___x_4928_);
v___x_4932_ = v___x_4665_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4928_);
lean_ctor_set(v_reuseFailAlloc_4933_, 1, v_k_4923_);
lean_ctor_set(v_reuseFailAlloc_4933_, 2, v_v_4924_);
lean_ctor_set(v_reuseFailAlloc_4933_, 3, v___x_4930_);
lean_ctor_set(v_reuseFailAlloc_4933_, 4, v_r_4922_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
}
else
{
lean_object* v___x_4939_; lean_object* v___x_4941_; 
v___x_4939_ = lean_unsigned_to_nat(2u);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 4, v_impl_4808_);
lean_ctor_set(v___x_4665_, 3, v_r_4922_);
lean_ctor_set(v___x_4665_, 0, v___x_4939_);
v___x_4941_ = v___x_4665_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4939_);
lean_ctor_set(v_reuseFailAlloc_4942_, 1, v_k_4660_);
lean_ctor_set(v_reuseFailAlloc_4942_, 2, v_v_4661_);
lean_ctor_set(v_reuseFailAlloc_4942_, 3, v_r_4922_);
lean_ctor_set(v_reuseFailAlloc_4942_, 4, v_impl_4808_);
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
}
}
}
}
else
{
lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4944_ = lean_unsigned_to_nat(1u);
v___x_4945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4944_);
lean_ctor_set(v___x_4945_, 1, v_k_4656_);
lean_ctor_set(v___x_4945_, 2, v_v_4657_);
lean_ctor_set(v___x_4945_, 3, v_t_4658_);
lean_ctor_set(v___x_4945_, 4, v_t_4658_);
return v___x_4945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(lean_object* v_as_4946_, size_t v_sz_4947_, size_t v_i_4948_, lean_object* v_b_4949_){
_start:
{
uint8_t v___x_4950_; 
v___x_4950_ = lean_usize_dec_lt(v_i_4948_, v_sz_4947_);
if (v___x_4950_ == 0)
{
return v_b_4949_;
}
else
{
lean_object* v_a_4951_; lean_object* v_fst_4952_; lean_object* v_snd_4953_; lean_object* v_r_4954_; size_t v___x_4955_; size_t v___x_4956_; 
v_a_4951_ = lean_array_uget_borrowed(v_as_4946_, v_i_4948_);
v_fst_4952_ = lean_ctor_get(v_a_4951_, 0);
v_snd_4953_ = lean_ctor_get(v_a_4951_, 1);
lean_inc(v_snd_4953_);
lean_inc(v_fst_4952_);
v_r_4954_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_fst_4952_, v_snd_4953_, v_b_4949_);
v___x_4955_ = ((size_t)1ULL);
v___x_4956_ = lean_usize_add(v_i_4948_, v___x_4955_);
v_i_4948_ = v___x_4956_;
v_b_4949_ = v_r_4954_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2___boxed(lean_object* v_as_4958_, lean_object* v_sz_4959_, lean_object* v_i_4960_, lean_object* v_b_4961_){
_start:
{
size_t v_sz_boxed_4962_; size_t v_i_boxed_4963_; lean_object* v_res_4964_; 
v_sz_boxed_4962_ = lean_unbox_usize(v_sz_4959_);
lean_dec(v_sz_4959_);
v_i_boxed_4963_ = lean_unbox_usize(v_i_4960_);
lean_dec(v_i_4960_);
v_res_4964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v_as_4958_, v_sz_boxed_4962_, v_i_boxed_4963_, v_b_4961_);
lean_dec_ref(v_as_4958_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(lean_object* v_a_4967_, lean_object* v_x_4968_){
_start:
{
lean_object* v___y_4970_; 
if (lean_obj_tag(v_x_4968_) == 0)
{
lean_object* v___x_4973_; 
v___x_4973_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___y_4970_ = v___x_4973_;
goto v___jp_4969_;
}
else
{
lean_object* v_val_4974_; 
v_val_4974_ = lean_ctor_get(v_x_4968_, 0);
lean_inc(v_val_4974_);
lean_dec_ref_known(v_x_4968_, 1);
v___y_4970_ = v_val_4974_;
goto v___jp_4969_;
}
v___jp_4969_:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4971_ = lean_array_push(v___y_4970_, v_a_4967_);
v___x_4972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4971_);
return v___x_4972_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_x_4977_){
_start:
{
if (lean_obj_tag(v_x_4977_) == 0)
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v_val_4980_; lean_object* v___x_4981_; 
v___x_4978_ = lean_box(0);
v___x_4979_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4975_, v___x_4978_);
v_val_4980_ = lean_ctor_get(v___x_4979_, 0);
lean_inc(v_val_4980_);
lean_dec(v___x_4979_);
v___x_4981_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4981_, 0, v_a_4976_);
lean_ctor_set(v___x_4981_, 1, v_val_4980_);
lean_ctor_set(v___x_4981_, 2, v_x_4977_);
return v___x_4981_;
}
else
{
lean_object* v_key_4982_; lean_object* v_value_4983_; lean_object* v_tail_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4999_; 
v_key_4982_ = lean_ctor_get(v_x_4977_, 0);
v_value_4983_ = lean_ctor_get(v_x_4977_, 1);
v_tail_4984_ = lean_ctor_get(v_x_4977_, 2);
v_isSharedCheck_4999_ = !lean_is_exclusive(v_x_4977_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4986_ = v_x_4977_;
v_isShared_4987_ = v_isSharedCheck_4999_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_tail_4984_);
lean_inc(v_value_4983_);
lean_inc(v_key_4982_);
lean_dec(v_x_4977_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4999_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
uint8_t v___x_4988_; 
v___x_4988_ = lean_name_eq(v_key_4982_, v_a_4976_);
if (v___x_4988_ == 0)
{
lean_object* v_tail_4989_; lean_object* v___x_4991_; 
v_tail_4989_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_4975_, v_a_4976_, v_tail_4984_);
if (v_isShared_4987_ == 0)
{
lean_ctor_set(v___x_4986_, 2, v_tail_4989_);
v___x_4991_ = v___x_4986_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_key_4982_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v_value_4983_);
lean_ctor_set(v_reuseFailAlloc_4992_, 2, v_tail_4989_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
else
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v_val_4995_; lean_object* v___x_4997_; 
lean_dec(v_key_4982_);
v___x_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4993_, 0, v_value_4983_);
v___x_4994_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0(v_a_4975_, v___x_4993_);
v_val_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_val_4995_);
lean_dec(v___x_4994_);
if (v_isShared_4987_ == 0)
{
lean_ctor_set(v___x_4986_, 1, v_val_4995_);
lean_ctor_set(v___x_4986_, 0, v_a_4976_);
v___x_4997_ = v___x_4986_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4976_);
lean_ctor_set(v_reuseFailAlloc_4998_, 1, v_val_4995_);
lean_ctor_set(v_reuseFailAlloc_4998_, 2, v_tail_4984_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(lean_object* v_x_5000_, lean_object* v_x_5001_){
_start:
{
if (lean_obj_tag(v_x_5001_) == 0)
{
return v_x_5000_;
}
else
{
lean_object* v_key_5002_; lean_object* v_value_5003_; lean_object* v_tail_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5030_; 
v_key_5002_ = lean_ctor_get(v_x_5001_, 0);
v_value_5003_ = lean_ctor_get(v_x_5001_, 1);
v_tail_5004_ = lean_ctor_get(v_x_5001_, 2);
v_isSharedCheck_5030_ = !lean_is_exclusive(v_x_5001_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5006_ = v_x_5001_;
v_isShared_5007_ = v_isSharedCheck_5030_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_tail_5004_);
lean_inc(v_value_5003_);
lean_inc(v_key_5002_);
lean_dec(v_x_5001_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5030_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5008_; uint64_t v___y_5010_; 
v___x_5008_ = lean_array_get_size(v_x_5000_);
if (lean_obj_tag(v_key_5002_) == 0)
{
uint64_t v___x_5028_; 
v___x_5028_ = 1723ULL;
v___y_5010_ = v___x_5028_;
goto v___jp_5009_;
}
else
{
uint64_t v_hash_5029_; 
v_hash_5029_ = lean_ctor_get_uint64(v_key_5002_, sizeof(void*)*2);
v___y_5010_ = v_hash_5029_;
goto v___jp_5009_;
}
v___jp_5009_:
{
uint64_t v___x_5011_; uint64_t v___x_5012_; uint64_t v_fold_5013_; uint64_t v___x_5014_; uint64_t v___x_5015_; uint64_t v___x_5016_; size_t v___x_5017_; size_t v___x_5018_; size_t v___x_5019_; size_t v___x_5020_; size_t v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5024_; 
v___x_5011_ = 32ULL;
v___x_5012_ = lean_uint64_shift_right(v___y_5010_, v___x_5011_);
v_fold_5013_ = lean_uint64_xor(v___y_5010_, v___x_5012_);
v___x_5014_ = 16ULL;
v___x_5015_ = lean_uint64_shift_right(v_fold_5013_, v___x_5014_);
v___x_5016_ = lean_uint64_xor(v_fold_5013_, v___x_5015_);
v___x_5017_ = lean_uint64_to_usize(v___x_5016_);
v___x_5018_ = lean_usize_of_nat(v___x_5008_);
v___x_5019_ = ((size_t)1ULL);
v___x_5020_ = lean_usize_sub(v___x_5018_, v___x_5019_);
v___x_5021_ = lean_usize_land(v___x_5017_, v___x_5020_);
v___x_5022_ = lean_array_uget_borrowed(v_x_5000_, v___x_5021_);
lean_inc(v___x_5022_);
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 2, v___x_5022_);
v___x_5024_ = v___x_5006_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_key_5002_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v_value_5003_);
lean_ctor_set(v_reuseFailAlloc_5027_, 2, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
lean_object* v___x_5025_; 
v___x_5025_ = lean_array_uset(v_x_5000_, v___x_5021_, v___x_5024_);
v_x_5000_ = v___x_5025_;
v_x_5001_ = v_tail_5004_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(lean_object* v_i_5031_, lean_object* v_source_5032_, lean_object* v_target_5033_){
_start:
{
lean_object* v___x_5034_; uint8_t v___x_5035_; 
v___x_5034_ = lean_array_get_size(v_source_5032_);
v___x_5035_ = lean_nat_dec_lt(v_i_5031_, v___x_5034_);
if (v___x_5035_ == 0)
{
lean_dec_ref(v_source_5032_);
lean_dec(v_i_5031_);
return v_target_5033_;
}
else
{
lean_object* v_es_5036_; lean_object* v___x_5037_; lean_object* v_source_5038_; lean_object* v_target_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v_es_5036_ = lean_array_fget(v_source_5032_, v_i_5031_);
v___x_5037_ = lean_box(0);
v_source_5038_ = lean_array_fset(v_source_5032_, v_i_5031_, v___x_5037_);
v_target_5039_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_target_5033_, v_es_5036_);
v___x_5040_ = lean_unsigned_to_nat(1u);
v___x_5041_ = lean_nat_add(v_i_5031_, v___x_5040_);
lean_dec(v_i_5031_);
v_i_5031_ = v___x_5041_;
v_source_5032_ = v_source_5038_;
v_target_5033_ = v_target_5039_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(lean_object* v_data_5043_){
_start:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v_nbuckets_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5044_ = lean_array_get_size(v_data_5043_);
v___x_5045_ = lean_unsigned_to_nat(2u);
v_nbuckets_5046_ = lean_nat_mul(v___x_5044_, v___x_5045_);
v___x_5047_ = lean_unsigned_to_nat(0u);
v___x_5048_ = lean_box(0);
v___x_5049_ = lean_mk_array(v_nbuckets_5046_, v___x_5048_);
v___x_5050_ = lean_array_propagate_mark(v_data_5043_, v___x_5049_);
v___x_5051_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v___x_5047_, v_data_5043_, v___x_5050_);
return v___x_5051_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(lean_object* v_a_5052_, lean_object* v_x_5053_){
_start:
{
if (lean_obj_tag(v_x_5053_) == 0)
{
uint8_t v___x_5054_; 
v___x_5054_ = 0;
return v___x_5054_;
}
else
{
lean_object* v_key_5055_; lean_object* v_tail_5056_; uint8_t v___x_5057_; 
v_key_5055_ = lean_ctor_get(v_x_5053_, 0);
v_tail_5056_ = lean_ctor_get(v_x_5053_, 2);
v___x_5057_ = lean_name_eq(v_key_5055_, v_a_5052_);
if (v___x_5057_ == 0)
{
v_x_5053_ = v_tail_5056_;
goto _start;
}
else
{
return v___x_5057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_5059_, lean_object* v_x_5060_){
_start:
{
uint8_t v_res_5061_; lean_object* v_r_5062_; 
v_res_5061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5059_, v_x_5060_);
lean_dec(v_x_5060_);
lean_dec(v_a_5059_);
v_r_5062_ = lean_box(v_res_5061_);
return v_r_5062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(lean_object* v_a_5063_, lean_object* v_m_5064_, lean_object* v_a_5065_){
_start:
{
lean_object* v___y_5067_; lean_object* v___y_5068_; size_t v___y_5069_; lean_object* v___y_5070_; lean_object* v_size_5073_; lean_object* v_buckets_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5121_; 
v_size_5073_ = lean_ctor_get(v_m_5064_, 0);
v_buckets_5074_ = lean_ctor_get(v_m_5064_, 1);
v_isSharedCheck_5121_ = !lean_is_exclusive(v_m_5064_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5076_ = v_m_5064_;
v_isShared_5077_ = v_isSharedCheck_5121_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_buckets_5074_);
lean_inc(v_size_5073_);
lean_dec(v_m_5064_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5121_;
goto v_resetjp_5075_;
}
v___jp_5066_:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5071_ = lean_array_uset(v___y_5068_, v___y_5069_, v___y_5067_);
v___x_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___y_5070_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
return v___x_5072_;
}
v_resetjp_5075_:
{
lean_object* v___x_5078_; uint64_t v___y_5080_; 
v___x_5078_ = lean_array_get_size(v_buckets_5074_);
if (lean_obj_tag(v_a_5065_) == 0)
{
uint64_t v___x_5119_; 
v___x_5119_ = 1723ULL;
v___y_5080_ = v___x_5119_;
goto v___jp_5079_;
}
else
{
uint64_t v_hash_5120_; 
v_hash_5120_ = lean_ctor_get_uint64(v_a_5065_, sizeof(void*)*2);
v___y_5080_ = v_hash_5120_;
goto v___jp_5079_;
}
v___jp_5079_:
{
uint64_t v___x_5081_; uint64_t v___x_5082_; uint64_t v_fold_5083_; uint64_t v___x_5084_; uint64_t v___x_5085_; uint64_t v___x_5086_; size_t v___x_5087_; size_t v___x_5088_; size_t v___x_5089_; size_t v___x_5090_; size_t v___x_5091_; lean_object* v_bkt_5092_; uint8_t v___x_5093_; 
v___x_5081_ = 32ULL;
v___x_5082_ = lean_uint64_shift_right(v___y_5080_, v___x_5081_);
v_fold_5083_ = lean_uint64_xor(v___y_5080_, v___x_5082_);
v___x_5084_ = 16ULL;
v___x_5085_ = lean_uint64_shift_right(v_fold_5083_, v___x_5084_);
v___x_5086_ = lean_uint64_xor(v_fold_5083_, v___x_5085_);
v___x_5087_ = lean_uint64_to_usize(v___x_5086_);
v___x_5088_ = lean_usize_of_nat(v___x_5078_);
v___x_5089_ = ((size_t)1ULL);
v___x_5090_ = lean_usize_sub(v___x_5088_, v___x_5089_);
v___x_5091_ = lean_usize_land(v___x_5087_, v___x_5090_);
v_bkt_5092_ = lean_array_uget_borrowed(v_buckets_5074_, v___x_5091_);
v___x_5093_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5065_, v_bkt_5092_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v_size_x27_5097_; lean_object* v___x_5098_; lean_object* v_buckets_x27_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; 
v___x_5094_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg___lam__0___closed__0));
v___x_5095_ = lean_array_push(v___x_5094_, v_a_5063_);
v___x_5096_ = lean_unsigned_to_nat(1u);
v_size_x27_5097_ = lean_nat_add(v_size_5073_, v___x_5096_);
lean_dec(v_size_5073_);
lean_inc(v_bkt_5092_);
v___x_5098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5098_, 0, v_a_5065_);
lean_ctor_set(v___x_5098_, 1, v___x_5095_);
lean_ctor_set(v___x_5098_, 2, v_bkt_5092_);
v_buckets_x27_5099_ = lean_array_uset(v_buckets_5074_, v___x_5091_, v___x_5098_);
v___x_5100_ = lean_unsigned_to_nat(4u);
v___x_5101_ = lean_nat_mul(v_size_x27_5097_, v___x_5100_);
v___x_5102_ = lean_unsigned_to_nat(3u);
v___x_5103_ = lean_nat_div(v___x_5101_, v___x_5102_);
lean_dec(v___x_5101_);
v___x_5104_ = lean_array_get_size(v_buckets_x27_5099_);
v___x_5105_ = lean_nat_dec_le(v___x_5103_, v___x_5104_);
lean_dec(v___x_5103_);
if (v___x_5105_ == 0)
{
lean_object* v_val_5106_; lean_object* v___x_5108_; 
v_val_5106_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_buckets_x27_5099_);
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 1, v_val_5106_);
lean_ctor_set(v___x_5076_, 0, v_size_x27_5097_);
v___x_5108_ = v___x_5076_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_size_x27_5097_);
lean_ctor_set(v_reuseFailAlloc_5109_, 1, v_val_5106_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
else
{
lean_object* v___x_5111_; 
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 1, v_buckets_x27_5099_);
lean_ctor_set(v___x_5076_, 0, v_size_x27_5097_);
v___x_5111_ = v___x_5076_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_size_x27_5097_);
lean_ctor_set(v_reuseFailAlloc_5112_, 1, v_buckets_x27_5099_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
}
else
{
lean_object* v___x_5113_; lean_object* v_buckets_x27_5114_; lean_object* v_bkt_x27_5115_; uint8_t v___x_5116_; 
lean_inc(v_bkt_5092_);
lean_del_object(v___x_5076_);
v___x_5113_ = lean_box(0);
v_buckets_x27_5114_ = lean_array_uset(v_buckets_5074_, v___x_5091_, v___x_5113_);
lean_inc(v_a_5065_);
v_bkt_x27_5115_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5063_, v_a_5065_, v_bkt_5092_);
v___x_5116_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5065_, v_bkt_x27_5115_);
lean_dec(v_a_5065_);
if (v___x_5116_ == 0)
{
lean_object* v___x_5117_; lean_object* v___x_5118_; 
v___x_5117_ = lean_unsigned_to_nat(1u);
v___x_5118_ = lean_nat_sub(v_size_5073_, v___x_5117_);
lean_dec(v_size_5073_);
v___y_5067_ = v_bkt_x27_5115_;
v___y_5068_ = v_buckets_x27_5114_;
v___y_5069_ = v___x_5091_;
v___y_5070_ = v___x_5118_;
goto v___jp_5066_;
}
else
{
v___y_5067_ = v_bkt_x27_5115_;
v___y_5068_ = v_buckets_x27_5114_;
v___y_5069_ = v___x_5091_;
v___y_5070_ = v_size_5073_;
goto v___jp_5066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(lean_object* v_key_5122_, lean_object* v_as_5123_, size_t v_sz_5124_, size_t v_i_5125_, lean_object* v_b_5126_){
_start:
{
uint8_t v___x_5127_; 
v___x_5127_ = lean_usize_dec_lt(v_i_5125_, v_sz_5124_);
if (v___x_5127_ == 0)
{
lean_dec_ref(v_key_5122_);
return v_b_5126_;
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; size_t v___x_5131_; size_t v___x_5132_; 
v_a_5128_ = lean_array_uget_borrowed(v_as_5123_, v_i_5125_);
lean_inc_ref(v_key_5122_);
lean_inc_n(v_a_5128_, 2);
v___x_5129_ = lean_apply_1(v_key_5122_, v_a_5128_);
v___x_5130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5128_, v_b_5126_, v___x_5129_);
v___x_5131_ = ((size_t)1ULL);
v___x_5132_ = lean_usize_add(v_i_5125_, v___x_5131_);
v_i_5125_ = v___x_5132_;
v_b_5126_ = v___x_5130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg___boxed(lean_object* v_key_5134_, lean_object* v_as_5135_, lean_object* v_sz_5136_, lean_object* v_i_5137_, lean_object* v_b_5138_){
_start:
{
size_t v_sz_boxed_5139_; size_t v_i_boxed_5140_; lean_object* v_res_5141_; 
v_sz_boxed_5139_ = lean_unbox_usize(v_sz_5136_);
lean_dec(v_sz_5136_);
v_i_boxed_5140_ = lean_unbox_usize(v_i_5137_);
lean_dec(v_i_5137_);
v_res_5141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5134_, v_as_5135_, v_sz_boxed_5139_, v_i_boxed_5140_, v_b_5138_);
lean_dec_ref(v_as_5135_);
return v_res_5141_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5142_ = lean_box(0);
v___x_5143_ = lean_unsigned_to_nat(16u);
v___x_5144_ = lean_mk_array(v___x_5143_, v___x_5142_);
return v___x_5144_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v_groups_5147_; 
v___x_5145_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__0);
v___x_5146_ = lean_unsigned_to_nat(0u);
v_groups_5147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5147_, 0, v___x_5146_);
lean_ctor_set(v_groups_5147_, 1, v___x_5145_);
return v_groups_5147_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(lean_object* v_key_5148_, lean_object* v_xs_5149_){
_start:
{
lean_object* v_groups_5150_; size_t v_sz_5151_; size_t v___x_5152_; lean_object* v___x_5153_; 
v_groups_5150_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___closed__1);
v_sz_5151_ = lean_array_size(v_xs_5149_);
v___x_5152_ = ((size_t)0ULL);
v___x_5153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5148_, v_xs_5149_, v_sz_5151_, v___x_5152_, v_groups_5150_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg___boxed(lean_object* v_key_5154_, lean_object* v_xs_5155_){
_start:
{
lean_object* v_res_5156_; 
v_res_5156_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5154_, v_xs_5155_);
lean_dec_ref(v_xs_5155_);
return v_res_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos(lean_object* v_infos_5158_){
_start:
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5160_ = lean_unsigned_to_nat(0u);
v___x_5161_ = lean_array_get_size(v_infos_5158_);
v___x_5162_ = l_Array_filterMapM___at___00Lean_Server_DirectImports_convertImportInfos_spec__0(v_infos_5158_, v___x_5160_, v___x_5161_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5187_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5187_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5187_ == 0)
{
v___x_5165_ = v___x_5162_;
v_isShared_5166_ = v_isSharedCheck_5187_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5162_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5187_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___y_5168_; lean_object* v___f_5177_; lean_object* v___x_5178_; lean_object* v_size_5179_; lean_object* v_buckets_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; 
v___f_5177_ = ((lean_object*)(l_Lean_Server_DirectImports_convertImportInfos___closed__0));
v___x_5178_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v___f_5177_, v_a_5163_);
v_size_5179_ = lean_ctor_get(v___x_5178_, 0);
lean_inc(v_size_5179_);
v_buckets_5180_ = lean_ctor_get(v___x_5178_, 1);
lean_inc_ref(v_buckets_5180_);
lean_dec_ref(v___x_5178_);
v___x_5181_ = lean_mk_empty_array_with_capacity(v_size_5179_);
lean_dec(v_size_5179_);
v___x_5182_ = lean_array_get_size(v_buckets_5180_);
v___x_5183_ = lean_nat_dec_lt(v___x_5160_, v___x_5182_);
if (v___x_5183_ == 0)
{
lean_dec_ref(v_buckets_5180_);
v___y_5168_ = v___x_5181_;
goto v___jp_5167_;
}
else
{
size_t v___x_5184_; size_t v___x_5185_; lean_object* v___x_5186_; 
v___x_5184_ = ((size_t)0ULL);
v___x_5185_ = lean_usize_of_nat(v___x_5182_);
v___x_5186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_DirectImports_convertImportInfos_spec__5(v_buckets_5180_, v___x_5184_, v___x_5185_, v___x_5181_);
lean_dec_ref(v_buckets_5180_);
v___y_5168_ = v___x_5186_;
goto v___jp_5167_;
}
v___jp_5167_:
{
lean_object* v_r_5169_; size_t v_sz_5170_; size_t v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5175_; 
v_r_5169_ = lean_box(1);
v_sz_5170_ = lean_array_size(v___y_5168_);
v___x_5171_ = ((size_t)0ULL);
v___x_5172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_DirectImports_convertImportInfos_spec__2(v___y_5168_, v_sz_5170_, v___x_5171_, v_r_5169_);
lean_dec_ref(v___y_5168_);
v___x_5173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5173_, 0, v_a_5163_);
lean_ctor_set(v___x_5173_, 1, v___x_5172_);
if (v_isShared_5166_ == 0)
{
lean_ctor_set(v___x_5165_, 0, v___x_5173_);
v___x_5175_ = v___x_5165_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5173_);
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
else
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
v_a_5188_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5190_ = v___x_5162_;
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5162_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5188_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DirectImports_convertImportInfos___boxed(lean_object* v_infos_5196_, lean_object* v_a_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Lean_Server_DirectImports_convertImportInfos(v_infos_5196_);
lean_dec_ref(v_infos_5196_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1(lean_object* v_00_u03b2_5199_, lean_object* v_k_5200_, lean_object* v_v_5201_, lean_object* v_t_5202_, lean_object* v_hl_5203_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_5200_, v_v_5201_, v_t_5202_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(lean_object* v_00_u03b2_5205_, lean_object* v_key_5206_, lean_object* v_xs_5207_){
_start:
{
lean_object* v___x_5208_; 
v___x_5208_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___redArg(v_key_5206_, v_xs_5207_);
return v___x_5208_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3___boxed(lean_object* v_00_u03b2_5209_, lean_object* v_key_5210_, lean_object* v_xs_5211_){
_start:
{
lean_object* v_res_5212_; 
v_res_5212_ = l_Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3(v_00_u03b2_5209_, v_key_5210_, v_xs_5211_);
lean_dec_ref(v_xs_5211_);
return v_res_5212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4(lean_object* v_00_u03b2_5213_, lean_object* v_a_5214_, lean_object* v_m_5215_, lean_object* v_a_5216_){
_start:
{
lean_object* v___x_5217_; 
v___x_5217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4___redArg(v_a_5214_, v_m_5215_, v_a_5216_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(lean_object* v_00_u03b2_5218_, lean_object* v_key_5219_, lean_object* v_as_5220_, size_t v_sz_5221_, size_t v_i_5222_, lean_object* v_b_5223_){
_start:
{
lean_object* v___x_5224_; 
v___x_5224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___redArg(v_key_5219_, v_as_5220_, v_sz_5221_, v_i_5222_, v_b_5223_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5225_, lean_object* v_key_5226_, lean_object* v_as_5227_, lean_object* v_sz_5228_, lean_object* v_i_5229_, lean_object* v_b_5230_){
_start:
{
size_t v_sz_boxed_5231_; size_t v_i_boxed_5232_; lean_object* v_res_5233_; 
v_sz_boxed_5231_ = lean_unbox_usize(v_sz_5228_);
lean_dec(v_sz_5228_);
v_i_boxed_5232_ = lean_unbox_usize(v_i_5229_);
lean_dec(v_i_5229_);
v_res_5233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__5(v_00_u03b2_5225_, v_key_5226_, v_as_5227_, v_sz_boxed_5231_, v_i_boxed_5232_, v_b_5230_);
lean_dec_ref(v_as_5227_);
return v_res_5233_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_5234_, lean_object* v_a_5235_, lean_object* v_x_5236_){
_start:
{
uint8_t v___x_5237_; 
v___x_5237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___redArg(v_a_5235_, v_x_5236_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_5238_, lean_object* v_a_5239_, lean_object* v_x_5240_){
_start:
{
uint8_t v_res_5241_; lean_object* v_r_5242_; 
v_res_5241_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__5(v_00_u03b2_5238_, v_a_5239_, v_x_5240_);
lean_dec(v_x_5240_);
lean_dec(v_a_5239_);
v_r_5242_ = lean_box(v_res_5241_);
return v_r_5242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_5243_, lean_object* v_data_5244_){
_start:
{
lean_object* v___x_5245_; 
v___x_5245_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6___redArg(v_data_5244_);
return v___x_5245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_x_5249_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__7___redArg(v_a_5247_, v_a_5248_, v_x_5249_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_5251_, lean_object* v_i_5252_, lean_object* v_source_5253_, lean_object* v_target_5254_){
_start:
{
lean_object* v___x_5255_; 
v___x_5255_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9___redArg(v_i_5252_, v_source_5253_, v_target_5254_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_5256_, lean_object* v_x_5257_, lean_object* v_x_5258_){
_start:
{
lean_object* v___x_5259_; 
v___x_5259_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Server_DirectImports_convertImportInfos_spec__3_spec__4_spec__6_spec__9_spec__11___redArg(v_x_5257_, v_x_5258_);
return v___x_5259_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_TransientWorkerILean_hasRefs(lean_object* v_i_5260_){
_start:
{
lean_object* v_isSetupFailure_x3f_5261_; 
v_isSetupFailure_x3f_5261_ = lean_ctor_get(v_i_5260_, 3);
if (lean_obj_tag(v_isSetupFailure_x3f_5261_) == 0)
{
uint8_t v___x_5262_; 
v___x_5262_ = 0;
return v___x_5262_;
}
else
{
lean_object* v_val_5263_; uint8_t v___x_5264_; 
v_val_5263_ = lean_ctor_get(v_isSetupFailure_x3f_5261_, 0);
v___x_5264_ = lean_unbox(v_val_5263_);
if (v___x_5264_ == 0)
{
uint8_t v___x_5265_; 
v___x_5265_ = 1;
return v___x_5265_;
}
else
{
uint8_t v___x_5266_; 
v___x_5266_ = 0;
return v___x_5266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_TransientWorkerILean_hasRefs___boxed(lean_object* v_i_5267_){
_start:
{
uint8_t v_res_5268_; lean_object* v_r_5269_; 
v_res_5268_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_i_5267_);
lean_dec_ref(v_i_5267_);
v_r_5269_ = lean_box(v_res_5268_);
return v_r_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean(lean_object* v_self_5275_, lean_object* v_path_5276_, lean_object* v_ilean_5277_){
_start:
{
lean_object* v_module_5279_; lean_object* v_directImports_5280_; lean_object* v_references_5281_; lean_object* v_decls_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5334_; 
v_module_5279_ = lean_ctor_get(v_ilean_5277_, 1);
v_directImports_5280_ = lean_ctor_get(v_ilean_5277_, 2);
v_references_5281_ = lean_ctor_get(v_ilean_5277_, 3);
v_decls_5282_ = lean_ctor_get(v_ilean_5277_, 4);
v_isSharedCheck_5334_ = !lean_is_exclusive(v_ilean_5277_);
if (v_isSharedCheck_5334_ == 0)
{
lean_object* v_unused_5335_; 
v_unused_5335_ = lean_ctor_get(v_ilean_5277_, 0);
lean_dec(v_unused_5335_);
v___x_5284_ = v_ilean_5277_;
v_isShared_5285_ = v_isSharedCheck_5334_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_decls_5282_);
lean_inc(v_references_5281_);
lean_inc(v_directImports_5280_);
lean_inc(v_module_5279_);
lean_dec(v_ilean_5277_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5334_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
lean_object* v___x_5286_; 
lean_inc(v_module_5279_);
v___x_5286_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5279_);
if (lean_obj_tag(v___x_5286_) == 0)
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5325_; 
v_a_5287_ = lean_ctor_get(v___x_5286_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5289_ = v___x_5286_;
v_isShared_5290_ = v_isSharedCheck_5325_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5286_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5325_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
if (lean_obj_tag(v_a_5287_) == 1)
{
lean_object* v_val_5291_; lean_object* v___x_5292_; 
lean_del_object(v___x_5289_);
v_val_5291_ = lean_ctor_get(v_a_5287_, 0);
lean_inc(v_val_5291_);
lean_dec_ref_known(v_a_5287_, 1);
v___x_5292_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_5280_);
lean_dec_ref(v_directImports_5280_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5313_; 
v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5295_ = v___x_5292_;
v_isShared_5296_ = v_isSharedCheck_5313_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5292_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5313_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v_ileans_5297_; lean_object* v_workers_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5312_; 
v_ileans_5297_ = lean_ctor_get(v_self_5275_, 0);
v_workers_5298_ = lean_ctor_get(v_self_5275_, 1);
v_isSharedCheck_5312_ = !lean_is_exclusive(v_self_5275_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5300_ = v_self_5275_;
v_isShared_5301_ = v_isSharedCheck_5312_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_workers_5298_);
lean_inc(v_ileans_5297_);
lean_dec(v_self_5275_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5312_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5285_ == 0)
{
lean_ctor_set(v___x_5284_, 2, v_a_5293_);
lean_ctor_set(v___x_5284_, 1, v_path_5276_);
lean_ctor_set(v___x_5284_, 0, v_val_5291_);
v___x_5303_ = v___x_5284_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_val_5291_);
lean_ctor_set(v_reuseFailAlloc_5311_, 1, v_path_5276_);
lean_ctor_set(v_reuseFailAlloc_5311_, 2, v_a_5293_);
lean_ctor_set(v_reuseFailAlloc_5311_, 3, v_references_5281_);
lean_ctor_set(v_reuseFailAlloc_5311_, 4, v_decls_5282_);
v___x_5303_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
lean_object* v___x_5304_; lean_object* v___x_5306_; 
v___x_5304_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_module_5279_, v___x_5303_, v_ileans_5297_);
if (v_isShared_5301_ == 0)
{
lean_ctor_set(v___x_5300_, 0, v___x_5304_);
v___x_5306_ = v___x_5300_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5304_);
lean_ctor_set(v_reuseFailAlloc_5310_, 1, v_workers_5298_);
v___x_5306_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
lean_object* v___x_5308_; 
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 0, v___x_5306_);
v___x_5308_ = v___x_5295_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v___x_5306_);
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
}
}
else
{
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5321_; 
lean_dec(v_val_5291_);
lean_del_object(v___x_5284_);
lean_dec(v_decls_5282_);
lean_dec(v_references_5281_);
lean_dec(v_module_5279_);
lean_dec_ref(v_path_5276_);
lean_dec_ref(v_self_5275_);
v_a_5314_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5316_ = v___x_5292_;
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v___x_5292_);
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
else
{
lean_object* v___x_5323_; 
lean_dec(v_a_5287_);
lean_del_object(v___x_5284_);
lean_dec(v_decls_5282_);
lean_dec(v_references_5281_);
lean_dec_ref(v_directImports_5280_);
lean_dec(v_module_5279_);
lean_dec_ref(v_path_5276_);
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 0, v_self_5275_);
v___x_5323_ = v___x_5289_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_self_5275_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
}
else
{
lean_object* v_a_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5333_; 
lean_del_object(v___x_5284_);
lean_dec(v_decls_5282_);
lean_dec(v_references_5281_);
lean_dec_ref(v_directImports_5280_);
lean_dec(v_module_5279_);
lean_dec_ref(v_path_5276_);
lean_dec_ref(v_self_5275_);
v_a_5326_ = lean_ctor_get(v___x_5286_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5328_ = v___x_5286_;
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_a_5326_);
lean_dec(v___x_5286_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
lean_object* v___x_5331_; 
if (v_isShared_5329_ == 0)
{
v___x_5331_ = v___x_5328_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_addIlean___boxed(lean_object* v_self_5336_, lean_object* v_path_5337_, lean_object* v_ilean_5338_, lean_object* v_a_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_Lean_Server_References_addIlean(v_self_5336_, v_path_5337_, v_ilean_5338_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(lean_object* v_path_5341_, lean_object* v_t_5342_){
_start:
{
if (lean_obj_tag(v_t_5342_) == 0)
{
lean_object* v_v_5343_; lean_object* v_k_5344_; lean_object* v_l_5345_; lean_object* v_r_5346_; lean_object* v_ileanPath_5347_; uint8_t v___x_5348_; 
v_v_5343_ = lean_ctor_get(v_t_5342_, 2);
lean_inc(v_v_5343_);
v_k_5344_ = lean_ctor_get(v_t_5342_, 1);
lean_inc(v_k_5344_);
v_l_5345_ = lean_ctor_get(v_t_5342_, 3);
lean_inc(v_l_5345_);
v_r_5346_ = lean_ctor_get(v_t_5342_, 4);
lean_inc(v_r_5346_);
lean_dec_ref_known(v_t_5342_, 5);
v_ileanPath_5347_ = lean_ctor_get(v_v_5343_, 1);
v___x_5348_ = lean_string_dec_eq(v_ileanPath_5347_, v_path_5341_);
if (v___x_5348_ == 0)
{
lean_object* v_impl_5349_; lean_object* v_impl_5350_; lean_object* v___x_5351_; 
lean_dec(v_k_5344_);
lean_dec(v_v_5343_);
v_impl_5349_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5341_, v_l_5345_);
v_impl_5350_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5341_, v_r_5346_);
v___x_5351_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_5349_, v_impl_5350_);
return v___x_5351_;
}
else
{
lean_object* v_impl_5352_; lean_object* v_impl_5353_; lean_object* v___x_5354_; 
v_impl_5352_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5341_, v_l_5345_);
v_impl_5353_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5341_, v_r_5346_);
v___x_5354_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_5344_, v_v_5343_, v_impl_5352_, v_impl_5353_);
return v___x_5354_;
}
}
else
{
return v_t_5342_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg___boxed(lean_object* v_path_5355_, lean_object* v_t_5356_){
_start:
{
lean_object* v_res_5357_; 
v_res_5357_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_5355_, v_t_5356_);
lean_dec_ref(v_path_5355_);
return v_res_5357_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(lean_object* v_k_5358_, lean_object* v_t_5359_){
_start:
{
if (lean_obj_tag(v_t_5359_) == 0)
{
lean_object* v_k_5360_; lean_object* v_v_5361_; lean_object* v_l_5362_; lean_object* v_r_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_6017_; 
v_k_5360_ = lean_ctor_get(v_t_5359_, 1);
v_v_5361_ = lean_ctor_get(v_t_5359_, 2);
v_l_5362_ = lean_ctor_get(v_t_5359_, 3);
v_r_5363_ = lean_ctor_get(v_t_5359_, 4);
v_isSharedCheck_6017_ = !lean_is_exclusive(v_t_5359_);
if (v_isSharedCheck_6017_ == 0)
{
lean_object* v_unused_6018_; 
v_unused_6018_ = lean_ctor_get(v_t_5359_, 0);
lean_dec(v_unused_6018_);
v___x_5365_ = v_t_5359_;
v_isShared_5366_ = v_isSharedCheck_6017_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_r_5363_);
lean_inc(v_l_5362_);
lean_inc(v_v_5361_);
lean_inc(v_k_5360_);
lean_dec(v_t_5359_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_6017_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
uint8_t v___x_5367_; 
v___x_5367_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5358_, v_k_5360_);
switch(v___x_5367_)
{
case 0:
{
lean_object* v_impl_5368_; lean_object* v___x_5369_; 
v_impl_5368_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5358_, v_l_5362_);
v___x_5369_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5368_) == 0)
{
if (lean_obj_tag(v_r_5363_) == 0)
{
lean_object* v_size_5370_; lean_object* v_size_5371_; lean_object* v_k_5372_; lean_object* v_v_5373_; lean_object* v_l_5374_; lean_object* v_r_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; uint8_t v___x_5378_; 
v_size_5370_ = lean_ctor_get(v_impl_5368_, 0);
lean_inc(v_size_5370_);
v_size_5371_ = lean_ctor_get(v_r_5363_, 0);
v_k_5372_ = lean_ctor_get(v_r_5363_, 1);
v_v_5373_ = lean_ctor_get(v_r_5363_, 2);
v_l_5374_ = lean_ctor_get(v_r_5363_, 3);
lean_inc(v_l_5374_);
v_r_5375_ = lean_ctor_get(v_r_5363_, 4);
v___x_5376_ = lean_unsigned_to_nat(3u);
v___x_5377_ = lean_nat_mul(v___x_5376_, v_size_5370_);
v___x_5378_ = lean_nat_dec_lt(v___x_5377_, v_size_5371_);
lean_dec(v___x_5377_);
if (v___x_5378_ == 0)
{
lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5382_; 
lean_dec(v_l_5374_);
v___x_5379_ = lean_nat_add(v___x_5369_, v_size_5370_);
lean_dec(v_size_5370_);
v___x_5380_ = lean_nat_add(v___x_5379_, v_size_5371_);
lean_dec(v___x_5379_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 3, v_impl_5368_);
lean_ctor_set(v___x_5365_, 0, v___x_5380_);
v___x_5382_ = v___x_5365_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5380_);
lean_ctor_set(v_reuseFailAlloc_5383_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5383_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5383_, 3, v_impl_5368_);
lean_ctor_set(v_reuseFailAlloc_5383_, 4, v_r_5363_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
else
{
lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5447_; 
lean_inc(v_r_5375_);
lean_inc(v_v_5373_);
lean_inc(v_k_5372_);
lean_inc(v_size_5371_);
v_isSharedCheck_5447_ = !lean_is_exclusive(v_r_5363_);
if (v_isSharedCheck_5447_ == 0)
{
lean_object* v_unused_5448_; lean_object* v_unused_5449_; lean_object* v_unused_5450_; lean_object* v_unused_5451_; lean_object* v_unused_5452_; 
v_unused_5448_ = lean_ctor_get(v_r_5363_, 4);
lean_dec(v_unused_5448_);
v_unused_5449_ = lean_ctor_get(v_r_5363_, 3);
lean_dec(v_unused_5449_);
v_unused_5450_ = lean_ctor_get(v_r_5363_, 2);
lean_dec(v_unused_5450_);
v_unused_5451_ = lean_ctor_get(v_r_5363_, 1);
lean_dec(v_unused_5451_);
v_unused_5452_ = lean_ctor_get(v_r_5363_, 0);
lean_dec(v_unused_5452_);
v___x_5385_ = v_r_5363_;
v_isShared_5386_ = v_isSharedCheck_5447_;
goto v_resetjp_5384_;
}
else
{
lean_dec(v_r_5363_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5447_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v_size_5387_; lean_object* v_k_5388_; lean_object* v_v_5389_; lean_object* v_l_5390_; lean_object* v_r_5391_; lean_object* v_size_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; uint8_t v___x_5395_; 
v_size_5387_ = lean_ctor_get(v_l_5374_, 0);
v_k_5388_ = lean_ctor_get(v_l_5374_, 1);
v_v_5389_ = lean_ctor_get(v_l_5374_, 2);
v_l_5390_ = lean_ctor_get(v_l_5374_, 3);
v_r_5391_ = lean_ctor_get(v_l_5374_, 4);
v_size_5392_ = lean_ctor_get(v_r_5375_, 0);
v___x_5393_ = lean_unsigned_to_nat(2u);
v___x_5394_ = lean_nat_mul(v___x_5393_, v_size_5392_);
v___x_5395_ = lean_nat_dec_lt(v_size_5387_, v___x_5394_);
lean_dec(v___x_5394_);
if (v___x_5395_ == 0)
{
lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5423_; 
lean_inc(v_r_5391_);
lean_inc(v_l_5390_);
lean_inc(v_v_5389_);
lean_inc(v_k_5388_);
v_isSharedCheck_5423_ = !lean_is_exclusive(v_l_5374_);
if (v_isSharedCheck_5423_ == 0)
{
lean_object* v_unused_5424_; lean_object* v_unused_5425_; lean_object* v_unused_5426_; lean_object* v_unused_5427_; lean_object* v_unused_5428_; 
v_unused_5424_ = lean_ctor_get(v_l_5374_, 4);
lean_dec(v_unused_5424_);
v_unused_5425_ = lean_ctor_get(v_l_5374_, 3);
lean_dec(v_unused_5425_);
v_unused_5426_ = lean_ctor_get(v_l_5374_, 2);
lean_dec(v_unused_5426_);
v_unused_5427_ = lean_ctor_get(v_l_5374_, 1);
lean_dec(v_unused_5427_);
v_unused_5428_ = lean_ctor_get(v_l_5374_, 0);
lean_dec(v_unused_5428_);
v___x_5397_ = v_l_5374_;
v_isShared_5398_ = v_isSharedCheck_5423_;
goto v_resetjp_5396_;
}
else
{
lean_dec(v_l_5374_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5423_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___y_5402_; lean_object* v___y_5403_; lean_object* v___y_5404_; lean_object* v___y_5413_; 
v___x_5399_ = lean_nat_add(v___x_5369_, v_size_5370_);
lean_dec(v_size_5370_);
v___x_5400_ = lean_nat_add(v___x_5399_, v_size_5371_);
lean_dec(v_size_5371_);
if (lean_obj_tag(v_l_5390_) == 0)
{
lean_object* v_size_5421_; 
v_size_5421_ = lean_ctor_get(v_l_5390_, 0);
lean_inc(v_size_5421_);
v___y_5413_ = v_size_5421_;
goto v___jp_5412_;
}
else
{
lean_object* v___x_5422_; 
v___x_5422_ = lean_unsigned_to_nat(0u);
v___y_5413_ = v___x_5422_;
goto v___jp_5412_;
}
v___jp_5401_:
{
lean_object* v___x_5405_; lean_object* v___x_5407_; 
v___x_5405_ = lean_nat_add(v___y_5402_, v___y_5404_);
lean_dec(v___y_5404_);
lean_dec(v___y_5402_);
if (v_isShared_5398_ == 0)
{
lean_ctor_set(v___x_5397_, 4, v_r_5375_);
lean_ctor_set(v___x_5397_, 3, v_r_5391_);
lean_ctor_set(v___x_5397_, 2, v_v_5373_);
lean_ctor_set(v___x_5397_, 1, v_k_5372_);
lean_ctor_set(v___x_5397_, 0, v___x_5405_);
v___x_5407_ = v___x_5397_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v___x_5405_);
lean_ctor_set(v_reuseFailAlloc_5411_, 1, v_k_5372_);
lean_ctor_set(v_reuseFailAlloc_5411_, 2, v_v_5373_);
lean_ctor_set(v_reuseFailAlloc_5411_, 3, v_r_5391_);
lean_ctor_set(v_reuseFailAlloc_5411_, 4, v_r_5375_);
v___x_5407_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
lean_object* v___x_5409_; 
if (v_isShared_5386_ == 0)
{
lean_ctor_set(v___x_5385_, 4, v___x_5407_);
lean_ctor_set(v___x_5385_, 3, v___y_5403_);
lean_ctor_set(v___x_5385_, 2, v_v_5389_);
lean_ctor_set(v___x_5385_, 1, v_k_5388_);
lean_ctor_set(v___x_5385_, 0, v___x_5400_);
v___x_5409_ = v___x_5385_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v___x_5400_);
lean_ctor_set(v_reuseFailAlloc_5410_, 1, v_k_5388_);
lean_ctor_set(v_reuseFailAlloc_5410_, 2, v_v_5389_);
lean_ctor_set(v_reuseFailAlloc_5410_, 3, v___y_5403_);
lean_ctor_set(v_reuseFailAlloc_5410_, 4, v___x_5407_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
v___jp_5412_:
{
lean_object* v___x_5414_; lean_object* v___x_5416_; 
v___x_5414_ = lean_nat_add(v___x_5399_, v___y_5413_);
lean_dec(v___y_5413_);
lean_dec(v___x_5399_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v_l_5390_);
lean_ctor_set(v___x_5365_, 3, v_impl_5368_);
lean_ctor_set(v___x_5365_, 0, v___x_5414_);
v___x_5416_ = v___x_5365_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v___x_5414_);
lean_ctor_set(v_reuseFailAlloc_5420_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5420_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5420_, 3, v_impl_5368_);
lean_ctor_set(v_reuseFailAlloc_5420_, 4, v_l_5390_);
v___x_5416_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
lean_object* v___x_5417_; 
v___x_5417_ = lean_nat_add(v___x_5369_, v_size_5392_);
if (lean_obj_tag(v_r_5391_) == 0)
{
lean_object* v_size_5418_; 
v_size_5418_ = lean_ctor_get(v_r_5391_, 0);
lean_inc(v_size_5418_);
v___y_5402_ = v___x_5417_;
v___y_5403_ = v___x_5416_;
v___y_5404_ = v_size_5418_;
goto v___jp_5401_;
}
else
{
lean_object* v___x_5419_; 
v___x_5419_ = lean_unsigned_to_nat(0u);
v___y_5402_ = v___x_5417_;
v___y_5403_ = v___x_5416_;
v___y_5404_ = v___x_5419_;
goto v___jp_5401_;
}
}
}
}
}
else
{
lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5433_; 
lean_del_object(v___x_5365_);
v___x_5429_ = lean_nat_add(v___x_5369_, v_size_5370_);
lean_dec(v_size_5370_);
v___x_5430_ = lean_nat_add(v___x_5429_, v_size_5371_);
lean_dec(v_size_5371_);
v___x_5431_ = lean_nat_add(v___x_5429_, v_size_5387_);
lean_dec(v___x_5429_);
lean_inc_ref(v_impl_5368_);
if (v_isShared_5386_ == 0)
{
lean_ctor_set(v___x_5385_, 4, v_l_5374_);
lean_ctor_set(v___x_5385_, 3, v_impl_5368_);
lean_ctor_set(v___x_5385_, 2, v_v_5361_);
lean_ctor_set(v___x_5385_, 1, v_k_5360_);
lean_ctor_set(v___x_5385_, 0, v___x_5431_);
v___x_5433_ = v___x_5385_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v___x_5431_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5446_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5446_, 3, v_impl_5368_);
lean_ctor_set(v_reuseFailAlloc_5446_, 4, v_l_5374_);
v___x_5433_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5440_; 
v_isSharedCheck_5440_ = !lean_is_exclusive(v_impl_5368_);
if (v_isSharedCheck_5440_ == 0)
{
lean_object* v_unused_5441_; lean_object* v_unused_5442_; lean_object* v_unused_5443_; lean_object* v_unused_5444_; lean_object* v_unused_5445_; 
v_unused_5441_ = lean_ctor_get(v_impl_5368_, 4);
lean_dec(v_unused_5441_);
v_unused_5442_ = lean_ctor_get(v_impl_5368_, 3);
lean_dec(v_unused_5442_);
v_unused_5443_ = lean_ctor_get(v_impl_5368_, 2);
lean_dec(v_unused_5443_);
v_unused_5444_ = lean_ctor_get(v_impl_5368_, 1);
lean_dec(v_unused_5444_);
v_unused_5445_ = lean_ctor_get(v_impl_5368_, 0);
lean_dec(v_unused_5445_);
v___x_5435_ = v_impl_5368_;
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
else
{
lean_dec(v_impl_5368_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5438_; 
if (v_isShared_5436_ == 0)
{
lean_ctor_set(v___x_5435_, 4, v_r_5375_);
lean_ctor_set(v___x_5435_, 3, v___x_5433_);
lean_ctor_set(v___x_5435_, 2, v_v_5373_);
lean_ctor_set(v___x_5435_, 1, v_k_5372_);
lean_ctor_set(v___x_5435_, 0, v___x_5430_);
v___x_5438_ = v___x_5435_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v___x_5430_);
lean_ctor_set(v_reuseFailAlloc_5439_, 1, v_k_5372_);
lean_ctor_set(v_reuseFailAlloc_5439_, 2, v_v_5373_);
lean_ctor_set(v_reuseFailAlloc_5439_, 3, v___x_5433_);
lean_ctor_set(v_reuseFailAlloc_5439_, 4, v_r_5375_);
v___x_5438_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
return v___x_5438_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5453_; lean_object* v___x_5454_; lean_object* v___x_5456_; 
v_size_5453_ = lean_ctor_get(v_impl_5368_, 0);
lean_inc(v_size_5453_);
v___x_5454_ = lean_nat_add(v___x_5369_, v_size_5453_);
lean_dec(v_size_5453_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 3, v_impl_5368_);
lean_ctor_set(v___x_5365_, 0, v___x_5454_);
v___x_5456_ = v___x_5365_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v___x_5454_);
lean_ctor_set(v_reuseFailAlloc_5457_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5457_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5457_, 3, v_impl_5368_);
lean_ctor_set(v_reuseFailAlloc_5457_, 4, v_r_5363_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
else
{
if (lean_obj_tag(v_r_5363_) == 0)
{
lean_object* v_l_5458_; 
v_l_5458_ = lean_ctor_get(v_r_5363_, 3);
lean_inc(v_l_5458_);
if (lean_obj_tag(v_l_5458_) == 0)
{
lean_object* v_r_5459_; 
v_r_5459_ = lean_ctor_get(v_r_5363_, 4);
lean_inc(v_r_5459_);
if (lean_obj_tag(v_r_5459_) == 0)
{
lean_object* v_size_5460_; lean_object* v_k_5461_; lean_object* v_v_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5475_; 
v_size_5460_ = lean_ctor_get(v_r_5363_, 0);
v_k_5461_ = lean_ctor_get(v_r_5363_, 1);
v_v_5462_ = lean_ctor_get(v_r_5363_, 2);
v_isSharedCheck_5475_ = !lean_is_exclusive(v_r_5363_);
if (v_isSharedCheck_5475_ == 0)
{
lean_object* v_unused_5476_; lean_object* v_unused_5477_; 
v_unused_5476_ = lean_ctor_get(v_r_5363_, 4);
lean_dec(v_unused_5476_);
v_unused_5477_ = lean_ctor_get(v_r_5363_, 3);
lean_dec(v_unused_5477_);
v___x_5464_ = v_r_5363_;
v_isShared_5465_ = v_isSharedCheck_5475_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_v_5462_);
lean_inc(v_k_5461_);
lean_inc(v_size_5460_);
lean_dec(v_r_5363_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5475_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v_size_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5470_; 
v_size_5466_ = lean_ctor_get(v_l_5458_, 0);
v___x_5467_ = lean_nat_add(v___x_5369_, v_size_5460_);
lean_dec(v_size_5460_);
v___x_5468_ = lean_nat_add(v___x_5369_, v_size_5466_);
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 4, v_l_5458_);
lean_ctor_set(v___x_5464_, 3, v_impl_5368_);
lean_ctor_set(v___x_5464_, 2, v_v_5361_);
lean_ctor_set(v___x_5464_, 1, v_k_5360_);
lean_ctor_set(v___x_5464_, 0, v___x_5468_);
v___x_5470_ = v___x_5464_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5468_);
lean_ctor_set(v_reuseFailAlloc_5474_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5474_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5474_, 3, v_impl_5368_);
lean_ctor_set(v_reuseFailAlloc_5474_, 4, v_l_5458_);
v___x_5470_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
lean_object* v___x_5472_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v_r_5459_);
lean_ctor_set(v___x_5365_, 3, v___x_5470_);
lean_ctor_set(v___x_5365_, 2, v_v_5462_);
lean_ctor_set(v___x_5365_, 1, v_k_5461_);
lean_ctor_set(v___x_5365_, 0, v___x_5467_);
v___x_5472_ = v___x_5365_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v___x_5467_);
lean_ctor_set(v_reuseFailAlloc_5473_, 1, v_k_5461_);
lean_ctor_set(v_reuseFailAlloc_5473_, 2, v_v_5462_);
lean_ctor_set(v_reuseFailAlloc_5473_, 3, v___x_5470_);
lean_ctor_set(v_reuseFailAlloc_5473_, 4, v_r_5459_);
v___x_5472_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
return v___x_5472_;
}
}
}
}
else
{
lean_object* v_k_5478_; lean_object* v_v_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5502_; 
v_k_5478_ = lean_ctor_get(v_r_5363_, 1);
v_v_5479_ = lean_ctor_get(v_r_5363_, 2);
v_isSharedCheck_5502_ = !lean_is_exclusive(v_r_5363_);
if (v_isSharedCheck_5502_ == 0)
{
lean_object* v_unused_5503_; lean_object* v_unused_5504_; lean_object* v_unused_5505_; 
v_unused_5503_ = lean_ctor_get(v_r_5363_, 4);
lean_dec(v_unused_5503_);
v_unused_5504_ = lean_ctor_get(v_r_5363_, 3);
lean_dec(v_unused_5504_);
v_unused_5505_ = lean_ctor_get(v_r_5363_, 0);
lean_dec(v_unused_5505_);
v___x_5481_ = v_r_5363_;
v_isShared_5482_ = v_isSharedCheck_5502_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_v_5479_);
lean_inc(v_k_5478_);
lean_dec(v_r_5363_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5502_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v_k_5483_; lean_object* v_v_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5498_; 
v_k_5483_ = lean_ctor_get(v_l_5458_, 1);
v_v_5484_ = lean_ctor_get(v_l_5458_, 2);
v_isSharedCheck_5498_ = !lean_is_exclusive(v_l_5458_);
if (v_isSharedCheck_5498_ == 0)
{
lean_object* v_unused_5499_; lean_object* v_unused_5500_; lean_object* v_unused_5501_; 
v_unused_5499_ = lean_ctor_get(v_l_5458_, 4);
lean_dec(v_unused_5499_);
v_unused_5500_ = lean_ctor_get(v_l_5458_, 3);
lean_dec(v_unused_5500_);
v_unused_5501_ = lean_ctor_get(v_l_5458_, 0);
lean_dec(v_unused_5501_);
v___x_5486_ = v_l_5458_;
v_isShared_5487_ = v_isSharedCheck_5498_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_v_5484_);
lean_inc(v_k_5483_);
lean_dec(v_l_5458_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5498_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5488_; lean_object* v___x_5490_; 
v___x_5488_ = lean_unsigned_to_nat(3u);
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 4, v_r_5459_);
lean_ctor_set(v___x_5486_, 3, v_r_5459_);
lean_ctor_set(v___x_5486_, 2, v_v_5361_);
lean_ctor_set(v___x_5486_, 1, v_k_5360_);
lean_ctor_set(v___x_5486_, 0, v___x_5369_);
v___x_5490_ = v___x_5486_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v___x_5369_);
lean_ctor_set(v_reuseFailAlloc_5497_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5497_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5497_, 3, v_r_5459_);
lean_ctor_set(v_reuseFailAlloc_5497_, 4, v_r_5459_);
v___x_5490_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5492_; 
if (v_isShared_5482_ == 0)
{
lean_ctor_set(v___x_5481_, 3, v_r_5459_);
lean_ctor_set(v___x_5481_, 0, v___x_5369_);
v___x_5492_ = v___x_5481_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5369_);
lean_ctor_set(v_reuseFailAlloc_5496_, 1, v_k_5478_);
lean_ctor_set(v_reuseFailAlloc_5496_, 2, v_v_5479_);
lean_ctor_set(v_reuseFailAlloc_5496_, 3, v_r_5459_);
lean_ctor_set(v_reuseFailAlloc_5496_, 4, v_r_5459_);
v___x_5492_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5494_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v___x_5492_);
lean_ctor_set(v___x_5365_, 3, v___x_5490_);
lean_ctor_set(v___x_5365_, 2, v_v_5484_);
lean_ctor_set(v___x_5365_, 1, v_k_5483_);
lean_ctor_set(v___x_5365_, 0, v___x_5488_);
v___x_5494_ = v___x_5365_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v___x_5488_);
lean_ctor_set(v_reuseFailAlloc_5495_, 1, v_k_5483_);
lean_ctor_set(v_reuseFailAlloc_5495_, 2, v_v_5484_);
lean_ctor_set(v_reuseFailAlloc_5495_, 3, v___x_5490_);
lean_ctor_set(v_reuseFailAlloc_5495_, 4, v___x_5492_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_5506_; 
v_r_5506_ = lean_ctor_get(v_r_5363_, 4);
lean_inc(v_r_5506_);
if (lean_obj_tag(v_r_5506_) == 0)
{
lean_object* v_k_5507_; lean_object* v_v_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5519_; 
v_k_5507_ = lean_ctor_get(v_r_5363_, 1);
v_v_5508_ = lean_ctor_get(v_r_5363_, 2);
v_isSharedCheck_5519_ = !lean_is_exclusive(v_r_5363_);
if (v_isSharedCheck_5519_ == 0)
{
lean_object* v_unused_5520_; lean_object* v_unused_5521_; lean_object* v_unused_5522_; 
v_unused_5520_ = lean_ctor_get(v_r_5363_, 4);
lean_dec(v_unused_5520_);
v_unused_5521_ = lean_ctor_get(v_r_5363_, 3);
lean_dec(v_unused_5521_);
v_unused_5522_ = lean_ctor_get(v_r_5363_, 0);
lean_dec(v_unused_5522_);
v___x_5510_ = v_r_5363_;
v_isShared_5511_ = v_isSharedCheck_5519_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_v_5508_);
lean_inc(v_k_5507_);
lean_dec(v_r_5363_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5519_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5512_; lean_object* v___x_5514_; 
v___x_5512_ = lean_unsigned_to_nat(3u);
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 4, v_l_5458_);
lean_ctor_set(v___x_5510_, 2, v_v_5361_);
lean_ctor_set(v___x_5510_, 1, v_k_5360_);
lean_ctor_set(v___x_5510_, 0, v___x_5369_);
v___x_5514_ = v___x_5510_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5369_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5518_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5518_, 3, v_l_5458_);
lean_ctor_set(v_reuseFailAlloc_5518_, 4, v_l_5458_);
v___x_5514_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5516_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v_r_5506_);
lean_ctor_set(v___x_5365_, 3, v___x_5514_);
lean_ctor_set(v___x_5365_, 2, v_v_5508_);
lean_ctor_set(v___x_5365_, 1, v_k_5507_);
lean_ctor_set(v___x_5365_, 0, v___x_5512_);
v___x_5516_ = v___x_5365_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v___x_5512_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v_k_5507_);
lean_ctor_set(v_reuseFailAlloc_5517_, 2, v_v_5508_);
lean_ctor_set(v_reuseFailAlloc_5517_, 3, v___x_5514_);
lean_ctor_set(v_reuseFailAlloc_5517_, 4, v_r_5506_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
}
else
{
lean_object* v_size_5523_; lean_object* v_k_5524_; lean_object* v_v_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5536_; 
v_size_5523_ = lean_ctor_get(v_r_5363_, 0);
v_k_5524_ = lean_ctor_get(v_r_5363_, 1);
v_v_5525_ = lean_ctor_get(v_r_5363_, 2);
v_isSharedCheck_5536_ = !lean_is_exclusive(v_r_5363_);
if (v_isSharedCheck_5536_ == 0)
{
lean_object* v_unused_5537_; lean_object* v_unused_5538_; 
v_unused_5537_ = lean_ctor_get(v_r_5363_, 4);
lean_dec(v_unused_5537_);
v_unused_5538_ = lean_ctor_get(v_r_5363_, 3);
lean_dec(v_unused_5538_);
v___x_5527_ = v_r_5363_;
v_isShared_5528_ = v_isSharedCheck_5536_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_v_5525_);
lean_inc(v_k_5524_);
lean_inc(v_size_5523_);
lean_dec(v_r_5363_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5536_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5530_; 
if (v_isShared_5528_ == 0)
{
lean_ctor_set(v___x_5527_, 3, v_r_5506_);
v___x_5530_ = v___x_5527_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5535_; 
v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_size_5523_);
lean_ctor_set(v_reuseFailAlloc_5535_, 1, v_k_5524_);
lean_ctor_set(v_reuseFailAlloc_5535_, 2, v_v_5525_);
lean_ctor_set(v_reuseFailAlloc_5535_, 3, v_r_5506_);
lean_ctor_set(v_reuseFailAlloc_5535_, 4, v_r_5506_);
v___x_5530_ = v_reuseFailAlloc_5535_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
lean_object* v___x_5531_; lean_object* v___x_5533_; 
v___x_5531_ = lean_unsigned_to_nat(2u);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v___x_5530_);
lean_ctor_set(v___x_5365_, 3, v_r_5506_);
lean_ctor_set(v___x_5365_, 0, v___x_5531_);
v___x_5533_ = v___x_5365_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v___x_5531_);
lean_ctor_set(v_reuseFailAlloc_5534_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5534_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5534_, 3, v_r_5506_);
lean_ctor_set(v_reuseFailAlloc_5534_, 4, v___x_5530_);
v___x_5533_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
return v___x_5533_;
}
}
}
}
}
}
else
{
lean_object* v___x_5540_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 3, v_r_5363_);
lean_ctor_set(v___x_5365_, 0, v___x_5369_);
v___x_5540_ = v___x_5365_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v___x_5369_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5541_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5541_, 3, v_r_5363_);
lean_ctor_set(v_reuseFailAlloc_5541_, 4, v_r_5363_);
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
case 1:
{
lean_del_object(v___x_5365_);
lean_dec(v_v_5361_);
lean_dec(v_k_5360_);
if (lean_obj_tag(v_l_5362_) == 0)
{
if (lean_obj_tag(v_r_5363_) == 0)
{
lean_object* v_size_5542_; lean_object* v_k_5543_; lean_object* v_v_5544_; lean_object* v_l_5545_; lean_object* v_r_5546_; lean_object* v_size_5547_; lean_object* v_k_5548_; lean_object* v_v_5549_; lean_object* v_l_5550_; lean_object* v_r_5551_; lean_object* v___x_5552_; uint8_t v___x_5553_; 
v_size_5542_ = lean_ctor_get(v_l_5362_, 0);
v_k_5543_ = lean_ctor_get(v_l_5362_, 1);
v_v_5544_ = lean_ctor_get(v_l_5362_, 2);
v_l_5545_ = lean_ctor_get(v_l_5362_, 3);
v_r_5546_ = lean_ctor_get(v_l_5362_, 4);
lean_inc(v_r_5546_);
v_size_5547_ = lean_ctor_get(v_r_5363_, 0);
v_k_5548_ = lean_ctor_get(v_r_5363_, 1);
v_v_5549_ = lean_ctor_get(v_r_5363_, 2);
v_l_5550_ = lean_ctor_get(v_r_5363_, 3);
lean_inc(v_l_5550_);
v_r_5551_ = lean_ctor_get(v_r_5363_, 4);
v___x_5552_ = lean_unsigned_to_nat(1u);
v___x_5553_ = lean_nat_dec_lt(v_size_5542_, v_size_5547_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5689_; 
lean_inc(v_l_5545_);
lean_inc(v_v_5544_);
lean_inc(v_k_5543_);
v_isSharedCheck_5689_ = !lean_is_exclusive(v_l_5362_);
if (v_isSharedCheck_5689_ == 0)
{
lean_object* v_unused_5690_; lean_object* v_unused_5691_; lean_object* v_unused_5692_; lean_object* v_unused_5693_; lean_object* v_unused_5694_; 
v_unused_5690_ = lean_ctor_get(v_l_5362_, 4);
lean_dec(v_unused_5690_);
v_unused_5691_ = lean_ctor_get(v_l_5362_, 3);
lean_dec(v_unused_5691_);
v_unused_5692_ = lean_ctor_get(v_l_5362_, 2);
lean_dec(v_unused_5692_);
v_unused_5693_ = lean_ctor_get(v_l_5362_, 1);
lean_dec(v_unused_5693_);
v_unused_5694_ = lean_ctor_get(v_l_5362_, 0);
lean_dec(v_unused_5694_);
v___x_5555_ = v_l_5362_;
v_isShared_5556_ = v_isSharedCheck_5689_;
goto v_resetjp_5554_;
}
else
{
lean_dec(v_l_5362_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5689_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5557_; lean_object* v_tree_5558_; 
v___x_5557_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_5543_, v_v_5544_, v_l_5545_, v_r_5546_);
v_tree_5558_ = lean_ctor_get(v___x_5557_, 2);
lean_inc(v_tree_5558_);
if (lean_obj_tag(v_tree_5558_) == 0)
{
lean_object* v_k_5559_; lean_object* v_v_5560_; lean_object* v_size_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; uint8_t v___x_5564_; 
v_k_5559_ = lean_ctor_get(v___x_5557_, 0);
lean_inc(v_k_5559_);
v_v_5560_ = lean_ctor_get(v___x_5557_, 1);
lean_inc(v_v_5560_);
lean_dec_ref(v___x_5557_);
v_size_5561_ = lean_ctor_get(v_tree_5558_, 0);
v___x_5562_ = lean_unsigned_to_nat(3u);
v___x_5563_ = lean_nat_mul(v___x_5562_, v_size_5561_);
v___x_5564_ = lean_nat_dec_lt(v___x_5563_, v_size_5547_);
lean_dec(v___x_5563_);
if (v___x_5564_ == 0)
{
lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5568_; 
lean_dec(v_l_5550_);
v___x_5565_ = lean_nat_add(v___x_5552_, v_size_5561_);
v___x_5566_ = lean_nat_add(v___x_5565_, v_size_5547_);
lean_dec(v___x_5565_);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v_r_5363_);
lean_ctor_set(v___x_5555_, 3, v_tree_5558_);
lean_ctor_set(v___x_5555_, 2, v_v_5560_);
lean_ctor_set(v___x_5555_, 1, v_k_5559_);
lean_ctor_set(v___x_5555_, 0, v___x_5566_);
v___x_5568_ = v___x_5555_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v___x_5566_);
lean_ctor_set(v_reuseFailAlloc_5569_, 1, v_k_5559_);
lean_ctor_set(v_reuseFailAlloc_5569_, 2, v_v_5560_);
lean_ctor_set(v_reuseFailAlloc_5569_, 3, v_tree_5558_);
lean_ctor_set(v_reuseFailAlloc_5569_, 4, v_r_5363_);
v___x_5568_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
return v___x_5568_;
}
}
else
{
lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5624_; 
lean_inc(v_r_5551_);
lean_inc(v_v_5549_);
lean_inc(v_k_5548_);
lean_inc(v_size_5547_);
v_isSharedCheck_5624_ = !lean_is_exclusive(v_r_5363_);
if (v_isSharedCheck_5624_ == 0)
{
lean_object* v_unused_5625_; lean_object* v_unused_5626_; lean_object* v_unused_5627_; lean_object* v_unused_5628_; lean_object* v_unused_5629_; 
v_unused_5625_ = lean_ctor_get(v_r_5363_, 4);
lean_dec(v_unused_5625_);
v_unused_5626_ = lean_ctor_get(v_r_5363_, 3);
lean_dec(v_unused_5626_);
v_unused_5627_ = lean_ctor_get(v_r_5363_, 2);
lean_dec(v_unused_5627_);
v_unused_5628_ = lean_ctor_get(v_r_5363_, 1);
lean_dec(v_unused_5628_);
v_unused_5629_ = lean_ctor_get(v_r_5363_, 0);
lean_dec(v_unused_5629_);
v___x_5571_ = v_r_5363_;
v_isShared_5572_ = v_isSharedCheck_5624_;
goto v_resetjp_5570_;
}
else
{
lean_dec(v_r_5363_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5624_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v_size_5573_; lean_object* v_k_5574_; lean_object* v_v_5575_; lean_object* v_l_5576_; lean_object* v_r_5577_; lean_object* v_size_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; uint8_t v___x_5581_; 
v_size_5573_ = lean_ctor_get(v_l_5550_, 0);
v_k_5574_ = lean_ctor_get(v_l_5550_, 1);
v_v_5575_ = lean_ctor_get(v_l_5550_, 2);
v_l_5576_ = lean_ctor_get(v_l_5550_, 3);
v_r_5577_ = lean_ctor_get(v_l_5550_, 4);
v_size_5578_ = lean_ctor_get(v_r_5551_, 0);
v___x_5579_ = lean_unsigned_to_nat(2u);
v___x_5580_ = lean_nat_mul(v___x_5579_, v_size_5578_);
v___x_5581_ = lean_nat_dec_lt(v_size_5573_, v___x_5580_);
lean_dec(v___x_5580_);
if (v___x_5581_ == 0)
{
lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5609_; 
lean_inc(v_r_5577_);
lean_inc(v_l_5576_);
lean_inc(v_v_5575_);
lean_inc(v_k_5574_);
v_isSharedCheck_5609_ = !lean_is_exclusive(v_l_5550_);
if (v_isSharedCheck_5609_ == 0)
{
lean_object* v_unused_5610_; lean_object* v_unused_5611_; lean_object* v_unused_5612_; lean_object* v_unused_5613_; lean_object* v_unused_5614_; 
v_unused_5610_ = lean_ctor_get(v_l_5550_, 4);
lean_dec(v_unused_5610_);
v_unused_5611_ = lean_ctor_get(v_l_5550_, 3);
lean_dec(v_unused_5611_);
v_unused_5612_ = lean_ctor_get(v_l_5550_, 2);
lean_dec(v_unused_5612_);
v_unused_5613_ = lean_ctor_get(v_l_5550_, 1);
lean_dec(v_unused_5613_);
v_unused_5614_ = lean_ctor_get(v_l_5550_, 0);
lean_dec(v_unused_5614_);
v___x_5583_ = v_l_5550_;
v_isShared_5584_ = v_isSharedCheck_5609_;
goto v_resetjp_5582_;
}
else
{
lean_dec(v_l_5550_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5609_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5599_; 
v___x_5585_ = lean_nat_add(v___x_5552_, v_size_5561_);
v___x_5586_ = lean_nat_add(v___x_5585_, v_size_5547_);
lean_dec(v_size_5547_);
if (lean_obj_tag(v_l_5576_) == 0)
{
lean_object* v_size_5607_; 
v_size_5607_ = lean_ctor_get(v_l_5576_, 0);
lean_inc(v_size_5607_);
v___y_5599_ = v_size_5607_;
goto v___jp_5598_;
}
else
{
lean_object* v___x_5608_; 
v___x_5608_ = lean_unsigned_to_nat(0u);
v___y_5599_ = v___x_5608_;
goto v___jp_5598_;
}
v___jp_5587_:
{
lean_object* v___x_5591_; lean_object* v___x_5593_; 
v___x_5591_ = lean_nat_add(v___y_5588_, v___y_5590_);
lean_dec(v___y_5590_);
lean_dec(v___y_5588_);
if (v_isShared_5584_ == 0)
{
lean_ctor_set(v___x_5583_, 4, v_r_5551_);
lean_ctor_set(v___x_5583_, 3, v_r_5577_);
lean_ctor_set(v___x_5583_, 2, v_v_5549_);
lean_ctor_set(v___x_5583_, 1, v_k_5548_);
lean_ctor_set(v___x_5583_, 0, v___x_5591_);
v___x_5593_ = v___x_5583_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v___x_5591_);
lean_ctor_set(v_reuseFailAlloc_5597_, 1, v_k_5548_);
lean_ctor_set(v_reuseFailAlloc_5597_, 2, v_v_5549_);
lean_ctor_set(v_reuseFailAlloc_5597_, 3, v_r_5577_);
lean_ctor_set(v_reuseFailAlloc_5597_, 4, v_r_5551_);
v___x_5593_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
lean_object* v___x_5595_; 
if (v_isShared_5572_ == 0)
{
lean_ctor_set(v___x_5571_, 4, v___x_5593_);
lean_ctor_set(v___x_5571_, 3, v___y_5589_);
lean_ctor_set(v___x_5571_, 2, v_v_5575_);
lean_ctor_set(v___x_5571_, 1, v_k_5574_);
lean_ctor_set(v___x_5571_, 0, v___x_5586_);
v___x_5595_ = v___x_5571_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5586_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_k_5574_);
lean_ctor_set(v_reuseFailAlloc_5596_, 2, v_v_5575_);
lean_ctor_set(v_reuseFailAlloc_5596_, 3, v___y_5589_);
lean_ctor_set(v_reuseFailAlloc_5596_, 4, v___x_5593_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
v___jp_5598_:
{
lean_object* v___x_5600_; lean_object* v___x_5602_; 
v___x_5600_ = lean_nat_add(v___x_5585_, v___y_5599_);
lean_dec(v___y_5599_);
lean_dec(v___x_5585_);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v_l_5576_);
lean_ctor_set(v___x_5555_, 3, v_tree_5558_);
lean_ctor_set(v___x_5555_, 2, v_v_5560_);
lean_ctor_set(v___x_5555_, 1, v_k_5559_);
lean_ctor_set(v___x_5555_, 0, v___x_5600_);
v___x_5602_ = v___x_5555_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v___x_5600_);
lean_ctor_set(v_reuseFailAlloc_5606_, 1, v_k_5559_);
lean_ctor_set(v_reuseFailAlloc_5606_, 2, v_v_5560_);
lean_ctor_set(v_reuseFailAlloc_5606_, 3, v_tree_5558_);
lean_ctor_set(v_reuseFailAlloc_5606_, 4, v_l_5576_);
v___x_5602_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
lean_object* v___x_5603_; 
v___x_5603_ = lean_nat_add(v___x_5552_, v_size_5578_);
if (lean_obj_tag(v_r_5577_) == 0)
{
lean_object* v_size_5604_; 
v_size_5604_ = lean_ctor_get(v_r_5577_, 0);
lean_inc(v_size_5604_);
v___y_5588_ = v___x_5603_;
v___y_5589_ = v___x_5602_;
v___y_5590_ = v_size_5604_;
goto v___jp_5587_;
}
else
{
lean_object* v___x_5605_; 
v___x_5605_ = lean_unsigned_to_nat(0u);
v___y_5588_ = v___x_5603_;
v___y_5589_ = v___x_5602_;
v___y_5590_ = v___x_5605_;
goto v___jp_5587_;
}
}
}
}
}
else
{
lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5619_; 
v___x_5615_ = lean_nat_add(v___x_5552_, v_size_5561_);
v___x_5616_ = lean_nat_add(v___x_5615_, v_size_5547_);
lean_dec(v_size_5547_);
v___x_5617_ = lean_nat_add(v___x_5615_, v_size_5573_);
lean_dec(v___x_5615_);
if (v_isShared_5572_ == 0)
{
lean_ctor_set(v___x_5571_, 4, v_l_5550_);
lean_ctor_set(v___x_5571_, 3, v_tree_5558_);
lean_ctor_set(v___x_5571_, 2, v_v_5560_);
lean_ctor_set(v___x_5571_, 1, v_k_5559_);
lean_ctor_set(v___x_5571_, 0, v___x_5617_);
v___x_5619_ = v___x_5571_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5617_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v_k_5559_);
lean_ctor_set(v_reuseFailAlloc_5623_, 2, v_v_5560_);
lean_ctor_set(v_reuseFailAlloc_5623_, 3, v_tree_5558_);
lean_ctor_set(v_reuseFailAlloc_5623_, 4, v_l_5550_);
v___x_5619_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
lean_object* v___x_5621_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v_r_5551_);
lean_ctor_set(v___x_5555_, 3, v___x_5619_);
lean_ctor_set(v___x_5555_, 2, v_v_5549_);
lean_ctor_set(v___x_5555_, 1, v_k_5548_);
lean_ctor_set(v___x_5555_, 0, v___x_5616_);
v___x_5621_ = v___x_5555_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5616_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v_k_5548_);
lean_ctor_set(v_reuseFailAlloc_5622_, 2, v_v_5549_);
lean_ctor_set(v_reuseFailAlloc_5622_, 3, v___x_5619_);
lean_ctor_set(v_reuseFailAlloc_5622_, 4, v_r_5551_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
}
}
else
{
lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5683_; 
lean_inc(v_r_5551_);
lean_inc(v_v_5549_);
lean_inc(v_k_5548_);
lean_inc(v_size_5547_);
v_isSharedCheck_5683_ = !lean_is_exclusive(v_r_5363_);
if (v_isSharedCheck_5683_ == 0)
{
lean_object* v_unused_5684_; lean_object* v_unused_5685_; lean_object* v_unused_5686_; lean_object* v_unused_5687_; lean_object* v_unused_5688_; 
v_unused_5684_ = lean_ctor_get(v_r_5363_, 4);
lean_dec(v_unused_5684_);
v_unused_5685_ = lean_ctor_get(v_r_5363_, 3);
lean_dec(v_unused_5685_);
v_unused_5686_ = lean_ctor_get(v_r_5363_, 2);
lean_dec(v_unused_5686_);
v_unused_5687_ = lean_ctor_get(v_r_5363_, 1);
lean_dec(v_unused_5687_);
v_unused_5688_ = lean_ctor_get(v_r_5363_, 0);
lean_dec(v_unused_5688_);
v___x_5631_ = v_r_5363_;
v_isShared_5632_ = v_isSharedCheck_5683_;
goto v_resetjp_5630_;
}
else
{
lean_dec(v_r_5363_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5683_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
if (lean_obj_tag(v_l_5550_) == 0)
{
if (lean_obj_tag(v_r_5551_) == 0)
{
lean_object* v_k_5633_; lean_object* v_v_5634_; lean_object* v_size_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5639_; 
v_k_5633_ = lean_ctor_get(v___x_5557_, 0);
lean_inc(v_k_5633_);
v_v_5634_ = lean_ctor_get(v___x_5557_, 1);
lean_inc(v_v_5634_);
lean_dec_ref(v___x_5557_);
v_size_5635_ = lean_ctor_get(v_l_5550_, 0);
v___x_5636_ = lean_nat_add(v___x_5552_, v_size_5547_);
lean_dec(v_size_5547_);
v___x_5637_ = lean_nat_add(v___x_5552_, v_size_5635_);
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 4, v_l_5550_);
lean_ctor_set(v___x_5631_, 3, v_tree_5558_);
lean_ctor_set(v___x_5631_, 2, v_v_5634_);
lean_ctor_set(v___x_5631_, 1, v_k_5633_);
lean_ctor_set(v___x_5631_, 0, v___x_5637_);
v___x_5639_ = v___x_5631_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v___x_5637_);
lean_ctor_set(v_reuseFailAlloc_5643_, 1, v_k_5633_);
lean_ctor_set(v_reuseFailAlloc_5643_, 2, v_v_5634_);
lean_ctor_set(v_reuseFailAlloc_5643_, 3, v_tree_5558_);
lean_ctor_set(v_reuseFailAlloc_5643_, 4, v_l_5550_);
v___x_5639_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
lean_object* v___x_5641_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v_r_5551_);
lean_ctor_set(v___x_5555_, 3, v___x_5639_);
lean_ctor_set(v___x_5555_, 2, v_v_5549_);
lean_ctor_set(v___x_5555_, 1, v_k_5548_);
lean_ctor_set(v___x_5555_, 0, v___x_5636_);
v___x_5641_ = v___x_5555_;
goto v_reusejp_5640_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v___x_5636_);
lean_ctor_set(v_reuseFailAlloc_5642_, 1, v_k_5548_);
lean_ctor_set(v_reuseFailAlloc_5642_, 2, v_v_5549_);
lean_ctor_set(v_reuseFailAlloc_5642_, 3, v___x_5639_);
lean_ctor_set(v_reuseFailAlloc_5642_, 4, v_r_5551_);
v___x_5641_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5640_;
}
v_reusejp_5640_:
{
return v___x_5641_;
}
}
}
else
{
lean_object* v_k_5644_; lean_object* v_v_5645_; lean_object* v_k_5646_; lean_object* v_v_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5661_; 
lean_dec(v_size_5547_);
v_k_5644_ = lean_ctor_get(v___x_5557_, 0);
lean_inc(v_k_5644_);
v_v_5645_ = lean_ctor_get(v___x_5557_, 1);
lean_inc(v_v_5645_);
lean_dec_ref(v___x_5557_);
v_k_5646_ = lean_ctor_get(v_l_5550_, 1);
v_v_5647_ = lean_ctor_get(v_l_5550_, 2);
v_isSharedCheck_5661_ = !lean_is_exclusive(v_l_5550_);
if (v_isSharedCheck_5661_ == 0)
{
lean_object* v_unused_5662_; lean_object* v_unused_5663_; lean_object* v_unused_5664_; 
v_unused_5662_ = lean_ctor_get(v_l_5550_, 4);
lean_dec(v_unused_5662_);
v_unused_5663_ = lean_ctor_get(v_l_5550_, 3);
lean_dec(v_unused_5663_);
v_unused_5664_ = lean_ctor_get(v_l_5550_, 0);
lean_dec(v_unused_5664_);
v___x_5649_ = v_l_5550_;
v_isShared_5650_ = v_isSharedCheck_5661_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_v_5647_);
lean_inc(v_k_5646_);
lean_dec(v_l_5550_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5661_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5651_; lean_object* v___x_5653_; 
v___x_5651_ = lean_unsigned_to_nat(3u);
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 4, v_r_5551_);
lean_ctor_set(v___x_5649_, 3, v_r_5551_);
lean_ctor_set(v___x_5649_, 2, v_v_5645_);
lean_ctor_set(v___x_5649_, 1, v_k_5644_);
lean_ctor_set(v___x_5649_, 0, v___x_5552_);
v___x_5653_ = v___x_5649_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v_k_5644_);
lean_ctor_set(v_reuseFailAlloc_5660_, 2, v_v_5645_);
lean_ctor_set(v_reuseFailAlloc_5660_, 3, v_r_5551_);
lean_ctor_set(v_reuseFailAlloc_5660_, 4, v_r_5551_);
v___x_5653_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
lean_object* v___x_5655_; 
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 3, v_r_5551_);
lean_ctor_set(v___x_5631_, 0, v___x_5552_);
v___x_5655_ = v___x_5631_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5659_, 1, v_k_5548_);
lean_ctor_set(v_reuseFailAlloc_5659_, 2, v_v_5549_);
lean_ctor_set(v_reuseFailAlloc_5659_, 3, v_r_5551_);
lean_ctor_set(v_reuseFailAlloc_5659_, 4, v_r_5551_);
v___x_5655_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
lean_object* v___x_5657_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v___x_5655_);
lean_ctor_set(v___x_5555_, 3, v___x_5653_);
lean_ctor_set(v___x_5555_, 2, v_v_5647_);
lean_ctor_set(v___x_5555_, 1, v_k_5646_);
lean_ctor_set(v___x_5555_, 0, v___x_5651_);
v___x_5657_ = v___x_5555_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v___x_5651_);
lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_k_5646_);
lean_ctor_set(v_reuseFailAlloc_5658_, 2, v_v_5647_);
lean_ctor_set(v_reuseFailAlloc_5658_, 3, v___x_5653_);
lean_ctor_set(v_reuseFailAlloc_5658_, 4, v___x_5655_);
v___x_5657_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
return v___x_5657_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_5551_) == 0)
{
lean_object* v_k_5665_; lean_object* v_v_5666_; lean_object* v___x_5667_; lean_object* v___x_5669_; 
lean_dec(v_size_5547_);
v_k_5665_ = lean_ctor_get(v___x_5557_, 0);
lean_inc(v_k_5665_);
v_v_5666_ = lean_ctor_get(v___x_5557_, 1);
lean_inc(v_v_5666_);
lean_dec_ref(v___x_5557_);
v___x_5667_ = lean_unsigned_to_nat(3u);
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 4, v_l_5550_);
lean_ctor_set(v___x_5631_, 2, v_v_5666_);
lean_ctor_set(v___x_5631_, 1, v_k_5665_);
lean_ctor_set(v___x_5631_, 0, v___x_5552_);
v___x_5669_ = v___x_5631_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5673_, 1, v_k_5665_);
lean_ctor_set(v_reuseFailAlloc_5673_, 2, v_v_5666_);
lean_ctor_set(v_reuseFailAlloc_5673_, 3, v_l_5550_);
lean_ctor_set(v_reuseFailAlloc_5673_, 4, v_l_5550_);
v___x_5669_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
lean_object* v___x_5671_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v_r_5551_);
lean_ctor_set(v___x_5555_, 3, v___x_5669_);
lean_ctor_set(v___x_5555_, 2, v_v_5549_);
lean_ctor_set(v___x_5555_, 1, v_k_5548_);
lean_ctor_set(v___x_5555_, 0, v___x_5667_);
v___x_5671_ = v___x_5555_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v___x_5667_);
lean_ctor_set(v_reuseFailAlloc_5672_, 1, v_k_5548_);
lean_ctor_set(v_reuseFailAlloc_5672_, 2, v_v_5549_);
lean_ctor_set(v_reuseFailAlloc_5672_, 3, v___x_5669_);
lean_ctor_set(v_reuseFailAlloc_5672_, 4, v_r_5551_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
else
{
lean_object* v_k_5674_; lean_object* v_v_5675_; lean_object* v___x_5677_; 
v_k_5674_ = lean_ctor_get(v___x_5557_, 0);
lean_inc(v_k_5674_);
v_v_5675_ = lean_ctor_get(v___x_5557_, 1);
lean_inc(v_v_5675_);
lean_dec_ref(v___x_5557_);
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 3, v_r_5551_);
v___x_5677_ = v___x_5631_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_size_5547_);
lean_ctor_set(v_reuseFailAlloc_5682_, 1, v_k_5548_);
lean_ctor_set(v_reuseFailAlloc_5682_, 2, v_v_5549_);
lean_ctor_set(v_reuseFailAlloc_5682_, 3, v_r_5551_);
lean_ctor_set(v_reuseFailAlloc_5682_, 4, v_r_5551_);
v___x_5677_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
lean_object* v___x_5678_; lean_object* v___x_5680_; 
v___x_5678_ = lean_unsigned_to_nat(2u);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v___x_5677_);
lean_ctor_set(v___x_5555_, 3, v_r_5551_);
lean_ctor_set(v___x_5555_, 2, v_v_5675_);
lean_ctor_set(v___x_5555_, 1, v_k_5674_);
lean_ctor_set(v___x_5555_, 0, v___x_5678_);
v___x_5680_ = v___x_5555_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v___x_5678_);
lean_ctor_set(v_reuseFailAlloc_5681_, 1, v_k_5674_);
lean_ctor_set(v_reuseFailAlloc_5681_, 2, v_v_5675_);
lean_ctor_set(v_reuseFailAlloc_5681_, 3, v_r_5551_);
lean_ctor_set(v_reuseFailAlloc_5681_, 4, v___x_5677_);
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
}
}
else
{
lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5847_; 
lean_inc(v_r_5551_);
lean_inc(v_v_5549_);
lean_inc(v_k_5548_);
v_isSharedCheck_5847_ = !lean_is_exclusive(v_r_5363_);
if (v_isSharedCheck_5847_ == 0)
{
lean_object* v_unused_5848_; lean_object* v_unused_5849_; lean_object* v_unused_5850_; lean_object* v_unused_5851_; lean_object* v_unused_5852_; 
v_unused_5848_ = lean_ctor_get(v_r_5363_, 4);
lean_dec(v_unused_5848_);
v_unused_5849_ = lean_ctor_get(v_r_5363_, 3);
lean_dec(v_unused_5849_);
v_unused_5850_ = lean_ctor_get(v_r_5363_, 2);
lean_dec(v_unused_5850_);
v_unused_5851_ = lean_ctor_get(v_r_5363_, 1);
lean_dec(v_unused_5851_);
v_unused_5852_ = lean_ctor_get(v_r_5363_, 0);
lean_dec(v_unused_5852_);
v___x_5696_ = v_r_5363_;
v_isShared_5697_ = v_isSharedCheck_5847_;
goto v_resetjp_5695_;
}
else
{
lean_dec(v_r_5363_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5847_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v___x_5698_; lean_object* v_tree_5699_; 
v___x_5698_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_5548_, v_v_5549_, v_l_5550_, v_r_5551_);
v_tree_5699_ = lean_ctor_get(v___x_5698_, 2);
lean_inc(v_tree_5699_);
if (lean_obj_tag(v_tree_5699_) == 0)
{
lean_object* v_k_5700_; lean_object* v_v_5701_; lean_object* v_size_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; uint8_t v___x_5705_; 
v_k_5700_ = lean_ctor_get(v___x_5698_, 0);
lean_inc(v_k_5700_);
v_v_5701_ = lean_ctor_get(v___x_5698_, 1);
lean_inc(v_v_5701_);
lean_dec_ref(v___x_5698_);
v_size_5702_ = lean_ctor_get(v_tree_5699_, 0);
v___x_5703_ = lean_unsigned_to_nat(3u);
v___x_5704_ = lean_nat_mul(v___x_5703_, v_size_5702_);
v___x_5705_ = lean_nat_dec_lt(v___x_5704_, v_size_5542_);
lean_dec(v___x_5704_);
if (v___x_5705_ == 0)
{
lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5709_; 
lean_dec(v_r_5546_);
v___x_5706_ = lean_nat_add(v___x_5552_, v_size_5542_);
v___x_5707_ = lean_nat_add(v___x_5706_, v_size_5702_);
lean_dec(v___x_5706_);
if (v_isShared_5697_ == 0)
{
lean_ctor_set(v___x_5696_, 4, v_tree_5699_);
lean_ctor_set(v___x_5696_, 3, v_l_5362_);
lean_ctor_set(v___x_5696_, 2, v_v_5701_);
lean_ctor_set(v___x_5696_, 1, v_k_5700_);
lean_ctor_set(v___x_5696_, 0, v___x_5707_);
v___x_5709_ = v___x_5696_;
goto v_reusejp_5708_;
}
else
{
lean_object* v_reuseFailAlloc_5710_; 
v_reuseFailAlloc_5710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5710_, 0, v___x_5707_);
lean_ctor_set(v_reuseFailAlloc_5710_, 1, v_k_5700_);
lean_ctor_set(v_reuseFailAlloc_5710_, 2, v_v_5701_);
lean_ctor_set(v_reuseFailAlloc_5710_, 3, v_l_5362_);
lean_ctor_set(v_reuseFailAlloc_5710_, 4, v_tree_5699_);
v___x_5709_ = v_reuseFailAlloc_5710_;
goto v_reusejp_5708_;
}
v_reusejp_5708_:
{
return v___x_5709_;
}
}
else
{
lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5776_; 
lean_inc(v_l_5545_);
lean_inc(v_v_5544_);
lean_inc(v_k_5543_);
lean_inc(v_size_5542_);
v_isSharedCheck_5776_ = !lean_is_exclusive(v_l_5362_);
if (v_isSharedCheck_5776_ == 0)
{
lean_object* v_unused_5777_; lean_object* v_unused_5778_; lean_object* v_unused_5779_; lean_object* v_unused_5780_; lean_object* v_unused_5781_; 
v_unused_5777_ = lean_ctor_get(v_l_5362_, 4);
lean_dec(v_unused_5777_);
v_unused_5778_ = lean_ctor_get(v_l_5362_, 3);
lean_dec(v_unused_5778_);
v_unused_5779_ = lean_ctor_get(v_l_5362_, 2);
lean_dec(v_unused_5779_);
v_unused_5780_ = lean_ctor_get(v_l_5362_, 1);
lean_dec(v_unused_5780_);
v_unused_5781_ = lean_ctor_get(v_l_5362_, 0);
lean_dec(v_unused_5781_);
v___x_5712_ = v_l_5362_;
v_isShared_5713_ = v_isSharedCheck_5776_;
goto v_resetjp_5711_;
}
else
{
lean_dec(v_l_5362_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5776_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v_size_5714_; lean_object* v_size_5715_; lean_object* v_k_5716_; lean_object* v_v_5717_; lean_object* v_l_5718_; lean_object* v_r_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; uint8_t v___x_5722_; 
v_size_5714_ = lean_ctor_get(v_l_5545_, 0);
v_size_5715_ = lean_ctor_get(v_r_5546_, 0);
v_k_5716_ = lean_ctor_get(v_r_5546_, 1);
v_v_5717_ = lean_ctor_get(v_r_5546_, 2);
v_l_5718_ = lean_ctor_get(v_r_5546_, 3);
v_r_5719_ = lean_ctor_get(v_r_5546_, 4);
v___x_5720_ = lean_unsigned_to_nat(2u);
v___x_5721_ = lean_nat_mul(v___x_5720_, v_size_5714_);
v___x_5722_ = lean_nat_dec_lt(v_size_5715_, v___x_5721_);
lean_dec(v___x_5721_);
if (v___x_5722_ == 0)
{
lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5760_; 
lean_inc(v_r_5719_);
lean_inc(v_l_5718_);
lean_inc(v_v_5717_);
lean_inc(v_k_5716_);
lean_del_object(v___x_5712_);
v_isSharedCheck_5760_ = !lean_is_exclusive(v_r_5546_);
if (v_isSharedCheck_5760_ == 0)
{
lean_object* v_unused_5761_; lean_object* v_unused_5762_; lean_object* v_unused_5763_; lean_object* v_unused_5764_; lean_object* v_unused_5765_; 
v_unused_5761_ = lean_ctor_get(v_r_5546_, 4);
lean_dec(v_unused_5761_);
v_unused_5762_ = lean_ctor_get(v_r_5546_, 3);
lean_dec(v_unused_5762_);
v_unused_5763_ = lean_ctor_get(v_r_5546_, 2);
lean_dec(v_unused_5763_);
v_unused_5764_ = lean_ctor_get(v_r_5546_, 1);
lean_dec(v_unused_5764_);
v_unused_5765_ = lean_ctor_get(v_r_5546_, 0);
lean_dec(v_unused_5765_);
v___x_5724_ = v_r_5546_;
v_isShared_5725_ = v_isSharedCheck_5760_;
goto v_resetjp_5723_;
}
else
{
lean_dec(v_r_5546_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5760_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___y_5729_; lean_object* v___y_5730_; lean_object* v___y_5731_; lean_object* v___x_5748_; lean_object* v___y_5750_; 
v___x_5726_ = lean_nat_add(v___x_5552_, v_size_5542_);
lean_dec(v_size_5542_);
v___x_5727_ = lean_nat_add(v___x_5726_, v_size_5702_);
lean_dec(v___x_5726_);
v___x_5748_ = lean_nat_add(v___x_5552_, v_size_5714_);
if (lean_obj_tag(v_l_5718_) == 0)
{
lean_object* v_size_5758_; 
v_size_5758_ = lean_ctor_get(v_l_5718_, 0);
lean_inc(v_size_5758_);
v___y_5750_ = v_size_5758_;
goto v___jp_5749_;
}
else
{
lean_object* v___x_5759_; 
v___x_5759_ = lean_unsigned_to_nat(0u);
v___y_5750_ = v___x_5759_;
goto v___jp_5749_;
}
v___jp_5728_:
{
lean_object* v___x_5732_; lean_object* v___x_5734_; 
v___x_5732_ = lean_nat_add(v___y_5730_, v___y_5731_);
lean_dec(v___y_5731_);
lean_dec(v___y_5730_);
lean_inc_ref(v_tree_5699_);
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 4, v_tree_5699_);
lean_ctor_set(v___x_5724_, 3, v_r_5719_);
lean_ctor_set(v___x_5724_, 2, v_v_5701_);
lean_ctor_set(v___x_5724_, 1, v_k_5700_);
lean_ctor_set(v___x_5724_, 0, v___x_5732_);
v___x_5734_ = v___x_5724_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v___x_5732_);
lean_ctor_set(v_reuseFailAlloc_5747_, 1, v_k_5700_);
lean_ctor_set(v_reuseFailAlloc_5747_, 2, v_v_5701_);
lean_ctor_set(v_reuseFailAlloc_5747_, 3, v_r_5719_);
lean_ctor_set(v_reuseFailAlloc_5747_, 4, v_tree_5699_);
v___x_5734_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5741_; 
v_isSharedCheck_5741_ = !lean_is_exclusive(v_tree_5699_);
if (v_isSharedCheck_5741_ == 0)
{
lean_object* v_unused_5742_; lean_object* v_unused_5743_; lean_object* v_unused_5744_; lean_object* v_unused_5745_; lean_object* v_unused_5746_; 
v_unused_5742_ = lean_ctor_get(v_tree_5699_, 4);
lean_dec(v_unused_5742_);
v_unused_5743_ = lean_ctor_get(v_tree_5699_, 3);
lean_dec(v_unused_5743_);
v_unused_5744_ = lean_ctor_get(v_tree_5699_, 2);
lean_dec(v_unused_5744_);
v_unused_5745_ = lean_ctor_get(v_tree_5699_, 1);
lean_dec(v_unused_5745_);
v_unused_5746_ = lean_ctor_get(v_tree_5699_, 0);
lean_dec(v_unused_5746_);
v___x_5736_ = v_tree_5699_;
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
else
{
lean_dec(v_tree_5699_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v___x_5739_; 
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 4, v___x_5734_);
lean_ctor_set(v___x_5736_, 3, v___y_5729_);
lean_ctor_set(v___x_5736_, 2, v_v_5717_);
lean_ctor_set(v___x_5736_, 1, v_k_5716_);
lean_ctor_set(v___x_5736_, 0, v___x_5727_);
v___x_5739_ = v___x_5736_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5727_);
lean_ctor_set(v_reuseFailAlloc_5740_, 1, v_k_5716_);
lean_ctor_set(v_reuseFailAlloc_5740_, 2, v_v_5717_);
lean_ctor_set(v_reuseFailAlloc_5740_, 3, v___y_5729_);
lean_ctor_set(v_reuseFailAlloc_5740_, 4, v___x_5734_);
v___x_5739_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
return v___x_5739_;
}
}
}
}
v___jp_5749_:
{
lean_object* v___x_5751_; lean_object* v___x_5753_; 
v___x_5751_ = lean_nat_add(v___x_5748_, v___y_5750_);
lean_dec(v___y_5750_);
lean_dec(v___x_5748_);
if (v_isShared_5697_ == 0)
{
lean_ctor_set(v___x_5696_, 4, v_l_5718_);
lean_ctor_set(v___x_5696_, 3, v_l_5545_);
lean_ctor_set(v___x_5696_, 2, v_v_5544_);
lean_ctor_set(v___x_5696_, 1, v_k_5543_);
lean_ctor_set(v___x_5696_, 0, v___x_5751_);
v___x_5753_ = v___x_5696_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v___x_5751_);
lean_ctor_set(v_reuseFailAlloc_5757_, 1, v_k_5543_);
lean_ctor_set(v_reuseFailAlloc_5757_, 2, v_v_5544_);
lean_ctor_set(v_reuseFailAlloc_5757_, 3, v_l_5545_);
lean_ctor_set(v_reuseFailAlloc_5757_, 4, v_l_5718_);
v___x_5753_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
lean_object* v___x_5754_; 
v___x_5754_ = lean_nat_add(v___x_5552_, v_size_5702_);
if (lean_obj_tag(v_r_5719_) == 0)
{
lean_object* v_size_5755_; 
v_size_5755_ = lean_ctor_get(v_r_5719_, 0);
lean_inc(v_size_5755_);
v___y_5729_ = v___x_5753_;
v___y_5730_ = v___x_5754_;
v___y_5731_ = v_size_5755_;
goto v___jp_5728_;
}
else
{
lean_object* v___x_5756_; 
v___x_5756_ = lean_unsigned_to_nat(0u);
v___y_5729_ = v___x_5753_;
v___y_5730_ = v___x_5754_;
v___y_5731_ = v___x_5756_;
goto v___jp_5728_;
}
}
}
}
}
else
{
lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5771_; 
v___x_5766_ = lean_nat_add(v___x_5552_, v_size_5542_);
lean_dec(v_size_5542_);
v___x_5767_ = lean_nat_add(v___x_5766_, v_size_5702_);
lean_dec(v___x_5766_);
v___x_5768_ = lean_nat_add(v___x_5552_, v_size_5702_);
v___x_5769_ = lean_nat_add(v___x_5768_, v_size_5715_);
lean_dec(v___x_5768_);
if (v_isShared_5697_ == 0)
{
lean_ctor_set(v___x_5696_, 4, v_tree_5699_);
lean_ctor_set(v___x_5696_, 3, v_r_5546_);
lean_ctor_set(v___x_5696_, 2, v_v_5701_);
lean_ctor_set(v___x_5696_, 1, v_k_5700_);
lean_ctor_set(v___x_5696_, 0, v___x_5769_);
v___x_5771_ = v___x_5696_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5769_);
lean_ctor_set(v_reuseFailAlloc_5775_, 1, v_k_5700_);
lean_ctor_set(v_reuseFailAlloc_5775_, 2, v_v_5701_);
lean_ctor_set(v_reuseFailAlloc_5775_, 3, v_r_5546_);
lean_ctor_set(v_reuseFailAlloc_5775_, 4, v_tree_5699_);
v___x_5771_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
lean_object* v___x_5773_; 
if (v_isShared_5713_ == 0)
{
lean_ctor_set(v___x_5712_, 4, v___x_5771_);
lean_ctor_set(v___x_5712_, 0, v___x_5767_);
v___x_5773_ = v___x_5712_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v___x_5767_);
lean_ctor_set(v_reuseFailAlloc_5774_, 1, v_k_5543_);
lean_ctor_set(v_reuseFailAlloc_5774_, 2, v_v_5544_);
lean_ctor_set(v_reuseFailAlloc_5774_, 3, v_l_5545_);
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
}
}
}
else
{
if (lean_obj_tag(v_l_5545_) == 0)
{
lean_object* v___x_5783_; uint8_t v_isShared_5784_; uint8_t v_isSharedCheck_5805_; 
lean_inc_ref(v_l_5545_);
lean_inc(v_v_5544_);
lean_inc(v_k_5543_);
lean_inc(v_size_5542_);
v_isSharedCheck_5805_ = !lean_is_exclusive(v_l_5362_);
if (v_isSharedCheck_5805_ == 0)
{
lean_object* v_unused_5806_; lean_object* v_unused_5807_; lean_object* v_unused_5808_; lean_object* v_unused_5809_; lean_object* v_unused_5810_; 
v_unused_5806_ = lean_ctor_get(v_l_5362_, 4);
lean_dec(v_unused_5806_);
v_unused_5807_ = lean_ctor_get(v_l_5362_, 3);
lean_dec(v_unused_5807_);
v_unused_5808_ = lean_ctor_get(v_l_5362_, 2);
lean_dec(v_unused_5808_);
v_unused_5809_ = lean_ctor_get(v_l_5362_, 1);
lean_dec(v_unused_5809_);
v_unused_5810_ = lean_ctor_get(v_l_5362_, 0);
lean_dec(v_unused_5810_);
v___x_5783_ = v_l_5362_;
v_isShared_5784_ = v_isSharedCheck_5805_;
goto v_resetjp_5782_;
}
else
{
lean_dec(v_l_5362_);
v___x_5783_ = lean_box(0);
v_isShared_5784_ = v_isSharedCheck_5805_;
goto v_resetjp_5782_;
}
v_resetjp_5782_:
{
if (lean_obj_tag(v_r_5546_) == 0)
{
lean_object* v_k_5785_; lean_object* v_v_5786_; lean_object* v_size_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5791_; 
v_k_5785_ = lean_ctor_get(v___x_5698_, 0);
lean_inc(v_k_5785_);
v_v_5786_ = lean_ctor_get(v___x_5698_, 1);
lean_inc(v_v_5786_);
lean_dec_ref(v___x_5698_);
v_size_5787_ = lean_ctor_get(v_r_5546_, 0);
v___x_5788_ = lean_nat_add(v___x_5552_, v_size_5542_);
lean_dec(v_size_5542_);
v___x_5789_ = lean_nat_add(v___x_5552_, v_size_5787_);
if (v_isShared_5697_ == 0)
{
lean_ctor_set(v___x_5696_, 4, v_tree_5699_);
lean_ctor_set(v___x_5696_, 3, v_r_5546_);
lean_ctor_set(v___x_5696_, 2, v_v_5786_);
lean_ctor_set(v___x_5696_, 1, v_k_5785_);
lean_ctor_set(v___x_5696_, 0, v___x_5789_);
v___x_5791_ = v___x_5696_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v___x_5789_);
lean_ctor_set(v_reuseFailAlloc_5795_, 1, v_k_5785_);
lean_ctor_set(v_reuseFailAlloc_5795_, 2, v_v_5786_);
lean_ctor_set(v_reuseFailAlloc_5795_, 3, v_r_5546_);
lean_ctor_set(v_reuseFailAlloc_5795_, 4, v_tree_5699_);
v___x_5791_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
lean_object* v___x_5793_; 
if (v_isShared_5784_ == 0)
{
lean_ctor_set(v___x_5783_, 4, v___x_5791_);
lean_ctor_set(v___x_5783_, 0, v___x_5788_);
v___x_5793_ = v___x_5783_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v___x_5788_);
lean_ctor_set(v_reuseFailAlloc_5794_, 1, v_k_5543_);
lean_ctor_set(v_reuseFailAlloc_5794_, 2, v_v_5544_);
lean_ctor_set(v_reuseFailAlloc_5794_, 3, v_l_5545_);
lean_ctor_set(v_reuseFailAlloc_5794_, 4, v___x_5791_);
v___x_5793_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
return v___x_5793_;
}
}
}
else
{
lean_object* v_k_5796_; lean_object* v_v_5797_; lean_object* v___x_5798_; lean_object* v___x_5800_; 
lean_dec(v_size_5542_);
v_k_5796_ = lean_ctor_get(v___x_5698_, 0);
lean_inc(v_k_5796_);
v_v_5797_ = lean_ctor_get(v___x_5698_, 1);
lean_inc(v_v_5797_);
lean_dec_ref(v___x_5698_);
v___x_5798_ = lean_unsigned_to_nat(3u);
if (v_isShared_5697_ == 0)
{
lean_ctor_set(v___x_5696_, 4, v_r_5546_);
lean_ctor_set(v___x_5696_, 3, v_r_5546_);
lean_ctor_set(v___x_5696_, 2, v_v_5797_);
lean_ctor_set(v___x_5696_, 1, v_k_5796_);
lean_ctor_set(v___x_5696_, 0, v___x_5552_);
v___x_5800_ = v___x_5696_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5804_; 
v_reuseFailAlloc_5804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5804_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5804_, 1, v_k_5796_);
lean_ctor_set(v_reuseFailAlloc_5804_, 2, v_v_5797_);
lean_ctor_set(v_reuseFailAlloc_5804_, 3, v_r_5546_);
lean_ctor_set(v_reuseFailAlloc_5804_, 4, v_r_5546_);
v___x_5800_ = v_reuseFailAlloc_5804_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
lean_object* v___x_5802_; 
if (v_isShared_5784_ == 0)
{
lean_ctor_set(v___x_5783_, 4, v___x_5800_);
lean_ctor_set(v___x_5783_, 0, v___x_5798_);
v___x_5802_ = v___x_5783_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5798_);
lean_ctor_set(v_reuseFailAlloc_5803_, 1, v_k_5543_);
lean_ctor_set(v_reuseFailAlloc_5803_, 2, v_v_5544_);
lean_ctor_set(v_reuseFailAlloc_5803_, 3, v_l_5545_);
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
}
}
else
{
if (lean_obj_tag(v_r_5546_) == 0)
{
lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5835_; 
lean_inc(v_l_5545_);
lean_inc(v_v_5544_);
lean_inc(v_k_5543_);
v_isSharedCheck_5835_ = !lean_is_exclusive(v_l_5362_);
if (v_isSharedCheck_5835_ == 0)
{
lean_object* v_unused_5836_; lean_object* v_unused_5837_; lean_object* v_unused_5838_; lean_object* v_unused_5839_; lean_object* v_unused_5840_; 
v_unused_5836_ = lean_ctor_get(v_l_5362_, 4);
lean_dec(v_unused_5836_);
v_unused_5837_ = lean_ctor_get(v_l_5362_, 3);
lean_dec(v_unused_5837_);
v_unused_5838_ = lean_ctor_get(v_l_5362_, 2);
lean_dec(v_unused_5838_);
v_unused_5839_ = lean_ctor_get(v_l_5362_, 1);
lean_dec(v_unused_5839_);
v_unused_5840_ = lean_ctor_get(v_l_5362_, 0);
lean_dec(v_unused_5840_);
v___x_5812_ = v_l_5362_;
v_isShared_5813_ = v_isSharedCheck_5835_;
goto v_resetjp_5811_;
}
else
{
lean_dec(v_l_5362_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5835_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v_k_5814_; lean_object* v_v_5815_; lean_object* v_k_5816_; lean_object* v_v_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5831_; 
v_k_5814_ = lean_ctor_get(v___x_5698_, 0);
lean_inc(v_k_5814_);
v_v_5815_ = lean_ctor_get(v___x_5698_, 1);
lean_inc(v_v_5815_);
lean_dec_ref(v___x_5698_);
v_k_5816_ = lean_ctor_get(v_r_5546_, 1);
v_v_5817_ = lean_ctor_get(v_r_5546_, 2);
v_isSharedCheck_5831_ = !lean_is_exclusive(v_r_5546_);
if (v_isSharedCheck_5831_ == 0)
{
lean_object* v_unused_5832_; lean_object* v_unused_5833_; lean_object* v_unused_5834_; 
v_unused_5832_ = lean_ctor_get(v_r_5546_, 4);
lean_dec(v_unused_5832_);
v_unused_5833_ = lean_ctor_get(v_r_5546_, 3);
lean_dec(v_unused_5833_);
v_unused_5834_ = lean_ctor_get(v_r_5546_, 0);
lean_dec(v_unused_5834_);
v___x_5819_ = v_r_5546_;
v_isShared_5820_ = v_isSharedCheck_5831_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_v_5817_);
lean_inc(v_k_5816_);
lean_dec(v_r_5546_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5831_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
lean_object* v___x_5821_; lean_object* v___x_5823_; 
v___x_5821_ = lean_unsigned_to_nat(3u);
if (v_isShared_5820_ == 0)
{
lean_ctor_set(v___x_5819_, 4, v_l_5545_);
lean_ctor_set(v___x_5819_, 3, v_l_5545_);
lean_ctor_set(v___x_5819_, 2, v_v_5544_);
lean_ctor_set(v___x_5819_, 1, v_k_5543_);
lean_ctor_set(v___x_5819_, 0, v___x_5552_);
v___x_5823_ = v___x_5819_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5830_, 1, v_k_5543_);
lean_ctor_set(v_reuseFailAlloc_5830_, 2, v_v_5544_);
lean_ctor_set(v_reuseFailAlloc_5830_, 3, v_l_5545_);
lean_ctor_set(v_reuseFailAlloc_5830_, 4, v_l_5545_);
v___x_5823_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
lean_object* v___x_5825_; 
if (v_isShared_5697_ == 0)
{
lean_ctor_set(v___x_5696_, 4, v_l_5545_);
lean_ctor_set(v___x_5696_, 3, v_l_5545_);
lean_ctor_set(v___x_5696_, 2, v_v_5815_);
lean_ctor_set(v___x_5696_, 1, v_k_5814_);
lean_ctor_set(v___x_5696_, 0, v___x_5552_);
v___x_5825_ = v___x_5696_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5829_, 1, v_k_5814_);
lean_ctor_set(v_reuseFailAlloc_5829_, 2, v_v_5815_);
lean_ctor_set(v_reuseFailAlloc_5829_, 3, v_l_5545_);
lean_ctor_set(v_reuseFailAlloc_5829_, 4, v_l_5545_);
v___x_5825_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
lean_object* v___x_5827_; 
if (v_isShared_5813_ == 0)
{
lean_ctor_set(v___x_5812_, 4, v___x_5825_);
lean_ctor_set(v___x_5812_, 3, v___x_5823_);
lean_ctor_set(v___x_5812_, 2, v_v_5817_);
lean_ctor_set(v___x_5812_, 1, v_k_5816_);
lean_ctor_set(v___x_5812_, 0, v___x_5821_);
v___x_5827_ = v___x_5812_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v___x_5821_);
lean_ctor_set(v_reuseFailAlloc_5828_, 1, v_k_5816_);
lean_ctor_set(v_reuseFailAlloc_5828_, 2, v_v_5817_);
lean_ctor_set(v_reuseFailAlloc_5828_, 3, v___x_5823_);
lean_ctor_set(v_reuseFailAlloc_5828_, 4, v___x_5825_);
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
else
{
lean_object* v_k_5841_; lean_object* v_v_5842_; lean_object* v___x_5843_; lean_object* v___x_5845_; 
v_k_5841_ = lean_ctor_get(v___x_5698_, 0);
lean_inc(v_k_5841_);
v_v_5842_ = lean_ctor_get(v___x_5698_, 1);
lean_inc(v_v_5842_);
lean_dec_ref(v___x_5698_);
v___x_5843_ = lean_unsigned_to_nat(2u);
if (v_isShared_5697_ == 0)
{
lean_ctor_set(v___x_5696_, 4, v_r_5546_);
lean_ctor_set(v___x_5696_, 3, v_l_5362_);
lean_ctor_set(v___x_5696_, 2, v_v_5842_);
lean_ctor_set(v___x_5696_, 1, v_k_5841_);
lean_ctor_set(v___x_5696_, 0, v___x_5843_);
v___x_5845_ = v___x_5696_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5843_);
lean_ctor_set(v_reuseFailAlloc_5846_, 1, v_k_5841_);
lean_ctor_set(v_reuseFailAlloc_5846_, 2, v_v_5842_);
lean_ctor_set(v_reuseFailAlloc_5846_, 3, v_l_5362_);
lean_ctor_set(v_reuseFailAlloc_5846_, 4, v_r_5546_);
v___x_5845_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
return v___x_5845_;
}
}
}
}
}
}
}
else
{
return v_l_5362_;
}
}
else
{
return v_r_5363_;
}
}
default: 
{
lean_object* v_impl_5853_; lean_object* v___x_5854_; 
v_impl_5853_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_5358_, v_r_5363_);
v___x_5854_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_5853_) == 0)
{
if (lean_obj_tag(v_l_5362_) == 0)
{
lean_object* v_size_5855_; lean_object* v_size_5856_; lean_object* v_k_5857_; lean_object* v_v_5858_; lean_object* v_l_5859_; lean_object* v_r_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; uint8_t v___x_5863_; 
v_size_5855_ = lean_ctor_get(v_impl_5853_, 0);
lean_inc(v_size_5855_);
v_size_5856_ = lean_ctor_get(v_l_5362_, 0);
v_k_5857_ = lean_ctor_get(v_l_5362_, 1);
v_v_5858_ = lean_ctor_get(v_l_5362_, 2);
v_l_5859_ = lean_ctor_get(v_l_5362_, 3);
v_r_5860_ = lean_ctor_get(v_l_5362_, 4);
lean_inc(v_r_5860_);
v___x_5861_ = lean_unsigned_to_nat(3u);
v___x_5862_ = lean_nat_mul(v___x_5861_, v_size_5855_);
v___x_5863_ = lean_nat_dec_lt(v___x_5862_, v_size_5856_);
lean_dec(v___x_5862_);
if (v___x_5863_ == 0)
{
lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5867_; 
lean_dec(v_r_5860_);
v___x_5864_ = lean_nat_add(v___x_5854_, v_size_5856_);
v___x_5865_ = lean_nat_add(v___x_5864_, v_size_5855_);
lean_dec(v_size_5855_);
lean_dec(v___x_5864_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v_impl_5853_);
lean_ctor_set(v___x_5365_, 0, v___x_5865_);
v___x_5867_ = v___x_5365_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v___x_5865_);
lean_ctor_set(v_reuseFailAlloc_5868_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5868_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5868_, 3, v_l_5362_);
lean_ctor_set(v_reuseFailAlloc_5868_, 4, v_impl_5853_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
else
{
lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5934_; 
lean_inc(v_l_5859_);
lean_inc(v_v_5858_);
lean_inc(v_k_5857_);
lean_inc(v_size_5856_);
v_isSharedCheck_5934_ = !lean_is_exclusive(v_l_5362_);
if (v_isSharedCheck_5934_ == 0)
{
lean_object* v_unused_5935_; lean_object* v_unused_5936_; lean_object* v_unused_5937_; lean_object* v_unused_5938_; lean_object* v_unused_5939_; 
v_unused_5935_ = lean_ctor_get(v_l_5362_, 4);
lean_dec(v_unused_5935_);
v_unused_5936_ = lean_ctor_get(v_l_5362_, 3);
lean_dec(v_unused_5936_);
v_unused_5937_ = lean_ctor_get(v_l_5362_, 2);
lean_dec(v_unused_5937_);
v_unused_5938_ = lean_ctor_get(v_l_5362_, 1);
lean_dec(v_unused_5938_);
v_unused_5939_ = lean_ctor_get(v_l_5362_, 0);
lean_dec(v_unused_5939_);
v___x_5870_ = v_l_5362_;
v_isShared_5871_ = v_isSharedCheck_5934_;
goto v_resetjp_5869_;
}
else
{
lean_dec(v_l_5362_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5934_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
lean_object* v_size_5872_; lean_object* v_size_5873_; lean_object* v_k_5874_; lean_object* v_v_5875_; lean_object* v_l_5876_; lean_object* v_r_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; uint8_t v___x_5880_; 
v_size_5872_ = lean_ctor_get(v_l_5859_, 0);
v_size_5873_ = lean_ctor_get(v_r_5860_, 0);
v_k_5874_ = lean_ctor_get(v_r_5860_, 1);
v_v_5875_ = lean_ctor_get(v_r_5860_, 2);
v_l_5876_ = lean_ctor_get(v_r_5860_, 3);
v_r_5877_ = lean_ctor_get(v_r_5860_, 4);
v___x_5878_ = lean_unsigned_to_nat(2u);
v___x_5879_ = lean_nat_mul(v___x_5878_, v_size_5872_);
v___x_5880_ = lean_nat_dec_lt(v_size_5873_, v___x_5879_);
lean_dec(v___x_5879_);
if (v___x_5880_ == 0)
{
lean_object* v___x_5882_; uint8_t v_isShared_5883_; uint8_t v_isSharedCheck_5909_; 
lean_inc(v_r_5877_);
lean_inc(v_l_5876_);
lean_inc(v_v_5875_);
lean_inc(v_k_5874_);
v_isSharedCheck_5909_ = !lean_is_exclusive(v_r_5860_);
if (v_isSharedCheck_5909_ == 0)
{
lean_object* v_unused_5910_; lean_object* v_unused_5911_; lean_object* v_unused_5912_; lean_object* v_unused_5913_; lean_object* v_unused_5914_; 
v_unused_5910_ = lean_ctor_get(v_r_5860_, 4);
lean_dec(v_unused_5910_);
v_unused_5911_ = lean_ctor_get(v_r_5860_, 3);
lean_dec(v_unused_5911_);
v_unused_5912_ = lean_ctor_get(v_r_5860_, 2);
lean_dec(v_unused_5912_);
v_unused_5913_ = lean_ctor_get(v_r_5860_, 1);
lean_dec(v_unused_5913_);
v_unused_5914_ = lean_ctor_get(v_r_5860_, 0);
lean_dec(v_unused_5914_);
v___x_5882_ = v_r_5860_;
v_isShared_5883_ = v_isSharedCheck_5909_;
goto v_resetjp_5881_;
}
else
{
lean_dec(v_r_5860_);
v___x_5882_ = lean_box(0);
v_isShared_5883_ = v_isSharedCheck_5909_;
goto v_resetjp_5881_;
}
v_resetjp_5881_:
{
lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___y_5887_; lean_object* v___y_5888_; lean_object* v___y_5889_; lean_object* v___x_5897_; lean_object* v___y_5899_; 
v___x_5884_ = lean_nat_add(v___x_5854_, v_size_5856_);
lean_dec(v_size_5856_);
v___x_5885_ = lean_nat_add(v___x_5884_, v_size_5855_);
lean_dec(v___x_5884_);
v___x_5897_ = lean_nat_add(v___x_5854_, v_size_5872_);
if (lean_obj_tag(v_l_5876_) == 0)
{
lean_object* v_size_5907_; 
v_size_5907_ = lean_ctor_get(v_l_5876_, 0);
lean_inc(v_size_5907_);
v___y_5899_ = v_size_5907_;
goto v___jp_5898_;
}
else
{
lean_object* v___x_5908_; 
v___x_5908_ = lean_unsigned_to_nat(0u);
v___y_5899_ = v___x_5908_;
goto v___jp_5898_;
}
v___jp_5886_:
{
lean_object* v___x_5890_; lean_object* v___x_5892_; 
v___x_5890_ = lean_nat_add(v___y_5887_, v___y_5889_);
lean_dec(v___y_5889_);
lean_dec(v___y_5887_);
if (v_isShared_5883_ == 0)
{
lean_ctor_set(v___x_5882_, 4, v_impl_5853_);
lean_ctor_set(v___x_5882_, 3, v_r_5877_);
lean_ctor_set(v___x_5882_, 2, v_v_5361_);
lean_ctor_set(v___x_5882_, 1, v_k_5360_);
lean_ctor_set(v___x_5882_, 0, v___x_5890_);
v___x_5892_ = v___x_5882_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v___x_5890_);
lean_ctor_set(v_reuseFailAlloc_5896_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5896_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5896_, 3, v_r_5877_);
lean_ctor_set(v_reuseFailAlloc_5896_, 4, v_impl_5853_);
v___x_5892_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
lean_object* v___x_5894_; 
if (v_isShared_5871_ == 0)
{
lean_ctor_set(v___x_5870_, 4, v___x_5892_);
lean_ctor_set(v___x_5870_, 3, v___y_5888_);
lean_ctor_set(v___x_5870_, 2, v_v_5875_);
lean_ctor_set(v___x_5870_, 1, v_k_5874_);
lean_ctor_set(v___x_5870_, 0, v___x_5885_);
v___x_5894_ = v___x_5870_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v___x_5885_);
lean_ctor_set(v_reuseFailAlloc_5895_, 1, v_k_5874_);
lean_ctor_set(v_reuseFailAlloc_5895_, 2, v_v_5875_);
lean_ctor_set(v_reuseFailAlloc_5895_, 3, v___y_5888_);
lean_ctor_set(v_reuseFailAlloc_5895_, 4, v___x_5892_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
return v___x_5894_;
}
}
}
v___jp_5898_:
{
lean_object* v___x_5900_; lean_object* v___x_5902_; 
v___x_5900_ = lean_nat_add(v___x_5897_, v___y_5899_);
lean_dec(v___y_5899_);
lean_dec(v___x_5897_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v_l_5876_);
lean_ctor_set(v___x_5365_, 3, v_l_5859_);
lean_ctor_set(v___x_5365_, 2, v_v_5858_);
lean_ctor_set(v___x_5365_, 1, v_k_5857_);
lean_ctor_set(v___x_5365_, 0, v___x_5900_);
v___x_5902_ = v___x_5365_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5906_; 
v_reuseFailAlloc_5906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5906_, 0, v___x_5900_);
lean_ctor_set(v_reuseFailAlloc_5906_, 1, v_k_5857_);
lean_ctor_set(v_reuseFailAlloc_5906_, 2, v_v_5858_);
lean_ctor_set(v_reuseFailAlloc_5906_, 3, v_l_5859_);
lean_ctor_set(v_reuseFailAlloc_5906_, 4, v_l_5876_);
v___x_5902_ = v_reuseFailAlloc_5906_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
lean_object* v___x_5903_; 
v___x_5903_ = lean_nat_add(v___x_5854_, v_size_5855_);
lean_dec(v_size_5855_);
if (lean_obj_tag(v_r_5877_) == 0)
{
lean_object* v_size_5904_; 
v_size_5904_ = lean_ctor_get(v_r_5877_, 0);
lean_inc(v_size_5904_);
v___y_5887_ = v___x_5903_;
v___y_5888_ = v___x_5902_;
v___y_5889_ = v_size_5904_;
goto v___jp_5886_;
}
else
{
lean_object* v___x_5905_; 
v___x_5905_ = lean_unsigned_to_nat(0u);
v___y_5887_ = v___x_5903_;
v___y_5888_ = v___x_5902_;
v___y_5889_ = v___x_5905_;
goto v___jp_5886_;
}
}
}
}
}
else
{
lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5920_; 
lean_del_object(v___x_5365_);
v___x_5915_ = lean_nat_add(v___x_5854_, v_size_5856_);
lean_dec(v_size_5856_);
v___x_5916_ = lean_nat_add(v___x_5915_, v_size_5855_);
lean_dec(v___x_5915_);
v___x_5917_ = lean_nat_add(v___x_5854_, v_size_5855_);
lean_dec(v_size_5855_);
v___x_5918_ = lean_nat_add(v___x_5917_, v_size_5873_);
lean_dec(v___x_5917_);
lean_inc_ref(v_impl_5853_);
if (v_isShared_5871_ == 0)
{
lean_ctor_set(v___x_5870_, 4, v_impl_5853_);
lean_ctor_set(v___x_5870_, 3, v_r_5860_);
lean_ctor_set(v___x_5870_, 2, v_v_5361_);
lean_ctor_set(v___x_5870_, 1, v_k_5360_);
lean_ctor_set(v___x_5870_, 0, v___x_5918_);
v___x_5920_ = v___x_5870_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5933_; 
v_reuseFailAlloc_5933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5933_, 0, v___x_5918_);
lean_ctor_set(v_reuseFailAlloc_5933_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5933_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5933_, 3, v_r_5860_);
lean_ctor_set(v_reuseFailAlloc_5933_, 4, v_impl_5853_);
v___x_5920_ = v_reuseFailAlloc_5933_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_5927_; 
v_isSharedCheck_5927_ = !lean_is_exclusive(v_impl_5853_);
if (v_isSharedCheck_5927_ == 0)
{
lean_object* v_unused_5928_; lean_object* v_unused_5929_; lean_object* v_unused_5930_; lean_object* v_unused_5931_; lean_object* v_unused_5932_; 
v_unused_5928_ = lean_ctor_get(v_impl_5853_, 4);
lean_dec(v_unused_5928_);
v_unused_5929_ = lean_ctor_get(v_impl_5853_, 3);
lean_dec(v_unused_5929_);
v_unused_5930_ = lean_ctor_get(v_impl_5853_, 2);
lean_dec(v_unused_5930_);
v_unused_5931_ = lean_ctor_get(v_impl_5853_, 1);
lean_dec(v_unused_5931_);
v_unused_5932_ = lean_ctor_get(v_impl_5853_, 0);
lean_dec(v_unused_5932_);
v___x_5922_ = v_impl_5853_;
v_isShared_5923_ = v_isSharedCheck_5927_;
goto v_resetjp_5921_;
}
else
{
lean_dec(v_impl_5853_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_5927_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v___x_5925_; 
if (v_isShared_5923_ == 0)
{
lean_ctor_set(v___x_5922_, 4, v___x_5920_);
lean_ctor_set(v___x_5922_, 3, v_l_5859_);
lean_ctor_set(v___x_5922_, 2, v_v_5858_);
lean_ctor_set(v___x_5922_, 1, v_k_5857_);
lean_ctor_set(v___x_5922_, 0, v___x_5916_);
v___x_5925_ = v___x_5922_;
goto v_reusejp_5924_;
}
else
{
lean_object* v_reuseFailAlloc_5926_; 
v_reuseFailAlloc_5926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5926_, 0, v___x_5916_);
lean_ctor_set(v_reuseFailAlloc_5926_, 1, v_k_5857_);
lean_ctor_set(v_reuseFailAlloc_5926_, 2, v_v_5858_);
lean_ctor_set(v_reuseFailAlloc_5926_, 3, v_l_5859_);
lean_ctor_set(v_reuseFailAlloc_5926_, 4, v___x_5920_);
v___x_5925_ = v_reuseFailAlloc_5926_;
goto v_reusejp_5924_;
}
v_reusejp_5924_:
{
return v___x_5925_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_5940_; lean_object* v___x_5941_; lean_object* v___x_5943_; 
v_size_5940_ = lean_ctor_get(v_impl_5853_, 0);
lean_inc(v_size_5940_);
v___x_5941_ = lean_nat_add(v___x_5854_, v_size_5940_);
lean_dec(v_size_5940_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v_impl_5853_);
lean_ctor_set(v___x_5365_, 0, v___x_5941_);
v___x_5943_ = v___x_5365_;
goto v_reusejp_5942_;
}
else
{
lean_object* v_reuseFailAlloc_5944_; 
v_reuseFailAlloc_5944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5944_, 0, v___x_5941_);
lean_ctor_set(v_reuseFailAlloc_5944_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5944_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5944_, 3, v_l_5362_);
lean_ctor_set(v_reuseFailAlloc_5944_, 4, v_impl_5853_);
v___x_5943_ = v_reuseFailAlloc_5944_;
goto v_reusejp_5942_;
}
v_reusejp_5942_:
{
return v___x_5943_;
}
}
}
else
{
if (lean_obj_tag(v_l_5362_) == 0)
{
lean_object* v_l_5945_; 
v_l_5945_ = lean_ctor_get(v_l_5362_, 3);
if (lean_obj_tag(v_l_5945_) == 0)
{
lean_object* v_r_5946_; 
lean_inc_ref(v_l_5945_);
v_r_5946_ = lean_ctor_get(v_l_5362_, 4);
lean_inc(v_r_5946_);
if (lean_obj_tag(v_r_5946_) == 0)
{
lean_object* v_size_5947_; lean_object* v_k_5948_; lean_object* v_v_5949_; lean_object* v___x_5951_; uint8_t v_isShared_5952_; uint8_t v_isSharedCheck_5962_; 
v_size_5947_ = lean_ctor_get(v_l_5362_, 0);
v_k_5948_ = lean_ctor_get(v_l_5362_, 1);
v_v_5949_ = lean_ctor_get(v_l_5362_, 2);
v_isSharedCheck_5962_ = !lean_is_exclusive(v_l_5362_);
if (v_isSharedCheck_5962_ == 0)
{
lean_object* v_unused_5963_; lean_object* v_unused_5964_; 
v_unused_5963_ = lean_ctor_get(v_l_5362_, 4);
lean_dec(v_unused_5963_);
v_unused_5964_ = lean_ctor_get(v_l_5362_, 3);
lean_dec(v_unused_5964_);
v___x_5951_ = v_l_5362_;
v_isShared_5952_ = v_isSharedCheck_5962_;
goto v_resetjp_5950_;
}
else
{
lean_inc(v_v_5949_);
lean_inc(v_k_5948_);
lean_inc(v_size_5947_);
lean_dec(v_l_5362_);
v___x_5951_ = lean_box(0);
v_isShared_5952_ = v_isSharedCheck_5962_;
goto v_resetjp_5950_;
}
v_resetjp_5950_:
{
lean_object* v_size_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5957_; 
v_size_5953_ = lean_ctor_get(v_r_5946_, 0);
v___x_5954_ = lean_nat_add(v___x_5854_, v_size_5947_);
lean_dec(v_size_5947_);
v___x_5955_ = lean_nat_add(v___x_5854_, v_size_5953_);
if (v_isShared_5952_ == 0)
{
lean_ctor_set(v___x_5951_, 4, v_impl_5853_);
lean_ctor_set(v___x_5951_, 3, v_r_5946_);
lean_ctor_set(v___x_5951_, 2, v_v_5361_);
lean_ctor_set(v___x_5951_, 1, v_k_5360_);
lean_ctor_set(v___x_5951_, 0, v___x_5955_);
v___x_5957_ = v___x_5951_;
goto v_reusejp_5956_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v___x_5955_);
lean_ctor_set(v_reuseFailAlloc_5961_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5961_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5961_, 3, v_r_5946_);
lean_ctor_set(v_reuseFailAlloc_5961_, 4, v_impl_5853_);
v___x_5957_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5956_;
}
v_reusejp_5956_:
{
lean_object* v___x_5959_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v___x_5957_);
lean_ctor_set(v___x_5365_, 3, v_l_5945_);
lean_ctor_set(v___x_5365_, 2, v_v_5949_);
lean_ctor_set(v___x_5365_, 1, v_k_5948_);
lean_ctor_set(v___x_5365_, 0, v___x_5954_);
v___x_5959_ = v___x_5365_;
goto v_reusejp_5958_;
}
else
{
lean_object* v_reuseFailAlloc_5960_; 
v_reuseFailAlloc_5960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5960_, 0, v___x_5954_);
lean_ctor_set(v_reuseFailAlloc_5960_, 1, v_k_5948_);
lean_ctor_set(v_reuseFailAlloc_5960_, 2, v_v_5949_);
lean_ctor_set(v_reuseFailAlloc_5960_, 3, v_l_5945_);
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
else
{
lean_object* v_k_5965_; lean_object* v_v_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5977_; 
v_k_5965_ = lean_ctor_get(v_l_5362_, 1);
v_v_5966_ = lean_ctor_get(v_l_5362_, 2);
v_isSharedCheck_5977_ = !lean_is_exclusive(v_l_5362_);
if (v_isSharedCheck_5977_ == 0)
{
lean_object* v_unused_5978_; lean_object* v_unused_5979_; lean_object* v_unused_5980_; 
v_unused_5978_ = lean_ctor_get(v_l_5362_, 4);
lean_dec(v_unused_5978_);
v_unused_5979_ = lean_ctor_get(v_l_5362_, 3);
lean_dec(v_unused_5979_);
v_unused_5980_ = lean_ctor_get(v_l_5362_, 0);
lean_dec(v_unused_5980_);
v___x_5968_ = v_l_5362_;
v_isShared_5969_ = v_isSharedCheck_5977_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_v_5966_);
lean_inc(v_k_5965_);
lean_dec(v_l_5362_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5977_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5970_; lean_object* v___x_5972_; 
v___x_5970_ = lean_unsigned_to_nat(3u);
if (v_isShared_5969_ == 0)
{
lean_ctor_set(v___x_5968_, 3, v_r_5946_);
lean_ctor_set(v___x_5968_, 2, v_v_5361_);
lean_ctor_set(v___x_5968_, 1, v_k_5360_);
lean_ctor_set(v___x_5968_, 0, v___x_5854_);
v___x_5972_ = v___x_5968_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v___x_5854_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5976_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5976_, 3, v_r_5946_);
lean_ctor_set(v_reuseFailAlloc_5976_, 4, v_r_5946_);
v___x_5972_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
lean_object* v___x_5974_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v___x_5972_);
lean_ctor_set(v___x_5365_, 3, v_l_5945_);
lean_ctor_set(v___x_5365_, 2, v_v_5966_);
lean_ctor_set(v___x_5365_, 1, v_k_5965_);
lean_ctor_set(v___x_5365_, 0, v___x_5970_);
v___x_5974_ = v___x_5365_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v___x_5970_);
lean_ctor_set(v_reuseFailAlloc_5975_, 1, v_k_5965_);
lean_ctor_set(v_reuseFailAlloc_5975_, 2, v_v_5966_);
lean_ctor_set(v_reuseFailAlloc_5975_, 3, v_l_5945_);
lean_ctor_set(v_reuseFailAlloc_5975_, 4, v___x_5972_);
v___x_5974_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
return v___x_5974_;
}
}
}
}
}
else
{
lean_object* v_r_5981_; 
v_r_5981_ = lean_ctor_get(v_l_5362_, 4);
lean_inc(v_r_5981_);
if (lean_obj_tag(v_r_5981_) == 0)
{
lean_object* v_k_5982_; lean_object* v_v_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_6006_; 
lean_inc(v_l_5945_);
v_k_5982_ = lean_ctor_get(v_l_5362_, 1);
v_v_5983_ = lean_ctor_get(v_l_5362_, 2);
v_isSharedCheck_6006_ = !lean_is_exclusive(v_l_5362_);
if (v_isSharedCheck_6006_ == 0)
{
lean_object* v_unused_6007_; lean_object* v_unused_6008_; lean_object* v_unused_6009_; 
v_unused_6007_ = lean_ctor_get(v_l_5362_, 4);
lean_dec(v_unused_6007_);
v_unused_6008_ = lean_ctor_get(v_l_5362_, 3);
lean_dec(v_unused_6008_);
v_unused_6009_ = lean_ctor_get(v_l_5362_, 0);
lean_dec(v_unused_6009_);
v___x_5985_ = v_l_5362_;
v_isShared_5986_ = v_isSharedCheck_6006_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_v_5983_);
lean_inc(v_k_5982_);
lean_dec(v_l_5362_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_6006_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v_k_5987_; lean_object* v_v_5988_; lean_object* v___x_5990_; uint8_t v_isShared_5991_; uint8_t v_isSharedCheck_6002_; 
v_k_5987_ = lean_ctor_get(v_r_5981_, 1);
v_v_5988_ = lean_ctor_get(v_r_5981_, 2);
v_isSharedCheck_6002_ = !lean_is_exclusive(v_r_5981_);
if (v_isSharedCheck_6002_ == 0)
{
lean_object* v_unused_6003_; lean_object* v_unused_6004_; lean_object* v_unused_6005_; 
v_unused_6003_ = lean_ctor_get(v_r_5981_, 4);
lean_dec(v_unused_6003_);
v_unused_6004_ = lean_ctor_get(v_r_5981_, 3);
lean_dec(v_unused_6004_);
v_unused_6005_ = lean_ctor_get(v_r_5981_, 0);
lean_dec(v_unused_6005_);
v___x_5990_ = v_r_5981_;
v_isShared_5991_ = v_isSharedCheck_6002_;
goto v_resetjp_5989_;
}
else
{
lean_inc(v_v_5988_);
lean_inc(v_k_5987_);
lean_dec(v_r_5981_);
v___x_5990_ = lean_box(0);
v_isShared_5991_ = v_isSharedCheck_6002_;
goto v_resetjp_5989_;
}
v_resetjp_5989_:
{
lean_object* v___x_5992_; lean_object* v___x_5994_; 
v___x_5992_ = lean_unsigned_to_nat(3u);
if (v_isShared_5991_ == 0)
{
lean_ctor_set(v___x_5990_, 4, v_l_5945_);
lean_ctor_set(v___x_5990_, 3, v_l_5945_);
lean_ctor_set(v___x_5990_, 2, v_v_5983_);
lean_ctor_set(v___x_5990_, 1, v_k_5982_);
lean_ctor_set(v___x_5990_, 0, v___x_5854_);
v___x_5994_ = v___x_5990_;
goto v_reusejp_5993_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v___x_5854_);
lean_ctor_set(v_reuseFailAlloc_6001_, 1, v_k_5982_);
lean_ctor_set(v_reuseFailAlloc_6001_, 2, v_v_5983_);
lean_ctor_set(v_reuseFailAlloc_6001_, 3, v_l_5945_);
lean_ctor_set(v_reuseFailAlloc_6001_, 4, v_l_5945_);
v___x_5994_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5993_;
}
v_reusejp_5993_:
{
lean_object* v___x_5996_; 
if (v_isShared_5986_ == 0)
{
lean_ctor_set(v___x_5985_, 4, v_l_5945_);
lean_ctor_set(v___x_5985_, 2, v_v_5361_);
lean_ctor_set(v___x_5985_, 1, v_k_5360_);
lean_ctor_set(v___x_5985_, 0, v___x_5854_);
v___x_5996_ = v___x_5985_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_6000_; 
v_reuseFailAlloc_6000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6000_, 0, v___x_5854_);
lean_ctor_set(v_reuseFailAlloc_6000_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_6000_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_6000_, 3, v_l_5945_);
lean_ctor_set(v_reuseFailAlloc_6000_, 4, v_l_5945_);
v___x_5996_ = v_reuseFailAlloc_6000_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
lean_object* v___x_5998_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v___x_5996_);
lean_ctor_set(v___x_5365_, 3, v___x_5994_);
lean_ctor_set(v___x_5365_, 2, v_v_5988_);
lean_ctor_set(v___x_5365_, 1, v_k_5987_);
lean_ctor_set(v___x_5365_, 0, v___x_5992_);
v___x_5998_ = v___x_5365_;
goto v_reusejp_5997_;
}
else
{
lean_object* v_reuseFailAlloc_5999_; 
v_reuseFailAlloc_5999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5999_, 0, v___x_5992_);
lean_ctor_set(v_reuseFailAlloc_5999_, 1, v_k_5987_);
lean_ctor_set(v_reuseFailAlloc_5999_, 2, v_v_5988_);
lean_ctor_set(v_reuseFailAlloc_5999_, 3, v___x_5994_);
lean_ctor_set(v_reuseFailAlloc_5999_, 4, v___x_5996_);
v___x_5998_ = v_reuseFailAlloc_5999_;
goto v_reusejp_5997_;
}
v_reusejp_5997_:
{
return v___x_5998_;
}
}
}
}
}
}
else
{
lean_object* v___x_6010_; lean_object* v___x_6012_; 
v___x_6010_ = lean_unsigned_to_nat(2u);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v_r_5981_);
lean_ctor_set(v___x_5365_, 0, v___x_6010_);
v___x_6012_ = v___x_5365_;
goto v_reusejp_6011_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v___x_6010_);
lean_ctor_set(v_reuseFailAlloc_6013_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_6013_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_6013_, 3, v_l_5362_);
lean_ctor_set(v_reuseFailAlloc_6013_, 4, v_r_5981_);
v___x_6012_ = v_reuseFailAlloc_6013_;
goto v_reusejp_6011_;
}
v_reusejp_6011_:
{
return v___x_6012_;
}
}
}
}
else
{
lean_object* v___x_6015_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 4, v_l_5362_);
lean_ctor_set(v___x_5365_, 0, v___x_5854_);
v___x_6015_ = v___x_5365_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v___x_5854_);
lean_ctor_set(v_reuseFailAlloc_6016_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_6016_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_6016_, 3, v_l_5362_);
lean_ctor_set(v_reuseFailAlloc_6016_, 4, v_l_5362_);
v___x_6015_ = v_reuseFailAlloc_6016_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
return v___x_6015_;
}
}
}
}
}
}
}
else
{
return v_t_5359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg___boxed(lean_object* v_k_6019_, lean_object* v_t_6020_){
_start:
{
lean_object* v_res_6021_; 
v_res_6021_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6019_, v_t_6020_);
lean_dec(v_k_6019_);
return v_res_6021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(lean_object* v_init_6022_, lean_object* v_x_6023_){
_start:
{
if (lean_obj_tag(v_x_6023_) == 0)
{
lean_object* v_k_6024_; lean_object* v_l_6025_; lean_object* v_r_6026_; lean_object* v___x_6027_; lean_object* v_ileans_6028_; lean_object* v_workers_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6038_; 
v_k_6024_ = lean_ctor_get(v_x_6023_, 1);
v_l_6025_ = lean_ctor_get(v_x_6023_, 3);
v_r_6026_ = lean_ctor_get(v_x_6023_, 4);
v___x_6027_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6022_, v_l_6025_);
v_ileans_6028_ = lean_ctor_get(v___x_6027_, 0);
v_workers_6029_ = lean_ctor_get(v___x_6027_, 1);
v_isSharedCheck_6038_ = !lean_is_exclusive(v___x_6027_);
if (v_isSharedCheck_6038_ == 0)
{
v___x_6031_ = v___x_6027_;
v_isShared_6032_ = v_isSharedCheck_6038_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_workers_6029_);
lean_inc(v_ileans_6028_);
lean_dec(v___x_6027_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6038_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6033_; lean_object* v___x_6035_; 
v___x_6033_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6024_, v_ileans_6028_);
if (v_isShared_6032_ == 0)
{
lean_ctor_set(v___x_6031_, 0, v___x_6033_);
v___x_6035_ = v___x_6031_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6037_; 
v_reuseFailAlloc_6037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6033_);
lean_ctor_set(v_reuseFailAlloc_6037_, 1, v_workers_6029_);
v___x_6035_ = v_reuseFailAlloc_6037_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
v_init_6022_ = v___x_6035_;
v_x_6023_ = v_r_6026_;
goto _start;
}
}
}
else
{
return v_init_6022_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2___boxed(lean_object* v_init_6039_, lean_object* v_x_6040_){
_start:
{
lean_object* v_res_6041_; 
v_res_6041_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6039_, v_x_6040_);
lean_dec(v_x_6040_);
return v_res_6041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean(lean_object* v_self_6042_, lean_object* v_path_6043_){
_start:
{
lean_object* v_ileans_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; 
v_ileans_6044_ = lean_ctor_get(v_self_6042_, 0);
lean_inc(v_ileans_6044_);
v___x_6045_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6043_, v_ileans_6044_);
v___x_6046_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_self_6042_, v___x_6045_);
lean_dec(v___x_6045_);
return v___x_6046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeIlean___boxed(lean_object* v_self_6047_, lean_object* v_path_6048_){
_start:
{
lean_object* v_res_6049_; 
v_res_6049_ = l_Lean_Server_References_removeIlean(v_self_6047_, v_path_6048_);
lean_dec_ref(v_path_6048_);
return v_res_6049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(lean_object* v_00_u03b2_6050_, lean_object* v_k_6051_, lean_object* v_t_6052_, lean_object* v_h_6053_){
_start:
{
lean_object* v___x_6054_; 
v___x_6054_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_k_6051_, v_t_6052_);
return v___x_6054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___boxed(lean_object* v_00_u03b2_6055_, lean_object* v_k_6056_, lean_object* v_t_6057_, lean_object* v_h_6058_){
_start:
{
lean_object* v_res_6059_; 
v_res_6059_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0(v_00_u03b2_6055_, v_k_6056_, v_t_6057_, v_h_6058_);
lean_dec(v_k_6056_);
return v_res_6059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(lean_object* v_path_6060_, lean_object* v_t_6061_, lean_object* v_hl_6062_){
_start:
{
lean_object* v___x_6063_; 
v___x_6063_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___redArg(v_path_6060_, v_t_6061_);
return v___x_6063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1___boxed(lean_object* v_path_6064_, lean_object* v_t_6065_, lean_object* v_hl_6066_){
_start:
{
lean_object* v_res_6067_; 
v_res_6067_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_Server_References_removeIlean_spec__1(v_path_6064_, v_t_6065_, v_hl_6066_);
lean_dec_ref(v_path_6064_);
return v_res_6067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(lean_object* v_init_6068_, lean_object* v_t_6069_){
_start:
{
lean_object* v___x_6070_; 
v___x_6070_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2_spec__2(v_init_6068_, v_t_6069_);
return v___x_6070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2___boxed(lean_object* v_init_6071_, lean_object* v_t_6072_){
_start:
{
lean_object* v_res_6073_; 
v_res_6073_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_removeIlean_spec__2(v_init_6071_, v_t_6072_);
lean_dec(v_t_6072_);
return v_res_6073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(lean_object* v_t_6074_, lean_object* v_k_6075_){
_start:
{
if (lean_obj_tag(v_t_6074_) == 0)
{
lean_object* v_k_6076_; lean_object* v_v_6077_; lean_object* v_l_6078_; lean_object* v_r_6079_; uint8_t v___x_6080_; 
v_k_6076_ = lean_ctor_get(v_t_6074_, 1);
v_v_6077_ = lean_ctor_get(v_t_6074_, 2);
v_l_6078_ = lean_ctor_get(v_t_6074_, 3);
v_r_6079_ = lean_ctor_get(v_t_6074_, 4);
v___x_6080_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6075_, v_k_6076_);
switch(v___x_6080_)
{
case 0:
{
v_t_6074_ = v_l_6078_;
goto _start;
}
case 1:
{
lean_object* v___x_6082_; 
lean_inc(v_v_6077_);
v___x_6082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6082_, 0, v_v_6077_);
return v___x_6082_;
}
default: 
{
v_t_6074_ = v_r_6079_;
goto _start;
}
}
}
else
{
lean_object* v___x_6084_; 
v___x_6084_ = lean_box(0);
return v___x_6084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg___boxed(lean_object* v_t_6085_, lean_object* v_k_6086_){
_start:
{
lean_object* v_res_6087_; 
v_res_6087_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6085_, v_k_6086_);
lean_dec(v_k_6086_);
lean_dec(v_t_6085_);
return v_res_6087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo(lean_object* v_self_6088_, lean_object* v_name_6089_, lean_object* v_moduleUri_6090_, lean_object* v_version_6091_, lean_object* v_directImports_6092_, uint8_t v_isSetupFailure_6093_){
_start:
{
lean_object* v___x_6095_; 
v___x_6095_ = l_Lean_Server_DirectImports_convertImportInfos(v_directImports_6092_);
if (lean_obj_tag(v___x_6095_) == 0)
{
lean_object* v_a_6096_; lean_object* v___x_6098_; uint8_t v_isShared_6099_; uint8_t v_isSharedCheck_6162_; 
v_a_6096_ = lean_ctor_get(v___x_6095_, 0);
v_isSharedCheck_6162_ = !lean_is_exclusive(v___x_6095_);
if (v_isSharedCheck_6162_ == 0)
{
v___x_6098_ = v___x_6095_;
v_isShared_6099_ = v_isSharedCheck_6162_;
goto v_resetjp_6097_;
}
else
{
lean_inc(v_a_6096_);
lean_dec(v___x_6095_);
v___x_6098_ = lean_box(0);
v_isShared_6099_ = v_isSharedCheck_6162_;
goto v_resetjp_6097_;
}
v_resetjp_6097_:
{
lean_object* v_ileans_6100_; lean_object* v_workers_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; 
v_ileans_6100_ = lean_ctor_get(v_self_6088_, 0);
v_workers_6101_ = lean_ctor_get(v_self_6088_, 1);
v___x_6102_ = lean_box(1);
v___x_6103_ = lean_box(v_isSetupFailure_6093_);
v___x_6104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
v___x_6105_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6101_, v_name_6089_);
if (lean_obj_tag(v___x_6105_) == 1)
{
lean_object* v_val_6106_; lean_object* v_version_6107_; lean_object* v_refs_6108_; lean_object* v_decls_6109_; lean_object* v___x_6111_; uint8_t v_isShared_6112_; uint8_t v_isSharedCheck_6144_; 
v_val_6106_ = lean_ctor_get(v___x_6105_, 0);
lean_inc(v_val_6106_);
lean_dec_ref_known(v___x_6105_, 1);
v_version_6107_ = lean_ctor_get(v_val_6106_, 1);
v_refs_6108_ = lean_ctor_get(v_val_6106_, 4);
v_decls_6109_ = lean_ctor_get(v_val_6106_, 5);
v_isSharedCheck_6144_ = !lean_is_exclusive(v_val_6106_);
if (v_isSharedCheck_6144_ == 0)
{
lean_object* v_unused_6145_; lean_object* v_unused_6146_; lean_object* v_unused_6147_; 
v_unused_6145_ = lean_ctor_get(v_val_6106_, 3);
lean_dec(v_unused_6145_);
v_unused_6146_ = lean_ctor_get(v_val_6106_, 2);
lean_dec(v_unused_6146_);
v_unused_6147_ = lean_ctor_get(v_val_6106_, 0);
lean_dec(v_unused_6147_);
v___x_6111_ = v_val_6106_;
v_isShared_6112_ = v_isSharedCheck_6144_;
goto v_resetjp_6110_;
}
else
{
lean_inc(v_decls_6109_);
lean_inc(v_refs_6108_);
lean_inc(v_version_6107_);
lean_dec(v_val_6106_);
v___x_6111_ = lean_box(0);
v_isShared_6112_ = v_isSharedCheck_6144_;
goto v_resetjp_6110_;
}
v_resetjp_6110_:
{
uint8_t v___x_6113_; 
v___x_6113_ = lean_nat_dec_lt(v_version_6091_, v_version_6107_);
if (v___x_6113_ == 0)
{
lean_object* v___x_6115_; uint8_t v_isShared_6116_; uint8_t v_isSharedCheck_6138_; 
lean_inc(v_workers_6101_);
lean_inc(v_ileans_6100_);
v_isSharedCheck_6138_ = !lean_is_exclusive(v_self_6088_);
if (v_isSharedCheck_6138_ == 0)
{
lean_object* v_unused_6139_; lean_object* v_unused_6140_; 
v_unused_6139_ = lean_ctor_get(v_self_6088_, 1);
lean_dec(v_unused_6139_);
v_unused_6140_ = lean_ctor_get(v_self_6088_, 0);
lean_dec(v_unused_6140_);
v___x_6115_ = v_self_6088_;
v_isShared_6116_ = v_isSharedCheck_6138_;
goto v_resetjp_6114_;
}
else
{
lean_dec(v_self_6088_);
v___x_6115_ = lean_box(0);
v_isShared_6116_ = v_isSharedCheck_6138_;
goto v_resetjp_6114_;
}
v_resetjp_6114_:
{
uint8_t v___x_6117_; 
v___x_6117_ = lean_nat_dec_eq(v_version_6091_, v_version_6107_);
lean_dec(v_version_6107_);
if (v___x_6117_ == 0)
{
lean_object* v___x_6119_; 
lean_dec(v_decls_6109_);
lean_dec(v_refs_6108_);
if (v_isShared_6112_ == 0)
{
lean_ctor_set(v___x_6111_, 5, v___x_6102_);
lean_ctor_set(v___x_6111_, 4, v___x_6102_);
lean_ctor_set(v___x_6111_, 3, v___x_6104_);
lean_ctor_set(v___x_6111_, 2, v_a_6096_);
lean_ctor_set(v___x_6111_, 1, v_version_6091_);
lean_ctor_set(v___x_6111_, 0, v_moduleUri_6090_);
v___x_6119_ = v___x_6111_;
goto v_reusejp_6118_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_moduleUri_6090_);
lean_ctor_set(v_reuseFailAlloc_6127_, 1, v_version_6091_);
lean_ctor_set(v_reuseFailAlloc_6127_, 2, v_a_6096_);
lean_ctor_set(v_reuseFailAlloc_6127_, 3, v___x_6104_);
lean_ctor_set(v_reuseFailAlloc_6127_, 4, v___x_6102_);
lean_ctor_set(v_reuseFailAlloc_6127_, 5, v___x_6102_);
v___x_6119_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6118_;
}
v_reusejp_6118_:
{
lean_object* v___x_6120_; lean_object* v___x_6122_; 
v___x_6120_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6089_, v___x_6119_, v_workers_6101_);
if (v_isShared_6116_ == 0)
{
lean_ctor_set(v___x_6115_, 1, v___x_6120_);
v___x_6122_ = v___x_6115_;
goto v_reusejp_6121_;
}
else
{
lean_object* v_reuseFailAlloc_6126_; 
v_reuseFailAlloc_6126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6126_, 0, v_ileans_6100_);
lean_ctor_set(v_reuseFailAlloc_6126_, 1, v___x_6120_);
v___x_6122_ = v_reuseFailAlloc_6126_;
goto v_reusejp_6121_;
}
v_reusejp_6121_:
{
lean_object* v___x_6124_; 
if (v_isShared_6099_ == 0)
{
lean_ctor_set(v___x_6098_, 0, v___x_6122_);
v___x_6124_ = v___x_6098_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v___x_6122_);
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
lean_object* v___x_6129_; 
if (v_isShared_6112_ == 0)
{
lean_ctor_set(v___x_6111_, 3, v___x_6104_);
lean_ctor_set(v___x_6111_, 2, v_a_6096_);
lean_ctor_set(v___x_6111_, 1, v_version_6091_);
lean_ctor_set(v___x_6111_, 0, v_moduleUri_6090_);
v___x_6129_ = v___x_6111_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6137_; 
v_reuseFailAlloc_6137_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_moduleUri_6090_);
lean_ctor_set(v_reuseFailAlloc_6137_, 1, v_version_6091_);
lean_ctor_set(v_reuseFailAlloc_6137_, 2, v_a_6096_);
lean_ctor_set(v_reuseFailAlloc_6137_, 3, v___x_6104_);
lean_ctor_set(v_reuseFailAlloc_6137_, 4, v_refs_6108_);
lean_ctor_set(v_reuseFailAlloc_6137_, 5, v_decls_6109_);
v___x_6129_ = v_reuseFailAlloc_6137_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
lean_object* v___x_6130_; lean_object* v___x_6132_; 
v___x_6130_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6089_, v___x_6129_, v_workers_6101_);
if (v_isShared_6116_ == 0)
{
lean_ctor_set(v___x_6115_, 1, v___x_6130_);
v___x_6132_ = v___x_6115_;
goto v_reusejp_6131_;
}
else
{
lean_object* v_reuseFailAlloc_6136_; 
v_reuseFailAlloc_6136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6136_, 0, v_ileans_6100_);
lean_ctor_set(v_reuseFailAlloc_6136_, 1, v___x_6130_);
v___x_6132_ = v_reuseFailAlloc_6136_;
goto v_reusejp_6131_;
}
v_reusejp_6131_:
{
lean_object* v___x_6134_; 
if (v_isShared_6099_ == 0)
{
lean_ctor_set(v___x_6098_, 0, v___x_6132_);
v___x_6134_ = v___x_6098_;
goto v_reusejp_6133_;
}
else
{
lean_object* v_reuseFailAlloc_6135_; 
v_reuseFailAlloc_6135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6135_, 0, v___x_6132_);
v___x_6134_ = v_reuseFailAlloc_6135_;
goto v_reusejp_6133_;
}
v_reusejp_6133_:
{
return v___x_6134_;
}
}
}
}
}
}
else
{
lean_object* v___x_6142_; 
lean_del_object(v___x_6111_);
lean_dec(v_decls_6109_);
lean_dec(v_refs_6108_);
lean_dec(v_version_6107_);
lean_dec_ref_known(v___x_6104_, 1);
lean_dec(v_a_6096_);
lean_dec(v_version_6091_);
lean_dec_ref(v_moduleUri_6090_);
lean_dec(v_name_6089_);
if (v_isShared_6099_ == 0)
{
lean_ctor_set(v___x_6098_, 0, v_self_6088_);
v___x_6142_ = v___x_6098_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6143_; 
v_reuseFailAlloc_6143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6143_, 0, v_self_6088_);
v___x_6142_ = v_reuseFailAlloc_6143_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
return v___x_6142_;
}
}
}
}
else
{
lean_object* v___x_6149_; uint8_t v_isShared_6150_; uint8_t v_isSharedCheck_6159_; 
lean_inc(v_workers_6101_);
lean_inc(v_ileans_6100_);
lean_dec(v___x_6105_);
v_isSharedCheck_6159_ = !lean_is_exclusive(v_self_6088_);
if (v_isSharedCheck_6159_ == 0)
{
lean_object* v_unused_6160_; lean_object* v_unused_6161_; 
v_unused_6160_ = lean_ctor_get(v_self_6088_, 1);
lean_dec(v_unused_6160_);
v_unused_6161_ = lean_ctor_get(v_self_6088_, 0);
lean_dec(v_unused_6161_);
v___x_6149_ = v_self_6088_;
v_isShared_6150_ = v_isSharedCheck_6159_;
goto v_resetjp_6148_;
}
else
{
lean_dec(v_self_6088_);
v___x_6149_ = lean_box(0);
v_isShared_6150_ = v_isSharedCheck_6159_;
goto v_resetjp_6148_;
}
v_resetjp_6148_:
{
lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6154_; 
v___x_6151_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6151_, 0, v_moduleUri_6090_);
lean_ctor_set(v___x_6151_, 1, v_version_6091_);
lean_ctor_set(v___x_6151_, 2, v_a_6096_);
lean_ctor_set(v___x_6151_, 3, v___x_6104_);
lean_ctor_set(v___x_6151_, 4, v___x_6102_);
lean_ctor_set(v___x_6151_, 5, v___x_6102_);
v___x_6152_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6089_, v___x_6151_, v_workers_6101_);
if (v_isShared_6150_ == 0)
{
lean_ctor_set(v___x_6149_, 1, v___x_6152_);
v___x_6154_ = v___x_6149_;
goto v_reusejp_6153_;
}
else
{
lean_object* v_reuseFailAlloc_6158_; 
v_reuseFailAlloc_6158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6158_, 0, v_ileans_6100_);
lean_ctor_set(v_reuseFailAlloc_6158_, 1, v___x_6152_);
v___x_6154_ = v_reuseFailAlloc_6158_;
goto v_reusejp_6153_;
}
v_reusejp_6153_:
{
lean_object* v___x_6156_; 
if (v_isShared_6099_ == 0)
{
lean_ctor_set(v___x_6098_, 0, v___x_6154_);
v___x_6156_ = v___x_6098_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6157_; 
v_reuseFailAlloc_6157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6157_, 0, v___x_6154_);
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
}
else
{
lean_object* v_a_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6170_; 
lean_dec(v_version_6091_);
lean_dec_ref(v_moduleUri_6090_);
lean_dec(v_name_6089_);
lean_dec_ref(v_self_6088_);
v_a_6163_ = lean_ctor_get(v___x_6095_, 0);
v_isSharedCheck_6170_ = !lean_is_exclusive(v___x_6095_);
if (v_isSharedCheck_6170_ == 0)
{
v___x_6165_ = v___x_6095_;
v_isShared_6166_ = v_isSharedCheck_6170_;
goto v_resetjp_6164_;
}
else
{
lean_inc(v_a_6163_);
lean_dec(v___x_6095_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6170_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
lean_object* v___x_6168_; 
if (v_isShared_6166_ == 0)
{
v___x_6168_ = v___x_6165_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_a_6163_);
v___x_6168_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
return v___x_6168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerSetupInfo___boxed(lean_object* v_self_6171_, lean_object* v_name_6172_, lean_object* v_moduleUri_6173_, lean_object* v_version_6174_, lean_object* v_directImports_6175_, lean_object* v_isSetupFailure_6176_, lean_object* v_a_6177_){
_start:
{
uint8_t v_isSetupFailure_boxed_6178_; lean_object* v_res_6179_; 
v_isSetupFailure_boxed_6178_ = lean_unbox(v_isSetupFailure_6176_);
v_res_6179_ = l_Lean_Server_References_updateWorkerSetupInfo(v_self_6171_, v_name_6172_, v_moduleUri_6173_, v_version_6174_, v_directImports_6175_, v_isSetupFailure_boxed_6178_);
lean_dec_ref(v_directImports_6175_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(lean_object* v_00_u03b4_6180_, lean_object* v_t_6181_, lean_object* v_k_6182_){
_start:
{
lean_object* v___x_6183_; 
v___x_6183_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_t_6181_, v_k_6182_);
return v___x_6183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___boxed(lean_object* v_00_u03b4_6184_, lean_object* v_t_6185_, lean_object* v_k_6186_){
_start:
{
lean_object* v_res_6187_; 
v_res_6187_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0(v_00_u03b4_6184_, v_t_6185_, v_k_6186_);
lean_dec(v_k_6186_);
lean_dec(v_t_6185_);
return v_res_6187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___lam__0(lean_object* v_x_6188_, lean_object* v_____s_6189_){
_start:
{
lean_object* v_fst_6190_; lean_object* v_snd_6191_; lean_object* v_r_6192_; lean_object* v___x_6193_; 
v_fst_6190_ = lean_ctor_get(v_x_6188_, 0);
lean_inc(v_fst_6190_);
v_snd_6191_ = lean_ctor_get(v_x_6188_, 1);
lean_inc(v_snd_6191_);
lean_dec_ref(v_x_6188_);
v_r_6192_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_RefInfo_toLspRefInfo_spec__0___redArg(v_fst_6190_, v_snd_6191_, v_____s_6189_);
v___x_6193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6193_, 0, v_r_6192_);
return v___x_6193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(lean_object* v_t_6194_, lean_object* v_k_6195_, lean_object* v_fallback_6196_){
_start:
{
if (lean_obj_tag(v_t_6194_) == 0)
{
lean_object* v_k_6197_; lean_object* v_v_6198_; lean_object* v_l_6199_; lean_object* v_r_6200_; uint8_t v___x_6201_; 
v_k_6197_ = lean_ctor_get(v_t_6194_, 1);
v_v_6198_ = lean_ctor_get(v_t_6194_, 2);
v_l_6199_ = lean_ctor_get(v_t_6194_, 3);
v_r_6200_ = lean_ctor_get(v_t_6194_, 4);
v___x_6201_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6195_, v_k_6197_);
switch(v___x_6201_)
{
case 0:
{
v_t_6194_ = v_l_6199_;
goto _start;
}
case 1:
{
lean_inc(v_v_6198_);
return v_v_6198_;
}
default: 
{
v_t_6194_ = v_r_6200_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6196_);
return v_fallback_6196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg___boxed(lean_object* v_t_6204_, lean_object* v_k_6205_, lean_object* v_fallback_6206_){
_start:
{
lean_object* v_res_6207_; 
v_res_6207_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6204_, v_k_6205_, v_fallback_6206_);
lean_dec(v_fallback_6206_);
lean_dec_ref(v_k_6205_);
lean_dec(v_t_6204_);
return v_res_6207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(lean_object* v_init_6208_, lean_object* v_x_6209_){
_start:
{
if (lean_obj_tag(v_x_6209_) == 0)
{
lean_object* v_k_6210_; lean_object* v_v_6211_; lean_object* v_l_6212_; lean_object* v_r_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; 
v_k_6210_ = lean_ctor_get(v_x_6209_, 1);
lean_inc(v_k_6210_);
v_v_6211_ = lean_ctor_get(v_x_6209_, 2);
lean_inc(v_v_6211_);
v_l_6212_ = lean_ctor_get(v_x_6209_, 3);
lean_inc(v_l_6212_);
v_r_6213_ = lean_ctor_get(v_x_6209_, 4);
lean_inc(v_r_6213_);
lean_dec_ref_known(v_x_6209_, 5);
v___x_6214_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6208_, v_l_6212_);
v___x_6215_ = ((lean_object*)(l_Lean_Lsp_RefInfo_empty));
v___x_6216_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v___x_6214_, v_k_6210_, v___x_6215_);
v___x_6217_ = l_Lean_Lsp_RefInfo_merge(v___x_6216_, v_v_6211_);
v___x_6218_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_ModuleRefs_toLspModuleRefs_spec__0___redArg(v_k_6210_, v___x_6217_, v___x_6214_);
v_init_6208_ = v___x_6218_;
v_x_6209_ = v_r_6213_;
goto _start;
}
else
{
return v_init_6208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object* v_self_6221_, lean_object* v_name_6222_, lean_object* v_moduleUri_6223_, lean_object* v_version_6224_, lean_object* v_refs_6225_, lean_object* v_decls_6226_){
_start:
{
lean_object* v_ileans_6228_; lean_object* v_workers_6229_; lean_object* v___x_6230_; 
v_ileans_6228_ = lean_ctor_get(v_self_6221_, 0);
v_workers_6229_ = lean_ctor_get(v_self_6221_, 1);
v___x_6230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6229_, v_name_6222_);
if (lean_obj_tag(v___x_6230_) == 1)
{
lean_object* v_val_6231_; lean_object* v___x_6233_; uint8_t v_isShared_6234_; uint8_t v_isSharedCheck_6279_; 
v_val_6231_ = lean_ctor_get(v___x_6230_, 0);
v_isSharedCheck_6279_ = !lean_is_exclusive(v___x_6230_);
if (v_isSharedCheck_6279_ == 0)
{
v___x_6233_ = v___x_6230_;
v_isShared_6234_ = v_isSharedCheck_6279_;
goto v_resetjp_6232_;
}
else
{
lean_inc(v_val_6231_);
lean_dec(v___x_6230_);
v___x_6233_ = lean_box(0);
v_isShared_6234_ = v_isSharedCheck_6279_;
goto v_resetjp_6232_;
}
v_resetjp_6232_:
{
lean_object* v_version_6235_; lean_object* v_directImports_6236_; lean_object* v_isSetupFailure_x3f_6237_; lean_object* v_refs_6238_; lean_object* v_decls_6239_; lean_object* v___x_6241_; uint8_t v_isShared_6242_; uint8_t v_isSharedCheck_6277_; 
v_version_6235_ = lean_ctor_get(v_val_6231_, 1);
v_directImports_6236_ = lean_ctor_get(v_val_6231_, 2);
v_isSetupFailure_x3f_6237_ = lean_ctor_get(v_val_6231_, 3);
v_refs_6238_ = lean_ctor_get(v_val_6231_, 4);
v_decls_6239_ = lean_ctor_get(v_val_6231_, 5);
v_isSharedCheck_6277_ = !lean_is_exclusive(v_val_6231_);
if (v_isSharedCheck_6277_ == 0)
{
lean_object* v_unused_6278_; 
v_unused_6278_ = lean_ctor_get(v_val_6231_, 0);
lean_dec(v_unused_6278_);
v___x_6241_ = v_val_6231_;
v_isShared_6242_ = v_isSharedCheck_6277_;
goto v_resetjp_6240_;
}
else
{
lean_inc(v_decls_6239_);
lean_inc(v_refs_6238_);
lean_inc(v_isSetupFailure_x3f_6237_);
lean_inc(v_directImports_6236_);
lean_inc(v_version_6235_);
lean_dec(v_val_6231_);
v___x_6241_ = lean_box(0);
v_isShared_6242_ = v_isSharedCheck_6277_;
goto v_resetjp_6240_;
}
v_resetjp_6240_:
{
uint8_t v___x_6243_; 
v___x_6243_ = lean_nat_dec_lt(v_version_6224_, v_version_6235_);
if (v___x_6243_ == 0)
{
lean_object* v___x_6245_; uint8_t v_isShared_6246_; uint8_t v_isSharedCheck_6271_; 
lean_inc(v_workers_6229_);
lean_inc(v_ileans_6228_);
v_isSharedCheck_6271_ = !lean_is_exclusive(v_self_6221_);
if (v_isSharedCheck_6271_ == 0)
{
lean_object* v_unused_6272_; lean_object* v_unused_6273_; 
v_unused_6272_ = lean_ctor_get(v_self_6221_, 1);
lean_dec(v_unused_6272_);
v_unused_6273_ = lean_ctor_get(v_self_6221_, 0);
lean_dec(v_unused_6273_);
v___x_6245_ = v_self_6221_;
v_isShared_6246_ = v_isSharedCheck_6271_;
goto v_resetjp_6244_;
}
else
{
lean_dec(v_self_6221_);
v___x_6245_ = lean_box(0);
v_isShared_6246_ = v_isSharedCheck_6271_;
goto v_resetjp_6244_;
}
v_resetjp_6244_:
{
uint8_t v___x_6247_; 
v___x_6247_ = lean_nat_dec_eq(v_version_6224_, v_version_6235_);
lean_dec(v_version_6235_);
if (v___x_6247_ == 0)
{
lean_object* v___x_6249_; 
lean_dec(v_decls_6239_);
lean_dec(v_refs_6238_);
if (v_isShared_6242_ == 0)
{
lean_ctor_set(v___x_6241_, 5, v_decls_6226_);
lean_ctor_set(v___x_6241_, 4, v_refs_6225_);
lean_ctor_set(v___x_6241_, 1, v_version_6224_);
lean_ctor_set(v___x_6241_, 0, v_moduleUri_6223_);
v___x_6249_ = v___x_6241_;
goto v_reusejp_6248_;
}
else
{
lean_object* v_reuseFailAlloc_6257_; 
v_reuseFailAlloc_6257_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6257_, 0, v_moduleUri_6223_);
lean_ctor_set(v_reuseFailAlloc_6257_, 1, v_version_6224_);
lean_ctor_set(v_reuseFailAlloc_6257_, 2, v_directImports_6236_);
lean_ctor_set(v_reuseFailAlloc_6257_, 3, v_isSetupFailure_x3f_6237_);
lean_ctor_set(v_reuseFailAlloc_6257_, 4, v_refs_6225_);
lean_ctor_set(v_reuseFailAlloc_6257_, 5, v_decls_6226_);
v___x_6249_ = v_reuseFailAlloc_6257_;
goto v_reusejp_6248_;
}
v_reusejp_6248_:
{
lean_object* v___x_6250_; lean_object* v___x_6252_; 
v___x_6250_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6222_, v___x_6249_, v_workers_6229_);
if (v_isShared_6246_ == 0)
{
lean_ctor_set(v___x_6245_, 1, v___x_6250_);
v___x_6252_ = v___x_6245_;
goto v_reusejp_6251_;
}
else
{
lean_object* v_reuseFailAlloc_6256_; 
v_reuseFailAlloc_6256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6256_, 0, v_ileans_6228_);
lean_ctor_set(v_reuseFailAlloc_6256_, 1, v___x_6250_);
v___x_6252_ = v_reuseFailAlloc_6256_;
goto v_reusejp_6251_;
}
v_reusejp_6251_:
{
lean_object* v___x_6254_; 
if (v_isShared_6234_ == 0)
{
lean_ctor_set_tag(v___x_6233_, 0);
lean_ctor_set(v___x_6233_, 0, v___x_6252_);
v___x_6254_ = v___x_6233_;
goto v_reusejp_6253_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v___x_6252_);
v___x_6254_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6253_;
}
v_reusejp_6253_:
{
return v___x_6254_;
}
}
}
}
else
{
lean_object* v___f_6258_; lean_object* v_mergedRefs_6259_; lean_object* v_mergedDecls_6260_; lean_object* v___x_6262_; 
v___f_6258_ = ((lean_object*)(l_Lean_Server_References_updateWorkerRefs___closed__0));
v_mergedRefs_6259_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_refs_6238_, v_refs_6225_);
v_mergedDecls_6260_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_box(0), v_decls_6226_, v_decls_6239_, v___f_6258_);
lean_dec(v_decls_6226_);
if (v_isShared_6242_ == 0)
{
lean_ctor_set(v___x_6241_, 5, v_mergedDecls_6260_);
lean_ctor_set(v___x_6241_, 4, v_mergedRefs_6259_);
lean_ctor_set(v___x_6241_, 1, v_version_6224_);
lean_ctor_set(v___x_6241_, 0, v_moduleUri_6223_);
v___x_6262_ = v___x_6241_;
goto v_reusejp_6261_;
}
else
{
lean_object* v_reuseFailAlloc_6270_; 
v_reuseFailAlloc_6270_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6270_, 0, v_moduleUri_6223_);
lean_ctor_set(v_reuseFailAlloc_6270_, 1, v_version_6224_);
lean_ctor_set(v_reuseFailAlloc_6270_, 2, v_directImports_6236_);
lean_ctor_set(v_reuseFailAlloc_6270_, 3, v_isSetupFailure_x3f_6237_);
lean_ctor_set(v_reuseFailAlloc_6270_, 4, v_mergedRefs_6259_);
lean_ctor_set(v_reuseFailAlloc_6270_, 5, v_mergedDecls_6260_);
v___x_6262_ = v_reuseFailAlloc_6270_;
goto v_reusejp_6261_;
}
v_reusejp_6261_:
{
lean_object* v___x_6263_; lean_object* v___x_6265_; 
v___x_6263_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6222_, v___x_6262_, v_workers_6229_);
if (v_isShared_6246_ == 0)
{
lean_ctor_set(v___x_6245_, 1, v___x_6263_);
v___x_6265_ = v___x_6245_;
goto v_reusejp_6264_;
}
else
{
lean_object* v_reuseFailAlloc_6269_; 
v_reuseFailAlloc_6269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6269_, 0, v_ileans_6228_);
lean_ctor_set(v_reuseFailAlloc_6269_, 1, v___x_6263_);
v___x_6265_ = v_reuseFailAlloc_6269_;
goto v_reusejp_6264_;
}
v_reusejp_6264_:
{
lean_object* v___x_6267_; 
if (v_isShared_6234_ == 0)
{
lean_ctor_set_tag(v___x_6233_, 0);
lean_ctor_set(v___x_6233_, 0, v___x_6265_);
v___x_6267_ = v___x_6233_;
goto v_reusejp_6266_;
}
else
{
lean_object* v_reuseFailAlloc_6268_; 
v_reuseFailAlloc_6268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6268_, 0, v___x_6265_);
v___x_6267_ = v_reuseFailAlloc_6268_;
goto v_reusejp_6266_;
}
v_reusejp_6266_:
{
return v___x_6267_;
}
}
}
}
}
}
else
{
lean_object* v___x_6275_; 
lean_del_object(v___x_6241_);
lean_dec(v_decls_6239_);
lean_dec(v_refs_6238_);
lean_dec(v_isSetupFailure_x3f_6237_);
lean_dec_ref(v_directImports_6236_);
lean_dec(v_version_6235_);
lean_dec(v_decls_6226_);
lean_dec(v_refs_6225_);
lean_dec(v_version_6224_);
lean_dec_ref(v_moduleUri_6223_);
lean_dec(v_name_6222_);
if (v_isShared_6234_ == 0)
{
lean_ctor_set_tag(v___x_6233_, 0);
lean_ctor_set(v___x_6233_, 0, v_self_6221_);
v___x_6275_ = v___x_6233_;
goto v_reusejp_6274_;
}
else
{
lean_object* v_reuseFailAlloc_6276_; 
v_reuseFailAlloc_6276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_self_6221_);
v___x_6275_ = v_reuseFailAlloc_6276_;
goto v_reusejp_6274_;
}
v_reusejp_6274_:
{
return v___x_6275_;
}
}
}
}
}
else
{
lean_object* v___x_6281_; uint8_t v_isShared_6282_; uint8_t v_isSharedCheck_6291_; 
lean_inc(v_workers_6229_);
lean_inc(v_ileans_6228_);
lean_dec(v___x_6230_);
v_isSharedCheck_6291_ = !lean_is_exclusive(v_self_6221_);
if (v_isSharedCheck_6291_ == 0)
{
lean_object* v_unused_6292_; lean_object* v_unused_6293_; 
v_unused_6292_ = lean_ctor_get(v_self_6221_, 1);
lean_dec(v_unused_6292_);
v_unused_6293_ = lean_ctor_get(v_self_6221_, 0);
lean_dec(v_unused_6293_);
v___x_6281_ = v_self_6221_;
v_isShared_6282_ = v_isSharedCheck_6291_;
goto v_resetjp_6280_;
}
else
{
lean_dec(v_self_6221_);
v___x_6281_ = lean_box(0);
v_isShared_6282_ = v_isSharedCheck_6291_;
goto v_resetjp_6280_;
}
v_resetjp_6280_:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6288_; 
v___x_6283_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6284_ = lean_box(0);
v___x_6285_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6285_, 0, v_moduleUri_6223_);
lean_ctor_set(v___x_6285_, 1, v_version_6224_);
lean_ctor_set(v___x_6285_, 2, v___x_6283_);
lean_ctor_set(v___x_6285_, 3, v___x_6284_);
lean_ctor_set(v___x_6285_, 4, v_refs_6225_);
lean_ctor_set(v___x_6285_, 5, v_decls_6226_);
v___x_6286_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6222_, v___x_6285_, v_workers_6229_);
if (v_isShared_6282_ == 0)
{
lean_ctor_set(v___x_6281_, 1, v___x_6286_);
v___x_6288_ = v___x_6281_;
goto v_reusejp_6287_;
}
else
{
lean_object* v_reuseFailAlloc_6290_; 
v_reuseFailAlloc_6290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6290_, 0, v_ileans_6228_);
lean_ctor_set(v_reuseFailAlloc_6290_, 1, v___x_6286_);
v___x_6288_ = v_reuseFailAlloc_6290_;
goto v_reusejp_6287_;
}
v_reusejp_6287_:
{
lean_object* v___x_6289_; 
v___x_6289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6289_, 0, v___x_6288_);
return v___x_6289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_updateWorkerRefs___boxed(lean_object* v_self_6294_, lean_object* v_name_6295_, lean_object* v_moduleUri_6296_, lean_object* v_version_6297_, lean_object* v_refs_6298_, lean_object* v_decls_6299_, lean_object* v_a_6300_){
_start:
{
lean_object* v_res_6301_; 
v_res_6301_ = l_Lean_Server_References_updateWorkerRefs(v_self_6294_, v_name_6295_, v_moduleUri_6296_, v_version_6297_, v_refs_6298_, v_decls_6299_);
return v_res_6301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(lean_object* v_00_u03b4_6302_, lean_object* v_t_6303_, lean_object* v_k_6304_, lean_object* v_fallback_6305_){
_start:
{
lean_object* v___x_6306_; 
v___x_6306_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___redArg(v_t_6303_, v_k_6304_, v_fallback_6305_);
return v___x_6306_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0___boxed(lean_object* v_00_u03b4_6307_, lean_object* v_t_6308_, lean_object* v_k_6309_, lean_object* v_fallback_6310_){
_start:
{
lean_object* v_res_6311_; 
v_res_6311_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_References_updateWorkerRefs_spec__0(v_00_u03b4_6307_, v_t_6308_, v_k_6309_, v_fallback_6310_);
lean_dec(v_fallback_6310_);
lean_dec_ref(v_k_6309_);
lean_dec(v_t_6308_);
return v_res_6311_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1(lean_object* v_init_6312_, lean_object* v_t_6313_){
_start:
{
lean_object* v___x_6314_; 
v___x_6314_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_updateWorkerRefs_spec__1_spec__1(v_init_6312_, v_t_6313_);
return v___x_6314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object* v_self_6315_, lean_object* v_name_6316_, lean_object* v_moduleUri_6317_, lean_object* v_version_6318_, lean_object* v_refs_6319_, lean_object* v_decls_6320_){
_start:
{
lean_object* v_ileans_6322_; lean_object* v_workers_6323_; lean_object* v___x_6324_; 
v_ileans_6322_ = lean_ctor_get(v_self_6315_, 0);
v_workers_6323_ = lean_ctor_get(v_self_6315_, 1);
v___x_6324_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6323_, v_name_6316_);
if (lean_obj_tag(v___x_6324_) == 1)
{
lean_object* v_val_6325_; lean_object* v___x_6327_; uint8_t v_isShared_6328_; uint8_t v_isSharedCheck_6359_; 
v_val_6325_ = lean_ctor_get(v___x_6324_, 0);
v_isSharedCheck_6359_ = !lean_is_exclusive(v___x_6324_);
if (v_isSharedCheck_6359_ == 0)
{
v___x_6327_ = v___x_6324_;
v_isShared_6328_ = v_isSharedCheck_6359_;
goto v_resetjp_6326_;
}
else
{
lean_inc(v_val_6325_);
lean_dec(v___x_6324_);
v___x_6327_ = lean_box(0);
v_isShared_6328_ = v_isSharedCheck_6359_;
goto v_resetjp_6326_;
}
v_resetjp_6326_:
{
lean_object* v_version_6329_; lean_object* v_directImports_6330_; lean_object* v_isSetupFailure_x3f_6331_; lean_object* v___x_6333_; uint8_t v_isShared_6334_; uint8_t v_isSharedCheck_6355_; 
v_version_6329_ = lean_ctor_get(v_val_6325_, 1);
v_directImports_6330_ = lean_ctor_get(v_val_6325_, 2);
v_isSetupFailure_x3f_6331_ = lean_ctor_get(v_val_6325_, 3);
v_isSharedCheck_6355_ = !lean_is_exclusive(v_val_6325_);
if (v_isSharedCheck_6355_ == 0)
{
lean_object* v_unused_6356_; lean_object* v_unused_6357_; lean_object* v_unused_6358_; 
v_unused_6356_ = lean_ctor_get(v_val_6325_, 5);
lean_dec(v_unused_6356_);
v_unused_6357_ = lean_ctor_get(v_val_6325_, 4);
lean_dec(v_unused_6357_);
v_unused_6358_ = lean_ctor_get(v_val_6325_, 0);
lean_dec(v_unused_6358_);
v___x_6333_ = v_val_6325_;
v_isShared_6334_ = v_isSharedCheck_6355_;
goto v_resetjp_6332_;
}
else
{
lean_inc(v_isSetupFailure_x3f_6331_);
lean_inc(v_directImports_6330_);
lean_inc(v_version_6329_);
lean_dec(v_val_6325_);
v___x_6333_ = lean_box(0);
v_isShared_6334_ = v_isSharedCheck_6355_;
goto v_resetjp_6332_;
}
v_resetjp_6332_:
{
uint8_t v___x_6335_; 
v___x_6335_ = lean_nat_dec_lt(v_version_6318_, v_version_6329_);
lean_dec(v_version_6329_);
if (v___x_6335_ == 0)
{
lean_object* v___x_6337_; uint8_t v_isShared_6338_; uint8_t v_isSharedCheck_6349_; 
lean_inc(v_workers_6323_);
lean_inc(v_ileans_6322_);
v_isSharedCheck_6349_ = !lean_is_exclusive(v_self_6315_);
if (v_isSharedCheck_6349_ == 0)
{
lean_object* v_unused_6350_; lean_object* v_unused_6351_; 
v_unused_6350_ = lean_ctor_get(v_self_6315_, 1);
lean_dec(v_unused_6350_);
v_unused_6351_ = lean_ctor_get(v_self_6315_, 0);
lean_dec(v_unused_6351_);
v___x_6337_ = v_self_6315_;
v_isShared_6338_ = v_isSharedCheck_6349_;
goto v_resetjp_6336_;
}
else
{
lean_dec(v_self_6315_);
v___x_6337_ = lean_box(0);
v_isShared_6338_ = v_isSharedCheck_6349_;
goto v_resetjp_6336_;
}
v_resetjp_6336_:
{
lean_object* v___x_6340_; 
if (v_isShared_6334_ == 0)
{
lean_ctor_set(v___x_6333_, 5, v_decls_6320_);
lean_ctor_set(v___x_6333_, 4, v_refs_6319_);
lean_ctor_set(v___x_6333_, 1, v_version_6318_);
lean_ctor_set(v___x_6333_, 0, v_moduleUri_6317_);
v___x_6340_ = v___x_6333_;
goto v_reusejp_6339_;
}
else
{
lean_object* v_reuseFailAlloc_6348_; 
v_reuseFailAlloc_6348_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6348_, 0, v_moduleUri_6317_);
lean_ctor_set(v_reuseFailAlloc_6348_, 1, v_version_6318_);
lean_ctor_set(v_reuseFailAlloc_6348_, 2, v_directImports_6330_);
lean_ctor_set(v_reuseFailAlloc_6348_, 3, v_isSetupFailure_x3f_6331_);
lean_ctor_set(v_reuseFailAlloc_6348_, 4, v_refs_6319_);
lean_ctor_set(v_reuseFailAlloc_6348_, 5, v_decls_6320_);
v___x_6340_ = v_reuseFailAlloc_6348_;
goto v_reusejp_6339_;
}
v_reusejp_6339_:
{
lean_object* v___x_6341_; lean_object* v___x_6343_; 
v___x_6341_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6316_, v___x_6340_, v_workers_6323_);
if (v_isShared_6338_ == 0)
{
lean_ctor_set(v___x_6337_, 1, v___x_6341_);
v___x_6343_ = v___x_6337_;
goto v_reusejp_6342_;
}
else
{
lean_object* v_reuseFailAlloc_6347_; 
v_reuseFailAlloc_6347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6347_, 0, v_ileans_6322_);
lean_ctor_set(v_reuseFailAlloc_6347_, 1, v___x_6341_);
v___x_6343_ = v_reuseFailAlloc_6347_;
goto v_reusejp_6342_;
}
v_reusejp_6342_:
{
lean_object* v___x_6345_; 
if (v_isShared_6328_ == 0)
{
lean_ctor_set_tag(v___x_6327_, 0);
lean_ctor_set(v___x_6327_, 0, v___x_6343_);
v___x_6345_ = v___x_6327_;
goto v_reusejp_6344_;
}
else
{
lean_object* v_reuseFailAlloc_6346_; 
v_reuseFailAlloc_6346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6346_, 0, v___x_6343_);
v___x_6345_ = v_reuseFailAlloc_6346_;
goto v_reusejp_6344_;
}
v_reusejp_6344_:
{
return v___x_6345_;
}
}
}
}
}
else
{
lean_object* v___x_6353_; 
lean_del_object(v___x_6333_);
lean_dec(v_isSetupFailure_x3f_6331_);
lean_dec_ref(v_directImports_6330_);
lean_dec(v_decls_6320_);
lean_dec(v_refs_6319_);
lean_dec(v_version_6318_);
lean_dec_ref(v_moduleUri_6317_);
lean_dec(v_name_6316_);
if (v_isShared_6328_ == 0)
{
lean_ctor_set_tag(v___x_6327_, 0);
lean_ctor_set(v___x_6327_, 0, v_self_6315_);
v___x_6353_ = v___x_6327_;
goto v_reusejp_6352_;
}
else
{
lean_object* v_reuseFailAlloc_6354_; 
v_reuseFailAlloc_6354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6354_, 0, v_self_6315_);
v___x_6353_ = v_reuseFailAlloc_6354_;
goto v_reusejp_6352_;
}
v_reusejp_6352_:
{
return v___x_6353_;
}
}
}
}
}
else
{
lean_object* v___x_6361_; uint8_t v_isShared_6362_; uint8_t v_isSharedCheck_6371_; 
lean_inc(v_workers_6323_);
lean_inc(v_ileans_6322_);
lean_dec(v___x_6324_);
v_isSharedCheck_6371_ = !lean_is_exclusive(v_self_6315_);
if (v_isSharedCheck_6371_ == 0)
{
lean_object* v_unused_6372_; lean_object* v_unused_6373_; 
v_unused_6372_ = lean_ctor_get(v_self_6315_, 1);
lean_dec(v_unused_6372_);
v_unused_6373_ = lean_ctor_get(v_self_6315_, 0);
lean_dec(v_unused_6373_);
v___x_6361_ = v_self_6315_;
v_isShared_6362_ = v_isSharedCheck_6371_;
goto v_resetjp_6360_;
}
else
{
lean_dec(v_self_6315_);
v___x_6361_ = lean_box(0);
v_isShared_6362_ = v_isSharedCheck_6371_;
goto v_resetjp_6360_;
}
v_resetjp_6360_:
{
lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6368_; 
v___x_6363_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__1));
v___x_6364_ = lean_box(0);
v___x_6365_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6365_, 0, v_moduleUri_6317_);
lean_ctor_set(v___x_6365_, 1, v_version_6318_);
lean_ctor_set(v___x_6365_, 2, v___x_6363_);
lean_ctor_set(v___x_6365_, 3, v___x_6364_);
lean_ctor_set(v___x_6365_, 4, v_refs_6319_);
lean_ctor_set(v___x_6365_, 5, v_decls_6320_);
v___x_6366_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_name_6316_, v___x_6365_, v_workers_6323_);
if (v_isShared_6362_ == 0)
{
lean_ctor_set(v___x_6361_, 1, v___x_6366_);
v___x_6368_ = v___x_6361_;
goto v_reusejp_6367_;
}
else
{
lean_object* v_reuseFailAlloc_6370_; 
v_reuseFailAlloc_6370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6370_, 0, v_ileans_6322_);
lean_ctor_set(v_reuseFailAlloc_6370_, 1, v___x_6366_);
v___x_6368_ = v_reuseFailAlloc_6370_;
goto v_reusejp_6367_;
}
v_reusejp_6367_:
{
lean_object* v___x_6369_; 
v___x_6369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6369_, 0, v___x_6368_);
return v___x_6369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_finalizeWorkerRefs___boxed(lean_object* v_self_6374_, lean_object* v_name_6375_, lean_object* v_moduleUri_6376_, lean_object* v_version_6377_, lean_object* v_refs_6378_, lean_object* v_decls_6379_, lean_object* v_a_6380_){
_start:
{
lean_object* v_res_6381_; 
v_res_6381_ = l_Lean_Server_References_finalizeWorkerRefs(v_self_6374_, v_name_6375_, v_moduleUri_6376_, v_version_6377_, v_refs_6378_, v_decls_6379_);
return v_res_6381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object* v_self_6382_, lean_object* v_name_6383_){
_start:
{
lean_object* v_ileans_6384_; lean_object* v_workers_6385_; lean_object* v___x_6387_; uint8_t v_isShared_6388_; uint8_t v_isSharedCheck_6393_; 
v_ileans_6384_ = lean_ctor_get(v_self_6382_, 0);
v_workers_6385_ = lean_ctor_get(v_self_6382_, 1);
v_isSharedCheck_6393_ = !lean_is_exclusive(v_self_6382_);
if (v_isSharedCheck_6393_ == 0)
{
v___x_6387_ = v_self_6382_;
v_isShared_6388_ = v_isSharedCheck_6393_;
goto v_resetjp_6386_;
}
else
{
lean_inc(v_workers_6385_);
lean_inc(v_ileans_6384_);
lean_dec(v_self_6382_);
v___x_6387_ = lean_box(0);
v_isShared_6388_ = v_isSharedCheck_6393_;
goto v_resetjp_6386_;
}
v_resetjp_6386_:
{
lean_object* v___x_6389_; lean_object* v___x_6391_; 
v___x_6389_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Server_References_removeIlean_spec__0___redArg(v_name_6383_, v_workers_6385_);
if (v_isShared_6388_ == 0)
{
lean_ctor_set(v___x_6387_, 1, v___x_6389_);
v___x_6391_ = v___x_6387_;
goto v_reusejp_6390_;
}
else
{
lean_object* v_reuseFailAlloc_6392_; 
v_reuseFailAlloc_6392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6392_, 0, v_ileans_6384_);
lean_ctor_set(v_reuseFailAlloc_6392_, 1, v___x_6389_);
v___x_6391_ = v_reuseFailAlloc_6392_;
goto v_reusejp_6390_;
}
v_reusejp_6390_:
{
return v___x_6391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_removeWorkerRefs___boxed(lean_object* v_self_6394_, lean_object* v_name_6395_){
_start:
{
lean_object* v_res_6396_; 
v_res_6396_ = l_Lean_Server_References_removeWorkerRefs(v_self_6394_, v_name_6395_);
lean_dec(v_name_6395_);
return v_res_6396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(lean_object* v_init_6397_, lean_object* v_x_6398_){
_start:
{
if (lean_obj_tag(v_x_6398_) == 0)
{
lean_object* v_v_6399_; lean_object* v_k_6400_; lean_object* v_l_6401_; lean_object* v_r_6402_; lean_object* v_moduleUri_6403_; lean_object* v_refs_6404_; lean_object* v_decls_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; 
v_v_6399_ = lean_ctor_get(v_x_6398_, 2);
lean_inc(v_v_6399_);
v_k_6400_ = lean_ctor_get(v_x_6398_, 1);
lean_inc(v_k_6400_);
v_l_6401_ = lean_ctor_get(v_x_6398_, 3);
lean_inc(v_l_6401_);
v_r_6402_ = lean_ctor_get(v_x_6398_, 4);
lean_inc(v_r_6402_);
lean_dec_ref_known(v_x_6398_, 5);
v_moduleUri_6403_ = lean_ctor_get(v_v_6399_, 0);
lean_inc_ref(v_moduleUri_6403_);
v_refs_6404_ = lean_ctor_get(v_v_6399_, 3);
lean_inc(v_refs_6404_);
v_decls_6405_ = lean_ctor_get(v_v_6399_, 4);
lean_inc(v_decls_6405_);
lean_dec(v_v_6399_);
v___x_6406_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6397_, v_l_6401_);
v___x_6407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6407_, 0, v_refs_6404_);
lean_ctor_set(v___x_6407_, 1, v_decls_6405_);
v___x_6408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6408_, 0, v_moduleUri_6403_);
lean_ctor_set(v___x_6408_, 1, v___x_6407_);
v___x_6409_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6400_, v___x_6408_, v___x_6406_);
v_init_6397_ = v___x_6409_;
v_x_6398_ = v_r_6402_;
goto _start;
}
else
{
return v_init_6397_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(lean_object* v_init_6411_, lean_object* v_x_6412_){
_start:
{
if (lean_obj_tag(v_x_6412_) == 0)
{
lean_object* v_v_6413_; lean_object* v_k_6414_; lean_object* v_l_6415_; lean_object* v_r_6416_; lean_object* v_moduleUri_6417_; lean_object* v_refs_6418_; lean_object* v_decls_6419_; lean_object* v___x_6420_; uint8_t v___x_6421_; 
v_v_6413_ = lean_ctor_get(v_x_6412_, 2);
lean_inc(v_v_6413_);
v_k_6414_ = lean_ctor_get(v_x_6412_, 1);
lean_inc(v_k_6414_);
v_l_6415_ = lean_ctor_get(v_x_6412_, 3);
lean_inc(v_l_6415_);
v_r_6416_ = lean_ctor_get(v_x_6412_, 4);
lean_inc(v_r_6416_);
lean_dec_ref_known(v_x_6412_, 5);
v_moduleUri_6417_ = lean_ctor_get(v_v_6413_, 0);
lean_inc_ref(v_moduleUri_6417_);
v_refs_6418_ = lean_ctor_get(v_v_6413_, 4);
lean_inc(v_refs_6418_);
v_decls_6419_ = lean_ctor_get(v_v_6413_, 5);
lean_inc(v_decls_6419_);
v___x_6420_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6411_, v_l_6415_);
v___x_6421_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6413_);
lean_dec(v_v_6413_);
if (v___x_6421_ == 0)
{
lean_dec(v_decls_6419_);
lean_dec(v_refs_6418_);
lean_dec_ref(v_moduleUri_6417_);
lean_dec(v_k_6414_);
v_init_6411_ = v___x_6420_;
v_x_6412_ = v_r_6416_;
goto _start;
}
else
{
lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; 
v___x_6423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6423_, 0, v_refs_6418_);
lean_ctor_set(v___x_6423_, 1, v_decls_6419_);
v___x_6424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6424_, 0, v_moduleUri_6417_);
lean_ctor_set(v___x_6424_, 1, v___x_6423_);
v___x_6425_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6414_, v___x_6424_, v___x_6420_);
v_init_6411_ = v___x_6425_;
v_x_6412_ = v_r_6416_;
goto _start;
}
}
else
{
return v_init_6411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefs(lean_object* v_self_6427_){
_start:
{
lean_object* v_ileans_6428_; lean_object* v_workers_6429_; lean_object* v___x_6430_; lean_object* v_ileanRefs_6431_; lean_object* v___x_6432_; 
v_ileans_6428_ = lean_ctor_get(v_self_6427_, 0);
lean_inc(v_ileans_6428_);
v_workers_6429_ = lean_ctor_get(v_self_6427_, 1);
lean_inc(v_workers_6429_);
lean_dec_ref(v_self_6427_);
v___x_6430_ = lean_box(1);
v_ileanRefs_6431_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v___x_6430_, v_ileans_6428_);
v___x_6432_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_ileanRefs_6431_, v_workers_6429_);
return v___x_6432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0(lean_object* v_init_6433_, lean_object* v_t_6434_){
_start:
{
lean_object* v___x_6435_; 
v___x_6435_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__0_spec__0(v_init_6433_, v_t_6434_);
return v___x_6435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1(lean_object* v_init_6436_, lean_object* v_t_6437_){
_start:
{
lean_object* v___x_6438_; 
v___x_6438_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefs_spec__1_spec__2(v_init_6436_, v_t_6437_);
return v___x_6438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(lean_object* v_init_6439_, lean_object* v_x_6440_){
_start:
{
if (lean_obj_tag(v_x_6440_) == 0)
{
lean_object* v_k_6441_; lean_object* v_v_6442_; lean_object* v_l_6443_; lean_object* v_r_6444_; lean_object* v___x_6445_; lean_object* v_a_6446_; uint8_t v___x_6447_; 
v_k_6441_ = lean_ctor_get(v_x_6440_, 1);
lean_inc(v_k_6441_);
v_v_6442_ = lean_ctor_get(v_x_6440_, 2);
lean_inc(v_v_6442_);
v_l_6443_ = lean_ctor_get(v_x_6440_, 3);
lean_inc(v_l_6443_);
v_r_6444_ = lean_ctor_get(v_x_6440_, 4);
lean_inc(v_r_6444_);
lean_dec_ref_known(v_x_6440_, 5);
v___x_6445_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v_init_6439_, v_l_6443_);
v_a_6446_ = lean_ctor_get(v___x_6445_, 0);
lean_inc(v_a_6446_);
v___x_6447_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_v_6442_);
if (v___x_6447_ == 0)
{
lean_object* v_a_6448_; 
lean_dec(v_a_6446_);
lean_dec(v_v_6442_);
lean_dec(v_k_6441_);
v_a_6448_ = lean_ctor_get(v___x_6445_, 0);
lean_inc(v_a_6448_);
lean_dec_ref(v___x_6445_);
v_init_6439_ = v_a_6448_;
v_x_6440_ = v_r_6444_;
goto _start;
}
else
{
lean_object* v_moduleUri_6450_; lean_object* v_directImports_6451_; lean_object* v___x_6452_; lean_object* v___x_6453_; 
lean_dec_ref(v___x_6445_);
v_moduleUri_6450_ = lean_ctor_get(v_v_6442_, 0);
lean_inc_ref(v_moduleUri_6450_);
v_directImports_6451_ = lean_ctor_get(v_v_6442_, 2);
lean_inc_ref(v_directImports_6451_);
lean_dec(v_v_6442_);
v___x_6452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6452_, 0, v_moduleUri_6450_);
lean_ctor_set(v___x_6452_, 1, v_directImports_6451_);
v___x_6453_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6441_, v___x_6452_, v_a_6446_);
v_init_6439_ = v___x_6453_;
v_x_6440_ = v_r_6444_;
goto _start;
}
}
else
{
lean_object* v___x_6455_; 
v___x_6455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6455_, 0, v_init_6439_);
return v___x_6455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(lean_object* v_init_6456_, lean_object* v_x_6457_){
_start:
{
if (lean_obj_tag(v_x_6457_) == 0)
{
lean_object* v_k_6458_; lean_object* v_v_6459_; lean_object* v_l_6460_; lean_object* v_r_6461_; lean_object* v___x_6462_; lean_object* v_a_6463_; lean_object* v_moduleUri_6464_; lean_object* v_directImports_6465_; lean_object* v___x_6466_; lean_object* v___x_6467_; 
v_k_6458_ = lean_ctor_get(v_x_6457_, 1);
lean_inc(v_k_6458_);
v_v_6459_ = lean_ctor_get(v_x_6457_, 2);
lean_inc(v_v_6459_);
v_l_6460_ = lean_ctor_get(v_x_6457_, 3);
lean_inc(v_l_6460_);
v_r_6461_ = lean_ctor_get(v_x_6457_, 4);
lean_inc(v_r_6461_);
lean_dec_ref_known(v_x_6457_, 5);
v___x_6462_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_init_6456_, v_l_6460_);
v_a_6463_ = lean_ctor_get(v___x_6462_, 0);
lean_inc(v_a_6463_);
lean_dec_ref(v___x_6462_);
v_moduleUri_6464_ = lean_ctor_get(v_v_6459_, 0);
lean_inc_ref(v_moduleUri_6464_);
v_directImports_6465_ = lean_ctor_get(v_v_6459_, 2);
lean_inc_ref(v_directImports_6465_);
lean_dec(v_v_6459_);
v___x_6466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6466_, 0, v_moduleUri_6464_);
lean_ctor_set(v___x_6466_, 1, v_directImports_6465_);
v___x_6467_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_DirectImports_convertImportInfos_spec__1___redArg(v_k_6458_, v___x_6466_, v_a_6463_);
v_init_6456_ = v___x_6467_;
v_x_6457_ = v_r_6461_;
goto _start;
}
else
{
lean_object* v___x_6469_; 
v___x_6469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6469_, 0, v_init_6456_);
return v___x_6469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allDirectImports(lean_object* v_self_6470_){
_start:
{
lean_object* v_ileans_6471_; lean_object* v_workers_6472_; lean_object* v___y_6474_; lean_object* v_allDirectImports_6477_; lean_object* v___x_6478_; lean_object* v_a_6479_; 
v_ileans_6471_ = lean_ctor_get(v_self_6470_, 0);
lean_inc(v_ileans_6471_);
v_workers_6472_ = lean_ctor_get(v_self_6470_, 1);
lean_inc(v_workers_6472_);
lean_dec_ref(v_self_6470_);
v_allDirectImports_6477_ = lean_box(1);
v___x_6478_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__1(v_allDirectImports_6477_, v_ileans_6471_);
v_a_6479_ = lean_ctor_get(v___x_6478_, 0);
lean_inc(v_a_6479_);
lean_dec_ref(v___x_6478_);
v___y_6474_ = v_a_6479_;
goto v___jp_6473_;
v___jp_6473_:
{
lean_object* v___x_6475_; lean_object* v_a_6476_; 
v___x_6475_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_allDirectImports_spec__0(v___y_6474_, v_workers_6472_);
v_a_6476_ = lean_ctor_get(v___x_6475_, 0);
lean_inc(v_a_6476_);
lean_dec_ref(v___x_6475_);
return v_a_6476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f(lean_object* v_self_6480_, lean_object* v_mod_6481_){
_start:
{
lean_object* v_ileans_6482_; lean_object* v_workers_6483_; lean_object* v___x_6485_; uint8_t v_isShared_6486_; uint8_t v_isSharedCheck_6520_; 
v_ileans_6482_ = lean_ctor_get(v_self_6480_, 0);
v_workers_6483_ = lean_ctor_get(v_self_6480_, 1);
v_isSharedCheck_6520_ = !lean_is_exclusive(v_self_6480_);
if (v_isSharedCheck_6520_ == 0)
{
v___x_6485_ = v_self_6480_;
v_isShared_6486_ = v_isSharedCheck_6520_;
goto v_resetjp_6484_;
}
else
{
lean_inc(v_workers_6483_);
lean_inc(v_ileans_6482_);
lean_dec(v_self_6480_);
v___x_6485_ = lean_box(0);
v_isShared_6486_ = v_isSharedCheck_6520_;
goto v_resetjp_6484_;
}
v_resetjp_6484_:
{
lean_object* v___x_6505_; 
v___x_6505_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6483_, v_mod_6481_);
lean_dec(v_workers_6483_);
if (lean_obj_tag(v___x_6505_) == 1)
{
lean_object* v_val_6506_; lean_object* v___x_6508_; uint8_t v_isShared_6509_; uint8_t v_isSharedCheck_6519_; 
v_val_6506_ = lean_ctor_get(v___x_6505_, 0);
v_isSharedCheck_6519_ = !lean_is_exclusive(v___x_6505_);
if (v_isSharedCheck_6519_ == 0)
{
v___x_6508_ = v___x_6505_;
v_isShared_6509_ = v_isSharedCheck_6519_;
goto v_resetjp_6507_;
}
else
{
lean_inc(v_val_6506_);
lean_dec(v___x_6505_);
v___x_6508_ = lean_box(0);
v_isShared_6509_ = v_isSharedCheck_6519_;
goto v_resetjp_6507_;
}
v_resetjp_6507_:
{
uint8_t v___x_6510_; 
v___x_6510_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6506_);
if (v___x_6510_ == 0)
{
lean_del_object(v___x_6508_);
lean_dec(v_val_6506_);
goto v___jp_6487_;
}
else
{
lean_object* v_moduleUri_6511_; lean_object* v_refs_6512_; lean_object* v_decls_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6517_; 
lean_del_object(v___x_6485_);
lean_dec(v_ileans_6482_);
v_moduleUri_6511_ = lean_ctor_get(v_val_6506_, 0);
lean_inc_ref(v_moduleUri_6511_);
v_refs_6512_ = lean_ctor_get(v_val_6506_, 4);
lean_inc(v_refs_6512_);
v_decls_6513_ = lean_ctor_get(v_val_6506_, 5);
lean_inc(v_decls_6513_);
lean_dec(v_val_6506_);
v___x_6514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6514_, 0, v_refs_6512_);
lean_ctor_set(v___x_6514_, 1, v_decls_6513_);
v___x_6515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6515_, 0, v_moduleUri_6511_);
lean_ctor_set(v___x_6515_, 1, v___x_6514_);
if (v_isShared_6509_ == 0)
{
lean_ctor_set(v___x_6508_, 0, v___x_6515_);
v___x_6517_ = v___x_6508_;
goto v_reusejp_6516_;
}
else
{
lean_object* v_reuseFailAlloc_6518_; 
v_reuseFailAlloc_6518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6518_, 0, v___x_6515_);
v___x_6517_ = v_reuseFailAlloc_6518_;
goto v_reusejp_6516_;
}
v_reusejp_6516_:
{
return v___x_6517_;
}
}
}
}
else
{
lean_dec(v___x_6505_);
goto v___jp_6487_;
}
v___jp_6487_:
{
lean_object* v___x_6488_; 
v___x_6488_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6482_, v_mod_6481_);
lean_dec(v_ileans_6482_);
if (lean_obj_tag(v___x_6488_) == 1)
{
lean_object* v_val_6489_; lean_object* v___x_6491_; uint8_t v_isShared_6492_; uint8_t v_isSharedCheck_6503_; 
v_val_6489_ = lean_ctor_get(v___x_6488_, 0);
v_isSharedCheck_6503_ = !lean_is_exclusive(v___x_6488_);
if (v_isSharedCheck_6503_ == 0)
{
v___x_6491_ = v___x_6488_;
v_isShared_6492_ = v_isSharedCheck_6503_;
goto v_resetjp_6490_;
}
else
{
lean_inc(v_val_6489_);
lean_dec(v___x_6488_);
v___x_6491_ = lean_box(0);
v_isShared_6492_ = v_isSharedCheck_6503_;
goto v_resetjp_6490_;
}
v_resetjp_6490_:
{
lean_object* v_moduleUri_6493_; lean_object* v_refs_6494_; lean_object* v_decls_6495_; lean_object* v___x_6497_; 
v_moduleUri_6493_ = lean_ctor_get(v_val_6489_, 0);
lean_inc_ref(v_moduleUri_6493_);
v_refs_6494_ = lean_ctor_get(v_val_6489_, 3);
lean_inc(v_refs_6494_);
v_decls_6495_ = lean_ctor_get(v_val_6489_, 4);
lean_inc(v_decls_6495_);
lean_dec(v_val_6489_);
if (v_isShared_6486_ == 0)
{
lean_ctor_set(v___x_6485_, 1, v_decls_6495_);
lean_ctor_set(v___x_6485_, 0, v_refs_6494_);
v___x_6497_ = v___x_6485_;
goto v_reusejp_6496_;
}
else
{
lean_object* v_reuseFailAlloc_6502_; 
v_reuseFailAlloc_6502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6502_, 0, v_refs_6494_);
lean_ctor_set(v_reuseFailAlloc_6502_, 1, v_decls_6495_);
v___x_6497_ = v_reuseFailAlloc_6502_;
goto v_reusejp_6496_;
}
v_reusejp_6496_:
{
lean_object* v___x_6498_; lean_object* v___x_6500_; 
v___x_6498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6498_, 0, v_moduleUri_6493_);
lean_ctor_set(v___x_6498_, 1, v___x_6497_);
if (v_isShared_6492_ == 0)
{
lean_ctor_set(v___x_6491_, 0, v___x_6498_);
v___x_6500_ = v___x_6491_;
goto v_reusejp_6499_;
}
else
{
lean_object* v_reuseFailAlloc_6501_; 
v_reuseFailAlloc_6501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6501_, 0, v___x_6498_);
v___x_6500_ = v_reuseFailAlloc_6501_;
goto v_reusejp_6499_;
}
v_reusejp_6499_:
{
return v___x_6500_;
}
}
}
}
else
{
lean_object* v___x_6504_; 
lean_dec(v___x_6488_);
lean_del_object(v___x_6485_);
v___x_6504_ = lean_box(0);
return v___x_6504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getModuleRefs_x3f___boxed(lean_object* v_self_6521_, lean_object* v_mod_6522_){
_start:
{
lean_object* v_res_6523_; 
v_res_6523_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6521_, v_mod_6522_);
lean_dec(v_mod_6522_);
return v_res_6523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f(lean_object* v_self_6524_, lean_object* v_mod_6525_){
_start:
{
lean_object* v_ileans_6526_; lean_object* v_workers_6527_; lean_object* v___x_6540_; 
v_ileans_6526_ = lean_ctor_get(v_self_6524_, 0);
v_workers_6527_ = lean_ctor_get(v_self_6524_, 1);
v___x_6540_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6527_, v_mod_6525_);
if (lean_obj_tag(v___x_6540_) == 1)
{
lean_object* v_val_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6550_; 
v_val_6541_ = lean_ctor_get(v___x_6540_, 0);
v_isSharedCheck_6550_ = !lean_is_exclusive(v___x_6540_);
if (v_isSharedCheck_6550_ == 0)
{
v___x_6543_ = v___x_6540_;
v_isShared_6544_ = v_isSharedCheck_6550_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_val_6541_);
lean_dec(v___x_6540_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6550_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
uint8_t v___x_6545_; 
v___x_6545_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6541_);
if (v___x_6545_ == 0)
{
lean_del_object(v___x_6543_);
lean_dec(v_val_6541_);
goto v___jp_6528_;
}
else
{
lean_object* v_directImports_6546_; lean_object* v___x_6548_; 
v_directImports_6546_ = lean_ctor_get(v_val_6541_, 2);
lean_inc_ref(v_directImports_6546_);
lean_dec(v_val_6541_);
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 0, v_directImports_6546_);
v___x_6548_ = v___x_6543_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_directImports_6546_);
v___x_6548_ = v_reuseFailAlloc_6549_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
return v___x_6548_;
}
}
}
}
else
{
lean_dec(v___x_6540_);
goto v___jp_6528_;
}
v___jp_6528_:
{
lean_object* v___x_6529_; 
v___x_6529_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6526_, v_mod_6525_);
if (lean_obj_tag(v___x_6529_) == 1)
{
lean_object* v_val_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6538_; 
v_val_6530_ = lean_ctor_get(v___x_6529_, 0);
v_isSharedCheck_6538_ = !lean_is_exclusive(v___x_6529_);
if (v_isSharedCheck_6538_ == 0)
{
v___x_6532_ = v___x_6529_;
v_isShared_6533_ = v_isSharedCheck_6538_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_val_6530_);
lean_dec(v___x_6529_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6538_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v_directImports_6534_; lean_object* v___x_6536_; 
v_directImports_6534_ = lean_ctor_get(v_val_6530_, 2);
lean_inc_ref(v_directImports_6534_);
lean_dec(v_val_6530_);
if (v_isShared_6533_ == 0)
{
lean_ctor_set(v___x_6532_, 0, v_directImports_6534_);
v___x_6536_ = v___x_6532_;
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
else
{
lean_object* v___x_6539_; 
lean_dec(v___x_6529_);
v___x_6539_ = lean_box(0);
return v___x_6539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDirectImports_x3f___boxed(lean_object* v_self_6551_, lean_object* v_mod_6552_){
_start:
{
lean_object* v_res_6553_; 
v_res_6553_ = l_Lean_Server_References_getDirectImports_x3f(v_self_6551_, v_mod_6552_);
lean_dec(v_mod_6552_);
lean_dec_ref(v_self_6551_);
return v_res_6553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f(lean_object* v_self_6554_, lean_object* v_mod_6555_){
_start:
{
lean_object* v_ileans_6556_; lean_object* v_workers_6557_; lean_object* v___x_6570_; 
v_ileans_6556_ = lean_ctor_get(v_self_6554_, 0);
v_workers_6557_ = lean_ctor_get(v_self_6554_, 1);
v___x_6570_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_workers_6557_, v_mod_6555_);
if (lean_obj_tag(v___x_6570_) == 1)
{
lean_object* v_val_6571_; lean_object* v___x_6573_; uint8_t v_isShared_6574_; uint8_t v_isSharedCheck_6580_; 
v_val_6571_ = lean_ctor_get(v___x_6570_, 0);
v_isSharedCheck_6580_ = !lean_is_exclusive(v___x_6570_);
if (v_isSharedCheck_6580_ == 0)
{
v___x_6573_ = v___x_6570_;
v_isShared_6574_ = v_isSharedCheck_6580_;
goto v_resetjp_6572_;
}
else
{
lean_inc(v_val_6571_);
lean_dec(v___x_6570_);
v___x_6573_ = lean_box(0);
v_isShared_6574_ = v_isSharedCheck_6580_;
goto v_resetjp_6572_;
}
v_resetjp_6572_:
{
uint8_t v___x_6575_; 
v___x_6575_ = l_Lean_Server_TransientWorkerILean_hasRefs(v_val_6571_);
if (v___x_6575_ == 0)
{
lean_del_object(v___x_6573_);
lean_dec(v_val_6571_);
goto v___jp_6558_;
}
else
{
lean_object* v_decls_6576_; lean_object* v___x_6578_; 
v_decls_6576_ = lean_ctor_get(v_val_6571_, 5);
lean_inc(v_decls_6576_);
lean_dec(v_val_6571_);
if (v_isShared_6574_ == 0)
{
lean_ctor_set(v___x_6573_, 0, v_decls_6576_);
v___x_6578_ = v___x_6573_;
goto v_reusejp_6577_;
}
else
{
lean_object* v_reuseFailAlloc_6579_; 
v_reuseFailAlloc_6579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6579_, 0, v_decls_6576_);
v___x_6578_ = v_reuseFailAlloc_6579_;
goto v_reusejp_6577_;
}
v_reusejp_6577_:
{
return v___x_6578_;
}
}
}
}
else
{
lean_dec(v___x_6570_);
goto v___jp_6558_;
}
v___jp_6558_:
{
lean_object* v___x_6559_; 
v___x_6559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_ileans_6556_, v_mod_6555_);
if (lean_obj_tag(v___x_6559_) == 1)
{
lean_object* v_val_6560_; lean_object* v___x_6562_; uint8_t v_isShared_6563_; uint8_t v_isSharedCheck_6568_; 
v_val_6560_ = lean_ctor_get(v___x_6559_, 0);
v_isSharedCheck_6568_ = !lean_is_exclusive(v___x_6559_);
if (v_isSharedCheck_6568_ == 0)
{
v___x_6562_ = v___x_6559_;
v_isShared_6563_ = v_isSharedCheck_6568_;
goto v_resetjp_6561_;
}
else
{
lean_inc(v_val_6560_);
lean_dec(v___x_6559_);
v___x_6562_ = lean_box(0);
v_isShared_6563_ = v_isSharedCheck_6568_;
goto v_resetjp_6561_;
}
v_resetjp_6561_:
{
lean_object* v_decls_6564_; lean_object* v___x_6566_; 
v_decls_6564_ = lean_ctor_get(v_val_6560_, 4);
lean_inc(v_decls_6564_);
lean_dec(v_val_6560_);
if (v_isShared_6563_ == 0)
{
lean_ctor_set(v___x_6562_, 0, v_decls_6564_);
v___x_6566_ = v___x_6562_;
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
else
{
lean_object* v___x_6569_; 
lean_dec(v___x_6559_);
v___x_6569_ = lean_box(0);
return v___x_6569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_getDecls_x3f___boxed(lean_object* v_self_6581_, lean_object* v_mod_6582_){
_start:
{
lean_object* v_res_6583_; 
v_res_6583_ = l_Lean_Server_References_getDecls_x3f(v_self_6581_, v_mod_6582_);
lean_dec(v_mod_6582_);
lean_dec_ref(v_self_6581_);
return v_res_6583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(lean_object* v_init_6584_, lean_object* v_x_6585_){
_start:
{
if (lean_obj_tag(v_x_6585_) == 0)
{
lean_object* v_k_6586_; lean_object* v_v_6587_; lean_object* v_l_6588_; lean_object* v_r_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; 
v_k_6586_ = lean_ctor_get(v_x_6585_, 1);
v_v_6587_ = lean_ctor_get(v_x_6585_, 2);
v_l_6588_ = lean_ctor_get(v_x_6585_, 3);
v_r_6589_ = lean_ctor_get(v_x_6585_, 4);
v___x_6590_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6584_, v_l_6588_);
lean_inc(v_v_6587_);
lean_inc(v_k_6586_);
v___x_6591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6591_, 0, v_k_6586_);
lean_ctor_set(v___x_6591_, 1, v_v_6587_);
v___x_6592_ = lean_array_push(v___x_6590_, v___x_6591_);
v_init_6584_ = v___x_6592_;
v_x_6585_ = v_r_6589_;
goto _start;
}
else
{
return v_init_6584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2___boxed(lean_object* v_init_6594_, lean_object* v_x_6595_){
_start:
{
lean_object* v_res_6596_; 
v_res_6596_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6594_, v_x_6595_);
lean_dec(v_x_6595_);
return v_res_6596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(lean_object* v_t_6597_, lean_object* v_k_6598_){
_start:
{
if (lean_obj_tag(v_t_6597_) == 0)
{
lean_object* v_k_6599_; lean_object* v_v_6600_; lean_object* v_l_6601_; lean_object* v_r_6602_; uint8_t v___x_6603_; 
v_k_6599_ = lean_ctor_get(v_t_6597_, 1);
v_v_6600_ = lean_ctor_get(v_t_6597_, 2);
v_l_6601_ = lean_ctor_get(v_t_6597_, 3);
v_r_6602_ = lean_ctor_get(v_t_6597_, 4);
v___x_6603_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_6598_, v_k_6599_);
switch(v___x_6603_)
{
case 0:
{
v_t_6597_ = v_l_6601_;
goto _start;
}
case 1:
{
lean_object* v___x_6605_; 
lean_inc(v_v_6600_);
v___x_6605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6605_, 0, v_v_6600_);
return v___x_6605_;
}
default: 
{
v_t_6597_ = v_r_6602_;
goto _start;
}
}
}
else
{
lean_object* v___x_6607_; 
v___x_6607_ = lean_box(0);
return v___x_6607_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg___boxed(lean_object* v_t_6608_, lean_object* v_k_6609_){
_start:
{
lean_object* v_res_6610_; 
v_res_6610_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6608_, v_k_6609_);
lean_dec_ref(v_k_6609_);
lean_dec(v_t_6608_);
return v_res_6610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(lean_object* v_ident_6611_, lean_object* v_as_6612_, size_t v_sz_6613_, size_t v_i_6614_, lean_object* v_b_6615_){
_start:
{
lean_object* v_a_6617_; uint8_t v___x_6621_; 
v___x_6621_ = lean_usize_dec_lt(v_i_6614_, v_sz_6613_);
if (v___x_6621_ == 0)
{
return v_b_6615_;
}
else
{
lean_object* v_a_6622_; lean_object* v_snd_6623_; lean_object* v_snd_6624_; lean_object* v_fst_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6653_; 
v_a_6622_ = lean_array_uget(v_as_6612_, v_i_6614_);
v_snd_6623_ = lean_ctor_get(v_a_6622_, 1);
lean_inc(v_snd_6623_);
v_snd_6624_ = lean_ctor_get(v_snd_6623_, 1);
lean_inc(v_snd_6624_);
v_fst_6625_ = lean_ctor_get(v_a_6622_, 0);
v_isSharedCheck_6653_ = !lean_is_exclusive(v_a_6622_);
if (v_isSharedCheck_6653_ == 0)
{
lean_object* v_unused_6654_; 
v_unused_6654_ = lean_ctor_get(v_a_6622_, 1);
lean_dec(v_unused_6654_);
v___x_6627_ = v_a_6622_;
v_isShared_6628_ = v_isSharedCheck_6653_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_fst_6625_);
lean_dec(v_a_6622_);
v___x_6627_ = lean_box(0);
v_isShared_6628_ = v_isSharedCheck_6653_;
goto v_resetjp_6626_;
}
v_resetjp_6626_:
{
lean_object* v_fst_6629_; lean_object* v___x_6631_; uint8_t v_isShared_6632_; uint8_t v_isSharedCheck_6651_; 
v_fst_6629_ = lean_ctor_get(v_snd_6623_, 0);
v_isSharedCheck_6651_ = !lean_is_exclusive(v_snd_6623_);
if (v_isSharedCheck_6651_ == 0)
{
lean_object* v_unused_6652_; 
v_unused_6652_ = lean_ctor_get(v_snd_6623_, 1);
lean_dec(v_unused_6652_);
v___x_6631_ = v_snd_6623_;
v_isShared_6632_ = v_isSharedCheck_6651_;
goto v_resetjp_6630_;
}
else
{
lean_inc(v_fst_6629_);
lean_dec(v_snd_6623_);
v___x_6631_ = lean_box(0);
v_isShared_6632_ = v_isSharedCheck_6651_;
goto v_resetjp_6630_;
}
v_resetjp_6630_:
{
lean_object* v_fst_6633_; lean_object* v_snd_6634_; lean_object* v___x_6636_; uint8_t v_isShared_6637_; uint8_t v_isSharedCheck_6650_; 
v_fst_6633_ = lean_ctor_get(v_snd_6624_, 0);
v_snd_6634_ = lean_ctor_get(v_snd_6624_, 1);
v_isSharedCheck_6650_ = !lean_is_exclusive(v_snd_6624_);
if (v_isSharedCheck_6650_ == 0)
{
v___x_6636_ = v_snd_6624_;
v_isShared_6637_ = v_isSharedCheck_6650_;
goto v_resetjp_6635_;
}
else
{
lean_inc(v_snd_6634_);
lean_inc(v_fst_6633_);
lean_dec(v_snd_6624_);
v___x_6636_ = lean_box(0);
v_isShared_6637_ = v_isSharedCheck_6650_;
goto v_resetjp_6635_;
}
v_resetjp_6635_:
{
lean_object* v___x_6638_; 
v___x_6638_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_fst_6633_, v_ident_6611_);
lean_dec(v_fst_6633_);
if (lean_obj_tag(v___x_6638_) == 1)
{
lean_object* v_val_6639_; lean_object* v___x_6641_; 
v_val_6639_ = lean_ctor_get(v___x_6638_, 0);
lean_inc(v_val_6639_);
lean_dec_ref_known(v___x_6638_, 1);
if (v_isShared_6637_ == 0)
{
lean_ctor_set(v___x_6636_, 0, v_val_6639_);
v___x_6641_ = v___x_6636_;
goto v_reusejp_6640_;
}
else
{
lean_object* v_reuseFailAlloc_6649_; 
v_reuseFailAlloc_6649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6649_, 0, v_val_6639_);
lean_ctor_set(v_reuseFailAlloc_6649_, 1, v_snd_6634_);
v___x_6641_ = v_reuseFailAlloc_6649_;
goto v_reusejp_6640_;
}
v_reusejp_6640_:
{
lean_object* v___x_6643_; 
if (v_isShared_6632_ == 0)
{
lean_ctor_set(v___x_6631_, 1, v___x_6641_);
lean_ctor_set(v___x_6631_, 0, v_fst_6625_);
v___x_6643_ = v___x_6631_;
goto v_reusejp_6642_;
}
else
{
lean_object* v_reuseFailAlloc_6648_; 
v_reuseFailAlloc_6648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6648_, 0, v_fst_6625_);
lean_ctor_set(v_reuseFailAlloc_6648_, 1, v___x_6641_);
v___x_6643_ = v_reuseFailAlloc_6648_;
goto v_reusejp_6642_;
}
v_reusejp_6642_:
{
lean_object* v___x_6645_; 
if (v_isShared_6628_ == 0)
{
lean_ctor_set(v___x_6627_, 1, v___x_6643_);
lean_ctor_set(v___x_6627_, 0, v_fst_6629_);
v___x_6645_ = v___x_6627_;
goto v_reusejp_6644_;
}
else
{
lean_object* v_reuseFailAlloc_6647_; 
v_reuseFailAlloc_6647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6647_, 0, v_fst_6629_);
lean_ctor_set(v_reuseFailAlloc_6647_, 1, v___x_6643_);
v___x_6645_ = v_reuseFailAlloc_6647_;
goto v_reusejp_6644_;
}
v_reusejp_6644_:
{
lean_object* v___x_6646_; 
v___x_6646_ = lean_array_push(v_b_6615_, v___x_6645_);
v_a_6617_ = v___x_6646_;
goto v___jp_6616_;
}
}
}
}
else
{
lean_dec(v___x_6638_);
lean_del_object(v___x_6636_);
lean_dec(v_snd_6634_);
lean_del_object(v___x_6631_);
lean_dec(v_fst_6629_);
lean_del_object(v___x_6627_);
lean_dec(v_fst_6625_);
v_a_6617_ = v_b_6615_;
goto v___jp_6616_;
}
}
}
}
}
v___jp_6616_:
{
size_t v___x_6618_; size_t v___x_6619_; 
v___x_6618_ = ((size_t)1ULL);
v___x_6619_ = lean_usize_add(v_i_6614_, v___x_6618_);
v_i_6614_ = v___x_6619_;
v_b_6615_ = v_a_6617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1___boxed(lean_object* v_ident_6655_, lean_object* v_as_6656_, lean_object* v_sz_6657_, lean_object* v_i_6658_, lean_object* v_b_6659_){
_start:
{
size_t v_sz_boxed_6660_; size_t v_i_boxed_6661_; lean_object* v_res_6662_; 
v_sz_boxed_6660_ = lean_unbox_usize(v_sz_6657_);
lean_dec(v_sz_6657_);
v_i_boxed_6661_ = lean_unbox_usize(v_i_6658_);
lean_dec(v_i_6658_);
v_res_6662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6655_, v_as_6656_, v_sz_boxed_6660_, v_i_boxed_6661_, v_b_6659_);
lean_dec_ref(v_as_6656_);
lean_dec_ref(v_ident_6655_);
return v_res_6662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_allRefsFor(lean_object* v_self_6669_, lean_object* v_ident_6670_){
_start:
{
lean_object* v___y_6672_; 
if (lean_obj_tag(v_ident_6670_) == 0)
{
lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v___x_6679_; 
v___x_6677_ = l_Lean_Server_References_allRefs(v_self_6669_);
v___x_6678_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__1));
v___x_6679_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v___x_6678_, v___x_6677_);
lean_dec(v___x_6677_);
v___y_6672_ = v___x_6679_;
goto v___jp_6671_;
}
else
{
lean_object* v_moduleName_6680_; lean_object* v_identModuleName_6681_; lean_object* v___x_6682_; 
v_moduleName_6680_ = lean_ctor_get(v_ident_6670_, 0);
lean_inc_ref(v_moduleName_6680_);
v_identModuleName_6681_ = l_String_toName(v_moduleName_6680_);
v___x_6682_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6669_, v_identModuleName_6681_);
if (lean_obj_tag(v___x_6682_) == 0)
{
lean_object* v___x_6683_; 
lean_dec(v_identModuleName_6681_);
v___x_6683_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__2));
v___y_6672_ = v___x_6683_;
goto v___jp_6671_;
}
else
{
lean_object* v_val_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; 
v_val_6684_ = lean_ctor_get(v___x_6682_, 0);
lean_inc(v_val_6684_);
lean_dec_ref_known(v___x_6682_, 1);
v___x_6685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6685_, 0, v_identModuleName_6681_);
lean_ctor_set(v___x_6685_, 1, v_val_6684_);
v___x_6686_ = lean_unsigned_to_nat(1u);
v___x_6687_ = lean_mk_empty_array_with_capacity(v___x_6686_);
v___x_6688_ = lean_array_push(v___x_6687_, v___x_6685_);
v___y_6672_ = v___x_6688_;
goto v___jp_6671_;
}
}
v___jp_6671_:
{
lean_object* v_result_6673_; size_t v_sz_6674_; size_t v___x_6675_; lean_object* v___x_6676_; 
v_result_6673_ = ((lean_object*)(l_Lean_Server_References_allRefsFor___closed__0));
v_sz_6674_ = lean_array_size(v___y_6672_);
v___x_6675_ = ((size_t)0ULL);
v___x_6676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_allRefsFor_spec__1(v_ident_6670_, v___y_6672_, v_sz_6674_, v___x_6675_, v_result_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v_ident_6670_);
return v___x_6676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(lean_object* v_00_u03b4_6689_, lean_object* v_t_6690_, lean_object* v_k_6691_){
_start:
{
lean_object* v___x_6692_; 
v___x_6692_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___redArg(v_t_6690_, v_k_6691_);
return v___x_6692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0___boxed(lean_object* v_00_u03b4_6693_, lean_object* v_t_6694_, lean_object* v_k_6695_){
_start:
{
lean_object* v_res_6696_; 
v_res_6696_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_allRefsFor_spec__0(v_00_u03b4_6693_, v_t_6694_, v_k_6695_);
lean_dec_ref(v_k_6695_);
lean_dec(v_t_6694_);
return v_res_6696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(lean_object* v_init_6697_, lean_object* v_t_6698_){
_start:
{
lean_object* v___x_6699_; 
v___x_6699_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2_spec__2(v_init_6697_, v_t_6698_);
return v___x_6699_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2___boxed(lean_object* v_init_6700_, lean_object* v_t_6701_){
_start:
{
lean_object* v_res_6702_; 
v_res_6702_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_References_allRefsFor_spec__2(v_init_6700_, v_t_6701_);
lean_dec(v_t_6701_);
return v_res_6702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt(lean_object* v_self_6703_, lean_object* v_module_6704_, lean_object* v_pos_6705_, uint8_t v_includeStop_6706_){
_start:
{
lean_object* v___x_6707_; 
v___x_6707_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6703_, v_module_6704_);
if (lean_obj_tag(v___x_6707_) == 1)
{
lean_object* v_val_6708_; lean_object* v_snd_6709_; lean_object* v_fst_6710_; lean_object* v___x_6711_; 
v_val_6708_ = lean_ctor_get(v___x_6707_, 0);
lean_inc(v_val_6708_);
lean_dec_ref_known(v___x_6707_, 1);
v_snd_6709_ = lean_ctor_get(v_val_6708_, 1);
lean_inc(v_snd_6709_);
lean_dec(v_val_6708_);
v_fst_6710_ = lean_ctor_get(v_snd_6709_, 0);
lean_inc(v_fst_6710_);
lean_dec(v_snd_6709_);
v___x_6711_ = l_Lean_Lsp_ModuleRefs_findAt(v_fst_6710_, v_pos_6705_, v_includeStop_6706_);
return v___x_6711_;
}
else
{
lean_object* v___x_6712_; 
lean_dec(v___x_6707_);
v___x_6712_ = ((lean_object*)(l_Lean_Lsp_ModuleRefs_findAt___closed__0));
return v___x_6712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findAt___boxed(lean_object* v_self_6713_, lean_object* v_module_6714_, lean_object* v_pos_6715_, lean_object* v_includeStop_6716_){
_start:
{
uint8_t v_includeStop_boxed_6717_; lean_object* v_res_6718_; 
v_includeStop_boxed_6717_ = lean_unbox(v_includeStop_6716_);
v_res_6718_ = l_Lean_Server_References_findAt(v_self_6713_, v_module_6714_, v_pos_6715_, v_includeStop_boxed_6717_);
lean_dec_ref(v_pos_6715_);
lean_dec(v_module_6714_);
return v_res_6718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f(lean_object* v_self_6719_, lean_object* v_module_6720_, lean_object* v_pos_6721_, uint8_t v_includeStop_6722_){
_start:
{
lean_object* v___x_6723_; 
v___x_6723_ = l_Lean_Server_References_getModuleRefs_x3f(v_self_6719_, v_module_6720_);
if (lean_obj_tag(v___x_6723_) == 0)
{
lean_object* v___x_6724_; 
v___x_6724_ = lean_box(0);
return v___x_6724_;
}
else
{
lean_object* v_val_6725_; lean_object* v_snd_6726_; lean_object* v_fst_6727_; lean_object* v___x_6728_; 
v_val_6725_ = lean_ctor_get(v___x_6723_, 0);
lean_inc(v_val_6725_);
lean_dec_ref_known(v___x_6723_, 1);
v_snd_6726_ = lean_ctor_get(v_val_6725_, 1);
lean_inc(v_snd_6726_);
lean_dec(v_val_6725_);
v_fst_6727_ = lean_ctor_get(v_snd_6726_, 0);
lean_inc(v_fst_6727_);
lean_dec(v_snd_6726_);
v___x_6728_ = l_Lean_Lsp_ModuleRefs_findRange_x3f(v_fst_6727_, v_pos_6721_, v_includeStop_6722_);
lean_dec(v_fst_6727_);
return v___x_6728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_findRange_x3f___boxed(lean_object* v_self_6729_, lean_object* v_module_6730_, lean_object* v_pos_6731_, lean_object* v_includeStop_6732_){
_start:
{
uint8_t v_includeStop_boxed_6733_; lean_object* v_res_6734_; 
v_includeStop_boxed_6733_ = lean_unbox(v_includeStop_6732_);
v_res_6734_ = l_Lean_Server_References_findRange_x3f(v_self_6729_, v_module_6730_, v_pos_6731_, v_includeStop_boxed_6733_);
lean_dec_ref(v_pos_6731_);
lean_dec(v_module_6730_);
return v_res_6734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(lean_object* v_t_6735_, lean_object* v_k_6736_){
_start:
{
if (lean_obj_tag(v_t_6735_) == 0)
{
lean_object* v_k_6737_; lean_object* v_v_6738_; lean_object* v_l_6739_; lean_object* v_r_6740_; uint8_t v___x_6741_; 
v_k_6737_ = lean_ctor_get(v_t_6735_, 1);
v_v_6738_ = lean_ctor_get(v_t_6735_, 2);
v_l_6739_ = lean_ctor_get(v_t_6735_, 3);
v_r_6740_ = lean_ctor_get(v_t_6735_, 4);
v___x_6741_ = lean_string_compare(v_k_6736_, v_k_6737_);
switch(v___x_6741_)
{
case 0:
{
v_t_6735_ = v_l_6739_;
goto _start;
}
case 1:
{
lean_object* v___x_6743_; 
lean_inc(v_v_6738_);
v___x_6743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6743_, 0, v_v_6738_);
return v___x_6743_;
}
default: 
{
v_t_6735_ = v_r_6740_;
goto _start;
}
}
}
else
{
lean_object* v___x_6745_; 
v___x_6745_ = lean_box(0);
return v___x_6745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg___boxed(lean_object* v_t_6746_, lean_object* v_k_6747_){
_start:
{
lean_object* v_res_6748_; 
v_res_6748_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6746_, v_k_6747_);
lean_dec_ref(v_k_6747_);
lean_dec(v_t_6746_);
return v_res_6748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f(lean_object* v_ds_6749_, lean_object* v_name_6750_){
_start:
{
lean_object* v___x_6751_; 
v___x_6751_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_ds_6749_, v_name_6750_);
if (lean_obj_tag(v___x_6751_) == 0)
{
lean_object* v___x_6752_; 
lean_dec_ref(v_name_6750_);
v___x_6752_ = lean_box(0);
return v___x_6752_;
}
else
{
lean_object* v_val_6753_; lean_object* v___x_6755_; uint8_t v_isShared_6756_; uint8_t v_isSharedCheck_6763_; 
v_val_6753_ = lean_ctor_get(v___x_6751_, 0);
v_isSharedCheck_6763_ = !lean_is_exclusive(v___x_6751_);
if (v_isSharedCheck_6763_ == 0)
{
v___x_6755_ = v___x_6751_;
v_isShared_6756_ = v_isSharedCheck_6763_;
goto v_resetjp_6754_;
}
else
{
lean_inc(v_val_6753_);
lean_dec(v___x_6751_);
v___x_6755_ = lean_box(0);
v_isShared_6756_ = v_isSharedCheck_6763_;
goto v_resetjp_6754_;
}
v_resetjp_6754_:
{
lean_object* v___x_6757_; lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6761_; 
v___x_6757_ = l_Lean_Lsp_DeclInfo_range(v_val_6753_);
v___x_6758_ = l_Lean_Lsp_DeclInfo_selectionRange(v_val_6753_);
lean_dec(v_val_6753_);
v___x_6759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6759_, 0, v_name_6750_);
lean_ctor_set(v___x_6759_, 1, v___x_6757_);
lean_ctor_set(v___x_6759_, 2, v___x_6758_);
if (v_isShared_6756_ == 0)
{
lean_ctor_set(v___x_6755_, 0, v___x_6759_);
v___x_6761_ = v___x_6755_;
goto v_reusejp_6760_;
}
else
{
lean_object* v_reuseFailAlloc_6762_; 
v_reuseFailAlloc_6762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6762_, 0, v___x_6759_);
v___x_6761_ = v_reuseFailAlloc_6762_;
goto v_reusejp_6760_;
}
v_reusejp_6760_:
{
return v___x_6761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_ParentDecl_ofDecls_x3f___boxed(lean_object* v_ds_6764_, lean_object* v_name_6765_){
_start:
{
lean_object* v_res_6766_; 
v_res_6766_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_ds_6764_, v_name_6765_);
lean_dec(v_ds_6764_);
return v_res_6766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(lean_object* v_00_u03b4_6767_, lean_object* v_t_6768_, lean_object* v_k_6769_){
_start:
{
lean_object* v___x_6770_; 
v___x_6770_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___redArg(v_t_6768_, v_k_6769_);
return v___x_6770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0___boxed(lean_object* v_00_u03b4_6771_, lean_object* v_t_6772_, lean_object* v_k_6773_){
_start:
{
lean_object* v_res_6774_; 
v_res_6774_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_ParentDecl_ofDecls_x3f_spec__0(v_00_u03b4_6771_, v_t_6772_, v_k_6773_);
lean_dec_ref(v_k_6773_);
lean_dec(v_t_6772_);
return v_res_6774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(lean_object* v_fst_6775_, lean_object* v_fst_6776_, lean_object* v_snd_6777_, lean_object* v_as_6778_, size_t v_sz_6779_, size_t v_i_6780_, lean_object* v_b_6781_){
_start:
{
uint8_t v___x_6782_; 
v___x_6782_ = lean_usize_dec_lt(v_i_6780_, v_sz_6779_);
if (v___x_6782_ == 0)
{
lean_dec(v_fst_6776_);
lean_dec_ref(v_fst_6775_);
return v_b_6781_;
}
else
{
lean_object* v_a_6783_; lean_object* v___y_6785_; lean_object* v___x_6793_; 
v_a_6783_ = lean_array_uget_borrowed(v_as_6778_, v_i_6780_);
v___x_6793_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_a_6783_);
if (lean_obj_tag(v___x_6793_) == 0)
{
lean_object* v___x_6794_; 
v___x_6794_ = lean_box(0);
v___y_6785_ = v___x_6794_;
goto v___jp_6784_;
}
else
{
lean_object* v_val_6795_; lean_object* v___x_6796_; 
v_val_6795_ = lean_ctor_get(v___x_6793_, 0);
lean_inc(v_val_6795_);
lean_dec_ref_known(v___x_6793_, 1);
v___x_6796_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6777_, v_val_6795_);
v___y_6785_ = v___x_6796_;
goto v___jp_6784_;
}
v___jp_6784_:
{
lean_object* v___x_6786_; lean_object* v___x_6787_; lean_object* v___x_6788_; lean_object* v___x_6789_; size_t v___x_6790_; size_t v___x_6791_; 
v___x_6786_ = l_Lean_Lsp_RefInfo_Location_range(v_a_6783_);
lean_inc_ref(v_fst_6775_);
v___x_6787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6787_, 0, v_fst_6775_);
lean_ctor_set(v___x_6787_, 1, v___x_6786_);
lean_inc(v_fst_6776_);
v___x_6788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6788_, 0, v___x_6787_);
lean_ctor_set(v___x_6788_, 1, v_fst_6776_);
lean_ctor_set(v___x_6788_, 2, v___y_6785_);
v___x_6789_ = lean_array_push(v_b_6781_, v___x_6788_);
v___x_6790_ = ((size_t)1ULL);
v___x_6791_ = lean_usize_add(v_i_6780_, v___x_6790_);
v_i_6780_ = v___x_6791_;
v_b_6781_ = v___x_6789_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0___boxed(lean_object* v_fst_6797_, lean_object* v_fst_6798_, lean_object* v_snd_6799_, lean_object* v_as_6800_, lean_object* v_sz_6801_, lean_object* v_i_6802_, lean_object* v_b_6803_){
_start:
{
size_t v_sz_boxed_6804_; size_t v_i_boxed_6805_; lean_object* v_res_6806_; 
v_sz_boxed_6804_ = lean_unbox_usize(v_sz_6801_);
lean_dec(v_sz_6801_);
v_i_boxed_6805_ = lean_unbox_usize(v_i_6802_);
lean_dec(v_i_6802_);
v_res_6806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6797_, v_fst_6798_, v_snd_6799_, v_as_6800_, v_sz_boxed_6804_, v_i_boxed_6805_, v_b_6803_);
lean_dec_ref(v_as_6800_);
lean_dec(v_snd_6799_);
return v_res_6806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(uint8_t v_includeDefinition_6807_, lean_object* v_as_6808_, size_t v_sz_6809_, size_t v_i_6810_, lean_object* v_b_6811_){
_start:
{
uint8_t v___x_6812_; 
v___x_6812_ = lean_usize_dec_lt(v_i_6810_, v_sz_6809_);
if (v___x_6812_ == 0)
{
return v_b_6811_;
}
else
{
lean_object* v_a_6813_; lean_object* v_snd_6814_; lean_object* v_snd_6815_; lean_object* v_fst_6816_; lean_object* v_fst_6817_; lean_object* v_fst_6818_; lean_object* v_snd_6819_; lean_object* v___x_6821_; uint8_t v_isShared_6822_; uint8_t v_isSharedCheck_6846_; 
v_a_6813_ = lean_array_uget_borrowed(v_as_6808_, v_i_6810_);
v_snd_6814_ = lean_ctor_get(v_a_6813_, 1);
v_snd_6815_ = lean_ctor_get(v_snd_6814_, 1);
lean_inc(v_snd_6815_);
v_fst_6816_ = lean_ctor_get(v_a_6813_, 0);
v_fst_6817_ = lean_ctor_get(v_snd_6814_, 0);
v_fst_6818_ = lean_ctor_get(v_snd_6815_, 0);
v_snd_6819_ = lean_ctor_get(v_snd_6815_, 1);
v_isSharedCheck_6846_ = !lean_is_exclusive(v_snd_6815_);
if (v_isSharedCheck_6846_ == 0)
{
v___x_6821_ = v_snd_6815_;
v_isShared_6822_ = v_isSharedCheck_6846_;
goto v_resetjp_6820_;
}
else
{
lean_inc(v_snd_6819_);
lean_inc(v_fst_6818_);
lean_dec(v_snd_6815_);
v___x_6821_ = lean_box(0);
v_isShared_6822_ = v_isSharedCheck_6846_;
goto v_resetjp_6820_;
}
v_resetjp_6820_:
{
lean_object* v_result_6824_; 
if (v_includeDefinition_6807_ == 0)
{
lean_del_object(v___x_6821_);
v_result_6824_ = v_b_6811_;
goto v___jp_6823_;
}
else
{
lean_object* v_definition_x3f_6832_; 
v_definition_x3f_6832_ = lean_ctor_get(v_fst_6818_, 0);
if (lean_obj_tag(v_definition_x3f_6832_) == 1)
{
lean_object* v_val_6833_; lean_object* v___y_6835_; lean_object* v___x_6842_; 
v_val_6833_ = lean_ctor_get(v_definition_x3f_6832_, 0);
v___x_6842_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6833_);
if (lean_obj_tag(v___x_6842_) == 0)
{
lean_object* v___x_6843_; 
v___x_6843_ = lean_box(0);
v___y_6835_ = v___x_6843_;
goto v___jp_6834_;
}
else
{
lean_object* v_val_6844_; lean_object* v___x_6845_; 
v_val_6844_ = lean_ctor_get(v___x_6842_, 0);
lean_inc(v_val_6844_);
lean_dec_ref_known(v___x_6842_, 1);
v___x_6845_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6819_, v_val_6844_);
v___y_6835_ = v___x_6845_;
goto v___jp_6834_;
}
v___jp_6834_:
{
lean_object* v___x_6836_; lean_object* v___x_6838_; 
v___x_6836_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6833_);
lean_inc(v_fst_6816_);
if (v_isShared_6822_ == 0)
{
lean_ctor_set(v___x_6821_, 1, v___x_6836_);
lean_ctor_set(v___x_6821_, 0, v_fst_6816_);
v___x_6838_ = v___x_6821_;
goto v_reusejp_6837_;
}
else
{
lean_object* v_reuseFailAlloc_6841_; 
v_reuseFailAlloc_6841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6841_, 0, v_fst_6816_);
lean_ctor_set(v_reuseFailAlloc_6841_, 1, v___x_6836_);
v___x_6838_ = v_reuseFailAlloc_6841_;
goto v_reusejp_6837_;
}
v_reusejp_6837_:
{
lean_object* v___x_6839_; lean_object* v___x_6840_; 
lean_inc(v_fst_6817_);
v___x_6839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6839_, 0, v___x_6838_);
lean_ctor_set(v___x_6839_, 1, v_fst_6817_);
lean_ctor_set(v___x_6839_, 2, v___y_6835_);
v___x_6840_ = lean_array_push(v_b_6811_, v___x_6839_);
v_result_6824_ = v___x_6840_;
goto v___jp_6823_;
}
}
}
else
{
lean_del_object(v___x_6821_);
v_result_6824_ = v_b_6811_;
goto v___jp_6823_;
}
}
v___jp_6823_:
{
lean_object* v_usages_6825_; size_t v_sz_6826_; size_t v___x_6827_; lean_object* v___x_6828_; size_t v___x_6829_; size_t v___x_6830_; 
v_usages_6825_ = lean_ctor_get(v_fst_6818_, 1);
lean_inc_ref(v_usages_6825_);
lean_dec(v_fst_6818_);
v_sz_6826_ = lean_array_size(v_usages_6825_);
v___x_6827_ = ((size_t)0ULL);
lean_inc(v_fst_6817_);
lean_inc(v_fst_6816_);
v___x_6828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__0(v_fst_6816_, v_fst_6817_, v_snd_6819_, v_usages_6825_, v_sz_6826_, v___x_6827_, v_result_6824_);
lean_dec_ref(v_usages_6825_);
lean_dec(v_snd_6819_);
v___x_6829_ = ((size_t)1ULL);
v___x_6830_ = lean_usize_add(v_i_6810_, v___x_6829_);
v_i_6810_ = v___x_6830_;
v_b_6811_ = v___x_6828_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1___boxed(lean_object* v_includeDefinition_6847_, lean_object* v_as_6848_, lean_object* v_sz_6849_, lean_object* v_i_6850_, lean_object* v_b_6851_){
_start:
{
uint8_t v_includeDefinition_boxed_6852_; size_t v_sz_boxed_6853_; size_t v_i_boxed_6854_; lean_object* v_res_6855_; 
v_includeDefinition_boxed_6852_ = lean_unbox(v_includeDefinition_6847_);
v_sz_boxed_6853_ = lean_unbox_usize(v_sz_6849_);
lean_dec(v_sz_6849_);
v_i_boxed_6854_ = lean_unbox_usize(v_i_6850_);
lean_dec(v_i_6850_);
v_res_6855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_boxed_6852_, v_as_6848_, v_sz_boxed_6853_, v_i_boxed_6854_, v_b_6851_);
lean_dec_ref(v_as_6848_);
return v_res_6855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo(lean_object* v_self_6858_, lean_object* v_ident_6859_, uint8_t v_includeDefinition_6860_){
_start:
{
lean_object* v_result_6861_; lean_object* v___x_6862_; size_t v_sz_6863_; size_t v___x_6864_; lean_object* v___x_6865_; 
v_result_6861_ = ((lean_object*)(l_Lean_Server_References_referringTo___closed__0));
v___x_6862_ = l_Lean_Server_References_allRefsFor(v_self_6858_, v_ident_6859_);
v_sz_6863_ = lean_array_size(v___x_6862_);
v___x_6864_ = ((size_t)0ULL);
v___x_6865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_referringTo_spec__1(v_includeDefinition_6860_, v___x_6862_, v_sz_6863_, v___x_6864_, v_result_6861_);
lean_dec_ref(v___x_6862_);
return v___x_6865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_referringTo___boxed(lean_object* v_self_6866_, lean_object* v_ident_6867_, lean_object* v_includeDefinition_6868_){
_start:
{
uint8_t v_includeDefinition_boxed_6869_; lean_object* v_res_6870_; 
v_includeDefinition_boxed_6869_ = lean_unbox(v_includeDefinition_6868_);
v_res_6870_ = l_Lean_Server_References_referringTo(v_self_6866_, v_ident_6867_, v_includeDefinition_boxed_6869_);
return v_res_6870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(lean_object* v_as_6874_, size_t v_sz_6875_, size_t v_i_6876_, lean_object* v_b_6877_){
_start:
{
uint8_t v___x_6878_; 
v___x_6878_ = lean_usize_dec_lt(v_i_6876_, v_sz_6875_);
if (v___x_6878_ == 0)
{
lean_inc_ref(v_b_6877_);
return v_b_6877_;
}
else
{
lean_object* v_a_6879_; lean_object* v_snd_6880_; lean_object* v_snd_6881_; lean_object* v_fst_6882_; lean_object* v_fst_6883_; lean_object* v_fst_6884_; lean_object* v_snd_6885_; lean_object* v___x_6887_; uint8_t v_isShared_6888_; uint8_t v_isSharedCheck_6923_; 
v_a_6879_ = lean_array_uget_borrowed(v_as_6874_, v_i_6876_);
v_snd_6880_ = lean_ctor_get(v_a_6879_, 1);
v_snd_6881_ = lean_ctor_get(v_snd_6880_, 1);
lean_inc(v_snd_6881_);
v_fst_6882_ = lean_ctor_get(v_snd_6881_, 0);
lean_inc(v_fst_6882_);
v_fst_6883_ = lean_ctor_get(v_a_6879_, 0);
v_fst_6884_ = lean_ctor_get(v_snd_6880_, 0);
v_snd_6885_ = lean_ctor_get(v_snd_6881_, 1);
v_isSharedCheck_6923_ = !lean_is_exclusive(v_snd_6881_);
if (v_isSharedCheck_6923_ == 0)
{
lean_object* v_unused_6924_; 
v_unused_6924_ = lean_ctor_get(v_snd_6881_, 0);
lean_dec(v_unused_6924_);
v___x_6887_ = v_snd_6881_;
v_isShared_6888_ = v_isSharedCheck_6923_;
goto v_resetjp_6886_;
}
else
{
lean_inc(v_snd_6885_);
lean_dec(v_snd_6881_);
v___x_6887_ = lean_box(0);
v_isShared_6888_ = v_isSharedCheck_6923_;
goto v_resetjp_6886_;
}
v_resetjp_6886_:
{
lean_object* v_definition_x3f_6889_; lean_object* v___x_6891_; uint8_t v_isShared_6892_; uint8_t v_isSharedCheck_6921_; 
v_definition_x3f_6889_ = lean_ctor_get(v_fst_6882_, 0);
v_isSharedCheck_6921_ = !lean_is_exclusive(v_fst_6882_);
if (v_isSharedCheck_6921_ == 0)
{
lean_object* v_unused_6922_; 
v_unused_6922_ = lean_ctor_get(v_fst_6882_, 1);
lean_dec(v_unused_6922_);
v___x_6891_ = v_fst_6882_;
v_isShared_6892_ = v_isSharedCheck_6921_;
goto v_resetjp_6890_;
}
else
{
lean_inc(v_definition_x3f_6889_);
lean_dec(v_fst_6882_);
v___x_6891_ = lean_box(0);
v_isShared_6892_ = v_isSharedCheck_6921_;
goto v_resetjp_6890_;
}
v_resetjp_6890_:
{
lean_object* v___x_6893_; 
v___x_6893_ = lean_box(0);
if (lean_obj_tag(v_definition_x3f_6889_) == 1)
{
lean_object* v_val_6894_; lean_object* v___x_6896_; uint8_t v_isShared_6897_; uint8_t v_isSharedCheck_6916_; 
v_val_6894_ = lean_ctor_get(v_definition_x3f_6889_, 0);
v_isSharedCheck_6916_ = !lean_is_exclusive(v_definition_x3f_6889_);
if (v_isSharedCheck_6916_ == 0)
{
v___x_6896_ = v_definition_x3f_6889_;
v_isShared_6897_ = v_isSharedCheck_6916_;
goto v_resetjp_6895_;
}
else
{
lean_inc(v_val_6894_);
lean_dec(v_definition_x3f_6889_);
v___x_6896_ = lean_box(0);
v_isShared_6897_ = v_isSharedCheck_6916_;
goto v_resetjp_6895_;
}
v_resetjp_6895_:
{
lean_object* v___y_6899_; lean_object* v___x_6912_; 
v___x_6912_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_6894_);
if (lean_obj_tag(v___x_6912_) == 0)
{
lean_object* v___x_6913_; 
lean_dec(v_snd_6885_);
v___x_6913_ = lean_box(0);
v___y_6899_ = v___x_6913_;
goto v___jp_6898_;
}
else
{
lean_object* v_val_6914_; lean_object* v___x_6915_; 
v_val_6914_ = lean_ctor_get(v___x_6912_, 0);
lean_inc(v_val_6914_);
lean_dec_ref_known(v___x_6912_, 1);
v___x_6915_ = l_Lean_Server_References_ParentDecl_ofDecls_x3f(v_snd_6885_, v_val_6914_);
lean_dec(v_snd_6885_);
v___y_6899_ = v___x_6915_;
goto v___jp_6898_;
}
v___jp_6898_:
{
lean_object* v___x_6900_; lean_object* v___x_6902_; 
v___x_6900_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6894_);
lean_dec(v_val_6894_);
lean_inc(v_fst_6883_);
if (v_isShared_6892_ == 0)
{
lean_ctor_set(v___x_6891_, 1, v___x_6900_);
lean_ctor_set(v___x_6891_, 0, v_fst_6883_);
v___x_6902_ = v___x_6891_;
goto v_reusejp_6901_;
}
else
{
lean_object* v_reuseFailAlloc_6911_; 
v_reuseFailAlloc_6911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6911_, 0, v_fst_6883_);
lean_ctor_set(v_reuseFailAlloc_6911_, 1, v___x_6900_);
v___x_6902_ = v_reuseFailAlloc_6911_;
goto v_reusejp_6901_;
}
v_reusejp_6901_:
{
lean_object* v___x_6903_; lean_object* v___x_6905_; 
lean_inc(v_fst_6884_);
v___x_6903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6903_, 0, v___x_6902_);
lean_ctor_set(v___x_6903_, 1, v_fst_6884_);
lean_ctor_set(v___x_6903_, 2, v___y_6899_);
if (v_isShared_6897_ == 0)
{
lean_ctor_set(v___x_6896_, 0, v___x_6903_);
v___x_6905_ = v___x_6896_;
goto v_reusejp_6904_;
}
else
{
lean_object* v_reuseFailAlloc_6910_; 
v_reuseFailAlloc_6910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6910_, 0, v___x_6903_);
v___x_6905_ = v_reuseFailAlloc_6910_;
goto v_reusejp_6904_;
}
v_reusejp_6904_:
{
lean_object* v___x_6906_; lean_object* v___x_6908_; 
v___x_6906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6906_, 0, v___x_6905_);
if (v_isShared_6888_ == 0)
{
lean_ctor_set(v___x_6887_, 1, v___x_6893_);
lean_ctor_set(v___x_6887_, 0, v___x_6906_);
v___x_6908_ = v___x_6887_;
goto v_reusejp_6907_;
}
else
{
lean_object* v_reuseFailAlloc_6909_; 
v_reuseFailAlloc_6909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6909_, 0, v___x_6906_);
lean_ctor_set(v_reuseFailAlloc_6909_, 1, v___x_6893_);
v___x_6908_ = v_reuseFailAlloc_6909_;
goto v_reusejp_6907_;
}
v_reusejp_6907_:
{
return v___x_6908_;
}
}
}
}
}
}
else
{
lean_object* v___x_6917_; size_t v___x_6918_; size_t v___x_6919_; 
lean_del_object(v___x_6891_);
lean_dec(v_definition_x3f_6889_);
lean_del_object(v___x_6887_);
lean_dec(v_snd_6885_);
v___x_6917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v___x_6918_ = ((size_t)1ULL);
v___x_6919_ = lean_usize_add(v_i_6876_, v___x_6918_);
v_i_6876_ = v___x_6919_;
v_b_6877_ = v___x_6917_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___boxed(lean_object* v_as_6925_, lean_object* v_sz_6926_, lean_object* v_i_6927_, lean_object* v_b_6928_){
_start:
{
size_t v_sz_boxed_6929_; size_t v_i_boxed_6930_; lean_object* v_res_6931_; 
v_sz_boxed_6929_ = lean_unbox_usize(v_sz_6926_);
lean_dec(v_sz_6926_);
v_i_boxed_6930_ = lean_unbox_usize(v_i_6927_);
lean_dec(v_i_6927_);
v_res_6931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v_as_6925_, v_sz_boxed_6929_, v_i_boxed_6930_, v_b_6928_);
lean_dec_ref(v_b_6928_);
lean_dec_ref(v_as_6925_);
return v_res_6931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object* v_self_6932_, lean_object* v_ident_6933_){
_start:
{
lean_object* v___x_6934_; lean_object* v___x_6935_; lean_object* v___x_6936_; size_t v_sz_6937_; size_t v___x_6938_; lean_object* v___x_6939_; lean_object* v_fst_6940_; 
v___x_6934_ = l_Lean_Server_References_allRefsFor(v_self_6932_, v_ident_6933_);
v___x_6935_ = lean_box(0);
v___x_6936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0___closed__0));
v_sz_6937_ = lean_array_size(v___x_6934_);
v___x_6938_ = ((size_t)0ULL);
v___x_6939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_References_definitionOf_x3f_spec__0(v___x_6934_, v_sz_6937_, v___x_6938_, v___x_6936_);
lean_dec_ref(v___x_6934_);
v_fst_6940_ = lean_ctor_get(v___x_6939_, 0);
lean_inc(v_fst_6940_);
lean_dec_ref(v___x_6939_);
if (lean_obj_tag(v_fst_6940_) == 0)
{
return v___x_6935_;
}
else
{
lean_object* v_val_6941_; 
v_val_6941_ = lean_ctor_get(v_fst_6940_, 0);
lean_inc(v_val_6941_);
lean_dec_ref_known(v_fst_6940_, 1);
return v_val_6941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(lean_object* v_filterMapIdent_6942_, lean_object* v_a_6943_, lean_object* v_fst_6944_, lean_object* v_init_6945_, lean_object* v_x_6946_){
_start:
{
lean_object* v_d_6949_; 
if (lean_obj_tag(v_x_6946_) == 0)
{
lean_object* v_k_6951_; lean_object* v_v_6952_; lean_object* v_l_6953_; lean_object* v_r_6954_; lean_object* v___y_6956_; lean_object* v___x_6960_; 
v_k_6951_ = lean_ctor_get(v_x_6946_, 1);
lean_inc(v_k_6951_);
v_v_6952_ = lean_ctor_get(v_x_6946_, 2);
lean_inc(v_v_6952_);
v_l_6953_ = lean_ctor_get(v_x_6946_, 3);
lean_inc(v_l_6953_);
v_r_6954_ = lean_ctor_get(v_x_6946_, 4);
lean_inc(v_r_6954_);
lean_dec_ref_known(v_x_6946_, 5);
lean_inc_ref(v_fst_6944_);
lean_inc(v_a_6943_);
lean_inc_ref(v_filterMapIdent_6942_);
v___x_6960_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6942_, v_a_6943_, v_fst_6944_, v_init_6945_, v_l_6953_);
if (lean_obj_tag(v___x_6960_) == 0)
{
lean_object* v_a_6961_; 
lean_dec(v_r_6954_);
lean_dec(v_v_6952_);
lean_dec(v_k_6951_);
lean_dec_ref(v_fst_6944_);
lean_dec(v_a_6943_);
lean_dec_ref(v_filterMapIdent_6942_);
v_a_6961_ = lean_ctor_get(v___x_6960_, 0);
lean_inc(v_a_6961_);
lean_dec_ref_known(v___x_6960_, 1);
v_d_6949_ = v_a_6961_;
goto v___jp_6948_;
}
else
{
if (lean_obj_tag(v_k_6951_) == 0)
{
lean_object* v_definition_x3f_6962_; 
v_definition_x3f_6962_ = lean_ctor_get(v_v_6952_, 0);
lean_inc(v_definition_x3f_6962_);
lean_dec(v_v_6952_);
if (lean_obj_tag(v_definition_x3f_6962_) == 1)
{
lean_object* v_a_6963_; lean_object* v_identName_6964_; lean_object* v_val_6965_; lean_object* v___x_6966_; lean_object* v___x_6967_; 
v_a_6963_ = lean_ctor_get(v___x_6960_, 0);
lean_inc(v_a_6963_);
v_identName_6964_ = lean_ctor_get(v_k_6951_, 1);
lean_inc_ref(v_identName_6964_);
lean_dec_ref_known(v_k_6951_, 2);
v_val_6965_ = lean_ctor_get(v_definition_x3f_6962_, 0);
lean_inc(v_val_6965_);
lean_dec_ref_known(v_definition_x3f_6962_, 1);
v___x_6966_ = l_String_toName(v_identName_6964_);
lean_inc_ref(v_filterMapIdent_6942_);
v___x_6967_ = lean_apply_1(v_filterMapIdent_6942_, v___x_6966_);
if (lean_obj_tag(v___x_6967_) == 1)
{
lean_object* v_val_6968_; lean_object* v___x_6969_; lean_object* v___x_6970_; lean_object* v___x_6971_; 
lean_dec_ref_known(v___x_6960_, 1);
v_val_6968_ = lean_ctor_get(v___x_6967_, 0);
lean_inc(v_val_6968_);
lean_dec_ref_known(v___x_6967_, 1);
v___x_6969_ = l_Lean_Lsp_RefInfo_Location_range(v_val_6965_);
lean_dec(v_val_6965_);
lean_inc_ref(v_fst_6944_);
lean_inc(v_a_6943_);
v___x_6970_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6970_, 0, v_a_6943_);
lean_ctor_set(v___x_6970_, 1, v_fst_6944_);
lean_ctor_set(v___x_6970_, 2, v_val_6968_);
lean_ctor_set(v___x_6970_, 3, v___x_6969_);
v___x_6971_ = lean_array_push(v_a_6963_, v___x_6970_);
v_init_6945_ = v___x_6971_;
v_x_6946_ = v_r_6954_;
goto _start;
}
else
{
lean_dec(v___x_6967_);
lean_dec(v_val_6965_);
lean_dec(v_a_6963_);
v___y_6956_ = v___x_6960_;
goto v___jp_6955_;
}
}
else
{
lean_dec_ref_known(v_k_6951_, 2);
lean_dec(v_definition_x3f_6962_);
v___y_6956_ = v___x_6960_;
goto v___jp_6955_;
}
}
else
{
lean_dec(v_v_6952_);
lean_dec(v_k_6951_);
v___y_6956_ = v___x_6960_;
goto v___jp_6955_;
}
}
v___jp_6955_:
{
if (lean_obj_tag(v___y_6956_) == 0)
{
lean_object* v_a_6957_; 
lean_dec(v_r_6954_);
lean_dec_ref(v_fst_6944_);
lean_dec(v_a_6943_);
lean_dec_ref(v_filterMapIdent_6942_);
v_a_6957_ = lean_ctor_get(v___y_6956_, 0);
lean_inc(v_a_6957_);
lean_dec_ref_known(v___y_6956_, 1);
v_d_6949_ = v_a_6957_;
goto v___jp_6948_;
}
else
{
lean_object* v_a_6958_; 
v_a_6958_ = lean_ctor_get(v___y_6956_, 0);
lean_inc(v_a_6958_);
lean_dec_ref_known(v___y_6956_, 1);
v_init_6945_ = v_a_6958_;
v_x_6946_ = v_r_6954_;
goto _start;
}
}
}
else
{
lean_object* v___x_6973_; 
lean_dec_ref(v_fst_6944_);
lean_dec(v_a_6943_);
lean_dec_ref(v_filterMapIdent_6942_);
v___x_6973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6973_, 0, v_init_6945_);
return v___x_6973_;
}
v___jp_6948_:
{
lean_object* v___x_6950_; 
v___x_6950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6950_, 0, v_d_6949_);
return v___x_6950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg___boxed(lean_object* v_filterMapIdent_6974_, lean_object* v_a_6975_, lean_object* v_fst_6976_, lean_object* v_init_6977_, lean_object* v_x_6978_, lean_object* v___y_6979_){
_start:
{
lean_object* v_res_6980_; 
v_res_6980_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6974_, v_a_6975_, v_fst_6976_, v_init_6977_, v_x_6978_);
return v_res_6980_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(lean_object* v_filterMapIdent_6981_, lean_object* v_cancelTk_x3f_6982_, lean_object* v_init_6983_, lean_object* v_x_6984_){
_start:
{
lean_object* v_d_6987_; 
if (lean_obj_tag(v_x_6984_) == 0)
{
lean_object* v_k_6989_; lean_object* v_v_6990_; lean_object* v_l_6991_; lean_object* v_r_6992_; lean_object* v___x_6993_; 
v_k_6989_ = lean_ctor_get(v_x_6984_, 1);
lean_inc(v_k_6989_);
v_v_6990_ = lean_ctor_get(v_x_6984_, 2);
lean_inc(v_v_6990_);
v_l_6991_ = lean_ctor_get(v_x_6984_, 3);
lean_inc(v_l_6991_);
v_r_6992_ = lean_ctor_get(v_x_6984_, 4);
lean_inc(v_r_6992_);
lean_dec_ref_known(v_x_6984_, 5);
lean_inc(v_cancelTk_x3f_6982_);
lean_inc_ref(v_filterMapIdent_6981_);
v___x_6993_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_6981_, v_cancelTk_x3f_6982_, v_init_6983_, v_l_6991_);
if (lean_obj_tag(v___x_6993_) == 0)
{
lean_object* v_a_6994_; 
lean_dec(v_r_6992_);
lean_dec(v_v_6990_);
lean_dec(v_k_6989_);
lean_dec(v_cancelTk_x3f_6982_);
lean_dec_ref(v_filterMapIdent_6981_);
v_a_6994_ = lean_ctor_get(v___x_6993_, 0);
lean_inc(v_a_6994_);
lean_dec_ref_known(v___x_6993_, 1);
v_d_6987_ = v_a_6994_;
goto v___jp_6986_;
}
else
{
lean_object* v_snd_6995_; lean_object* v_a_6996_; lean_object* v_fst_6997_; lean_object* v_fst_6998_; lean_object* v___x_7000_; uint8_t v_isShared_7001_; uint8_t v_isSharedCheck_7031_; 
v_snd_6995_ = lean_ctor_get(v_v_6990_, 1);
lean_inc(v_snd_6995_);
v_a_6996_ = lean_ctor_get(v___x_6993_, 0);
lean_inc(v_a_6996_);
lean_dec_ref_known(v___x_6993_, 1);
v_fst_6997_ = lean_ctor_get(v_v_6990_, 0);
lean_inc(v_fst_6997_);
lean_dec(v_v_6990_);
v_fst_6998_ = lean_ctor_get(v_snd_6995_, 0);
v_isSharedCheck_7031_ = !lean_is_exclusive(v_snd_6995_);
if (v_isSharedCheck_7031_ == 0)
{
lean_object* v_unused_7032_; 
v_unused_7032_ = lean_ctor_get(v_snd_6995_, 1);
lean_dec(v_unused_7032_);
v___x_7000_ = v_snd_6995_;
v_isShared_7001_ = v_isSharedCheck_7031_;
goto v_resetjp_6999_;
}
else
{
lean_inc(v_fst_6998_);
lean_dec(v_snd_6995_);
v___x_7000_ = lean_box(0);
v_isShared_7001_ = v_isSharedCheck_7031_;
goto v_resetjp_6999_;
}
v_resetjp_6999_:
{
lean_object* v_snd_7002_; lean_object* v___x_7004_; uint8_t v_isShared_7005_; uint8_t v_isSharedCheck_7029_; 
v_snd_7002_ = lean_ctor_get(v_a_6996_, 1);
v_isSharedCheck_7029_ = !lean_is_exclusive(v_a_6996_);
if (v_isSharedCheck_7029_ == 0)
{
lean_object* v_unused_7030_; 
v_unused_7030_ = lean_ctor_get(v_a_6996_, 0);
lean_dec(v_unused_7030_);
v___x_7004_ = v_a_6996_;
v_isShared_7005_ = v_isSharedCheck_7029_;
goto v_resetjp_7003_;
}
else
{
lean_inc(v_snd_7002_);
lean_dec(v_a_6996_);
v___x_7004_ = lean_box(0);
v_isShared_7005_ = v_isSharedCheck_7029_;
goto v_resetjp_7003_;
}
v_resetjp_7003_:
{
lean_object* v___x_7006_; lean_object* v_val_7008_; 
v___x_7006_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_6982_) == 1)
{
lean_object* v_val_7016_; uint8_t v___x_7017_; 
v_val_7016_ = lean_ctor_get(v_cancelTk_x3f_6982_, 0);
v___x_7017_ = l_IO_CancelToken_isSet(v_val_7016_);
if (v___x_7017_ == 0)
{
lean_del_object(v___x_7000_);
goto v___jp_7013_;
}
else
{
lean_object* v___x_7019_; uint8_t v_isShared_7020_; uint8_t v_isSharedCheck_7027_; 
lean_del_object(v___x_7004_);
lean_dec(v_fst_6998_);
lean_dec(v_fst_6997_);
lean_dec(v_r_6992_);
lean_dec(v_k_6989_);
lean_dec_ref(v_filterMapIdent_6981_);
v_isSharedCheck_7027_ = !lean_is_exclusive(v_cancelTk_x3f_6982_);
if (v_isSharedCheck_7027_ == 0)
{
lean_object* v_unused_7028_; 
v_unused_7028_ = lean_ctor_get(v_cancelTk_x3f_6982_, 0);
lean_dec(v_unused_7028_);
v___x_7019_ = v_cancelTk_x3f_6982_;
v_isShared_7020_ = v_isSharedCheck_7027_;
goto v_resetjp_7018_;
}
else
{
lean_dec(v_cancelTk_x3f_6982_);
v___x_7019_ = lean_box(0);
v_isShared_7020_ = v_isSharedCheck_7027_;
goto v_resetjp_7018_;
}
v_resetjp_7018_:
{
lean_object* v___x_7022_; 
lean_inc(v_snd_7002_);
if (v_isShared_7020_ == 0)
{
lean_ctor_set(v___x_7019_, 0, v_snd_7002_);
v___x_7022_ = v___x_7019_;
goto v_reusejp_7021_;
}
else
{
lean_object* v_reuseFailAlloc_7026_; 
v_reuseFailAlloc_7026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7026_, 0, v_snd_7002_);
v___x_7022_ = v_reuseFailAlloc_7026_;
goto v_reusejp_7021_;
}
v_reusejp_7021_:
{
lean_object* v___x_7024_; 
if (v_isShared_7001_ == 0)
{
lean_ctor_set(v___x_7000_, 1, v_snd_7002_);
lean_ctor_set(v___x_7000_, 0, v___x_7022_);
v___x_7024_ = v___x_7000_;
goto v_reusejp_7023_;
}
else
{
lean_object* v_reuseFailAlloc_7025_; 
v_reuseFailAlloc_7025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7025_, 0, v___x_7022_);
lean_ctor_set(v_reuseFailAlloc_7025_, 1, v_snd_7002_);
v___x_7024_ = v_reuseFailAlloc_7025_;
goto v_reusejp_7023_;
}
v_reusejp_7023_:
{
v_d_6987_ = v___x_7024_;
goto v___jp_6986_;
}
}
}
}
}
else
{
lean_del_object(v___x_7000_);
goto v___jp_7013_;
}
v___jp_7007_:
{
lean_object* v___x_7010_; 
if (v_isShared_7005_ == 0)
{
lean_ctor_set(v___x_7004_, 1, v_val_7008_);
lean_ctor_set(v___x_7004_, 0, v___x_7006_);
v___x_7010_ = v___x_7004_;
goto v_reusejp_7009_;
}
else
{
lean_object* v_reuseFailAlloc_7012_; 
v_reuseFailAlloc_7012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7012_, 0, v___x_7006_);
lean_ctor_set(v_reuseFailAlloc_7012_, 1, v_val_7008_);
v___x_7010_ = v_reuseFailAlloc_7012_;
goto v_reusejp_7009_;
}
v_reusejp_7009_:
{
v_init_6983_ = v___x_7010_;
v_x_6984_ = v_r_6992_;
goto _start;
}
}
v___jp_7013_:
{
lean_object* v___x_7014_; lean_object* v_a_7015_; 
lean_inc_ref(v_filterMapIdent_6981_);
v___x_7014_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_6981_, v_k_6989_, v_fst_6997_, v_snd_7002_, v_fst_6998_);
v_a_7015_ = lean_ctor_get(v___x_7014_, 0);
lean_inc(v_a_7015_);
lean_dec_ref(v___x_7014_);
v_val_7008_ = v_a_7015_;
goto v___jp_7007_;
}
}
}
}
}
else
{
lean_object* v___x_7033_; 
lean_dec(v_cancelTk_x3f_6982_);
lean_dec_ref(v_filterMapIdent_6981_);
v___x_7033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7033_, 0, v_init_6983_);
return v___x_7033_;
}
v___jp_6986_:
{
lean_object* v___x_6988_; 
v___x_6988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6988_, 0, v_d_6987_);
return v___x_6988_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg___boxed(lean_object* v_filterMapIdent_7034_, lean_object* v_cancelTk_x3f_7035_, lean_object* v_init_7036_, lean_object* v_x_7037_, lean_object* v___y_7038_){
_start:
{
lean_object* v_res_7039_; 
v_res_7039_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7034_, v_cancelTk_x3f_7035_, v_init_7036_, v_x_7037_);
return v_res_7039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg(lean_object* v_self_7045_, lean_object* v_filterMapIdent_7046_, lean_object* v_cancelTk_x3f_7047_){
_start:
{
lean_object* v___x_7049_; lean_object* v___x_7050_; lean_object* v___x_7051_; lean_object* v_val_7053_; lean_object* v_a_7057_; 
v___x_7049_ = l_Lean_Server_References_allRefs(v_self_7045_);
v___x_7050_ = ((lean_object*)(l_Lean_Server_References_definitionsMatching___redArg___closed__1));
v___x_7051_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7046_, v_cancelTk_x3f_7047_, v___x_7050_, v___x_7049_);
v_a_7057_ = lean_ctor_get(v___x_7051_, 0);
lean_inc(v_a_7057_);
lean_dec_ref(v___x_7051_);
v_val_7053_ = v_a_7057_;
goto v___jp_7052_;
v___jp_7052_:
{
lean_object* v_fst_7054_; 
v_fst_7054_ = lean_ctor_get(v_val_7053_, 0);
if (lean_obj_tag(v_fst_7054_) == 0)
{
lean_object* v_snd_7055_; 
v_snd_7055_ = lean_ctor_get(v_val_7053_, 1);
lean_inc(v_snd_7055_);
lean_dec_ref(v_val_7053_);
return v_snd_7055_;
}
else
{
lean_object* v_val_7056_; 
lean_inc_ref(v_fst_7054_);
lean_dec_ref(v_val_7053_);
v_val_7056_ = lean_ctor_get(v_fst_7054_, 0);
lean_inc(v_val_7056_);
lean_dec_ref_known(v_fst_7054_, 1);
return v_val_7056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___redArg___boxed(lean_object* v_self_7058_, lean_object* v_filterMapIdent_7059_, lean_object* v_cancelTk_x3f_7060_, lean_object* v_a_7061_){
_start:
{
lean_object* v_res_7062_; 
v_res_7062_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7058_, v_filterMapIdent_7059_, v_cancelTk_x3f_7060_);
return v_res_7062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching(lean_object* v_00_u03b1_7063_, lean_object* v_self_7064_, lean_object* v_filterMapIdent_7065_, lean_object* v_cancelTk_x3f_7066_){
_start:
{
lean_object* v___x_7068_; 
v___x_7068_ = l_Lean_Server_References_definitionsMatching___redArg(v_self_7064_, v_filterMapIdent_7065_, v_cancelTk_x3f_7066_);
return v___x_7068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_definitionsMatching___boxed(lean_object* v_00_u03b1_7069_, lean_object* v_self_7070_, lean_object* v_filterMapIdent_7071_, lean_object* v_cancelTk_x3f_7072_, lean_object* v_a_7073_){
_start:
{
lean_object* v_res_7074_; 
v_res_7074_ = l_Lean_Server_References_definitionsMatching(v_00_u03b1_7069_, v_self_7070_, v_filterMapIdent_7071_, v_cancelTk_x3f_7072_);
return v_res_7074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(lean_object* v_00_u03b1_7075_, lean_object* v_filterMapIdent_7076_, lean_object* v_a_7077_, lean_object* v_fst_7078_, lean_object* v_init_7079_, lean_object* v_x_7080_){
_start:
{
lean_object* v___x_7082_; 
v___x_7082_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___redArg(v_filterMapIdent_7076_, v_a_7077_, v_fst_7078_, v_init_7079_, v_x_7080_);
return v___x_7082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0___boxed(lean_object* v_00_u03b1_7083_, lean_object* v_filterMapIdent_7084_, lean_object* v_a_7085_, lean_object* v_fst_7086_, lean_object* v_init_7087_, lean_object* v_x_7088_, lean_object* v___y_7089_){
_start:
{
lean_object* v_res_7090_; 
v_res_7090_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__0(v_00_u03b1_7083_, v_filterMapIdent_7084_, v_a_7085_, v_fst_7086_, v_init_7087_, v_x_7088_);
return v_res_7090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(lean_object* v_00_u03b1_7091_, lean_object* v_filterMapIdent_7092_, lean_object* v_cancelTk_x3f_7093_, lean_object* v_init_7094_, lean_object* v_x_7095_){
_start:
{
lean_object* v___x_7097_; 
v___x_7097_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___redArg(v_filterMapIdent_7092_, v_cancelTk_x3f_7093_, v_init_7094_, v_x_7095_);
return v___x_7097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1___boxed(lean_object* v_00_u03b1_7098_, lean_object* v_filterMapIdent_7099_, lean_object* v_cancelTk_x3f_7100_, lean_object* v_init_7101_, lean_object* v_x_7102_, lean_object* v___y_7103_){
_start:
{
lean_object* v_res_7104_; 
v_res_7104_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_definitionsMatching_spec__1(v_00_u03b1_7098_, v_filterMapIdent_7099_, v_cancelTk_x3f_7100_, v_init_7101_, v_x_7102_);
return v_res_7104_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_References_importedBy_spec__0(lean_object* v_msg_7105_){
_start:
{
lean_object* v___x_7106_; lean_object* v___x_7107_; 
v___x_7106_ = ((lean_object*)(l_Lean_Server_instInhabitedModuleImport_default));
v___x_7107_ = lean_panic_fn_borrowed(v___x_7106_, v_msg_7105_);
return v___x_7107_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7111_; lean_object* v___x_7112_; lean_object* v___x_7113_; lean_object* v___x_7114_; lean_object* v___x_7115_; lean_object* v___x_7116_; 
v___x_7111_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__2));
v___x_7112_ = lean_unsigned_to_nat(14u);
v___x_7113_ = lean_unsigned_to_nat(22u);
v___x_7114_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__1));
v___x_7115_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__0));
v___x_7116_ = l_mkPanicMessageWithDecl(v___x_7115_, v___x_7114_, v___x_7113_, v___x_7112_, v___x_7111_);
return v___x_7116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(lean_object* v_requestedMod_7117_, lean_object* v_init_7118_, lean_object* v_x_7119_){
_start:
{
if (lean_obj_tag(v_x_7119_) == 0)
{
lean_object* v_k_7120_; lean_object* v_v_7121_; lean_object* v_l_7122_; lean_object* v_r_7123_; lean_object* v___x_7124_; lean_object* v_a_7125_; lean_object* v_fst_7126_; lean_object* v_snd_7127_; lean_object* v___y_7129_; lean_object* v_index_7144_; lean_object* v___x_7145_; 
v_k_7120_ = lean_ctor_get(v_x_7119_, 1);
v_v_7121_ = lean_ctor_get(v_x_7119_, 2);
v_l_7122_ = lean_ctor_get(v_x_7119_, 3);
v_r_7123_ = lean_ctor_get(v_x_7119_, 4);
v___x_7124_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7117_, v_init_7118_, v_l_7122_);
v_a_7125_ = lean_ctor_get(v___x_7124_, 0);
lean_inc(v_a_7125_);
v_fst_7126_ = lean_ctor_get(v_v_7121_, 0);
v_snd_7127_ = lean_ctor_get(v_v_7121_, 1);
v_index_7144_ = lean_ctor_get(v_snd_7127_, 1);
v___x_7145_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_References_updateWorkerSetupInfo_spec__0___redArg(v_index_7144_, v_requestedMod_7117_);
if (lean_obj_tag(v___x_7145_) == 1)
{
lean_object* v_val_7146_; lean_object* v___x_7147_; 
lean_dec_ref(v___x_7124_);
v_val_7146_ = lean_ctor_get(v___x_7145_, 0);
lean_inc(v_val_7146_);
lean_dec_ref_known(v___x_7145_, 1);
v___x_7147_ = l_Lean_Server_ModuleImport_collapseIdenticalImports_x3f(v_val_7146_);
lean_dec(v_val_7146_);
if (lean_obj_tag(v___x_7147_) == 0)
{
lean_object* v___x_7148_; lean_object* v___x_7149_; 
v___x_7148_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___closed__3);
v___x_7149_ = l_panic___at___00Lean_Server_References_importedBy_spec__0(v___x_7148_);
v___y_7129_ = v___x_7149_;
goto v___jp_7128_;
}
else
{
lean_object* v_val_7150_; 
v_val_7150_ = lean_ctor_get(v___x_7147_, 0);
lean_inc(v_val_7150_);
lean_dec_ref_known(v___x_7147_, 1);
v___y_7129_ = v_val_7150_;
goto v___jp_7128_;
}
}
else
{
lean_object* v_a_7151_; 
lean_dec(v___x_7145_);
lean_dec(v_a_7125_);
v_a_7151_ = lean_ctor_get(v___x_7124_, 0);
lean_inc(v_a_7151_);
lean_dec_ref(v___x_7124_);
v_init_7118_ = v_a_7151_;
v_x_7119_ = v_r_7123_;
goto _start;
}
v___jp_7128_:
{
uint8_t v_isAll_7130_; uint8_t v_isPrivate_7131_; uint8_t v_metaKind_7132_; lean_object* v___x_7134_; uint8_t v_isShared_7135_; uint8_t v_isSharedCheck_7141_; 
v_isAll_7130_ = lean_ctor_get_uint8(v___y_7129_, sizeof(void*)*2);
v_isPrivate_7131_ = lean_ctor_get_uint8(v___y_7129_, sizeof(void*)*2 + 1);
v_metaKind_7132_ = lean_ctor_get_uint8(v___y_7129_, sizeof(void*)*2 + 2);
v_isSharedCheck_7141_ = !lean_is_exclusive(v___y_7129_);
if (v_isSharedCheck_7141_ == 0)
{
lean_object* v_unused_7142_; lean_object* v_unused_7143_; 
v_unused_7142_ = lean_ctor_get(v___y_7129_, 1);
lean_dec(v_unused_7142_);
v_unused_7143_ = lean_ctor_get(v___y_7129_, 0);
lean_dec(v_unused_7143_);
v___x_7134_ = v___y_7129_;
v_isShared_7135_ = v_isSharedCheck_7141_;
goto v_resetjp_7133_;
}
else
{
lean_dec(v___y_7129_);
v___x_7134_ = lean_box(0);
v_isShared_7135_ = v_isSharedCheck_7141_;
goto v_resetjp_7133_;
}
v_resetjp_7133_:
{
lean_object* v___x_7137_; 
lean_inc(v_fst_7126_);
lean_inc(v_k_7120_);
if (v_isShared_7135_ == 0)
{
lean_ctor_set(v___x_7134_, 1, v_fst_7126_);
lean_ctor_set(v___x_7134_, 0, v_k_7120_);
v___x_7137_ = v___x_7134_;
goto v_reusejp_7136_;
}
else
{
lean_object* v_reuseFailAlloc_7140_; 
v_reuseFailAlloc_7140_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_7140_, 0, v_k_7120_);
lean_ctor_set(v_reuseFailAlloc_7140_, 1, v_fst_7126_);
lean_ctor_set_uint8(v_reuseFailAlloc_7140_, sizeof(void*)*2, v_isAll_7130_);
lean_ctor_set_uint8(v_reuseFailAlloc_7140_, sizeof(void*)*2 + 1, v_isPrivate_7131_);
lean_ctor_set_uint8(v_reuseFailAlloc_7140_, sizeof(void*)*2 + 2, v_metaKind_7132_);
v___x_7137_ = v_reuseFailAlloc_7140_;
goto v_reusejp_7136_;
}
v_reusejp_7136_:
{
lean_object* v___x_7138_; 
v___x_7138_ = lean_array_push(v_a_7125_, v___x_7137_);
v_init_7118_ = v___x_7138_;
v_x_7119_ = v_r_7123_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_7153_; 
v___x_7153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7153_, 0, v_init_7118_);
return v___x_7153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1___boxed(lean_object* v_requestedMod_7154_, lean_object* v_init_7155_, lean_object* v_x_7156_){
_start:
{
lean_object* v_res_7157_; 
v_res_7157_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7154_, v_init_7155_, v_x_7156_);
lean_dec(v_x_7156_);
lean_dec(v_requestedMod_7154_);
return v_res_7157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy(lean_object* v_self_7158_, lean_object* v_requestedMod_7159_){
_start:
{
lean_object* v_result_7160_; lean_object* v___x_7161_; lean_object* v___x_7162_; lean_object* v_a_7163_; 
v_result_7160_ = ((lean_object*)(l_Lean_Server_instEmptyCollectionDirectImports___closed__0));
v___x_7161_ = l_Lean_Server_References_allDirectImports(v_self_7158_);
v___x_7162_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Server_References_importedBy_spec__1(v_requestedMod_7159_, v_result_7160_, v___x_7161_);
lean_dec(v___x_7161_);
v_a_7163_ = lean_ctor_get(v___x_7162_, 0);
lean_inc(v_a_7163_);
lean_dec_ref(v___x_7162_);
return v_a_7163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_References_importedBy___boxed(lean_object* v_self_7164_, lean_object* v_requestedMod_7165_){
_start:
{
lean_object* v_res_7166_; 
v_res_7166_ = l_Lean_Server_References_importedBy(v_self_7164_, v_requestedMod_7165_);
lean_dec(v_requestedMod_7165_);
return v_res_7166_;
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

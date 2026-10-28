// Lean compiler output
// Module: Lean.Data.Lsp.Internal
// Imports: public import Lean.Data.Lsp.Basic public import Lean.Data.JsonRpc public import Lean.Data.DeclarationRange public import Init.Data.Array.GetLit public import Init.Data.Range.Polymorphic import Init.Omega
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_Lean_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_String_compare___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_Json_getArr_x3f(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_List_toJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Array_toJson___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
static const lean_string_object l_Lean_Lsp_instInhabitedImportInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Lsp_instInhabitedImportInfo_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedImportInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instInhabitedImportInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instInhabitedImportInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Lsp_instInhabitedImportInfo_default___closed__1 = (const lean_object*)&l_Lean_Lsp_instInhabitedImportInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedImportInfo_default = (const lean_object*)&l_Lean_Lsp_instInhabitedImportInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedImportInfo = (const lean_object*)&l_Lean_Lsp_instInhabitedImportInfo_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonImportInfo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonImportInfo___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonImportInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonImportInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonImportInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonImportInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonImportInfo = (const lean_object*)&l_Lean_Lsp_instToJsonImportInfo___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Expected array, got other JSON type"};
static const lean_object* l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonImportInfo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonImportInfo___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonImportInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonImportInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonImportInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonImportInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonImportInfo = (const lean_object*)&l_Lean_Lsp_instFromJsonImportInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqRefIdent_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRefIdent_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqRefIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqRefIdent_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqRefIdent___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqRefIdent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqRefIdent = (const lean_object*)&l_Lean_Lsp_instBEqRefIdent___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableRefIdent_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRefIdent_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instHashableRefIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instHashableRefIdent_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instHashableRefIdent___closed__0 = (const lean_object*)&l_Lean_Lsp_instHashableRefIdent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instHashableRefIdent = (const lean_object*)&l_Lean_Lsp_instHashableRefIdent___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instInhabitedRefIdent_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instInhabitedImportInfo_default___closed__0_value),((lean_object*)&l_Lean_Lsp_instInhabitedImportInfo_default___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instInhabitedRefIdent_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedRefIdent_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedRefIdent_default = (const lean_object*)&l_Lean_Lsp_instInhabitedRefIdent_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedRefIdent = (const lean_object*)&l_Lean_Lsp_instInhabitedRefIdent_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdRefIdent_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRefIdent_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdRefIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdRefIdent_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdRefIdent___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdRefIdent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdRefIdent = (const lean_object*)&l_Lean_Lsp_instOrdRefIdent___closed__0_value;
static const lean_string_object l_Lean_Lsp_RefIdent_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expected a 3-element array, got '"};
static const lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f___closed__0 = (const lean_object*)&l_Lean_Lsp_RefIdent_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1 = (const lean_object*)&l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lean_Lsp_RefIdent_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expected 0 or 1, got '"};
static const lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f___closed__2 = (const lean_object*)&l_Lean_Lsp_RefIdent_fromJson_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object*);
static lean_once_cell_t l_Lean_Lsp_RefIdent_toJson___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_RefIdent_toJson___closed__0;
static lean_once_cell_t l_Lean_Lsp_RefIdent_toJson___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_RefIdent_toJson___closed__1;
static lean_once_cell_t l_Lean_Lsp_RefIdent_toJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_RefIdent_toJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_RefIdent_toJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_RefIdent_toJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_RefIdent_toJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_RefIdent_toJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_RefIdent_toJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_RefIdent_toJson___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_RefIdent_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_RefIdent_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_RefIdent_instFromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_RefIdent_instFromJson = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJson___closed__0_value;
static const lean_closure_object l_Lean_Lsp_RefIdent_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_RefIdent_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_RefIdent_instToJson___closed__0 = (const lean_object*)&l_Lean_Lsp_RefIdent_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_RefIdent_instToJson = (const lean_object*)&l_Lean_Lsp_RefIdent_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeclInfo___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDeclInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDeclInfo___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDeclInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDeclInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDeclInfo = (const lean_object*)&l_Lean_Lsp_instToJsonDeclInfo___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Expected list of length 8, not length "};
static const lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Expected list"};
static const lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDeclInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDeclInfo___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonDeclInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDeclInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDeclInfo = (const lean_object*)&l_Lean_Lsp_instFromJsonDeclInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instEmptyCollectionDecls___aux__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instEmptyCollectionDecls;
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__0_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__7 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__7_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__2_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__3_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__4_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__8 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__8_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__6_value)}};
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDecls___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDecls___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDecls___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDecls___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDecls___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDecls___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDecls___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDecls___lam__2, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonDecls___closed__1_value),((lean_object*)&l_Lean_Lsp_instToJsonDecls___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDecls___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonDecls___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDecls = (const lean_object*)&l_Lean_Lsp_instToJsonDecls___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDecls___lam__0, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDecls___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__4_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDecls___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__5_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__6_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__1_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__2_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__3_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__7_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDecls___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__7_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__8_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__9_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDecls___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__9_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDecls = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_RefInfo_instInhabitedLocation_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instInhabitedImportInfo_default___closed__0_value)}};
static const lean_object* l_Lean_Lsp_RefInfo_instInhabitedLocation_default___closed__0 = (const lean_object*)&l_Lean_Lsp_RefInfo_instInhabitedLocation_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_RefInfo_instInhabitedLocation_default = (const lean_object*)&l_Lean_Lsp_RefInfo_instInhabitedLocation_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_RefInfo_instInhabitedLocation = (const lean_object*)&l_Lean_Lsp_RefInfo_instInhabitedLocation_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "usages"};
static const lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRefInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRefInfo___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonRefInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instToJsonRefInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRefInfo___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__1_value)} };
static const lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instToJsonRefInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instToJsonRefInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_List_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__3_value)} };
static const lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instToJsonRefInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRefInfo___lam__3, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__4_value),((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__2_value),((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__1_value)} };
static const lean_object* l_Lean_Lsp_instToJsonRefInfo___closed__5 = (const lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRefInfo = (const lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__5_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Expected list of length 4 or 5, not "};
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__1_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__2_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__2_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRefInfo___lam__1, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__3_value),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__4_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__9_value),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRefInfo = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instEmptyCollectionModuleRefs___aux__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instEmptyCollectionModuleRefs;
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_instToJsonModuleRefs___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonModuleRefs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonModuleRefs___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonModuleRefs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonModuleRefs___lam__0___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__0_value),((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonModuleRefs___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instToJsonModuleRefs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonModuleRefs___lam__2, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9_value),((lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__1_value)} };
static const lean_object* l_Lean_Lsp_instToJsonModuleRefs___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonModuleRefs = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonModuleRefs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected even-length array"};
static const lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonModuleRefs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonModuleRefs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonModuleRefs___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonModuleRefs___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonModuleRefs = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "LeanILeanHeaderSetupInfoParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(95, 71, 232, 96, 38, 120, 115, 9)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "isSetupFailure"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(120, 71, 255, 216, 122, 125, 37, 209)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "directImports"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18_value),LEAN_SCALAR_PTR_LITERAL(113, 107, 65, 139, 239, 150, 173, 242)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LeanIleanInfoParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 203, 234, 116, 96, 81, 39, 191)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "references"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 234, 189, 66, 81, 216, 208, 197)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decls"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11_value),LEAN_SCALAR_PTR_LITERAL(44, 160, 58, 0, 137, 124, 237, 95)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "importClosure"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "LeanImportClosureParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(168, 46, 39, 145, 64, 232, 10, 239)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 59, 80, 112, 20, 250, 24, 1)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportClosureParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImportClosureParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "staleDependency"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "LeanStaleDependencyParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 219, 232, 96, 172, 178, 164, 179)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 114, 98, 202, 15, 244, 42, 22)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanStaleDependencyParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "renamed"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "allExcept"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__5_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(29, 171, 189, 33, 127, 223, 44, 88)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__7_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "exceptions"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__8_value),LEAN_SCALAR_PTR_LITERAL(192, 220, 58, 79, 173, 93, 125, 104)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9_value;
static const lean_array_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__7_value),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__11_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "from"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12_value),LEAN_SCALAR_PTR_LITERAL(51, 132, 19, 107, 10, 182, 190, 14)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__13_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "to"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(203, 162, 13, 215, 195, 228, 231, 139)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15_value;
static const lean_array_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__13_value),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__16 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__16_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__16_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__17 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonOpenNamespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonOpenNamespace_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonOpenNamespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonOpenNamespace_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonOpenNamespace___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonOpenNamespace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonOpenNamespace = (const lean_object*)&l_Lean_Lsp_instToJsonOpenNamespace___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "identifier"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "LeanModuleQuery"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(173, 124, 7, 179, 233, 81, 44, 231)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 30, 163, 185, 99, 139, 146, 235)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "openNamespaces"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(84, 10, 255, 246, 172, 0, 163, 196)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanModuleQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleQuery___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanModuleQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanModuleQuery_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanModuleQuery___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery = (const lean_object*)&l_Lean_Lsp_instToJsonLeanModuleQuery___closed__0_value;
static const lean_string_object l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "a request id needs to be a number or a string"};
static const lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__0 = (const lean_object*)&l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__0_value)}};
static const lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1 = (const lean_object*)&l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "sourceRequestID"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "LeanQueryModuleParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 1, 217, 58, 51, 228, 82, 97)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(235, 152, 164, 59, 36, 1, 26, 169)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "queries"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(67, 69, 35, 158, 6, 191, 84, 222)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanQueryModuleParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanQueryModuleParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanQueryModuleParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanQueryModuleParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LeanIdentifier"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 34, 237, 78, 120, 102, 249, 11)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "decl"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(122, 197, 108, 116, 168, 105, 88, 191)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "isExactMatch"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(184, 254, 2, 171, 133, 246, 126, 123)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIdentifier___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanIdentifier_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanIdentifier___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanIdentifier___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanIdentifier = (const lean_object*)&l_Lean_Lsp_instToJsonLeanIdentifier___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "queryResults"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "LeanQueryModuleResponse"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(43, 4, 13, 130, 17, 133, 248, 128)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 102, 170, 178, 152, 193, 48, 141)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanQueryModuleResponse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanQueryModuleResponse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanQueryModuleResponse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse = (const lean_object*)&l_Lean_Lsp_instToJsonLeanQueryModuleResponse___closed__0_value;
static const lean_array_object l_Lean_Lsp_instInhabitedLeanQueryModuleResponse_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instInhabitedLeanQueryModuleResponse_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedLeanQueryModuleResponse_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedLeanQueryModuleResponse_default = (const lean_object*)&l_Lean_Lsp_instInhabitedLeanQueryModuleResponse_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedLeanQueryModuleResponse = (const lean_object*)&l_Lean_Lsp_instInhabitedLeanQueryModuleResponse_default___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LeanDeclIdent"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 27, 219, 221, 117, 72, 148, 223)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanDeclIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDeclIdent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDeclIdent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanDeclIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanDeclIdent_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanDeclIdent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent = (const lean_object*)&l_Lean_Lsp_instToJsonLeanDeclIdent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "originSelectionRange"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LeanLocationLink"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 146, 238, 203, 212, 254, 171, 194)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "originSelectionRange\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__5_value),LEAN_SCALAR_PTR_LITERAL(113, 74, 194, 55, 146, 231, 63, 35)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "targetUri"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10_value),LEAN_SCALAR_PTR_LITERAL(175, 177, 170, 233, 220, 50, 208, 212)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "targetRange"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15_value),LEAN_SCALAR_PTR_LITERAL(45, 64, 248, 134, 128, 146, 245, 203)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "targetSelectionRange"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20_value),LEAN_SCALAR_PTR_LITERAL(152, 179, 191, 7, 212, 29, 154, 211)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ident\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__26 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__26_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__26_value),LEAN_SCALAR_PTR_LITERAL(48, 54, 166, 138, 27, 67, 37, 23)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "isDefault"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31_value),LEAN_SCALAR_PTR_LITERAL(109, 30, 229, 216, 225, 52, 237, 248)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanLocationLink___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanLocationLink___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanLocationLink___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanLocationLink_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanLocationLink___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanLocationLink___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanLocationLink = (const lean_object*)&l_Lean_Lsp_instToJsonLeanLocationLink___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonImportInfo___lam__0(lean_object* v_info_7_){
_start:
{
lean_object* v_module_8_; uint8_t v_isPrivate_9_; uint8_t v_isAll_10_; uint8_t v_isMeta_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_module_8_ = lean_ctor_get(v_info_7_, 0);
v_isPrivate_9_ = lean_ctor_get_uint8(v_info_7_, sizeof(void*)*1);
v_isAll_10_ = lean_ctor_get_uint8(v_info_7_, sizeof(void*)*1 + 1);
v_isMeta_11_ = lean_ctor_get_uint8(v_info_7_, sizeof(void*)*1 + 2);
lean_inc_ref(v_module_8_);
v___x_12_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_12_, 0, v_module_8_);
v___x_13_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_13_, 0, v_isPrivate_9_);
v___x_14_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_14_, 0, v_isAll_10_);
v___x_15_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_15_, 0, v_isMeta_11_);
v___x_16_ = lean_unsigned_to_nat(4u);
v___x_17_ = lean_mk_empty_array_with_capacity(v___x_16_);
v___x_18_ = lean_array_push(v___x_17_, v___x_12_);
v___x_19_ = lean_array_push(v___x_18_, v___x_13_);
v___x_20_ = lean_array_push(v___x_19_, v___x_14_);
v___x_21_ = lean_array_push(v___x_20_, v___x_15_);
v___x_22_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonImportInfo___lam__0___boxed(lean_object* v_info_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Lsp_instToJsonImportInfo___lam__0(v_info_23_);
lean_dec_ref(v_info_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonImportInfo___lam__0(lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 4)
{
lean_object* v_elems_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_elems_33_ = lean_ctor_get(v_x_30_, 0);
v___x_34_ = lean_array_get_size(v_elems_33_);
v___x_35_ = lean_unsigned_to_nat(4u);
v___x_36_ = lean_nat_dec_eq(v___x_34_, v___x_35_);
if (v___x_36_ == 0)
{
goto v___jp_31_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_array_fget_borrowed(v_elems_33_, v___x_37_);
lean_inc(v___x_38_);
v___x_39_ = l_Lean_Json_getStr_x3f(v___x_38_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_39_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_a_48_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_39_, 1);
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_array_fget_borrowed(v_elems_33_, v___x_49_);
v___x_51_ = l_Lean_Json_getBool_x3f(v___x_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
lean_dec(v_a_48_);
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_a_60_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_60_);
lean_dec_ref_known(v___x_51_, 1);
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_array_fget_borrowed(v_elems_33_, v___x_61_);
v___x_63_ = l_Lean_Json_getBool_x3f(v___x_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
lean_dec(v_a_60_);
lean_dec(v_a_48_);
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
else
{
lean_object* v_a_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_a_72_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_63_, 1);
v___x_73_ = lean_unsigned_to_nat(3u);
v___x_74_ = lean_array_fget_borrowed(v_elems_33_, v___x_73_);
v___x_75_ = l_Lean_Json_getBool_x3f(v___x_74_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec(v_a_72_);
lean_dec(v_a_60_);
lean_dec(v_a_48_);
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
else
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_95_; 
v_a_84_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_95_ == 0)
{
v___x_86_ = v___x_75_;
v_isShared_87_ = v_isSharedCheck_95_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_75_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_95_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; uint8_t v___x_89_; uint8_t v___x_90_; uint8_t v___x_91_; lean_object* v___x_93_; 
v___x_88_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_88_, 0, v_a_48_);
v___x_89_ = lean_unbox(v_a_60_);
lean_dec(v_a_60_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_89_);
v___x_90_ = lean_unbox(v_a_72_);
lean_dec(v_a_72_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1 + 1, v___x_90_);
v___x_91_ = lean_unbox(v_a_84_);
lean_dec(v_a_84_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1 + 2, v___x_91_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_93_ = v___x_86_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
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
goto v___jp_31_;
}
v___jp_31_:
{
lean_object* v___x_32_; 
v___x_32_ = ((lean_object*)(l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__1));
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonImportInfo___lam__0___boxed(lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Lsp_instFromJsonImportInfo___lam__0(v_x_96_);
lean_dec(v_x_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorIdx___impl(lean_object* v_x_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_tag_nat(v_x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorIdx___impl___boxed(lean_object* v_x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Lsp_RefIdent_ctorIdx___impl(v_x_102_);
lean_dec_ref(v_x_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorElim___redArg(lean_object* v_t_104_, lean_object* v_k_105_){
_start:
{
lean_object* v_moduleName_106_; lean_object* v_identName_107_; lean_object* v___x_108_; 
v_moduleName_106_ = lean_ctor_get(v_t_104_, 0);
lean_inc_ref(v_moduleName_106_);
v_identName_107_ = lean_ctor_get(v_t_104_, 1);
lean_inc_ref(v_identName_107_);
lean_dec_ref(v_t_104_);
v___x_108_ = lean_apply_2(v_k_105_, v_moduleName_106_, v_identName_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorElim(lean_object* v_motive_109_, lean_object* v_ctorIdx_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_k_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_111_, v_k_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorElim___boxed(lean_object* v_motive_115_, lean_object* v_ctorIdx_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_k_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Lsp_RefIdent_ctorElim(v_motive_115_, v_ctorIdx_116_, v_t_117_, v_h_118_, v_k_119_);
lean_dec(v_ctorIdx_116_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_const_elim___redArg(lean_object* v_t_121_, lean_object* v_const_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_121_, v_const_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_const_elim(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_const_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_125_, v_const_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fvar_elim___redArg(lean_object* v_t_129_, lean_object* v_fvar_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_129_, v_fvar_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fvar_elim(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_fvar_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_133_, v_fvar_135_);
return v___x_136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqRefIdent_beq(lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
lean_object* v_a_140_; lean_object* v_a_141_; lean_object* v_b_142_; lean_object* v_b_143_; 
if (lean_obj_tag(v_x_137_) == 0)
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_moduleName_146_; lean_object* v_identName_147_; lean_object* v_moduleName_148_; lean_object* v_identName_149_; 
v_moduleName_146_ = lean_ctor_get(v_x_137_, 0);
v_identName_147_ = lean_ctor_get(v_x_137_, 1);
v_moduleName_148_ = lean_ctor_get(v_x_138_, 0);
v_identName_149_ = lean_ctor_get(v_x_138_, 1);
v_a_140_ = v_moduleName_146_;
v_a_141_ = v_identName_147_;
v_b_142_ = v_moduleName_148_;
v_b_143_ = v_identName_149_;
goto v___jp_139_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
}
else
{
if (lean_obj_tag(v_x_138_) == 1)
{
lean_object* v_moduleName_151_; lean_object* v_id_152_; lean_object* v_moduleName_153_; lean_object* v_id_154_; 
v_moduleName_151_ = lean_ctor_get(v_x_137_, 0);
v_id_152_ = lean_ctor_get(v_x_137_, 1);
v_moduleName_153_ = lean_ctor_get(v_x_138_, 0);
v_id_154_ = lean_ctor_get(v_x_138_, 1);
v_a_140_ = v_moduleName_151_;
v_a_141_ = v_id_152_;
v_b_142_ = v_moduleName_153_;
v_b_143_ = v_id_154_;
goto v___jp_139_;
}
else
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
}
v___jp_139_:
{
uint8_t v___x_144_; 
v___x_144_ = lean_string_dec_eq(v_a_140_, v_b_142_);
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = lean_string_dec_eq(v_a_141_, v_b_143_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRefIdent_beq___boxed(lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Lean_Lsp_instBEqRefIdent_beq(v_x_156_, v_x_157_);
lean_dec_ref(v_x_157_);
lean_dec_ref(v_x_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableRefIdent_hash(lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v_moduleName_163_; lean_object* v_identName_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; 
v_moduleName_163_ = lean_ctor_get(v_x_162_, 0);
v_identName_164_ = lean_ctor_get(v_x_162_, 1);
v___x_165_ = 0ULL;
v___x_166_ = lean_string_hash(v_moduleName_163_);
v___x_167_ = lean_uint64_mix_hash(v___x_165_, v___x_166_);
v___x_168_ = lean_string_hash(v_identName_164_);
v___x_169_ = lean_uint64_mix_hash(v___x_167_, v___x_168_);
return v___x_169_;
}
else
{
lean_object* v_moduleName_170_; lean_object* v_id_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; 
v_moduleName_170_ = lean_ctor_get(v_x_162_, 0);
v_id_171_ = lean_ctor_get(v_x_162_, 1);
v___x_172_ = 1ULL;
v___x_173_ = lean_string_hash(v_moduleName_170_);
v___x_174_ = lean_uint64_mix_hash(v___x_172_, v___x_173_);
v___x_175_ = lean_string_hash(v_id_171_);
v___x_176_ = lean_uint64_mix_hash(v___x_174_, v___x_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRefIdent_hash___boxed(lean_object* v_x_177_){
_start:
{
uint64_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Lean_Lsp_instHashableRefIdent_hash(v_x_177_);
lean_dec_ref(v_x_177_);
v_r_179_ = lean_box_uint64(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdRefIdent_ord(lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v_a_189_; lean_object* v_a_190_; lean_object* v_b_191_; lean_object* v_b_192_; 
if (lean_obj_tag(v_x_186_) == 0)
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v_moduleName_195_; lean_object* v_identName_196_; lean_object* v_moduleName_197_; lean_object* v_identName_198_; 
v_moduleName_195_ = lean_ctor_get(v_x_186_, 0);
v_identName_196_ = lean_ctor_get(v_x_186_, 1);
v_moduleName_197_ = lean_ctor_get(v_x_187_, 0);
v_identName_198_ = lean_ctor_get(v_x_187_, 1);
v_a_189_ = v_moduleName_195_;
v_a_190_ = v_identName_196_;
v_b_191_ = v_moduleName_197_;
v_b_192_ = v_identName_198_;
goto v___jp_188_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
else
{
if (lean_obj_tag(v_x_187_) == 0)
{
uint8_t v___x_200_; 
v___x_200_ = 2;
return v___x_200_;
}
else
{
lean_object* v_moduleName_201_; lean_object* v_id_202_; lean_object* v_moduleName_203_; lean_object* v_id_204_; 
v_moduleName_201_ = lean_ctor_get(v_x_186_, 0);
v_id_202_ = lean_ctor_get(v_x_186_, 1);
v_moduleName_203_ = lean_ctor_get(v_x_187_, 0);
v_id_204_ = lean_ctor_get(v_x_187_, 1);
v_a_189_ = v_moduleName_201_;
v_a_190_ = v_id_202_;
v_b_191_ = v_moduleName_203_;
v_b_192_ = v_id_204_;
goto v___jp_188_;
}
}
v___jp_188_:
{
uint8_t v___x_193_; 
v___x_193_ = lean_string_compare(v_a_189_, v_b_191_);
if (v___x_193_ == 1)
{
uint8_t v___x_194_; 
v___x_194_ = lean_string_compare(v_a_190_, v_b_192_);
return v___x_194_;
}
else
{
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRefIdent_ord___boxed(lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Lean_Lsp_instOrdRefIdent_ord(v_x_205_, v_x_206_);
lean_dec_ref(v_x_206_);
lean_dec_ref(v_x_205_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object* v_x_214_){
_start:
{
lean_object* v_j_216_; 
if (lean_obj_tag(v_x_214_) == 4)
{
lean_object* v_elems_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_elems_224_ = lean_ctor_get(v_x_214_, 0);
v___x_225_ = lean_array_get_size(v_elems_224_);
v___x_226_ = lean_unsigned_to_nat(3u);
v___x_227_ = lean_nat_dec_eq(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
v_j_216_ = v_x_214_;
goto v___jp_215_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_inc_ref(v_elems_224_);
lean_dec_ref_known(v_x_214_, 1);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_array_fget_borrowed(v_elems_224_, v___x_228_);
lean_inc(v___x_229_);
v___x_230_ = l_Lean_Json_getStr_x3f(v___x_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref(v_elems_224_);
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_a_239_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v___x_230_, 1);
v___x_240_ = lean_unsigned_to_nat(2u);
v___x_241_ = lean_array_fget_borrowed(v_elems_224_, v___x_240_);
lean_inc(v___x_241_);
v___x_242_ = l_Lean_Json_getStr_x3f(v___x_241_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec(v_a_239_);
lean_dec_ref(v_elems_224_);
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_a_251_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_242_, 1);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_array_fget(v_elems_224_, v___x_252_);
lean_dec_ref(v_elems_224_);
lean_inc(v___x_253_);
v___x_254_ = l_Lean_Json_getNat_x3f(v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec(v___x_253_);
lean_dec(v_a_251_);
lean_dec(v_a_239_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_286_; 
v_a_263_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_286_ == 0)
{
v___x_265_ = v___x_254_;
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_254_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
uint8_t v___x_267_; 
v___x_267_ = lean_nat_dec_eq(v_a_263_, v___x_252_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; 
v___x_268_ = lean_nat_dec_eq(v_a_263_, v___x_228_);
lean_dec(v_a_263_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec(v_a_251_);
lean_dec(v_a_239_);
v___x_269_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__2));
v___x_270_ = lean_unsigned_to_nat(80u);
v___x_271_ = l_Lean_Json_pretty(v___x_253_, v___x_270_);
v___x_272_ = lean_string_append(v___x_269_, v___x_271_);
lean_dec_ref(v___x_271_);
v___x_273_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_274_ = lean_string_append(v___x_272_, v___x_273_);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 0);
lean_ctor_set(v___x_265_, 0, v___x_274_);
v___x_276_ = v___x_265_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_280_; 
lean_dec(v___x_253_);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v_a_239_);
lean_ctor_set(v___x_278_, 1, v_a_251_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_278_);
v___x_280_ = v___x_265_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_dec(v_a_263_);
lean_dec(v___x_253_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_a_239_);
lean_ctor_set(v___x_282_, 1, v_a_251_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_282_);
v___x_284_ = v___x_265_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
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
v_j_216_ = v_x_214_;
goto v___jp_215_;
}
v___jp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_217_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__0));
v___x_218_ = lean_unsigned_to_nat(80u);
v___x_219_ = l_Lean_Json_pretty(v_j_216_, v___x_218_);
v___x_220_ = lean_string_append(v___x_217_, v___x_219_);
lean_dec_ref(v___x_219_);
v___x_221_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_222_ = lean_string_append(v___x_220_, v___x_221_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_toJson___closed__0(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l_Lean_JsonNumber_fromNat(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_toJson___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_obj_once(&l_Lean_Lsp_RefIdent_toJson___closed__0, &l_Lean_Lsp_RefIdent_toJson___closed__0_once, _init_l_Lean_Lsp_RefIdent_toJson___closed__0);
v___x_290_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_toJson___closed__2(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_291_ = lean_obj_once(&l_Lean_Lsp_RefIdent_toJson___closed__1, &l_Lean_Lsp_RefIdent_toJson___closed__1_once, _init_l_Lean_Lsp_RefIdent_toJson___closed__1);
v___x_292_ = lean_unsigned_to_nat(3u);
v___x_293_ = lean_mk_empty_array_with_capacity(v___x_292_);
v___x_294_ = lean_array_push(v___x_293_, v___x_291_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_toJson___closed__3(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = l_Lean_JsonNumber_fromNat(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_toJson___closed__4(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_obj_once(&l_Lean_Lsp_RefIdent_toJson___closed__3, &l_Lean_Lsp_RefIdent_toJson___closed__3_once, _init_l_Lean_Lsp_RefIdent_toJson___closed__3);
v___x_298_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Lsp_RefIdent_toJson___closed__5(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_obj_once(&l_Lean_Lsp_RefIdent_toJson___closed__4, &l_Lean_Lsp_RefIdent_toJson___closed__4_once, _init_l_Lean_Lsp_RefIdent_toJson___closed__4);
v___x_300_ = lean_unsigned_to_nat(3u);
v___x_301_ = lean_mk_empty_array_with_capacity(v___x_300_);
v___x_302_ = lean_array_push(v___x_301_, v___x_299_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v_moduleName_304_; lean_object* v_identName_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_moduleName_304_ = lean_ctor_get(v_x_303_, 0);
v_identName_305_ = lean_ctor_get(v_x_303_, 1);
lean_inc_ref(v_moduleName_304_);
v___x_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_306_, 0, v_moduleName_304_);
lean_inc_ref(v_identName_305_);
v___x_307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_307_, 0, v_identName_305_);
v___x_308_ = lean_obj_once(&l_Lean_Lsp_RefIdent_toJson___closed__2, &l_Lean_Lsp_RefIdent_toJson___closed__2_once, _init_l_Lean_Lsp_RefIdent_toJson___closed__2);
v___x_309_ = lean_array_push(v___x_308_, v___x_306_);
v___x_310_ = lean_array_push(v___x_309_, v___x_307_);
v___x_311_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
else
{
lean_object* v_moduleName_312_; lean_object* v_id_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_moduleName_312_ = lean_ctor_get(v_x_303_, 0);
v_id_313_ = lean_ctor_get(v_x_303_, 1);
lean_inc_ref(v_moduleName_312_);
v___x_314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_314_, 0, v_moduleName_312_);
lean_inc_ref(v_id_313_);
v___x_315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_315_, 0, v_id_313_);
v___x_316_ = lean_obj_once(&l_Lean_Lsp_RefIdent_toJson___closed__5, &l_Lean_Lsp_RefIdent_toJson___closed__5_once, _init_l_Lean_Lsp_RefIdent_toJson___closed__5);
v___x_317_ = lean_array_push(v___x_316_, v___x_314_);
v___x_318_ = lean_array_push(v___x_317_, v___x_315_);
v___x_319_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson___boxed(lean_object* v_x_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Lsp_RefIdent_toJson(v_x_320_);
lean_dec_ref(v_x_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges(lean_object* v_r_326_){
_start:
{
lean_object* v_range_327_; lean_object* v_pos_328_; lean_object* v_endPos_329_; lean_object* v_selectionRange_330_; lean_object* v_pos_331_; lean_object* v_endPos_332_; lean_object* v_charUtf16_333_; lean_object* v_endCharUtf16_334_; lean_object* v_line_335_; lean_object* v_line_336_; lean_object* v_charUtf16_337_; lean_object* v_endCharUtf16_338_; lean_object* v_line_339_; lean_object* v_line_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_range_327_ = lean_ctor_get(v_r_326_, 0);
v_pos_328_ = lean_ctor_get(v_range_327_, 0);
v_endPos_329_ = lean_ctor_get(v_range_327_, 2);
v_selectionRange_330_ = lean_ctor_get(v_r_326_, 1);
v_pos_331_ = lean_ctor_get(v_selectionRange_330_, 0);
v_endPos_332_ = lean_ctor_get(v_selectionRange_330_, 2);
v_charUtf16_333_ = lean_ctor_get(v_range_327_, 1);
v_endCharUtf16_334_ = lean_ctor_get(v_range_327_, 3);
v_line_335_ = lean_ctor_get(v_pos_328_, 0);
v_line_336_ = lean_ctor_get(v_endPos_329_, 0);
v_charUtf16_337_ = lean_ctor_get(v_selectionRange_330_, 1);
v_endCharUtf16_338_ = lean_ctor_get(v_selectionRange_330_, 3);
v_line_339_ = lean_ctor_get(v_pos_331_, 0);
v_line_340_ = lean_ctor_get(v_endPos_332_, 0);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_sub(v_line_335_, v___x_341_);
v___x_343_ = lean_nat_sub(v_line_336_, v___x_341_);
v___x_344_ = lean_nat_sub(v_line_339_, v___x_341_);
v___x_345_ = lean_nat_sub(v_line_340_, v___x_341_);
lean_inc(v_endCharUtf16_338_);
lean_inc(v_charUtf16_337_);
lean_inc(v_endCharUtf16_334_);
lean_inc(v_charUtf16_333_);
v___x_346_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_346_, 0, v___x_342_);
lean_ctor_set(v___x_346_, 1, v_charUtf16_333_);
lean_ctor_set(v___x_346_, 2, v___x_343_);
lean_ctor_set(v___x_346_, 3, v_endCharUtf16_334_);
lean_ctor_set(v___x_346_, 4, v___x_344_);
lean_ctor_set(v___x_346_, 5, v_charUtf16_337_);
lean_ctor_set(v___x_346_, 6, v___x_345_);
lean_ctor_set(v___x_346_, 7, v_endCharUtf16_338_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges___boxed(lean_object* v_r_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_r_347_);
lean_dec_ref(v_r_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range(lean_object* v_i_349_){
_start:
{
lean_object* v_rangeStartPosLine_350_; lean_object* v_rangeStartPosCharacter_351_; lean_object* v_rangeEndPosLine_352_; lean_object* v_rangeEndPosCharacter_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_rangeStartPosLine_350_ = lean_ctor_get(v_i_349_, 0);
v_rangeStartPosCharacter_351_ = lean_ctor_get(v_i_349_, 1);
v_rangeEndPosLine_352_ = lean_ctor_get(v_i_349_, 2);
v_rangeEndPosCharacter_353_ = lean_ctor_get(v_i_349_, 3);
lean_inc(v_rangeStartPosCharacter_351_);
lean_inc(v_rangeStartPosLine_350_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_rangeStartPosLine_350_);
lean_ctor_set(v___x_354_, 1, v_rangeStartPosCharacter_351_);
lean_inc(v_rangeEndPosCharacter_353_);
lean_inc(v_rangeEndPosLine_352_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v_rangeEndPosLine_352_);
lean_ctor_set(v___x_355_, 1, v_rangeEndPosCharacter_353_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range___boxed(lean_object* v_i_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Lsp_DeclInfo_range(v_i_357_);
lean_dec_ref(v_i_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange(lean_object* v_i_359_){
_start:
{
lean_object* v_selectionRangeStartPosLine_360_; lean_object* v_selectionRangeStartPosCharacter_361_; lean_object* v_selectionRangeEndPosLine_362_; lean_object* v_selectionRangeEndPosCharacter_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_selectionRangeStartPosLine_360_ = lean_ctor_get(v_i_359_, 4);
v_selectionRangeStartPosCharacter_361_ = lean_ctor_get(v_i_359_, 5);
v_selectionRangeEndPosLine_362_ = lean_ctor_get(v_i_359_, 6);
v_selectionRangeEndPosCharacter_363_ = lean_ctor_get(v_i_359_, 7);
lean_inc(v_selectionRangeStartPosCharacter_361_);
lean_inc(v_selectionRangeStartPosLine_360_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_selectionRangeStartPosLine_360_);
lean_ctor_set(v___x_364_, 1, v_selectionRangeStartPosCharacter_361_);
lean_inc(v_selectionRangeEndPosCharacter_363_);
lean_inc(v_selectionRangeEndPosLine_362_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_selectionRangeEndPosLine_362_);
lean_ctor_set(v___x_365_, 1, v_selectionRangeEndPosCharacter_363_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange___boxed(lean_object* v_i_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Lsp_DeclInfo_selectionRange(v_i_367_);
lean_dec_ref(v_i_367_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeclInfo___lam__0(lean_object* v_i_369_){
_start:
{
lean_object* v_rangeStartPosLine_370_; lean_object* v_rangeStartPosCharacter_371_; lean_object* v_rangeEndPosLine_372_; lean_object* v_rangeEndPosCharacter_373_; lean_object* v_selectionRangeStartPosLine_374_; lean_object* v_selectionRangeStartPosCharacter_375_; lean_object* v_selectionRangeEndPosLine_376_; lean_object* v_selectionRangeEndPosCharacter_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_rangeStartPosLine_370_ = lean_ctor_get(v_i_369_, 0);
lean_inc(v_rangeStartPosLine_370_);
v_rangeStartPosCharacter_371_ = lean_ctor_get(v_i_369_, 1);
lean_inc(v_rangeStartPosCharacter_371_);
v_rangeEndPosLine_372_ = lean_ctor_get(v_i_369_, 2);
lean_inc(v_rangeEndPosLine_372_);
v_rangeEndPosCharacter_373_ = lean_ctor_get(v_i_369_, 3);
lean_inc(v_rangeEndPosCharacter_373_);
v_selectionRangeStartPosLine_374_ = lean_ctor_get(v_i_369_, 4);
lean_inc(v_selectionRangeStartPosLine_374_);
v_selectionRangeStartPosCharacter_375_ = lean_ctor_get(v_i_369_, 5);
lean_inc(v_selectionRangeStartPosCharacter_375_);
v_selectionRangeEndPosLine_376_ = lean_ctor_get(v_i_369_, 6);
lean_inc(v_selectionRangeEndPosLine_376_);
v_selectionRangeEndPosCharacter_377_ = lean_ctor_get(v_i_369_, 7);
lean_inc(v_selectionRangeEndPosCharacter_377_);
lean_dec_ref(v_i_369_);
v___x_378_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_370_);
v___x_379_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
v___x_380_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_371_);
v___x_381_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_372_);
v___x_383_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___x_384_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_373_);
v___x_385_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
v___x_386_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_374_);
v___x_387_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
v___x_388_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_375_);
v___x_389_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
v___x_390_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_376_);
v___x_391_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
v___x_392_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_377_);
v___x_393_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
v___x_394_ = lean_unsigned_to_nat(8u);
v___x_395_ = lean_mk_empty_array_with_capacity(v___x_394_);
v___x_396_ = lean_array_push(v___x_395_, v___x_379_);
v___x_397_ = lean_array_push(v___x_396_, v___x_381_);
v___x_398_ = lean_array_push(v___x_397_, v___x_383_);
v___x_399_ = lean_array_push(v___x_398_, v___x_385_);
v___x_400_ = lean_array_push(v___x_399_, v___x_387_);
v___x_401_ = lean_array_push(v___x_400_, v___x_389_);
v___x_402_ = lean_array_push(v___x_401_, v___x_391_);
v___x_403_ = lean_array_push(v___x_402_, v___x_393_);
v___x_404_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0(lean_object* v___x_411_, lean_object* v_x_412_){
_start:
{
if (lean_obj_tag(v_x_412_) == 4)
{
lean_object* v_elems_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_530_; 
v_elems_413_ = lean_ctor_get(v_x_412_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_412_);
if (v_isSharedCheck_530_ == 0)
{
v___x_415_ = v_x_412_;
v_isShared_416_ = v_isSharedCheck_530_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_elems_413_);
lean_dec(v_x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_530_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_417_ = lean_array_get_size(v_elems_413_);
v___x_418_ = lean_unsigned_to_nat(8u);
v___x_419_ = lean_nat_dec_eq(v___x_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
lean_dec_ref(v_elems_413_);
v___x_420_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_421_ = l_Nat_reprFast(v___x_417_);
v___x_422_ = lean_string_append(v___x_420_, v___x_421_);
lean_dec_ref(v___x_421_);
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 0);
lean_ctor_set(v___x_415_, 0, v___x_422_);
v___x_424_ = v___x_415_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_del_object(v___x_415_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_array_get_borrowed(v___x_411_, v_elems_413_, v___x_426_);
lean_inc(v___x_427_);
v___x_428_ = l_Lean_Json_getNat_x3f(v___x_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_elems_413_);
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_a_437_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_428_, 1);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_array_get_borrowed(v___x_411_, v_elems_413_, v___x_438_);
lean_inc(v___x_439_);
v___x_440_ = l_Lean_Json_getNat_x3f(v___x_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_a_437_);
lean_dec_ref(v_elems_413_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_a_449_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_440_, 1);
v___x_450_ = lean_unsigned_to_nat(2u);
v___x_451_ = lean_array_get_borrowed(v___x_411_, v_elems_413_, v___x_450_);
lean_inc(v___x_451_);
v___x_452_ = l_Lean_Json_getNat_x3f(v___x_451_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_a_449_);
lean_dec(v_a_437_);
lean_dec_ref(v_elems_413_);
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_a_461_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_452_, 1);
v___x_462_ = lean_unsigned_to_nat(3u);
v___x_463_ = lean_array_get_borrowed(v___x_411_, v_elems_413_, v___x_462_);
lean_inc(v___x_463_);
v___x_464_ = l_Lean_Json_getNat_x3f(v___x_463_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_a_461_);
lean_dec(v_a_449_);
lean_dec(v_a_437_);
lean_dec_ref(v_elems_413_);
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_a_473_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_464_, 1);
v___x_474_ = lean_unsigned_to_nat(4u);
v___x_475_ = lean_array_get_borrowed(v___x_411_, v_elems_413_, v___x_474_);
lean_inc(v___x_475_);
v___x_476_ = l_Lean_Json_getNat_x3f(v___x_475_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec(v_a_473_);
lean_dec(v_a_461_);
lean_dec(v_a_449_);
lean_dec(v_a_437_);
lean_dec_ref(v_elems_413_);
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_a_485_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_476_, 1);
v___x_486_ = lean_unsigned_to_nat(5u);
v___x_487_ = lean_array_get_borrowed(v___x_411_, v_elems_413_, v___x_486_);
lean_inc(v___x_487_);
v___x_488_ = l_Lean_Json_getNat_x3f(v___x_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_a_485_);
lean_dec(v_a_473_);
lean_dec(v_a_461_);
lean_dec(v_a_449_);
lean_dec(v_a_437_);
lean_dec_ref(v_elems_413_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_a_497_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_488_, 1);
v___x_498_ = lean_unsigned_to_nat(6u);
v___x_499_ = lean_array_get_borrowed(v___x_411_, v_elems_413_, v___x_498_);
lean_inc(v___x_499_);
v___x_500_ = l_Lean_Json_getNat_x3f(v___x_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_a_497_);
lean_dec(v_a_485_);
lean_dec(v_a_473_);
lean_dec(v_a_461_);
lean_dec(v_a_449_);
lean_dec(v_a_437_);
lean_dec_ref(v_elems_413_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_a_509_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_500_, 1);
v___x_510_ = lean_unsigned_to_nat(7u);
v___x_511_ = lean_array_get(v___x_411_, v_elems_413_, v___x_510_);
lean_dec_ref(v_elems_413_);
v___x_512_ = l_Lean_Json_getNat_x3f(v___x_511_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_a_509_);
lean_dec(v_a_497_);
lean_dec(v_a_485_);
lean_dec(v_a_473_);
lean_dec(v_a_461_);
lean_dec(v_a_449_);
lean_dec(v_a_437_);
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_529_; 
v_a_521_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_529_ == 0)
{
v___x_523_ = v___x_512_;
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_512_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_525_, 0, v_a_437_);
lean_ctor_set(v___x_525_, 1, v_a_449_);
lean_ctor_set(v___x_525_, 2, v_a_461_);
lean_ctor_set(v___x_525_, 3, v_a_473_);
lean_ctor_set(v___x_525_, 4, v_a_485_);
lean_ctor_set(v___x_525_, 5, v_a_497_);
lean_ctor_set(v___x_525_, 6, v_a_509_);
lean_ctor_set(v___x_525_, 7, v_a_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_525_);
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
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
else
{
lean_object* v___x_531_; 
lean_dec(v_x_412_);
v___x_531_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__2));
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0___boxed(lean_object* v___x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Lsp_instFromJsonDeclInfo___lam__0(v___x_532_, v_x_533_);
lean_dec(v___x_532_);
return v_res_534_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls___aux__1(void){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_box(1);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls(void){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_box(1);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0(lean_object* v_f_540_, lean_object* v_a_541_, lean_object* v_b_542_, lean_object* v_c_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_a_541_);
lean_ctor_set(v___x_544_, 1, v_b_542_);
v___x_545_ = lean_apply_2(v_f_540_, v___x_544_, v_c_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg(lean_object* v_m_565_, lean_object* v_init_566_, lean_object* v_f_567_){
_start:
{
lean_object* v___f_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_a_571_; 
v___f_568_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_568_, 0, v_f_567_);
v___x_569_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_570_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_569_, v___f_568_, v_init_566_, v_m_565_);
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec(v___x_570_);
return v_a_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1(lean_object* v_00_u03b2_572_, lean_object* v_m_573_, lean_object* v_init_574_, lean_object* v_f_575_){
_start:
{
lean_object* v___f_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_a_579_; 
v___f_576_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_576_, 0, v_f_575_);
v___x_577_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_578_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_577_, v___f_576_, v_init_574_, v_m_573_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec(v___x_578_);
return v_a_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(lean_object* v___y_580_, lean_object* v_init_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v_k_583_; lean_object* v_v_584_; lean_object* v_l_585_; lean_object* v_r_586_; lean_object* v___x_587_; 
v_k_583_ = lean_ctor_get(v_x_582_, 1);
v_v_584_ = lean_ctor_get(v_x_582_, 2);
v_l_585_ = lean_ctor_get(v_x_582_, 3);
v_r_586_ = lean_ctor_get(v_x_582_, 4);
lean_inc_ref(v___y_580_);
v___x_587_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_580_, v_init_581_, v_l_585_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_dec_ref(v___y_580_);
return v___x_587_;
}
else
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
lean_inc(v_v_584_);
lean_inc(v_k_583_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_k_583_);
lean_ctor_set(v___x_589_, 1, v_v_584_);
lean_inc_ref(v___y_580_);
v___x_590_ = lean_apply_2(v___y_580_, v___x_589_, v_a_588_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_dec_ref(v___y_580_);
return v___x_590_;
}
else
{
lean_object* v_a_591_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v_init_581_ = v_a_591_;
v_x_582_ = v_r_586_;
goto _start;
}
}
}
else
{
lean_object* v___x_593_; 
lean_dec_ref(v___y_580_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v_init_581_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg___boxed(lean_object* v___y_594_, lean_object* v_init_595_, lean_object* v_x_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_594_, v_init_595_, v_x_596_);
lean_dec(v_x_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_602_; lean_object* v_a_603_; 
v___x_602_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_601_, v___y_600_, v___y_599_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___x_602_);
return v_a_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0___boxed(lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_605_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v_init_613_, lean_object* v_x_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_612_, v_init_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___boxed(lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v_init_618_, lean_object* v_x_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(v___y_616_, v___y_617_, v_init_618_, v_x_619_);
lean_dec(v_x_619_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__0(lean_object* v_x_621_){
_start:
{
lean_object* v_snd_622_; lean_object* v_fst_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_665_; 
v_snd_622_ = lean_ctor_get(v_x_621_, 1);
v_fst_623_ = lean_ctor_get(v_x_621_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_665_ == 0)
{
v___x_625_ = v_x_621_;
v_isShared_626_ = v_isSharedCheck_665_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_snd_622_);
lean_inc(v_fst_623_);
lean_dec(v_x_621_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_665_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_rangeStartPosLine_627_; lean_object* v_rangeStartPosCharacter_628_; lean_object* v_rangeEndPosLine_629_; lean_object* v_rangeEndPosCharacter_630_; lean_object* v_selectionRangeStartPosLine_631_; lean_object* v_selectionRangeStartPosCharacter_632_; lean_object* v_selectionRangeEndPosLine_633_; lean_object* v_selectionRangeEndPosCharacter_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v_rangeStartPosLine_627_ = lean_ctor_get(v_snd_622_, 0);
lean_inc(v_rangeStartPosLine_627_);
v_rangeStartPosCharacter_628_ = lean_ctor_get(v_snd_622_, 1);
lean_inc(v_rangeStartPosCharacter_628_);
v_rangeEndPosLine_629_ = lean_ctor_get(v_snd_622_, 2);
lean_inc(v_rangeEndPosLine_629_);
v_rangeEndPosCharacter_630_ = lean_ctor_get(v_snd_622_, 3);
lean_inc(v_rangeEndPosCharacter_630_);
v_selectionRangeStartPosLine_631_ = lean_ctor_get(v_snd_622_, 4);
lean_inc(v_selectionRangeStartPosLine_631_);
v_selectionRangeStartPosCharacter_632_ = lean_ctor_get(v_snd_622_, 5);
lean_inc(v_selectionRangeStartPosCharacter_632_);
v_selectionRangeEndPosLine_633_ = lean_ctor_get(v_snd_622_, 6);
lean_inc(v_selectionRangeEndPosLine_633_);
v_selectionRangeEndPosCharacter_634_ = lean_ctor_get(v_snd_622_, 7);
lean_inc(v_selectionRangeEndPosCharacter_634_);
lean_dec(v_snd_622_);
v___x_635_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_627_);
v___x_636_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
v___x_637_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_628_);
v___x_638_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
v___x_639_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_629_);
v___x_640_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_630_);
v___x_642_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
v___x_643_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_631_);
v___x_644_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
v___x_645_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_632_);
v___x_646_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___x_647_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_633_);
v___x_648_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
v___x_649_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_634_);
v___x_650_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = lean_unsigned_to_nat(8u);
v___x_652_ = lean_mk_empty_array_with_capacity(v___x_651_);
v___x_653_ = lean_array_push(v___x_652_, v___x_636_);
v___x_654_ = lean_array_push(v___x_653_, v___x_638_);
v___x_655_ = lean_array_push(v___x_654_, v___x_640_);
v___x_656_ = lean_array_push(v___x_655_, v___x_642_);
v___x_657_ = lean_array_push(v___x_656_, v___x_644_);
v___x_658_ = lean_array_push(v___x_657_, v___x_646_);
v___x_659_ = lean_array_push(v___x_658_, v___x_648_);
v___x_660_ = lean_array_push(v___x_659_, v___x_650_);
v___x_661_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_661_);
v___x_663_ = v___x_625_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_fst_623_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__1(lean_object* v_x1_666_, lean_object* v_x2_667_, lean_object* v_x3_668_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_x1_666_);
lean_ctor_set(v___x_669_, 1, v_x2_667_);
v___x_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v_x3_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__2(lean_object* v___f_671_, lean_object* v___f_672_, lean_object* v_m_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_674_ = lean_box(0);
v___x_675_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_676_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_675_, v___f_671_, v___x_674_, v_m_673_);
v___x_677_ = l_List_mapTR_loop___redArg(v___f_672_, v___x_676_, v___x_674_);
v___x_678_ = l_Lean_Json_mkObj(v___x_677_);
lean_dec(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0(lean_object* v___x_687_, lean_object* v_m_688_, lean_object* v_k_689_, lean_object* v_v_690_){
_start:
{
if (lean_obj_tag(v_v_690_) == 4)
{
lean_object* v_elems_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_810_; 
v_elems_691_ = lean_ctor_get(v_v_690_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_v_690_);
if (v_isSharedCheck_810_ == 0)
{
v___x_693_ = v_v_690_;
v_isShared_694_ = v_isSharedCheck_810_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_elems_691_);
lean_dec(v_v_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_810_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_695_ = lean_array_get_size(v_elems_691_);
v___x_696_ = lean_unsigned_to_nat(8u);
v___x_697_ = lean_nat_dec_eq(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec_ref(v_elems_691_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v___x_698_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_699_ = l_Nat_reprFast(v___x_695_);
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
lean_dec_ref(v___x_699_);
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 0);
lean_ctor_set(v___x_693_, 0, v___x_700_);
v___x_702_ = v___x_693_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_del_object(v___x_693_);
v___x_704_ = lean_box(0);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_array_get_borrowed(v___x_704_, v_elems_691_, v___x_705_);
lean_inc(v___x_706_);
v___x_707_ = l_Lean_Json_getNat_x3f(v___x_706_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_elems_691_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_a_716_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_707_, 1);
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = lean_array_get_borrowed(v___x_704_, v_elems_691_, v___x_717_);
lean_inc(v___x_718_);
v___x_719_ = l_Lean_Json_getNat_x3f(v___x_718_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_a_716_);
lean_dec_ref(v_elems_691_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_a_728_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_719_, 1);
v___x_729_ = lean_unsigned_to_nat(2u);
v___x_730_ = lean_array_get_borrowed(v___x_704_, v_elems_691_, v___x_729_);
lean_inc(v___x_730_);
v___x_731_ = l_Lean_Json_getNat_x3f(v___x_730_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_a_728_);
lean_dec(v_a_716_);
lean_dec_ref(v_elems_691_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_740_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_731_, 1);
v___x_741_ = lean_unsigned_to_nat(3u);
v___x_742_ = lean_array_get_borrowed(v___x_704_, v_elems_691_, v___x_741_);
lean_inc(v___x_742_);
v___x_743_ = l_Lean_Json_getNat_x3f(v___x_742_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_740_);
lean_dec(v_a_728_);
lean_dec(v_a_716_);
lean_dec_ref(v_elems_691_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_a_752_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_743_, 1);
v___x_753_ = lean_unsigned_to_nat(4u);
v___x_754_ = lean_array_get_borrowed(v___x_704_, v_elems_691_, v___x_753_);
lean_inc(v___x_754_);
v___x_755_ = l_Lean_Json_getNat_x3f(v___x_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_a_752_);
lean_dec(v_a_740_);
lean_dec(v_a_728_);
lean_dec(v_a_716_);
lean_dec_ref(v_elems_691_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_a_764_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_755_, 1);
v___x_765_ = lean_unsigned_to_nat(5u);
v___x_766_ = lean_array_get_borrowed(v___x_704_, v_elems_691_, v___x_765_);
lean_inc(v___x_766_);
v___x_767_ = l_Lean_Json_getNat_x3f(v___x_766_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_a_764_);
lean_dec(v_a_752_);
lean_dec(v_a_740_);
lean_dec(v_a_728_);
lean_dec(v_a_716_);
lean_dec_ref(v_elems_691_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_a_776_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_767_, 1);
v___x_777_ = lean_unsigned_to_nat(6u);
v___x_778_ = lean_array_get_borrowed(v___x_704_, v_elems_691_, v___x_777_);
lean_inc(v___x_778_);
v___x_779_ = l_Lean_Json_getNat_x3f(v___x_778_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v_a_776_);
lean_dec(v_a_764_);
lean_dec(v_a_752_);
lean_dec(v_a_740_);
lean_dec(v_a_728_);
lean_dec(v_a_716_);
lean_dec_ref(v_elems_691_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_a_788_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_779_, 1);
v___x_789_ = lean_unsigned_to_nat(7u);
v___x_790_ = lean_array_get(v___x_704_, v_elems_691_, v___x_789_);
lean_dec_ref(v_elems_691_);
v___x_791_ = l_Lean_Json_getNat_x3f(v___x_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_a_788_);
lean_dec(v_a_776_);
lean_dec(v_a_764_);
lean_dec(v_a_752_);
lean_dec(v_a_740_);
lean_dec(v_a_728_);
lean_dec(v_a_716_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_809_; 
v_a_800_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_809_ == 0)
{
v___x_802_ = v___x_791_;
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_791_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_804_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_804_, 0, v_a_716_);
lean_ctor_set(v___x_804_, 1, v_a_728_);
lean_ctor_set(v___x_804_, 2, v_a_740_);
lean_ctor_set(v___x_804_, 3, v_a_752_);
lean_ctor_set(v___x_804_, 4, v_a_764_);
lean_ctor_set(v___x_804_, 5, v_a_776_);
lean_ctor_set(v___x_804_, 6, v_a_788_);
lean_ctor_set(v___x_804_, 7, v_a_800_);
v___x_805_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_687_, v_k_689_, v___x_804_, v_m_688_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_805_);
v___x_807_ = v___x_802_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
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
else
{
lean_object* v___x_811_; 
lean_dec(v_v_690_);
lean_dec_ref(v_k_689_);
lean_dec(v_m_688_);
lean_dec_ref(v___x_687_);
v___x_811_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object* v___x_815_, lean_object* v_j_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Json_getObj_x3f(v_j_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref(v___x_815_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___f_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_a_826_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_817_, 1);
v___f_827_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__1));
v___x_828_ = lean_box(1);
v___x_829_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_815_, v___f_827_, v___x_828_, v_a_826_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object* v_range_857_, lean_object* v_parentDecl_x3f_858_){
_start:
{
if (lean_obj_tag(v_parentDecl_x3f_858_) == 0)
{
lean_object* v_start_859_; lean_object* v_end_860_; lean_object* v_line_861_; lean_object* v_character_862_; lean_object* v_line_863_; lean_object* v_character_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_start_859_ = lean_ctor_get(v_range_857_, 0);
v_end_860_ = lean_ctor_get(v_range_857_, 1);
v_line_861_ = lean_ctor_get(v_start_859_, 0);
v_character_862_ = lean_ctor_get(v_start_859_, 1);
v_line_863_ = lean_ctor_get(v_end_860_, 0);
v_character_864_ = lean_ctor_get(v_end_860_, 1);
v___x_865_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
lean_inc(v_character_864_);
lean_inc(v_line_863_);
lean_inc(v_character_862_);
lean_inc(v_line_861_);
v___x_866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_866_, 0, v_line_861_);
lean_ctor_set(v___x_866_, 1, v_character_862_);
lean_ctor_set(v___x_866_, 2, v_line_863_);
lean_ctor_set(v___x_866_, 3, v_character_864_);
lean_ctor_set(v___x_866_, 4, v___x_865_);
return v___x_866_;
}
else
{
lean_object* v_start_867_; lean_object* v_end_868_; lean_object* v_line_869_; lean_object* v_character_870_; lean_object* v_line_871_; lean_object* v_character_872_; lean_object* v_val_873_; lean_object* v___x_874_; 
v_start_867_ = lean_ctor_get(v_range_857_, 0);
v_end_868_ = lean_ctor_get(v_range_857_, 1);
v_line_869_ = lean_ctor_get(v_start_867_, 0);
v_character_870_ = lean_ctor_get(v_start_867_, 1);
v_line_871_ = lean_ctor_get(v_end_868_, 0);
v_character_872_ = lean_ctor_get(v_end_868_, 1);
v_val_873_ = lean_ctor_get(v_parentDecl_x3f_858_, 0);
lean_inc(v_val_873_);
lean_inc(v_character_872_);
lean_inc(v_line_871_);
lean_inc(v_character_870_);
lean_inc(v_line_869_);
v___x_874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_874_, 0, v_line_869_);
lean_ctor_set(v___x_874_, 1, v_character_870_);
lean_ctor_set(v___x_874_, 2, v_line_871_);
lean_ctor_set(v___x_874_, 3, v_character_872_);
lean_ctor_set(v___x_874_, 4, v_val_873_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk___boxed(lean_object* v_range_875_, lean_object* v_parentDecl_x3f_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_875_, v_parentDecl_x3f_876_);
lean_dec(v_parentDecl_x3f_876_);
lean_dec_ref(v_range_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object* v_l_878_){
_start:
{
lean_object* v_startPosLine_879_; lean_object* v_startPosCharacter_880_; lean_object* v_endPosLine_881_; lean_object* v_endPosCharacter_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_startPosLine_879_ = lean_ctor_get(v_l_878_, 0);
v_startPosCharacter_880_ = lean_ctor_get(v_l_878_, 1);
v_endPosLine_881_ = lean_ctor_get(v_l_878_, 2);
v_endPosCharacter_882_ = lean_ctor_get(v_l_878_, 3);
lean_inc(v_startPosCharacter_880_);
lean_inc(v_startPosLine_879_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v_startPosLine_879_);
lean_ctor_set(v___x_883_, 1, v_startPosCharacter_880_);
lean_inc(v_endPosCharacter_882_);
lean_inc(v_endPosLine_881_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_endPosLine_881_);
lean_ctor_set(v___x_884_, 1, v_endPosCharacter_882_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range___boxed(lean_object* v_l_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Lsp_RefInfo_Location_range(v_l_886_);
lean_dec_ref(v_l_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object* v_l_888_){
_start:
{
lean_object* v_parentDecl_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v_parentDecl_889_ = lean_ctor_get(v_l_888_, 4);
v___x_890_ = lean_string_utf8_byte_size(v_parentDecl_889_);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = lean_nat_dec_eq(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
lean_inc_ref(v_parentDecl_889_);
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v_parentDecl_889_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = lean_box(0);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f___boxed(lean_object* v_l_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_895_);
lean_dec_ref(v_l_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object* v_n_897_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = l_Lean_JsonNumber_fromNat(v_n_897_);
v___x_899_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object* v___f_900_, lean_object* v_l_901_){
_start:
{
lean_object* v_startPosLine_902_; lean_object* v_startPosCharacter_903_; lean_object* v_endPosLine_904_; lean_object* v_endPosCharacter_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v_range_911_; lean_object* v___x_912_; 
v_startPosLine_902_ = lean_ctor_get(v_l_901_, 0);
v_startPosCharacter_903_ = lean_ctor_get(v_l_901_, 1);
v_endPosLine_904_ = lean_ctor_get(v_l_901_, 2);
v_endPosCharacter_905_ = lean_ctor_get(v_l_901_, 3);
v___x_906_ = lean_box(0);
lean_inc(v_endPosCharacter_905_);
v___x_907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_907_, 0, v_endPosCharacter_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
lean_inc(v_endPosLine_904_);
v___x_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_908_, 0, v_endPosLine_904_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
lean_inc(v_startPosCharacter_903_);
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v_startPosCharacter_903_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_inc(v_startPosLine_902_);
v___x_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_910_, 0, v_startPosLine_902_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v_range_911_ = l_List_mapTR_loop___redArg(v___f_900_, v___x_910_, v___x_906_);
v___x_912_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_901_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; 
v___x_913_ = l_List_appendTR___redArg(v_range_911_, v___x_906_);
return v___x_913_;
}
else
{
lean_object* v_val_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_923_; 
v_val_914_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_923_ == 0)
{
v___x_916_ = v___x_912_;
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_val_914_);
lean_dec(v___x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_923_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set_tag(v___x_916_, 3);
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_val_914_);
v___x_919_ = v_reuseFailAlloc_922_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_906_);
v___x_921_ = l_List_appendTR___redArg(v_range_911_, v___x_920_);
return v___x_921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed(lean_object* v___f_924_, lean_object* v_l_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Lsp_instToJsonRefInfo___lam__1(v___f_924_, v_l_925_);
lean_dec_ref(v_l_925_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object* v_locationToList_927_, lean_object* v_x_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_apply_1(v_locationToList_927_, v_x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object* v___x_932_, lean_object* v___f_933_, lean_object* v_locationToList_934_, lean_object* v_i_935_){
_start:
{
lean_object* v_definition_x3f_936_; lean_object* v_usages_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_969_; 
v_definition_x3f_936_ = lean_ctor_get(v_i_935_, 0);
v_usages_937_ = lean_ctor_get(v_i_935_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_i_935_);
if (v_isSharedCheck_969_ == 0)
{
v___x_939_ = v_i_935_;
v_isShared_940_ = v_isSharedCheck_969_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_usages_937_);
lean_inc(v_definition_x3f_936_);
lean_dec(v_i_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_969_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___y_943_; 
v___x_941_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_936_) == 0)
{
lean_object* v___x_959_; 
lean_dec_ref(v_locationToList_934_);
v___x_959_ = lean_box(0);
v___y_943_ = v___x_959_;
goto v___jp_942_;
}
else
{
lean_object* v_val_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_val_960_ = lean_ctor_get(v_definition_x3f_936_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_definition_x3f_936_);
if (v_isSharedCheck_968_ == 0)
{
v___x_962_ = v_definition_x3f_936_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_val_960_);
lean_dec(v_definition_x3f_936_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = lean_apply_1(v_locationToList_934_, v_val_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
v___y_943_ = v___x_966_;
goto v___jp_942_;
}
}
}
v___jp_942_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
lean_inc_ref(v___x_932_);
v___x_944_ = l_Lean_Option_toJson___redArg(v___x_932_, v___y_943_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_944_);
lean_ctor_set(v___x_939_, 0, v___x_941_);
v___x_946_ = v___x_939_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_944_);
v___x_946_ = v_reuseFailAlloc_958_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; size_t v_sz_949_; size_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_947_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_948_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_949_ = lean_array_size(v_usages_937_);
v___x_950_ = ((size_t)0ULL);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_948_, v___f_933_, v_sz_949_, v___x_950_, v_usages_937_);
v___x_952_ = l_Lean_Array_toJson___redArg(v___x_932_, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_947_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_box(0);
v___x_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_946_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_Json_mkObj(v___x_956_);
lean_dec_ref_known(v___x_956_, 2);
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object* v_a_984_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_1066_; 
v___x_985_ = lean_array_get_size(v_a_984_);
v___x_986_ = lean_unsigned_to_nat(4u);
v___x_1066_ = lean_nat_dec_eq(v___x_985_, v___x_986_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_unsigned_to_nat(5u);
v___x_1068_ = lean_nat_dec_eq(v___x_985_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1069_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1070_ = l_Nat_reprFast(v___x_985_);
v___x_1071_ = lean_string_append(v___x_1069_, v___x_1070_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
else
{
goto v___jp_987_;
}
}
else
{
goto v___jp_987_;
}
v___jp_987_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_array_fget_borrowed(v_a_984_, v___x_988_);
lean_inc(v___x_989_);
v___x_990_ = l_Lean_Json_getNat_x3f(v___x_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_999_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_990_, 1);
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_array_fget_borrowed(v_a_984_, v___x_1000_);
lean_inc(v___x_1001_);
v___x_1002_ = l_Lean_Json_getNat_x3f(v___x_1001_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_a_999_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_a_1011_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1012_ = lean_unsigned_to_nat(2u);
v___x_1013_ = lean_array_fget_borrowed(v_a_984_, v___x_1012_);
lean_inc(v___x_1013_);
v___x_1014_ = l_Lean_Json_getNat_x3f(v___x_1013_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_a_1011_);
lean_dec(v_a_999_);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_a_1023_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1024_ = lean_unsigned_to_nat(3u);
v___x_1025_ = lean_array_fget_borrowed(v_a_984_, v___x_1024_);
lean_inc(v___x_1025_);
v___x_1026_ = l_Lean_Json_getNat_x3f(v___x_1025_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_a_1023_);
lean_dec(v_a_1011_);
lean_dec(v_a_999_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1065_; 
v_a_1035_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1037_ = v___x_1026_;
v_isShared_1038_ = v_isSharedCheck_1065_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1026_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1065_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(5u);
v___x_1040_ = lean_nat_dec_eq(v___x_985_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1041_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1042_, 0, v_a_999_);
lean_ctor_set(v___x_1042_, 1, v_a_1011_);
lean_ctor_set(v___x_1042_, 2, v_a_1023_);
lean_ctor_set(v___x_1042_, 3, v_a_1035_);
lean_ctor_set(v___x_1042_, 4, v___x_1041_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1042_);
v___x_1044_ = v___x_1037_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_del_object(v___x_1037_);
v___x_1046_ = lean_array_fget_borrowed(v_a_984_, v___x_986_);
lean_inc(v___x_1046_);
v___x_1047_ = l_Lean_Json_getStr_x3f(v___x_1046_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_a_1035_);
lean_dec(v_a_1023_);
lean_dec(v_a_1011_);
lean_dec(v_a_999_);
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1064_; 
v_a_1056_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1058_ = v___x_1047_;
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1047_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1060_, 0, v_a_999_);
lean_ctor_set(v___x_1060_, 1, v_a_1011_);
lean_ctor_set(v___x_1060_, 2, v_a_1023_);
lean_ctor_set(v___x_1060_, 3, v_a_1035_);
lean_ctor_set(v___x_1060_, 4, v_a_1056_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Lsp_instFromJsonRefInfo___lam__0(v_a_1073_);
lean_dec_ref(v_a_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v_toLocation_1078_, lean_object* v_j_1079_){
_start:
{
lean_object* v_definition_x3f_1081_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_j_1079_);
v___x_1114_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1079_, v___x_1075_, v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v_j_1079_);
lean_dec_ref(v_toLocation_1078_);
lean_dec_ref(v___x_1077_);
lean_dec_ref(v___x_1076_);
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
else
{
lean_object* v_a_1123_; 
v_a_1123_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1114_, 1);
if (lean_obj_tag(v_a_1123_) == 0)
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_box(0);
v_definition_x3f_1081_ = v___x_1124_;
goto v___jp_1080_;
}
else
{
lean_object* v_val_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1142_; 
v_val_1125_ = lean_ctor_get(v_a_1123_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_a_1123_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1127_ = v_a_1123_;
v_isShared_1128_ = v_isSharedCheck_1142_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_val_1125_);
lean_dec(v_a_1123_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1142_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; 
lean_inc_ref(v_toLocation_1078_);
v___x_1129_ = lean_apply_1(v_toLocation_1078_, v_val_1125_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_del_object(v___x_1127_);
lean_dec(v_j_1079_);
lean_dec_ref(v_toLocation_1078_);
lean_dec_ref(v___x_1077_);
lean_dec_ref(v___x_1076_);
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; 
v_a_1138_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1129_, 1);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v_a_1138_);
v___x_1140_ = v___x_1127_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
v_definition_x3f_1081_ = v___x_1140_;
goto v___jp_1080_;
}
}
}
}
}
v___jp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1083_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1079_, v___x_1076_, v___x_1082_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_definition_x3f_1081_);
lean_dec_ref(v_toLocation_1078_);
lean_dec_ref(v___x_1077_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
else
{
lean_object* v_a_1092_; size_t v_sz_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v_a_1092_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1083_, 1);
v_sz_1093_ = lean_array_size(v_a_1092_);
v___x_1094_ = ((size_t)0ULL);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1077_, v_toLocation_1078_, v_sz_1093_, v___x_1094_, v_a_1092_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_definition_x3f_1081_);
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1112_; 
v_a_1104_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1106_ = v___x_1095_;
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1095_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_definition_x3f_1081_);
lean_ctor_set(v___x_1108_, 1, v_a_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs___aux__1(void){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_box(1);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs(void){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_box(1);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1159_, lean_object* v_a_1160_, lean_object* v_b_1161_, lean_object* v_c_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_a_1160_);
lean_ctor_set(v___x_1163_, 1, v_b_1161_);
v___x_1164_ = lean_apply_2(v_f_1159_, v___x_1163_, v_c_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_1165_, lean_object* v_____do__lift_1166_){
_start:
{
lean_object* v_a_1167_; lean_object* v___x_1168_; 
v_a_1167_ = lean_ctor_get(v_____do__lift_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref(v_____do__lift_1166_);
v___x_1168_ = lean_apply_2(v_toPure_1165_, lean_box(0), v_a_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg(lean_object* v_inst_1169_, lean_object* v_m_1170_, lean_object* v_init_1171_, lean_object* v_f_1172_){
_start:
{
lean_object* v_toApplicative_1173_; lean_object* v_toBind_1174_; lean_object* v_toPure_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; 
v_toApplicative_1173_ = lean_ctor_get(v_inst_1169_, 0);
v_toBind_1174_ = lean_ctor_get(v_inst_1169_, 1);
lean_inc(v_toBind_1174_);
v_toPure_1175_ = lean_ctor_get(v_toApplicative_1173_, 1);
lean_inc(v_toPure_1175_);
v___f_1176_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1176_, 0, v_f_1172_);
v___x_1177_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1169_, v___f_1176_, v_init_1171_, v_m_1170_);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1178_, 0, v_toPure_1175_);
v___x_1179_ = lean_apply_4(v_toBind_1174_, lean_box(0), lean_box(0), v___x_1177_, v___f_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1(lean_object* v_m_1180_, lean_object* v_inst_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_m_1183_, lean_object* v_init_1184_, lean_object* v_f_1185_){
_start:
{
lean_object* v_toApplicative_1186_; lean_object* v_toBind_1187_; lean_object* v_toPure_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; 
v_toApplicative_1186_ = lean_ctor_get(v_inst_1181_, 0);
v_toBind_1187_ = lean_ctor_get(v_inst_1181_, 1);
lean_inc(v_toBind_1187_);
v_toPure_1188_ = lean_ctor_get(v_toApplicative_1186_, 1);
lean_inc(v_toPure_1188_);
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1189_, 0, v_f_1185_);
v___x_1190_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1181_, v___f_1189_, v_init_1184_, v_m_1183_);
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1191_, 0, v_toPure_1188_);
v___x_1192_ = lean_apply_4(v_toBind_1187_, lean_box(0), lean_box(0), v___x_1190_, v___f_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object* v_inst_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1194_, 0, lean_box(0));
lean_closure_set(v___x_1194_, 1, v_inst_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object* v_m_1195_, lean_object* v_inst_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1197_, 0, lean_box(0));
lean_closure_set(v___x_1197_, 1, v_inst_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* v___f_1198_, lean_object* v_x_1199_){
_start:
{
lean_object* v_startPosLine_1200_; lean_object* v_startPosCharacter_1201_; lean_object* v_endPosLine_1202_; lean_object* v_endPosCharacter_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_range_1209_; lean_object* v___x_1210_; 
v_startPosLine_1200_ = lean_ctor_get(v_x_1199_, 0);
v_startPosCharacter_1201_ = lean_ctor_get(v_x_1199_, 1);
v_endPosLine_1202_ = lean_ctor_get(v_x_1199_, 2);
v_endPosCharacter_1203_ = lean_ctor_get(v_x_1199_, 3);
v___x_1204_ = lean_box(0);
lean_inc(v_endPosCharacter_1203_);
v___x_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1205_, 0, v_endPosCharacter_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
lean_inc(v_endPosLine_1202_);
v___x_1206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_endPosLine_1202_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
lean_inc(v_startPosCharacter_1201_);
v___x_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_startPosCharacter_1201_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
lean_inc(v_startPosLine_1200_);
v___x_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_startPosLine_1200_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v_range_1209_ = l_List_mapTR_loop___redArg(v___f_1198_, v___x_1208_, v___x_1204_);
v___x_1210_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_x_1199_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1211_; 
v___x_1211_ = l_List_appendTR___redArg(v_range_1209_, v___x_1204_);
return v___x_1211_;
}
else
{
lean_object* v_val_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1221_; 
v_val_1212_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1214_ = v___x_1210_;
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_val_1212_);
lean_dec(v___x_1210_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set_tag(v___x_1214_, 3);
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_val_1212_);
v___x_1217_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___x_1204_);
v___x_1219_ = l_List_appendTR___redArg(v_range_1209_, v___x_1218_);
return v___x_1219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object* v___f_1222_, lean_object* v_x_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Lsp_instToJsonModuleRefs___lam__1(v___f_1222_, v_x_1223_);
lean_dec_ref(v_x_1223_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* v___f_1225_, lean_object* v___f_1226_, lean_object* v_a_1227_, lean_object* v_b_1228_, lean_object* v_c_1229_){
_start:
{
lean_object* v_definition_x3f_1230_; lean_object* v_usages_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1285_; 
v_definition_x3f_1230_ = lean_ctor_get(v_b_1228_, 0);
v_usages_1231_ = lean_ctor_get(v_b_1228_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_b_1228_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1233_ = v_b_1228_;
v_isShared_1234_ = v_isSharedCheck_1285_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_usages_1231_);
lean_inc(v_definition_x3f_1230_);
lean_dec(v_b_1228_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1285_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___y_1240_; lean_object* v___y_1259_; 
v___x_1235_ = l_Lean_Lsp_RefIdent_toJson(v_a_1227_);
v___x_1236_ = lean_array_push(v_c_1229_, v___x_1235_);
v___x_1237_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___closed__4));
v___x_1238_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1230_) == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref(v___f_1226_);
v___x_1261_ = lean_box(0);
v___y_1240_ = v___x_1261_;
goto v___jp_1239_;
}
else
{
lean_object* v_val_1262_; lean_object* v_startPosLine_1263_; lean_object* v_startPosCharacter_1264_; lean_object* v_endPosLine_1265_; lean_object* v_endPosCharacter_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_range_1272_; lean_object* v___x_1273_; 
v_val_1262_ = lean_ctor_get(v_definition_x3f_1230_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v_definition_x3f_1230_, 1);
v_startPosLine_1263_ = lean_ctor_get(v_val_1262_, 0);
v_startPosCharacter_1264_ = lean_ctor_get(v_val_1262_, 1);
v_endPosLine_1265_ = lean_ctor_get(v_val_1262_, 2);
v_endPosCharacter_1266_ = lean_ctor_get(v_val_1262_, 3);
v___x_1267_ = lean_box(0);
lean_inc(v_endPosCharacter_1266_);
v___x_1268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1268_, 0, v_endPosCharacter_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
lean_inc(v_endPosLine_1265_);
v___x_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_endPosLine_1265_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
lean_inc(v_startPosCharacter_1264_);
v___x_1270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_startPosCharacter_1264_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
lean_inc(v_startPosLine_1263_);
v___x_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_startPosLine_1263_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v_range_1272_ = l_List_mapTR_loop___redArg(v___f_1226_, v___x_1271_, v___x_1267_);
v___x_1273_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_1262_);
lean_dec(v_val_1262_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = l_List_appendTR___redArg(v_range_1272_, v___x_1267_);
v___y_1259_ = v___x_1274_;
goto v___jp_1258_;
}
else
{
lean_object* v_val_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1284_; 
v_val_1275_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1277_ = v___x_1273_;
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_val_1275_);
lean_dec(v___x_1273_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 3);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_val_1275_);
v___x_1280_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1267_);
v___x_1282_ = l_List_appendTR___redArg(v_range_1272_, v___x_1281_);
v___y_1259_ = v___x_1282_;
goto v___jp_1258_;
}
}
}
}
v___jp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = l_Lean_Option_toJson___redArg(v___x_1237_, v___y_1240_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1241_);
lean_ctor_set(v___x_1233_, 0, v___x_1238_);
v___x_1243_ = v___x_1233_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; size_t v_sz_1246_; size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1244_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1245_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1246_ = lean_array_size(v_usages_1231_);
v___x_1247_ = ((size_t)0ULL);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1245_, v___f_1225_, v_sz_1246_, v___x_1247_, v_usages_1231_);
v___x_1249_ = l_Lean_Array_toJson___redArg(v___x_1237_, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1244_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1243_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = l_Lean_Json_mkObj(v___x_1253_);
lean_dec_ref_known(v___x_1253_, 2);
v___x_1255_ = lean_array_push(v___x_1236_, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
v___jp_1258_:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___y_1259_);
v___y_1240_ = v___x_1260_;
goto v___jp_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0___boxed(lean_object* v___f_1286_, lean_object* v___f_1287_, lean_object* v_a_1288_, lean_object* v_b_1289_, lean_object* v_c_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Lsp_instToJsonModuleRefs___lam__0(v___f_1286_, v___f_1287_, v_a_1288_, v_b_1289_, v_c_1290_);
lean_dec_ref(v_a_1288_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object* v___x_1294_, lean_object* v___f_1295_, lean_object* v_m_1296_){
_start:
{
lean_object* v_a_1297_; lean_object* v___x_1298_; lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_a_1297_ = ((lean_object*)(l_Lean_Lsp_instToJsonModuleRefs___lam__2___closed__0));
v___x_1298_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1294_, v___f_1295_, v_a_1297_, v_m_1296_);
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set_tag(v___x_1301_, 4);
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object* v___x_1316_, lean_object* v___x_1317_, lean_object* v_a_1318_, lean_object* v___x_1319_, lean_object* v_toLocation_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v_next_1323_, lean_object* v_acc_1324_, lean_object* v_h_1325_, lean_object* v_G_1326_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_nat_dec_lt(v_next_1323_, v___x_1316_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_dec_ref(v_G_1326_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_acc_1324_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = lean_nat_mul(v___x_1317_, v_next_1323_);
v___x_1330_ = lean_array_fget_borrowed(v_a_1318_, v___x_1329_);
lean_inc(v___x_1330_);
v___x_1331_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v___x_1330_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec(v___x_1329_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_a_1340_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1331_, 1);
v___x_1341_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___closed__9));
v___x_1342_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__3));
v___x_1343_ = lean_nat_add(v___x_1329_, v___x_1319_);
lean_dec(v___x_1329_);
v___x_1344_ = lean_array_fget_borrowed(v_a_1318_, v___x_1343_);
lean_dec(v___x_1343_);
v___x_1345_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v___x_1344_);
v___x_1346_ = l_Lean_Json_getObjValAs_x3f___redArg(v___x_1344_, v___x_1342_, v___x_1345_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v_a_1340_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1467_; 
v_a_1355_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1357_ = v___x_1346_;
v_isShared_1358_ = v_isSharedCheck_1467_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1346_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1467_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v_definition_x3f_1361_; lean_object* v_a_1390_; 
v___x_1359_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__4));
if (lean_obj_tag(v_a_1355_) == 0)
{
lean_object* v___x_1392_; 
lean_del_object(v___x_1357_);
v___x_1392_ = lean_box(0);
v_definition_x3f_1361_ = v___x_1392_;
goto v___jp_1360_;
}
else
{
lean_object* v_val_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1458_; 
v_val_1393_ = lean_ctor_get(v_a_1355_, 0);
lean_inc(v_val_1393_);
lean_dec_ref_known(v_a_1355_, 1);
v___x_1394_ = lean_array_get_size(v_val_1393_);
v___x_1395_ = lean_unsigned_to_nat(4u);
v___x_1458_ = lean_nat_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = lean_unsigned_to_nat(5u);
v___x_1460_ = lean_nat_dec_eq(v___x_1394_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
lean_dec(v_val_1393_);
lean_dec(v_a_1340_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
v___x_1461_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1462_ = l_Nat_reprFast(v___x_1394_);
v___x_1463_ = lean_string_append(v___x_1461_, v___x_1462_);
lean_dec_ref(v___x_1462_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set_tag(v___x_1357_, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1463_);
v___x_1465_ = v___x_1357_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
else
{
lean_del_object(v___x_1357_);
goto v___jp_1396_;
}
}
else
{
lean_del_object(v___x_1357_);
goto v___jp_1396_;
}
v___jp_1396_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_array_fget_borrowed(v_val_1393_, v___x_1322_);
lean_inc(v___x_1397_);
v___x_1398_ = l_Lean_Json_getNat_x3f(v___x_1397_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_val_1393_);
lean_dec(v_a_1340_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_a_1407_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1398_, 1);
v___x_1408_ = lean_array_fget_borrowed(v_val_1393_, v___x_1319_);
lean_inc(v___x_1408_);
v___x_1409_ = l_Lean_Json_getNat_x3f(v___x_1408_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec(v_a_1407_);
lean_dec(v_val_1393_);
lean_dec(v_a_1340_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_a_1418_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1419_ = lean_array_fget_borrowed(v_val_1393_, v___x_1317_);
lean_inc(v___x_1419_);
v___x_1420_ = l_Lean_Json_getNat_x3f(v___x_1419_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_a_1418_);
lean_dec(v_a_1407_);
lean_dec(v_val_1393_);
lean_dec(v_a_1340_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_a_1429_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1430_ = lean_unsigned_to_nat(3u);
v___x_1431_ = lean_array_fget_borrowed(v_val_1393_, v___x_1430_);
lean_inc(v___x_1431_);
v___x_1432_ = l_Lean_Json_getNat_x3f(v___x_1431_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_a_1429_);
lean_dec(v_a_1418_);
lean_dec(v_a_1407_);
lean_dec(v_val_1393_);
lean_dec(v_a_1340_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_a_1441_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1442_ = lean_unsigned_to_nat(5u);
v___x_1443_ = lean_nat_dec_eq(v___x_1394_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec(v_val_1393_);
v___x_1444_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1445_, 0, v_a_1407_);
lean_ctor_set(v___x_1445_, 1, v_a_1418_);
lean_ctor_set(v___x_1445_, 2, v_a_1429_);
lean_ctor_set(v___x_1445_, 3, v_a_1441_);
lean_ctor_set(v___x_1445_, 4, v___x_1444_);
v_a_1390_ = v___x_1445_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_array_fget(v_val_1393_, v___x_1395_);
lean_dec(v_val_1393_);
v___x_1447_ = l_Lean_Json_getStr_x3f(v___x_1446_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_a_1441_);
lean_dec(v_a_1429_);
lean_dec(v_a_1418_);
lean_dec(v_a_1407_);
lean_dec(v_a_1340_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1457_, 0, v_a_1407_);
lean_ctor_set(v___x_1457_, 1, v_a_1418_);
lean_ctor_set(v___x_1457_, 2, v_a_1429_);
lean_ctor_set(v___x_1457_, 3, v_a_1441_);
lean_ctor_set(v___x_1457_, 4, v_a_1456_);
v_a_1390_ = v___x_1457_;
goto v___jp_1389_;
}
}
}
}
}
}
}
}
v___jp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
lean_inc(v___x_1344_);
v___x_1363_ = l_Lean_Json_getObjValAs_x3f___redArg(v___x_1344_, v___x_1359_, v___x_1362_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_definition_x3f_1361_);
lean_dec(v_a_1340_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_toLocation_1320_);
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
lean_object* v_a_1372_; size_t v_sz_1373_; size_t v___x_1374_; lean_object* v___x_1375_; 
v_a_1372_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1363_, 1);
v_sz_1373_ = lean_array_size(v_a_1372_);
v___x_1374_ = ((size_t)0ULL);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1341_, v_toLocation_1320_, v_sz_1373_, v___x_1374_, v_a_1372_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_definition_x3f_1361_);
lean_dec(v_a_1340_);
lean_dec_ref(v_G_1326_);
lean_dec(v_acc_1324_);
lean_dec_ref(v___x_1321_);
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
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_a_1384_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_definition_x3f_1361_);
lean_ctor_set(v___x_1385_, 1, v_a_1384_);
v___x_1386_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1321_, v_a_1340_, v___x_1385_, v_acc_1324_);
v___x_1387_ = lean_nat_add(v_next_1323_, v___x_1319_);
v___x_1388_ = lean_apply_4(v_G_1326_, v___x_1387_, v___x_1386_, lean_box(0), lean_box(0));
return v___x_1388_;
}
}
}
v___jp_1389_:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v_a_1390_);
v_definition_x3f_1361_ = v___x_1391_;
goto v___jp_1360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1___boxed(lean_object* v___x_1468_, lean_object* v___x_1469_, lean_object* v_a_1470_, lean_object* v___x_1471_, lean_object* v_toLocation_1472_, lean_object* v___x_1473_, lean_object* v___x_1474_, lean_object* v_next_1475_, lean_object* v_acc_1476_, lean_object* v_h_1477_, lean_object* v_G_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Lsp_instFromJsonModuleRefs___lam__1(v___x_1468_, v___x_1469_, v_a_1470_, v___x_1471_, v_toLocation_1472_, v___x_1473_, v___x_1474_, v_next_1475_, v_acc_1476_, v_h_1477_, v_G_1478_);
lean_dec(v_next_1475_);
lean_dec(v___x_1474_);
lean_dec(v___x_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v___x_1469_);
lean_dec(v___x_1468_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* v_toLocation_1483_, lean_object* v_j_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_Json_getArr_x3f(v_j_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_toLocation_1483_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v_a_1494_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1495_ = lean_array_get_size(v_a_1494_);
v___x_1496_ = lean_unsigned_to_nat(2u);
v___x_1497_ = lean_nat_mod(v___x_1495_, v___x_1496_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_nat_dec_eq(v___x_1497_, v___x_1498_);
lean_dec(v___x_1497_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; 
lean_dec(v_a_1494_);
lean_dec_ref(v_toLocation_1483_);
v___x_1500_ = ((lean_object*)(l_Lean_Lsp_instFromJsonModuleRefs___lam__0___closed__1));
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___f_1505_; lean_object* v___x_1506_; 
v___x_1501_ = ((lean_object*)(l_Lean_Lsp_instOrdRefIdent___closed__0));
v___x_1502_ = lean_box(1);
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_nat_shiftr(v___x_1495_, v___x_1503_);
v___f_1505_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonModuleRefs___lam__1___boxed), 11, 7);
lean_closure_set(v___f_1505_, 0, v___x_1504_);
lean_closure_set(v___f_1505_, 1, v___x_1496_);
lean_closure_set(v___f_1505_, 2, v_a_1494_);
lean_closure_set(v___f_1505_, 3, v___x_1503_);
lean_closure_set(v___f_1505_, 4, v_toLocation_1483_);
lean_closure_set(v___f_1505_, 5, v___x_1501_);
lean_closure_set(v___f_1505_, 6, v___x_1498_);
v___x_1506_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1505_, v___x_1498_, v___x_1502_, lean_box(0));
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object* v_j_1510_, lean_object* v_k_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = l_Lean_Json_getObjValD(v_j_1510_, v_k_1511_);
v___x_1513_ = l_Lean_Json_getNat_x3f(v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object* v_j_1514_, lean_object* v_k_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_j_1514_, v_k_1515_);
lean_dec_ref(v_k_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object* v_j_1517_, lean_object* v_k_1518_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = l_Lean_Json_getObjValD(v_j_1517_, v_k_1518_);
v___x_1520_ = l_Lean_Json_getBool_x3f(v___x_1519_);
lean_dec(v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object* v_j_1521_, lean_object* v_k_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_j_1521_, v_k_1522_);
lean_dec_ref(v_k_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1526_, size_t v_i_1527_, lean_object* v_bs_1528_){
_start:
{
uint8_t v___x_1531_; 
v___x_1531_ = lean_usize_dec_lt(v_i_1527_, v_sz_1526_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_bs_1528_);
return v___x_1532_;
}
else
{
lean_object* v_v_1533_; 
v_v_1533_ = lean_array_uget_borrowed(v_bs_1528_, v_i_1527_);
if (lean_obj_tag(v_v_1533_) == 4)
{
lean_object* v_elems_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_elems_1534_ = lean_ctor_get(v_v_1533_, 0);
v___x_1535_ = lean_array_get_size(v_elems_1534_);
v___x_1536_ = lean_unsigned_to_nat(4u);
v___x_1537_ = lean_nat_dec_eq(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_dec_ref(v_bs_1528_);
goto v___jp_1529_;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_array_fget_borrowed(v_elems_1534_, v___x_1538_);
lean_inc(v___x_1539_);
v___x_1540_ = l_Lean_Json_getStr_x3f(v___x_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_bs_1528_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_a_1549_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_array_fget_borrowed(v_elems_1534_, v___x_1550_);
v___x_1552_ = l_Lean_Json_getBool_x3f(v___x_1551_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1549_);
lean_dec_ref(v_bs_1528_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_a_1561_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1562_ = lean_unsigned_to_nat(2u);
v___x_1563_ = lean_array_fget_borrowed(v_elems_1534_, v___x_1562_);
v___x_1564_ = l_Lean_Json_getBool_x3f(v___x_1563_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_a_1561_);
lean_dec(v_a_1549_);
lean_dec_ref(v_bs_1528_);
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_a_1573_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1574_ = lean_unsigned_to_nat(3u);
v___x_1575_ = lean_array_fget_borrowed(v_elems_1534_, v___x_1574_);
v___x_1576_ = l_Lean_Json_getBool_x3f(v___x_1575_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_a_1573_);
lean_dec(v_a_1561_);
lean_dec(v_a_1549_);
lean_dec_ref(v_bs_1528_);
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v_bs_x27_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; uint8_t v___x_1589_; uint8_t v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v_a_1585_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1576_, 1);
v_bs_x27_1586_ = lean_array_uset(v_bs_1528_, v_i_1527_, v___x_1538_);
v___x_1587_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1587_, 0, v_a_1549_);
v___x_1588_ = lean_unbox(v_a_1561_);
lean_dec(v_a_1561_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*1, v___x_1588_);
v___x_1589_ = lean_unbox(v_a_1573_);
lean_dec(v_a_1573_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*1 + 1, v___x_1589_);
v___x_1590_ = lean_unbox(v_a_1585_);
lean_dec(v_a_1585_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*1 + 2, v___x_1590_);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_add(v_i_1527_, v___x_1591_);
v___x_1593_ = lean_array_uset(v_bs_x27_1586_, v_i_1527_, v___x_1587_);
v_i_1527_ = v___x_1592_;
v_bs_1528_ = v___x_1593_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1528_);
goto v___jp_1529_;
}
}
v___jp_1529_:
{
lean_object* v___x_1530_; 
v___x_1530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0));
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1595_, lean_object* v_i_1596_, lean_object* v_bs_1597_){
_start:
{
size_t v_sz_boxed_1598_; size_t v_i_boxed_1599_; lean_object* v_res_1600_; 
v_sz_boxed_1598_ = lean_unbox_usize(v_sz_1595_);
lean_dec(v_sz_1595_);
v_i_boxed_1599_ = lean_unbox_usize(v_i_1596_);
lean_dec(v_i_1596_);
v_res_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1598_, v_i_boxed_1599_, v_bs_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object* v_x_1602_){
_start:
{
if (lean_obj_tag(v_x_1602_) == 4)
{
lean_object* v_elems_1603_; size_t v_sz_1604_; size_t v___x_1605_; lean_object* v___x_1606_; 
v_elems_1603_ = lean_ctor_get(v_x_1602_, 0);
lean_inc_ref(v_elems_1603_);
lean_dec_ref_known(v_x_1602_, 1);
v_sz_1604_ = lean_array_size(v_elems_1603_);
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_1604_, v___x_1605_, v_elems_1603_);
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1607_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_1608_ = lean_unsigned_to_nat(80u);
v___x_1609_ = l_Lean_Json_pretty(v_x_1602_, v___x_1608_);
v___x_1610_ = lean_string_append(v___x_1607_, v___x_1609_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_1612_ = lean_string_append(v___x_1610_, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(lean_object* v_j_1614_, lean_object* v_k_1615_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = l_Lean_Json_getObjValD(v_j_1614_, v_k_1615_);
v___x_1617_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2___boxed(lean_object* v_j_1618_, lean_object* v_k_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_j_1618_, v_k_1619_);
lean_dec_ref(v_k_1619_);
return v_res_1620_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = 1;
v___x_1630_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4));
v___x_1631_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1630_, v___x_1629_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_1634_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5);
v___x_1635_ = lean_string_append(v___x_1634_, v___x_1633_);
return v___x_1635_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = 1;
v___x_1639_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8));
v___x_1640_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1639_, v___x_1638_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1641_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_1642_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1643_ = lean_string_append(v___x_1642_, v___x_1641_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1646_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10);
v___x_1647_ = lean_string_append(v___x_1646_, v___x_1645_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = 1;
v___x_1652_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14));
v___x_1653_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1652_, v___x_1651_);
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15);
v___x_1655_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1656_ = lean_string_append(v___x_1655_, v___x_1654_);
return v___x_1656_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1658_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16);
v___x_1659_ = lean_string_append(v___x_1658_, v___x_1657_);
return v___x_1659_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = 1;
v___x_1664_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19));
v___x_1665_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1664_, v___x_1663_);
return v___x_1665_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20);
v___x_1667_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1668_ = lean_string_append(v___x_1667_, v___x_1666_);
return v___x_1668_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1670_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21);
v___x_1671_ = lean_string_append(v___x_1670_, v___x_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson(lean_object* v_json_1672_){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_1672_);
v___x_1674_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_1672_, v___x_1673_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v_json_1672_);
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1679_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12);
v___x_1680_ = lean_string_append(v___x_1679_, v_a_1675_);
lean_dec(v_a_1675_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1680_);
v___x_1682_ = v___x_1677_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_a_1685_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1674_, 1);
v___x_1686_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
lean_inc(v_json_1672_);
v___x_1687_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_1672_, v___x_1686_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_a_1685_);
lean_dec(v_json_1672_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1692_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17);
v___x_1693_ = lean_string_append(v___x_1692_, v_a_1688_);
lean_dec(v_a_1688_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1693_);
v___x_1695_ = v___x_1690_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_a_1698_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1699_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1700_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_json_1672_, v___x_1699_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_a_1698_);
lean_dec(v_a_1685_);
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1705_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22);
v___x_1706_ = lean_string_append(v___x_1705_, v_a_1701_);
lean_dec(v_a_1701_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1706_);
v___x_1708_ = v___x_1703_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
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
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1720_; 
v_a_1711_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1713_ = v___x_1700_;
v_isShared_1714_ = v_isSharedCheck_1720_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1700_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1720_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1718_; 
v___x_1715_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1715_, 0, v_a_1685_);
lean_ctor_set(v___x_1715_, 1, v_a_1711_);
v___x_1716_ = lean_unbox(v_a_1698_);
lean_dec(v_a_1698_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*2, v___x_1716_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1715_);
v___x_1718_ = v___x_1713_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1715_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1723_, size_t v_i_1724_, lean_object* v_bs_1725_){
_start:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_usize_dec_lt(v_i_1724_, v_sz_1723_);
if (v___x_1726_ == 0)
{
return v_bs_1725_;
}
else
{
lean_object* v_v_1727_; lean_object* v_module_1728_; uint8_t v_isPrivate_1729_; uint8_t v_isAll_1730_; uint8_t v_isMeta_1731_; lean_object* v___x_1732_; lean_object* v_bs_x27_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; size_t v___x_1745_; size_t v___x_1746_; lean_object* v___x_1747_; 
v_v_1727_ = lean_array_uget_borrowed(v_bs_1725_, v_i_1724_);
v_module_1728_ = lean_ctor_get(v_v_1727_, 0);
lean_inc_ref(v_module_1728_);
v_isPrivate_1729_ = lean_ctor_get_uint8(v_v_1727_, sizeof(void*)*1);
v_isAll_1730_ = lean_ctor_get_uint8(v_v_1727_, sizeof(void*)*1 + 1);
v_isMeta_1731_ = lean_ctor_get_uint8(v_v_1727_, sizeof(void*)*1 + 2);
v___x_1732_ = lean_unsigned_to_nat(0u);
v_bs_x27_1733_ = lean_array_uset(v_bs_1725_, v_i_1724_, v___x_1732_);
v___x_1734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_module_1728_);
v___x_1735_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1735_, 0, v_isPrivate_1729_);
v___x_1736_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1736_, 0, v_isAll_1730_);
v___x_1737_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1737_, 0, v_isMeta_1731_);
v___x_1738_ = lean_unsigned_to_nat(4u);
v___x_1739_ = lean_mk_empty_array_with_capacity(v___x_1738_);
v___x_1740_ = lean_array_push(v___x_1739_, v___x_1734_);
v___x_1741_ = lean_array_push(v___x_1740_, v___x_1735_);
v___x_1742_ = lean_array_push(v___x_1741_, v___x_1736_);
v___x_1743_ = lean_array_push(v___x_1742_, v___x_1737_);
v___x_1744_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
v___x_1745_ = ((size_t)1ULL);
v___x_1746_ = lean_usize_add(v_i_1724_, v___x_1745_);
v___x_1747_ = lean_array_uset(v_bs_x27_1733_, v_i_1724_, v___x_1744_);
v_i_1724_ = v___x_1746_;
v_bs_1725_ = v___x_1747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1749_, lean_object* v_i_1750_, lean_object* v_bs_1751_){
_start:
{
size_t v_sz_boxed_1752_; size_t v_i_boxed_1753_; lean_object* v_res_1754_; 
v_sz_boxed_1752_ = lean_unbox_usize(v_sz_1749_);
lean_dec(v_sz_1749_);
v_i_boxed_1753_ = lean_unbox_usize(v_i_1750_);
lean_dec(v_i_1750_);
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1752_, v_i_boxed_1753_, v_bs_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1755_){
_start:
{
size_t v_sz_1756_; size_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_sz_1756_ = lean_array_size(v_a_1755_);
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1756_, v___x_1757_, v_a_1755_);
v___x_1759_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
if (lean_obj_tag(v_a_1760_) == 0)
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_array_to_list(v_a_1761_);
return v___x_1762_;
}
else
{
lean_object* v_head_1763_; lean_object* v_tail_1764_; lean_object* v___x_1765_; 
v_head_1763_ = lean_ctor_get(v_a_1760_, 0);
lean_inc(v_head_1763_);
v_tail_1764_ = lean_ctor_get(v_a_1760_, 1);
lean_inc(v_tail_1764_);
lean_dec_ref_known(v_a_1760_, 2);
v___x_1765_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1761_, v_head_1763_);
v_a_1760_ = v_tail_1764_;
v_a_1761_ = v___x_1765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1769_){
_start:
{
lean_object* v_version_1770_; uint8_t v_isSetupFailure_1771_; lean_object* v_directImports_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_version_1770_ = lean_ctor_get(v_x_1769_, 0);
lean_inc(v_version_1770_);
v_isSetupFailure_1771_ = lean_ctor_get_uint8(v_x_1769_, sizeof(void*)*2);
v_directImports_1772_ = lean_ctor_get(v_x_1769_, 1);
lean_inc_ref(v_directImports_1772_);
lean_dec_ref(v_x_1769_);
v___x_1773_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1774_ = l_Lean_JsonNumber_fromNat(v_version_1770_);
v___x_1775_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1773_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_box(0);
v___x_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1780_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1780_, 0, v_isSetupFailure_1771_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v___x_1777_);
v___x_1783_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1784_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1772_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1783_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
lean_ctor_set(v___x_1786_, 1, v___x_1777_);
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v___x_1777_);
v___x_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1782_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1778_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1791_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1789_, v___x_1790_);
v___x_1792_ = l_Lean_Json_mkObj(v___x_1791_);
lean_dec(v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1795_, lean_object* v_v_1796_, lean_object* v_t_1797_){
_start:
{
if (lean_obj_tag(v_t_1797_) == 0)
{
lean_object* v_size_1798_; lean_object* v_k_1799_; lean_object* v_v_1800_; lean_object* v_l_1801_; lean_object* v_r_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_2082_; 
v_size_1798_ = lean_ctor_get(v_t_1797_, 0);
v_k_1799_ = lean_ctor_get(v_t_1797_, 1);
v_v_1800_ = lean_ctor_get(v_t_1797_, 2);
v_l_1801_ = lean_ctor_get(v_t_1797_, 3);
v_r_1802_ = lean_ctor_get(v_t_1797_, 4);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_t_1797_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_1804_ = v_t_1797_;
v_isShared_1805_ = v_isSharedCheck_2082_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_r_1802_);
lean_inc(v_l_1801_);
lean_inc(v_v_1800_);
lean_inc(v_k_1799_);
lean_inc(v_size_1798_);
lean_dec(v_t_1797_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_2082_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_string_compare(v_k_1795_, v_k_1799_);
switch(v___x_1806_)
{
case 0:
{
lean_object* v_impl_1807_; lean_object* v___x_1808_; 
lean_dec(v_size_1798_);
v_impl_1807_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1795_, v_v_1796_, v_l_1801_);
v___x_1808_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1802_) == 0)
{
lean_object* v_size_1809_; lean_object* v_size_1810_; lean_object* v_k_1811_; lean_object* v_v_1812_; lean_object* v_l_1813_; lean_object* v_r_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_size_1809_ = lean_ctor_get(v_r_1802_, 0);
v_size_1810_ = lean_ctor_get(v_impl_1807_, 0);
v_k_1811_ = lean_ctor_get(v_impl_1807_, 1);
v_v_1812_ = lean_ctor_get(v_impl_1807_, 2);
v_l_1813_ = lean_ctor_get(v_impl_1807_, 3);
v_r_1814_ = lean_ctor_get(v_impl_1807_, 4);
lean_inc(v_r_1814_);
v___x_1815_ = lean_unsigned_to_nat(3u);
v___x_1816_ = lean_nat_mul(v___x_1815_, v_size_1809_);
v___x_1817_ = lean_nat_dec_lt(v___x_1816_, v_size_1810_);
lean_dec(v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_dec(v_r_1814_);
v___x_1818_ = lean_nat_add(v___x_1808_, v_size_1810_);
v___x_1819_ = lean_nat_add(v___x_1818_, v_size_1809_);
lean_dec(v___x_1818_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 3, v_impl_1807_);
lean_ctor_set(v___x_1804_, 0, v___x_1819_);
v___x_1821_ = v___x_1804_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_impl_1807_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v_r_1802_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
else
{
lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1888_; 
lean_inc(v_l_1813_);
lean_inc(v_v_1812_);
lean_inc(v_k_1811_);
lean_inc(v_size_1810_);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_impl_1807_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; lean_object* v_unused_1890_; lean_object* v_unused_1891_; lean_object* v_unused_1892_; lean_object* v_unused_1893_; 
v_unused_1889_ = lean_ctor_get(v_impl_1807_, 4);
lean_dec(v_unused_1889_);
v_unused_1890_ = lean_ctor_get(v_impl_1807_, 3);
lean_dec(v_unused_1890_);
v_unused_1891_ = lean_ctor_get(v_impl_1807_, 2);
lean_dec(v_unused_1891_);
v_unused_1892_ = lean_ctor_get(v_impl_1807_, 1);
lean_dec(v_unused_1892_);
v_unused_1893_ = lean_ctor_get(v_impl_1807_, 0);
lean_dec(v_unused_1893_);
v___x_1824_ = v_impl_1807_;
v_isShared_1825_ = v_isSharedCheck_1888_;
goto v_resetjp_1823_;
}
else
{
lean_dec(v_impl_1807_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1888_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_size_1826_; lean_object* v_size_1827_; lean_object* v_k_1828_; lean_object* v_v_1829_; lean_object* v_l_1830_; lean_object* v_r_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_size_1826_ = lean_ctor_get(v_l_1813_, 0);
v_size_1827_ = lean_ctor_get(v_r_1814_, 0);
v_k_1828_ = lean_ctor_get(v_r_1814_, 1);
v_v_1829_ = lean_ctor_get(v_r_1814_, 2);
v_l_1830_ = lean_ctor_get(v_r_1814_, 3);
v_r_1831_ = lean_ctor_get(v_r_1814_, 4);
v___x_1832_ = lean_unsigned_to_nat(2u);
v___x_1833_ = lean_nat_mul(v___x_1832_, v_size_1826_);
v___x_1834_ = lean_nat_dec_lt(v_size_1827_, v___x_1833_);
lean_dec(v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1863_; 
lean_inc(v_r_1831_);
lean_inc(v_l_1830_);
lean_inc(v_v_1829_);
lean_inc(v_k_1828_);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_r_1814_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; lean_object* v_unused_1868_; 
v_unused_1864_ = lean_ctor_get(v_r_1814_, 4);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_r_1814_, 3);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_r_1814_, 2);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_r_1814_, 1);
lean_dec(v_unused_1867_);
v_unused_1868_ = lean_ctor_get(v_r_1814_, 0);
lean_dec(v_unused_1868_);
v___x_1836_ = v_r_1814_;
v_isShared_1837_ = v_isSharedCheck_1863_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v_r_1814_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1863_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___x_1851_; lean_object* v___y_1853_; 
v___x_1838_ = lean_nat_add(v___x_1808_, v_size_1810_);
lean_dec(v_size_1810_);
v___x_1839_ = lean_nat_add(v___x_1838_, v_size_1809_);
lean_dec(v___x_1838_);
v___x_1851_ = lean_nat_add(v___x_1808_, v_size_1826_);
if (lean_obj_tag(v_l_1830_) == 0)
{
lean_object* v_size_1861_; 
v_size_1861_ = lean_ctor_get(v_l_1830_, 0);
lean_inc(v_size_1861_);
v___y_1853_ = v_size_1861_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_unsigned_to_nat(0u);
v___y_1853_ = v___x_1862_;
goto v___jp_1852_;
}
v___jp_1840_:
{
lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1844_ = lean_nat_add(v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 4, v_r_1802_);
lean_ctor_set(v___x_1836_, 3, v_r_1831_);
lean_ctor_set(v___x_1836_, 2, v_v_1800_);
lean_ctor_set(v___x_1836_, 1, v_k_1799_);
lean_ctor_set(v___x_1836_, 0, v___x_1844_);
v___x_1846_ = v___x_1836_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_r_1831_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_r_1802_);
v___x_1846_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 4, v___x_1846_);
lean_ctor_set(v___x_1824_, 3, v___y_1841_);
lean_ctor_set(v___x_1824_, 2, v_v_1829_);
lean_ctor_set(v___x_1824_, 1, v_k_1828_);
lean_ctor_set(v___x_1824_, 0, v___x_1839_);
v___x_1848_ = v___x_1824_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_k_1828_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_v_1829_);
lean_ctor_set(v_reuseFailAlloc_1849_, 3, v___y_1841_);
lean_ctor_set(v_reuseFailAlloc_1849_, 4, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
v___jp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_nat_add(v___x_1851_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec(v___x_1851_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v_l_1830_);
lean_ctor_set(v___x_1804_, 3, v_l_1813_);
lean_ctor_set(v___x_1804_, 2, v_v_1812_);
lean_ctor_set(v___x_1804_, 1, v_k_1811_);
lean_ctor_set(v___x_1804_, 0, v___x_1854_);
v___x_1856_ = v___x_1804_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_k_1811_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_v_1812_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_l_1813_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_l_1830_);
v___x_1856_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_nat_add(v___x_1808_, v_size_1809_);
if (lean_obj_tag(v_r_1831_) == 0)
{
lean_object* v_size_1858_; 
v_size_1858_ = lean_ctor_get(v_r_1831_, 0);
lean_inc(v_size_1858_);
v___y_1841_ = v___x_1856_;
v___y_1842_ = v___x_1857_;
v___y_1843_ = v_size_1858_;
goto v___jp_1840_;
}
else
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v___y_1841_ = v___x_1856_;
v___y_1842_ = v___x_1857_;
v___y_1843_ = v___x_1859_;
goto v___jp_1840_;
}
}
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_del_object(v___x_1804_);
v___x_1869_ = lean_nat_add(v___x_1808_, v_size_1810_);
lean_dec(v_size_1810_);
v___x_1870_ = lean_nat_add(v___x_1869_, v_size_1809_);
lean_dec(v___x_1869_);
v___x_1871_ = lean_nat_add(v___x_1808_, v_size_1809_);
v___x_1872_ = lean_nat_add(v___x_1871_, v_size_1827_);
lean_dec(v___x_1871_);
lean_inc_ref(v_r_1802_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 4, v_r_1802_);
lean_ctor_set(v___x_1824_, 3, v_r_1814_);
lean_ctor_set(v___x_1824_, 2, v_v_1800_);
lean_ctor_set(v___x_1824_, 1, v_k_1799_);
lean_ctor_set(v___x_1824_, 0, v___x_1872_);
v___x_1874_ = v___x_1824_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_1887_, 3, v_r_1814_);
lean_ctor_set(v_reuseFailAlloc_1887_, 4, v_r_1802_);
v___x_1874_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_isSharedCheck_1881_ = !lean_is_exclusive(v_r_1802_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; lean_object* v_unused_1883_; lean_object* v_unused_1884_; lean_object* v_unused_1885_; lean_object* v_unused_1886_; 
v_unused_1882_ = lean_ctor_get(v_r_1802_, 4);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_r_1802_, 3);
lean_dec(v_unused_1883_);
v_unused_1884_ = lean_ctor_get(v_r_1802_, 2);
lean_dec(v_unused_1884_);
v_unused_1885_ = lean_ctor_get(v_r_1802_, 1);
lean_dec(v_unused_1885_);
v_unused_1886_ = lean_ctor_get(v_r_1802_, 0);
lean_dec(v_unused_1886_);
v___x_1876_ = v_r_1802_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_dec(v_r_1802_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 4, v___x_1874_);
lean_ctor_set(v___x_1876_, 3, v_l_1813_);
lean_ctor_set(v___x_1876_, 2, v_v_1812_);
lean_ctor_set(v___x_1876_, 1, v_k_1811_);
lean_ctor_set(v___x_1876_, 0, v___x_1870_);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_k_1811_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_v_1812_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_l_1813_);
lean_ctor_set(v_reuseFailAlloc_1880_, 4, v___x_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1894_; 
v_l_1894_ = lean_ctor_get(v_impl_1807_, 3);
if (lean_obj_tag(v_l_1894_) == 0)
{
lean_object* v_r_1895_; lean_object* v_k_1896_; lean_object* v_v_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1908_; 
lean_inc_ref(v_l_1894_);
v_r_1895_ = lean_ctor_get(v_impl_1807_, 4);
v_k_1896_ = lean_ctor_get(v_impl_1807_, 1);
v_v_1897_ = lean_ctor_get(v_impl_1807_, 2);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_impl_1807_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; lean_object* v_unused_1910_; 
v_unused_1909_ = lean_ctor_get(v_impl_1807_, 3);
lean_dec(v_unused_1909_);
v_unused_1910_ = lean_ctor_get(v_impl_1807_, 0);
lean_dec(v_unused_1910_);
v___x_1899_ = v_impl_1807_;
v_isShared_1900_ = v_isSharedCheck_1908_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_r_1895_);
lean_inc(v_v_1897_);
lean_inc(v_k_1896_);
lean_dec(v_impl_1807_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1908_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1895_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 3, v_r_1895_);
lean_ctor_set(v___x_1899_, 2, v_v_1800_);
lean_ctor_set(v___x_1899_, 1, v_k_1799_);
lean_ctor_set(v___x_1899_, 0, v___x_1808_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_1907_, 3, v_r_1895_);
lean_ctor_set(v_reuseFailAlloc_1907_, 4, v_r_1895_);
v___x_1903_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v___x_1903_);
lean_ctor_set(v___x_1804_, 3, v_l_1894_);
lean_ctor_set(v___x_1804_, 2, v_v_1897_);
lean_ctor_set(v___x_1804_, 1, v_k_1896_);
lean_ctor_set(v___x_1804_, 0, v___x_1901_);
v___x_1905_ = v___x_1804_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_k_1896_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_v_1897_);
lean_ctor_set(v_reuseFailAlloc_1906_, 3, v_l_1894_);
lean_ctor_set(v_reuseFailAlloc_1906_, 4, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
else
{
lean_object* v_r_1911_; 
v_r_1911_ = lean_ctor_get(v_impl_1807_, 4);
lean_inc(v_r_1911_);
if (lean_obj_tag(v_r_1911_) == 0)
{
lean_object* v_k_1912_; lean_object* v_v_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1936_; 
lean_inc(v_l_1894_);
v_k_1912_ = lean_ctor_get(v_impl_1807_, 1);
v_v_1913_ = lean_ctor_get(v_impl_1807_, 2);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_impl_1807_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; lean_object* v_unused_1938_; lean_object* v_unused_1939_; 
v_unused_1937_ = lean_ctor_get(v_impl_1807_, 4);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v_impl_1807_, 3);
lean_dec(v_unused_1938_);
v_unused_1939_ = lean_ctor_get(v_impl_1807_, 0);
lean_dec(v_unused_1939_);
v___x_1915_ = v_impl_1807_;
v_isShared_1916_ = v_isSharedCheck_1936_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_v_1913_);
lean_inc(v_k_1912_);
lean_dec(v_impl_1807_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1936_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_k_1917_; lean_object* v_v_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1932_; 
v_k_1917_ = lean_ctor_get(v_r_1911_, 1);
v_v_1918_ = lean_ctor_get(v_r_1911_, 2);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_r_1911_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; lean_object* v_unused_1934_; lean_object* v_unused_1935_; 
v_unused_1933_ = lean_ctor_get(v_r_1911_, 4);
lean_dec(v_unused_1933_);
v_unused_1934_ = lean_ctor_get(v_r_1911_, 3);
lean_dec(v_unused_1934_);
v_unused_1935_ = lean_ctor_get(v_r_1911_, 0);
lean_dec(v_unused_1935_);
v___x_1920_ = v_r_1911_;
v_isShared_1921_ = v_isSharedCheck_1932_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_v_1918_);
lean_inc(v_k_1917_);
lean_dec(v_r_1911_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1932_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_unsigned_to_nat(3u);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 4, v_l_1894_);
lean_ctor_set(v___x_1920_, 3, v_l_1894_);
lean_ctor_set(v___x_1920_, 2, v_v_1913_);
lean_ctor_set(v___x_1920_, 1, v_k_1912_);
lean_ctor_set(v___x_1920_, 0, v___x_1808_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1912_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1913_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_l_1894_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_l_1894_);
v___x_1924_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1926_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 4, v_l_1894_);
lean_ctor_set(v___x_1915_, 2, v_v_1800_);
lean_ctor_set(v___x_1915_, 1, v_k_1799_);
lean_ctor_set(v___x_1915_, 0, v___x_1808_);
v___x_1926_ = v___x_1915_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_l_1894_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_l_1894_);
v___x_1926_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1928_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v___x_1926_);
lean_ctor_set(v___x_1804_, 3, v___x_1924_);
lean_ctor_set(v___x_1804_, 2, v_v_1918_);
lean_ctor_set(v___x_1804_, 1, v_k_1917_);
lean_ctor_set(v___x_1804_, 0, v___x_1922_);
v___x_1928_ = v___x_1804_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_k_1917_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_v_1918_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_unsigned_to_nat(2u);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v_r_1911_);
lean_ctor_set(v___x_1804_, 3, v_impl_1807_);
lean_ctor_set(v___x_1804_, 0, v___x_1940_);
v___x_1942_ = v___x_1804_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_1943_, 3, v_impl_1807_);
lean_ctor_set(v_reuseFailAlloc_1943_, 4, v_r_1911_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1945_; 
lean_dec(v_v_1800_);
lean_dec(v_k_1799_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 2, v_v_1796_);
lean_ctor_set(v___x_1804_, 1, v_k_1795_);
v___x_1945_ = v___x_1804_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_size_1798_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_k_1795_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_v_1796_);
lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_l_1801_);
lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_r_1802_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
default: 
{
lean_object* v_impl_1947_; lean_object* v___x_1948_; 
lean_dec(v_size_1798_);
v_impl_1947_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1795_, v_v_1796_, v_r_1802_);
v___x_1948_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1801_) == 0)
{
lean_object* v_size_1949_; lean_object* v_size_1950_; lean_object* v_k_1951_; lean_object* v_v_1952_; lean_object* v_l_1953_; lean_object* v_r_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v_size_1949_ = lean_ctor_get(v_l_1801_, 0);
v_size_1950_ = lean_ctor_get(v_impl_1947_, 0);
v_k_1951_ = lean_ctor_get(v_impl_1947_, 1);
v_v_1952_ = lean_ctor_get(v_impl_1947_, 2);
v_l_1953_ = lean_ctor_get(v_impl_1947_, 3);
lean_inc(v_l_1953_);
v_r_1954_ = lean_ctor_get(v_impl_1947_, 4);
v___x_1955_ = lean_unsigned_to_nat(3u);
v___x_1956_ = lean_nat_mul(v___x_1955_, v_size_1949_);
v___x_1957_ = lean_nat_dec_lt(v___x_1956_, v_size_1950_);
lean_dec(v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
lean_dec(v_l_1953_);
v___x_1958_ = lean_nat_add(v___x_1948_, v_size_1949_);
v___x_1959_ = lean_nat_add(v___x_1958_, v_size_1950_);
lean_dec(v___x_1958_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v_impl_1947_);
lean_ctor_set(v___x_1804_, 0, v___x_1959_);
v___x_1961_ = v___x_1804_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_1962_, 3, v_l_1801_);
lean_ctor_set(v_reuseFailAlloc_1962_, 4, v_impl_1947_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
else
{
lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2026_; 
lean_inc(v_r_1954_);
lean_inc(v_v_1952_);
lean_inc(v_k_1951_);
lean_inc(v_size_1950_);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_impl_1947_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; 
v_unused_2027_ = lean_ctor_get(v_impl_1947_, 4);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_impl_1947_, 3);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_impl_1947_, 2);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_impl_1947_, 1);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_impl_1947_, 0);
lean_dec(v_unused_2031_);
v___x_1964_ = v_impl_1947_;
v_isShared_1965_ = v_isSharedCheck_2026_;
goto v_resetjp_1963_;
}
else
{
lean_dec(v_impl_1947_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2026_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_size_1966_; lean_object* v_k_1967_; lean_object* v_v_1968_; lean_object* v_l_1969_; lean_object* v_r_1970_; lean_object* v_size_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v_size_1966_ = lean_ctor_get(v_l_1953_, 0);
v_k_1967_ = lean_ctor_get(v_l_1953_, 1);
v_v_1968_ = lean_ctor_get(v_l_1953_, 2);
v_l_1969_ = lean_ctor_get(v_l_1953_, 3);
v_r_1970_ = lean_ctor_get(v_l_1953_, 4);
v_size_1971_ = lean_ctor_get(v_r_1954_, 0);
v___x_1972_ = lean_unsigned_to_nat(2u);
v___x_1973_ = lean_nat_mul(v___x_1972_, v_size_1971_);
v___x_1974_ = lean_nat_dec_lt(v_size_1966_, v___x_1973_);
lean_dec(v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2002_; 
lean_inc(v_r_1970_);
lean_inc(v_l_1969_);
lean_inc(v_v_1968_);
lean_inc(v_k_1967_);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_l_1953_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; lean_object* v_unused_2004_; lean_object* v_unused_2005_; lean_object* v_unused_2006_; lean_object* v_unused_2007_; 
v_unused_2003_ = lean_ctor_get(v_l_1953_, 4);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_l_1953_, 3);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_l_1953_, 2);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_l_1953_, 1);
lean_dec(v_unused_2006_);
v_unused_2007_ = lean_ctor_get(v_l_1953_, 0);
lean_dec(v_unused_2007_);
v___x_1976_ = v_l_1953_;
v_isShared_1977_ = v_isSharedCheck_2002_;
goto v_resetjp_1975_;
}
else
{
lean_dec(v_l_1953_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2002_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1992_; 
v___x_1978_ = lean_nat_add(v___x_1948_, v_size_1949_);
v___x_1979_ = lean_nat_add(v___x_1978_, v_size_1950_);
lean_dec(v_size_1950_);
if (lean_obj_tag(v_l_1969_) == 0)
{
lean_object* v_size_2000_; 
v_size_2000_ = lean_ctor_get(v_l_1969_, 0);
lean_inc(v_size_2000_);
v___y_1992_ = v_size_2000_;
goto v___jp_1991_;
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_unsigned_to_nat(0u);
v___y_1992_ = v___x_2001_;
goto v___jp_1991_;
}
v___jp_1980_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_nat_add(v___y_1981_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec(v___y_1981_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 4, v_r_1954_);
lean_ctor_set(v___x_1976_, 3, v_r_1970_);
lean_ctor_set(v___x_1976_, 2, v_v_1952_);
lean_ctor_set(v___x_1976_, 1, v_k_1951_);
lean_ctor_set(v___x_1976_, 0, v___x_1984_);
v___x_1986_ = v___x_1976_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_k_1951_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_v_1952_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v_r_1970_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v_r_1954_);
v___x_1986_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1988_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 4, v___x_1986_);
lean_ctor_set(v___x_1964_, 3, v___y_1982_);
lean_ctor_set(v___x_1964_, 2, v_v_1968_);
lean_ctor_set(v___x_1964_, 1, v_k_1967_);
lean_ctor_set(v___x_1964_, 0, v___x_1979_);
v___x_1988_ = v___x_1964_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_k_1967_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_v_1968_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v___y_1982_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
v___jp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_nat_add(v___x_1978_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec(v___x_1978_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v_l_1969_);
lean_ctor_set(v___x_1804_, 0, v___x_1993_);
v___x_1995_ = v___x_1804_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_l_1801_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_l_1969_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_nat_add(v___x_1948_, v_size_1971_);
if (lean_obj_tag(v_r_1970_) == 0)
{
lean_object* v_size_1997_; 
v_size_1997_ = lean_ctor_get(v_r_1970_, 0);
lean_inc(v_size_1997_);
v___y_1981_ = v___x_1996_;
v___y_1982_ = v___x_1995_;
v___y_1983_ = v_size_1997_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_unsigned_to_nat(0u);
v___y_1981_ = v___x_1996_;
v___y_1982_ = v___x_1995_;
v___y_1983_ = v___x_1998_;
goto v___jp_1980_;
}
}
}
}
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_del_object(v___x_1804_);
v___x_2008_ = lean_nat_add(v___x_1948_, v_size_1949_);
v___x_2009_ = lean_nat_add(v___x_2008_, v_size_1950_);
lean_dec(v_size_1950_);
v___x_2010_ = lean_nat_add(v___x_2008_, v_size_1966_);
lean_dec(v___x_2008_);
lean_inc_ref(v_l_1801_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 4, v_l_1953_);
lean_ctor_set(v___x_1964_, 3, v_l_1801_);
lean_ctor_set(v___x_1964_, 2, v_v_1800_);
lean_ctor_set(v___x_1964_, 1, v_k_1799_);
lean_ctor_set(v___x_1964_, 0, v___x_2010_);
v___x_2012_ = v___x_1964_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_l_1801_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_l_1953_);
v___x_2012_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_isSharedCheck_2019_ = !lean_is_exclusive(v_l_1801_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; lean_object* v_unused_2023_; lean_object* v_unused_2024_; 
v_unused_2020_ = lean_ctor_get(v_l_1801_, 4);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_l_1801_, 3);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_l_1801_, 2);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_l_1801_, 1);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_l_1801_, 0);
lean_dec(v_unused_2024_);
v___x_2014_ = v_l_1801_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v_l_1801_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 4, v_r_1954_);
lean_ctor_set(v___x_2014_, 3, v___x_2012_);
lean_ctor_set(v___x_2014_, 2, v_v_1952_);
lean_ctor_set(v___x_2014_, 1, v_k_1951_);
lean_ctor_set(v___x_2014_, 0, v___x_2009_);
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_k_1951_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_v_1952_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_r_1954_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2032_; 
v_l_2032_ = lean_ctor_get(v_impl_1947_, 3);
lean_inc(v_l_2032_);
if (lean_obj_tag(v_l_2032_) == 0)
{
lean_object* v_r_2033_; lean_object* v_k_2034_; lean_object* v_v_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2058_; 
v_r_2033_ = lean_ctor_get(v_impl_1947_, 4);
v_k_2034_ = lean_ctor_get(v_impl_1947_, 1);
v_v_2035_ = lean_ctor_get(v_impl_1947_, 2);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_impl_1947_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; lean_object* v_unused_2060_; 
v_unused_2059_ = lean_ctor_get(v_impl_1947_, 3);
lean_dec(v_unused_2059_);
v_unused_2060_ = lean_ctor_get(v_impl_1947_, 0);
lean_dec(v_unused_2060_);
v___x_2037_ = v_impl_1947_;
v_isShared_2038_ = v_isSharedCheck_2058_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_r_2033_);
lean_inc(v_v_2035_);
lean_inc(v_k_2034_);
lean_dec(v_impl_1947_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2058_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_k_2039_; lean_object* v_v_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2054_; 
v_k_2039_ = lean_ctor_get(v_l_2032_, 1);
v_v_2040_ = lean_ctor_get(v_l_2032_, 2);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_l_2032_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; lean_object* v_unused_2056_; lean_object* v_unused_2057_; 
v_unused_2055_ = lean_ctor_get(v_l_2032_, 4);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_l_2032_, 3);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_l_2032_, 0);
lean_dec(v_unused_2057_);
v___x_2042_ = v_l_2032_;
v_isShared_2043_ = v_isSharedCheck_2054_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_v_2040_);
lean_inc(v_k_2039_);
lean_dec(v_l_2032_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2054_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2044_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2033_, 2);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 4, v_r_2033_);
lean_ctor_set(v___x_2042_, 3, v_r_2033_);
lean_ctor_set(v___x_2042_, 2, v_v_1800_);
lean_ctor_set(v___x_2042_, 1, v_k_1799_);
lean_ctor_set(v___x_2042_, 0, v___x_1948_);
v___x_2046_ = v___x_2042_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_r_2033_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_r_2033_);
v___x_2046_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2048_; 
lean_inc(v_r_2033_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 3, v_r_2033_);
lean_ctor_set(v___x_2037_, 0, v___x_1948_);
v___x_2048_ = v___x_2037_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_k_2034_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_v_2035_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v_r_2033_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_r_2033_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v___x_2048_);
lean_ctor_set(v___x_1804_, 3, v___x_2046_);
lean_ctor_set(v___x_1804_, 2, v_v_2040_);
lean_ctor_set(v___x_1804_, 1, v_k_2039_);
lean_ctor_set(v___x_1804_, 0, v___x_2044_);
v___x_2050_ = v___x_1804_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
else
{
lean_object* v_r_2061_; 
v_r_2061_ = lean_ctor_get(v_impl_1947_, 4);
lean_inc(v_r_2061_);
if (lean_obj_tag(v_r_2061_) == 0)
{
lean_object* v_k_2062_; lean_object* v_v_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2074_; 
v_k_2062_ = lean_ctor_get(v_impl_1947_, 1);
v_v_2063_ = lean_ctor_get(v_impl_1947_, 2);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_impl_1947_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; lean_object* v_unused_2076_; lean_object* v_unused_2077_; 
v_unused_2075_ = lean_ctor_get(v_impl_1947_, 4);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v_impl_1947_, 3);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_impl_1947_, 0);
lean_dec(v_unused_2077_);
v___x_2065_ = v_impl_1947_;
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_v_2063_);
lean_inc(v_k_2062_);
lean_dec(v_impl_1947_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_unsigned_to_nat(3u);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 4, v_l_2032_);
lean_ctor_set(v___x_2065_, 2, v_v_1800_);
lean_ctor_set(v___x_2065_, 1, v_k_1799_);
lean_ctor_set(v___x_2065_, 0, v___x_1948_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_l_2032_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_l_2032_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v_r_2061_);
lean_ctor_set(v___x_1804_, 3, v___x_2069_);
lean_ctor_set(v___x_1804_, 2, v_v_2063_);
lean_ctor_set(v___x_1804_, 1, v_k_2062_);
lean_ctor_set(v___x_1804_, 0, v___x_2067_);
v___x_2071_ = v___x_1804_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v_r_2061_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_unsigned_to_nat(2u);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v_impl_1947_);
lean_ctor_set(v___x_1804_, 3, v_r_2061_);
lean_ctor_set(v___x_1804_, 0, v___x_2078_);
v___x_2080_ = v___x_1804_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_r_2061_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v_impl_1947_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
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
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_unsigned_to_nat(1u);
v___x_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v_k_1795_);
lean_ctor_set(v___x_2084_, 2, v_v_1796_);
lean_ctor_set(v___x_2084_, 3, v_t_1797_);
lean_ctor_set(v___x_2084_, 4, v_t_1797_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object* v_init_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
lean_object* v_k_2087_; lean_object* v_v_2088_; lean_object* v_l_2089_; lean_object* v_r_2090_; lean_object* v___x_2091_; 
v_k_2087_ = lean_ctor_get(v_x_2086_, 1);
lean_inc(v_k_2087_);
v_v_2088_ = lean_ctor_get(v_x_2086_, 2);
lean_inc(v_v_2088_);
v_l_2089_ = lean_ctor_get(v_x_2086_, 3);
lean_inc(v_l_2089_);
v_r_2090_ = lean_ctor_get(v_x_2086_, 4);
lean_inc(v_r_2090_);
lean_dec_ref_known(v_x_2086_, 5);
v___x_2091_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v_init_2085_, v_l_2089_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_dec(v_r_2090_);
lean_dec(v_v_2088_);
lean_dec(v_k_2087_);
return v___x_2091_;
}
else
{
if (lean_obj_tag(v_v_2088_) == 4)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2206_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2206_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2206_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_elems_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_elems_2096_ = lean_ctor_get(v_v_2088_, 0);
lean_inc_ref(v_elems_2096_);
lean_dec_ref_known(v_v_2088_, 1);
v___x_2097_ = lean_array_get_size(v_elems_2096_);
v___x_2098_ = lean_unsigned_to_nat(8u);
v___x_2099_ = lean_nat_dec_eq(v___x_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
lean_dec_ref(v_elems_2096_);
lean_dec(v_a_2092_);
lean_dec(v_r_2090_);
lean_dec(v_k_2087_);
v___x_2100_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_2101_ = l_Nat_reprFast(v___x_2097_);
v___x_2102_ = lean_string_append(v___x_2100_, v___x_2101_);
lean_dec_ref(v___x_2101_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2102_);
v___x_2104_ = v___x_2094_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_del_object(v___x_2094_);
v___x_2106_ = lean_box(0);
v___x_2107_ = lean_unsigned_to_nat(0u);
v___x_2108_ = lean_array_get_borrowed(v___x_2106_, v_elems_2096_, v___x_2107_);
lean_inc(v___x_2108_);
v___x_2109_ = l_Lean_Json_getNat_x3f(v___x_2108_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_elems_2096_);
lean_dec(v_a_2092_);
lean_dec(v_r_2090_);
lean_dec(v_k_2087_);
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_a_2118_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2119_ = lean_unsigned_to_nat(1u);
v___x_2120_ = lean_array_get_borrowed(v___x_2106_, v_elems_2096_, v___x_2119_);
lean_inc(v___x_2120_);
v___x_2121_ = l_Lean_Json_getNat_x3f(v___x_2120_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_a_2118_);
lean_dec_ref(v_elems_2096_);
lean_dec(v_a_2092_);
lean_dec(v_r_2090_);
lean_dec(v_k_2087_);
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2130_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2131_ = lean_unsigned_to_nat(2u);
v___x_2132_ = lean_array_get_borrowed(v___x_2106_, v_elems_2096_, v___x_2131_);
lean_inc(v___x_2132_);
v___x_2133_ = l_Lean_Json_getNat_x3f(v___x_2132_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_a_2130_);
lean_dec(v_a_2118_);
lean_dec_ref(v_elems_2096_);
lean_dec(v_a_2092_);
lean_dec(v_r_2090_);
lean_dec(v_k_2087_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_a_2142_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2133_, 1);
v___x_2143_ = lean_unsigned_to_nat(3u);
v___x_2144_ = lean_array_get_borrowed(v___x_2106_, v_elems_2096_, v___x_2143_);
lean_inc(v___x_2144_);
v___x_2145_ = l_Lean_Json_getNat_x3f(v___x_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_2142_);
lean_dec(v_a_2130_);
lean_dec(v_a_2118_);
lean_dec_ref(v_elems_2096_);
lean_dec(v_a_2092_);
lean_dec(v_r_2090_);
lean_dec(v_k_2087_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_a_2154_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2155_ = lean_unsigned_to_nat(4u);
v___x_2156_ = lean_array_get_borrowed(v___x_2106_, v_elems_2096_, v___x_2155_);
lean_inc(v___x_2156_);
v___x_2157_ = l_Lean_Json_getNat_x3f(v___x_2156_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_a_2154_);
lean_dec(v_a_2142_);
lean_dec(v_a_2130_);
lean_dec(v_a_2118_);
lean_dec_ref(v_elems_2096_);
lean_dec(v_a_2092_);
lean_dec(v_r_2090_);
lean_dec(v_k_2087_);
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_a_2166_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2167_ = lean_unsigned_to_nat(5u);
v___x_2168_ = lean_array_get_borrowed(v___x_2106_, v_elems_2096_, v___x_2167_);
lean_inc(v___x_2168_);
v___x_2169_ = l_Lean_Json_getNat_x3f(v___x_2168_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_a_2166_);
lean_dec(v_a_2154_);
lean_dec(v_a_2142_);
lean_dec(v_a_2130_);
lean_dec(v_a_2118_);
lean_dec_ref(v_elems_2096_);
lean_dec(v_a_2092_);
lean_dec(v_r_2090_);
lean_dec(v_k_2087_);
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_a_2178_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2179_ = lean_unsigned_to_nat(6u);
v___x_2180_ = lean_array_get_borrowed(v___x_2106_, v_elems_2096_, v___x_2179_);
lean_inc(v___x_2180_);
v___x_2181_ = l_Lean_Json_getNat_x3f(v___x_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_2178_);
lean_dec(v_a_2166_);
lean_dec(v_a_2154_);
lean_dec(v_a_2142_);
lean_dec(v_a_2130_);
lean_dec(v_a_2118_);
lean_dec_ref(v_elems_2096_);
lean_dec(v_a_2092_);
lean_dec(v_r_2090_);
lean_dec(v_k_2087_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_a_2190_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2191_ = lean_unsigned_to_nat(7u);
v___x_2192_ = lean_array_get(v___x_2106_, v_elems_2096_, v___x_2191_);
lean_dec_ref(v_elems_2096_);
v___x_2193_ = l_Lean_Json_getNat_x3f(v___x_2192_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_a_2190_);
lean_dec(v_a_2178_);
lean_dec(v_a_2166_);
lean_dec(v_a_2154_);
lean_dec(v_a_2142_);
lean_dec(v_a_2130_);
lean_dec(v_a_2118_);
lean_dec(v_a_2092_);
lean_dec(v_r_2090_);
lean_dec(v_k_2087_);
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_a_2202_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2193_, 1);
v___x_2203_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2203_, 0, v_a_2118_);
lean_ctor_set(v___x_2203_, 1, v_a_2130_);
lean_ctor_set(v___x_2203_, 2, v_a_2142_);
lean_ctor_set(v___x_2203_, 3, v_a_2154_);
lean_ctor_set(v___x_2203_, 4, v_a_2166_);
lean_ctor_set(v___x_2203_, 5, v_a_2178_);
lean_ctor_set(v___x_2203_, 6, v_a_2190_);
lean_ctor_set(v___x_2203_, 7, v_a_2202_);
v___x_2204_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_2087_, v___x_2203_, v_a_2092_);
v_init_2085_ = v___x_2204_;
v_x_2086_ = v_r_2090_;
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
lean_object* v___x_2207_; 
lean_dec_ref_known(v___x_2091_, 1);
lean_dec(v_r_2090_);
lean_dec(v_v_2088_);
lean_dec(v_k_2087_);
v___x_2207_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_2207_;
}
}
}
else
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_init_2085_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(lean_object* v_j_2209_, lean_object* v_k_2210_){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = l_Lean_Json_getObjValD(v_j_2209_, v_k_2210_);
v___x_2212_ = l_Lean_Json_getObj_x3f(v___x_2211_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_a_2221_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2222_ = lean_box(1);
v___x_2223_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v___x_2222_, v_a_2221_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1___boxed(lean_object* v_j_2224_, lean_object* v_k_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_j_2224_, v_k_2225_);
lean_dec_ref(v_k_2225_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2227_, size_t v_i_2228_, lean_object* v_bs_2229_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = lean_usize_dec_lt(v_i_2228_, v_sz_2227_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_bs_2229_);
return v___x_2231_;
}
else
{
lean_object* v_v_2232_; lean_object* v___x_2233_; lean_object* v_bs_x27_2234_; size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; 
v_v_2232_ = lean_array_uget(v_bs_2229_, v_i_2228_);
v___x_2233_ = lean_unsigned_to_nat(0u);
v_bs_x27_2234_ = lean_array_uset(v_bs_2229_, v_i_2228_, v___x_2233_);
v___x_2235_ = ((size_t)1ULL);
v___x_2236_ = lean_usize_add(v_i_2228_, v___x_2235_);
v___x_2237_ = lean_array_uset(v_bs_x27_2234_, v_i_2228_, v_v_2232_);
v_i_2228_ = v___x_2236_;
v_bs_2229_ = v___x_2237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2239_, lean_object* v_i_2240_, lean_object* v_bs_2241_){
_start:
{
size_t v_sz_boxed_2242_; size_t v_i_boxed_2243_; lean_object* v_res_2244_; 
v_sz_boxed_2242_ = lean_unbox_usize(v_sz_2239_);
lean_dec(v_sz_2239_);
v_i_boxed_2243_ = lean_unbox_usize(v_i_2240_);
lean_dec(v_i_2240_);
v_res_2244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2242_, v_i_boxed_2243_, v_bs_2241_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2245_){
_start:
{
if (lean_obj_tag(v_x_2245_) == 4)
{
lean_object* v_elems_2246_; size_t v_sz_2247_; size_t v___x_2248_; lean_object* v___x_2249_; 
v_elems_2246_ = lean_ctor_get(v_x_2245_, 0);
lean_inc_ref(v_elems_2246_);
lean_dec_ref_known(v_x_2245_, 1);
v_sz_2247_ = lean_array_size(v_elems_2246_);
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2247_, v___x_2248_, v_elems_2246_);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2250_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2251_ = lean_unsigned_to_nat(80u);
v___x_2252_ = l_Lean_Json_pretty(v_x_2245_, v___x_2251_);
v___x_2253_ = lean_string_append(v___x_2250_, v___x_2252_);
lean_dec_ref(v___x_2252_);
v___x_2254_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_2255_ = lean_string_append(v___x_2253_, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2259_){
_start:
{
if (lean_obj_tag(v_x_2259_) == 0)
{
lean_object* v___x_2260_; 
v___x_2260_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2260_;
}
else
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2259_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2278_; 
v_a_2270_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2272_ = v___x_2261_;
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2261_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_a_2270_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2274_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object* v_j_2279_, lean_object* v_k_2280_){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = l_Lean_Json_getObjValD(v_j_2279_, v_k_2280_);
v___x_2282_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object* v_j_2283_, lean_object* v_k_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_j_2283_, v_k_2284_);
lean_dec_ref(v_k_2284_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object* v_k_2286_, lean_object* v_v_2287_, lean_object* v_t_2288_){
_start:
{
if (lean_obj_tag(v_t_2288_) == 0)
{
lean_object* v_size_2289_; lean_object* v_k_2290_; lean_object* v_v_2291_; lean_object* v_l_2292_; lean_object* v_r_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2573_; 
v_size_2289_ = lean_ctor_get(v_t_2288_, 0);
v_k_2290_ = lean_ctor_get(v_t_2288_, 1);
v_v_2291_ = lean_ctor_get(v_t_2288_, 2);
v_l_2292_ = lean_ctor_get(v_t_2288_, 3);
v_r_2293_ = lean_ctor_get(v_t_2288_, 4);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_t_2288_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2295_ = v_t_2288_;
v_isShared_2296_ = v_isSharedCheck_2573_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_r_2293_);
lean_inc(v_l_2292_);
lean_inc(v_v_2291_);
lean_inc(v_k_2290_);
lean_inc(v_size_2289_);
lean_dec(v_t_2288_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2573_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
uint8_t v___x_2297_; 
v___x_2297_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_2286_, v_k_2290_);
switch(v___x_2297_)
{
case 0:
{
lean_object* v_impl_2298_; lean_object* v___x_2299_; 
lean_dec(v_size_2289_);
v_impl_2298_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2286_, v_v_2287_, v_l_2292_);
v___x_2299_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2293_) == 0)
{
lean_object* v_size_2300_; lean_object* v_size_2301_; lean_object* v_k_2302_; lean_object* v_v_2303_; lean_object* v_l_2304_; lean_object* v_r_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_size_2300_ = lean_ctor_get(v_r_2293_, 0);
v_size_2301_ = lean_ctor_get(v_impl_2298_, 0);
v_k_2302_ = lean_ctor_get(v_impl_2298_, 1);
v_v_2303_ = lean_ctor_get(v_impl_2298_, 2);
v_l_2304_ = lean_ctor_get(v_impl_2298_, 3);
v_r_2305_ = lean_ctor_get(v_impl_2298_, 4);
lean_inc(v_r_2305_);
v___x_2306_ = lean_unsigned_to_nat(3u);
v___x_2307_ = lean_nat_mul(v___x_2306_, v_size_2300_);
v___x_2308_ = lean_nat_dec_lt(v___x_2307_, v_size_2301_);
lean_dec(v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
lean_dec(v_r_2305_);
v___x_2309_ = lean_nat_add(v___x_2299_, v_size_2301_);
v___x_2310_ = lean_nat_add(v___x_2309_, v_size_2300_);
lean_dec(v___x_2309_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 3, v_impl_2298_);
lean_ctor_set(v___x_2295_, 0, v___x_2310_);
v___x_2312_ = v___x_2295_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2313_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2313_, 3, v_impl_2298_);
lean_ctor_set(v_reuseFailAlloc_2313_, 4, v_r_2293_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
else
{
lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2379_; 
lean_inc(v_l_2304_);
lean_inc(v_v_2303_);
lean_inc(v_k_2302_);
lean_inc(v_size_2301_);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_impl_2298_);
if (v_isSharedCheck_2379_ == 0)
{
lean_object* v_unused_2380_; lean_object* v_unused_2381_; lean_object* v_unused_2382_; lean_object* v_unused_2383_; lean_object* v_unused_2384_; 
v_unused_2380_ = lean_ctor_get(v_impl_2298_, 4);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_impl_2298_, 3);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v_impl_2298_, 2);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_impl_2298_, 1);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_impl_2298_, 0);
lean_dec(v_unused_2384_);
v___x_2315_ = v_impl_2298_;
v_isShared_2316_ = v_isSharedCheck_2379_;
goto v_resetjp_2314_;
}
else
{
lean_dec(v_impl_2298_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2379_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v_size_2317_; lean_object* v_size_2318_; lean_object* v_k_2319_; lean_object* v_v_2320_; lean_object* v_l_2321_; lean_object* v_r_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v_size_2317_ = lean_ctor_get(v_l_2304_, 0);
v_size_2318_ = lean_ctor_get(v_r_2305_, 0);
v_k_2319_ = lean_ctor_get(v_r_2305_, 1);
v_v_2320_ = lean_ctor_get(v_r_2305_, 2);
v_l_2321_ = lean_ctor_get(v_r_2305_, 3);
v_r_2322_ = lean_ctor_get(v_r_2305_, 4);
v___x_2323_ = lean_unsigned_to_nat(2u);
v___x_2324_ = lean_nat_mul(v___x_2323_, v_size_2317_);
v___x_2325_ = lean_nat_dec_lt(v_size_2318_, v___x_2324_);
lean_dec(v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2354_; 
lean_inc(v_r_2322_);
lean_inc(v_l_2321_);
lean_inc(v_v_2320_);
lean_inc(v_k_2319_);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_r_2305_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; lean_object* v_unused_2356_; lean_object* v_unused_2357_; lean_object* v_unused_2358_; lean_object* v_unused_2359_; 
v_unused_2355_ = lean_ctor_get(v_r_2305_, 4);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_r_2305_, 3);
lean_dec(v_unused_2356_);
v_unused_2357_ = lean_ctor_get(v_r_2305_, 2);
lean_dec(v_unused_2357_);
v_unused_2358_ = lean_ctor_get(v_r_2305_, 1);
lean_dec(v_unused_2358_);
v_unused_2359_ = lean_ctor_get(v_r_2305_, 0);
lean_dec(v_unused_2359_);
v___x_2327_ = v_r_2305_;
v_isShared_2328_ = v_isSharedCheck_2354_;
goto v_resetjp_2326_;
}
else
{
lean_dec(v_r_2305_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2354_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___x_2342_; lean_object* v___y_2344_; 
v___x_2329_ = lean_nat_add(v___x_2299_, v_size_2301_);
lean_dec(v_size_2301_);
v___x_2330_ = lean_nat_add(v___x_2329_, v_size_2300_);
lean_dec(v___x_2329_);
v___x_2342_ = lean_nat_add(v___x_2299_, v_size_2317_);
if (lean_obj_tag(v_l_2321_) == 0)
{
lean_object* v_size_2352_; 
v_size_2352_ = lean_ctor_get(v_l_2321_, 0);
lean_inc(v_size_2352_);
v___y_2344_ = v_size_2352_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2353_; 
v___x_2353_ = lean_unsigned_to_nat(0u);
v___y_2344_ = v___x_2353_;
goto v___jp_2343_;
}
v___jp_2331_:
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2335_ = lean_nat_add(v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec(v___y_2333_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 4, v_r_2293_);
lean_ctor_set(v___x_2327_, 3, v_r_2322_);
lean_ctor_set(v___x_2327_, 2, v_v_2291_);
lean_ctor_set(v___x_2327_, 1, v_k_2290_);
lean_ctor_set(v___x_2327_, 0, v___x_2335_);
v___x_2337_ = v___x_2327_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_r_2322_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_r_2293_);
v___x_2337_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v___x_2337_);
lean_ctor_set(v___x_2315_, 3, v___y_2332_);
lean_ctor_set(v___x_2315_, 2, v_v_2320_);
lean_ctor_set(v___x_2315_, 1, v_k_2319_);
lean_ctor_set(v___x_2315_, 0, v___x_2330_);
v___x_2339_ = v___x_2315_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_k_2319_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_v_2320_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v___y_2332_);
lean_ctor_set(v_reuseFailAlloc_2340_, 4, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
v___jp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2345_ = lean_nat_add(v___x_2342_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec(v___x_2342_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 4, v_l_2321_);
lean_ctor_set(v___x_2295_, 3, v_l_2304_);
lean_ctor_set(v___x_2295_, 2, v_v_2303_);
lean_ctor_set(v___x_2295_, 1, v_k_2302_);
lean_ctor_set(v___x_2295_, 0, v___x_2345_);
v___x_2347_ = v___x_2295_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_k_2302_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_v_2303_);
lean_ctor_set(v_reuseFailAlloc_2351_, 3, v_l_2304_);
lean_ctor_set(v_reuseFailAlloc_2351_, 4, v_l_2321_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_nat_add(v___x_2299_, v_size_2300_);
if (lean_obj_tag(v_r_2322_) == 0)
{
lean_object* v_size_2349_; 
v_size_2349_ = lean_ctor_get(v_r_2322_, 0);
lean_inc(v_size_2349_);
v___y_2332_ = v___x_2347_;
v___y_2333_ = v___x_2348_;
v___y_2334_ = v_size_2349_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_unsigned_to_nat(0u);
v___y_2332_ = v___x_2347_;
v___y_2333_ = v___x_2348_;
v___y_2334_ = v___x_2350_;
goto v___jp_2331_;
}
}
}
}
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
lean_del_object(v___x_2295_);
v___x_2360_ = lean_nat_add(v___x_2299_, v_size_2301_);
lean_dec(v_size_2301_);
v___x_2361_ = lean_nat_add(v___x_2360_, v_size_2300_);
lean_dec(v___x_2360_);
v___x_2362_ = lean_nat_add(v___x_2299_, v_size_2300_);
v___x_2363_ = lean_nat_add(v___x_2362_, v_size_2318_);
lean_dec(v___x_2362_);
lean_inc_ref(v_r_2293_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v_r_2293_);
lean_ctor_set(v___x_2315_, 3, v_r_2305_);
lean_ctor_set(v___x_2315_, 2, v_v_2291_);
lean_ctor_set(v___x_2315_, 1, v_k_2290_);
lean_ctor_set(v___x_2315_, 0, v___x_2363_);
v___x_2365_ = v___x_2315_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2378_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2378_, 3, v_r_2305_);
lean_ctor_set(v_reuseFailAlloc_2378_, 4, v_r_2293_);
v___x_2365_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
v_isSharedCheck_2372_ = !lean_is_exclusive(v_r_2293_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; lean_object* v_unused_2374_; lean_object* v_unused_2375_; lean_object* v_unused_2376_; lean_object* v_unused_2377_; 
v_unused_2373_ = lean_ctor_get(v_r_2293_, 4);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_r_2293_, 3);
lean_dec(v_unused_2374_);
v_unused_2375_ = lean_ctor_get(v_r_2293_, 2);
lean_dec(v_unused_2375_);
v_unused_2376_ = lean_ctor_get(v_r_2293_, 1);
lean_dec(v_unused_2376_);
v_unused_2377_ = lean_ctor_get(v_r_2293_, 0);
lean_dec(v_unused_2377_);
v___x_2367_ = v_r_2293_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_dec(v_r_2293_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 4, v___x_2365_);
lean_ctor_set(v___x_2367_, 3, v_l_2304_);
lean_ctor_set(v___x_2367_, 2, v_v_2303_);
lean_ctor_set(v___x_2367_, 1, v_k_2302_);
lean_ctor_set(v___x_2367_, 0, v___x_2361_);
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_k_2302_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_v_2303_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_l_2304_);
lean_ctor_set(v_reuseFailAlloc_2371_, 4, v___x_2365_);
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
}
}
}
else
{
lean_object* v_l_2385_; 
v_l_2385_ = lean_ctor_get(v_impl_2298_, 3);
if (lean_obj_tag(v_l_2385_) == 0)
{
lean_object* v_r_2386_; lean_object* v_k_2387_; lean_object* v_v_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2399_; 
lean_inc_ref(v_l_2385_);
v_r_2386_ = lean_ctor_get(v_impl_2298_, 4);
v_k_2387_ = lean_ctor_get(v_impl_2298_, 1);
v_v_2388_ = lean_ctor_get(v_impl_2298_, 2);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_impl_2298_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; lean_object* v_unused_2401_; 
v_unused_2400_ = lean_ctor_get(v_impl_2298_, 3);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_impl_2298_, 0);
lean_dec(v_unused_2401_);
v___x_2390_ = v_impl_2298_;
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_r_2386_);
lean_inc(v_v_2388_);
lean_inc(v_k_2387_);
lean_dec(v_impl_2298_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2386_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 3, v_r_2386_);
lean_ctor_set(v___x_2390_, 2, v_v_2291_);
lean_ctor_set(v___x_2390_, 1, v_k_2290_);
lean_ctor_set(v___x_2390_, 0, v___x_2299_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_r_2386_);
lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_r_2386_);
v___x_2394_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2396_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 4, v___x_2394_);
lean_ctor_set(v___x_2295_, 3, v_l_2385_);
lean_ctor_set(v___x_2295_, 2, v_v_2388_);
lean_ctor_set(v___x_2295_, 1, v_k_2387_);
lean_ctor_set(v___x_2295_, 0, v___x_2392_);
v___x_2396_ = v___x_2295_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_2387_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_v_2388_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_l_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_object* v_r_2402_; 
v_r_2402_ = lean_ctor_get(v_impl_2298_, 4);
lean_inc(v_r_2402_);
if (lean_obj_tag(v_r_2402_) == 0)
{
lean_object* v_k_2403_; lean_object* v_v_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2427_; 
lean_inc(v_l_2385_);
v_k_2403_ = lean_ctor_get(v_impl_2298_, 1);
v_v_2404_ = lean_ctor_get(v_impl_2298_, 2);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_impl_2298_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; lean_object* v_unused_2429_; lean_object* v_unused_2430_; 
v_unused_2428_ = lean_ctor_get(v_impl_2298_, 4);
lean_dec(v_unused_2428_);
v_unused_2429_ = lean_ctor_get(v_impl_2298_, 3);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_impl_2298_, 0);
lean_dec(v_unused_2430_);
v___x_2406_ = v_impl_2298_;
v_isShared_2407_ = v_isSharedCheck_2427_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_v_2404_);
lean_inc(v_k_2403_);
lean_dec(v_impl_2298_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2427_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v_k_2408_; lean_object* v_v_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2423_; 
v_k_2408_ = lean_ctor_get(v_r_2402_, 1);
v_v_2409_ = lean_ctor_get(v_r_2402_, 2);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_r_2402_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; lean_object* v_unused_2425_; lean_object* v_unused_2426_; 
v_unused_2424_ = lean_ctor_get(v_r_2402_, 4);
lean_dec(v_unused_2424_);
v_unused_2425_ = lean_ctor_get(v_r_2402_, 3);
lean_dec(v_unused_2425_);
v_unused_2426_ = lean_ctor_get(v_r_2402_, 0);
lean_dec(v_unused_2426_);
v___x_2411_ = v_r_2402_;
v_isShared_2412_ = v_isSharedCheck_2423_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_v_2409_);
lean_inc(v_k_2408_);
lean_dec(v_r_2402_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2423_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = lean_unsigned_to_nat(3u);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 4, v_l_2385_);
lean_ctor_set(v___x_2411_, 3, v_l_2385_);
lean_ctor_set(v___x_2411_, 2, v_v_2404_);
lean_ctor_set(v___x_2411_, 1, v_k_2403_);
lean_ctor_set(v___x_2411_, 0, v___x_2299_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_k_2403_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_v_2404_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_l_2385_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v_l_2385_);
v___x_2415_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v_l_2385_);
lean_ctor_set(v___x_2406_, 2, v_v_2291_);
lean_ctor_set(v___x_2406_, 1, v_k_2290_);
lean_ctor_set(v___x_2406_, 0, v___x_2299_);
v___x_2417_ = v___x_2406_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2421_, 3, v_l_2385_);
lean_ctor_set(v_reuseFailAlloc_2421_, 4, v_l_2385_);
v___x_2417_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2419_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 4, v___x_2417_);
lean_ctor_set(v___x_2295_, 3, v___x_2415_);
lean_ctor_set(v___x_2295_, 2, v_v_2409_);
lean_ctor_set(v___x_2295_, 1, v_k_2408_);
lean_ctor_set(v___x_2295_, 0, v___x_2413_);
v___x_2419_ = v___x_2295_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_k_2408_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_v_2409_);
lean_ctor_set(v_reuseFailAlloc_2420_, 3, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2420_, 4, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
}
else
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2431_ = lean_unsigned_to_nat(2u);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 4, v_r_2402_);
lean_ctor_set(v___x_2295_, 3, v_impl_2298_);
lean_ctor_set(v___x_2295_, 0, v___x_2431_);
v___x_2433_ = v___x_2295_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v_impl_2298_);
lean_ctor_set(v_reuseFailAlloc_2434_, 4, v_r_2402_);
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
}
case 1:
{
lean_object* v___x_2436_; 
lean_dec(v_v_2291_);
lean_dec(v_k_2290_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 2, v_v_2287_);
lean_ctor_set(v___x_2295_, 1, v_k_2286_);
v___x_2436_ = v___x_2295_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_size_2289_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_l_2292_);
lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_r_2293_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
default: 
{
lean_object* v_impl_2438_; lean_object* v___x_2439_; 
lean_dec(v_size_2289_);
v_impl_2438_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2286_, v_v_2287_, v_r_2293_);
v___x_2439_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2292_) == 0)
{
lean_object* v_size_2440_; lean_object* v_size_2441_; lean_object* v_k_2442_; lean_object* v_v_2443_; lean_object* v_l_2444_; lean_object* v_r_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v_size_2440_ = lean_ctor_get(v_l_2292_, 0);
v_size_2441_ = lean_ctor_get(v_impl_2438_, 0);
v_k_2442_ = lean_ctor_get(v_impl_2438_, 1);
v_v_2443_ = lean_ctor_get(v_impl_2438_, 2);
v_l_2444_ = lean_ctor_get(v_impl_2438_, 3);
lean_inc(v_l_2444_);
v_r_2445_ = lean_ctor_get(v_impl_2438_, 4);
v___x_2446_ = lean_unsigned_to_nat(3u);
v___x_2447_ = lean_nat_mul(v___x_2446_, v_size_2440_);
v___x_2448_ = lean_nat_dec_lt(v___x_2447_, v_size_2441_);
lean_dec(v___x_2447_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
lean_dec(v_l_2444_);
v___x_2449_ = lean_nat_add(v___x_2439_, v_size_2440_);
v___x_2450_ = lean_nat_add(v___x_2449_, v_size_2441_);
lean_dec(v___x_2449_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 4, v_impl_2438_);
lean_ctor_set(v___x_2295_, 0, v___x_2450_);
v___x_2452_ = v___x_2295_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2453_, 3, v_l_2292_);
lean_ctor_set(v_reuseFailAlloc_2453_, 4, v_impl_2438_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
else
{
lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2517_; 
lean_inc(v_r_2445_);
lean_inc(v_v_2443_);
lean_inc(v_k_2442_);
lean_inc(v_size_2441_);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_impl_2438_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; lean_object* v_unused_2519_; lean_object* v_unused_2520_; lean_object* v_unused_2521_; lean_object* v_unused_2522_; 
v_unused_2518_ = lean_ctor_get(v_impl_2438_, 4);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v_impl_2438_, 3);
lean_dec(v_unused_2519_);
v_unused_2520_ = lean_ctor_get(v_impl_2438_, 2);
lean_dec(v_unused_2520_);
v_unused_2521_ = lean_ctor_get(v_impl_2438_, 1);
lean_dec(v_unused_2521_);
v_unused_2522_ = lean_ctor_get(v_impl_2438_, 0);
lean_dec(v_unused_2522_);
v___x_2455_ = v_impl_2438_;
v_isShared_2456_ = v_isSharedCheck_2517_;
goto v_resetjp_2454_;
}
else
{
lean_dec(v_impl_2438_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2517_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_size_2457_; lean_object* v_k_2458_; lean_object* v_v_2459_; lean_object* v_l_2460_; lean_object* v_r_2461_; lean_object* v_size_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v_size_2457_ = lean_ctor_get(v_l_2444_, 0);
v_k_2458_ = lean_ctor_get(v_l_2444_, 1);
v_v_2459_ = lean_ctor_get(v_l_2444_, 2);
v_l_2460_ = lean_ctor_get(v_l_2444_, 3);
v_r_2461_ = lean_ctor_get(v_l_2444_, 4);
v_size_2462_ = lean_ctor_get(v_r_2445_, 0);
v___x_2463_ = lean_unsigned_to_nat(2u);
v___x_2464_ = lean_nat_mul(v___x_2463_, v_size_2462_);
v___x_2465_ = lean_nat_dec_lt(v_size_2457_, v___x_2464_);
lean_dec(v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2493_; 
lean_inc(v_r_2461_);
lean_inc(v_l_2460_);
lean_inc(v_v_2459_);
lean_inc(v_k_2458_);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_l_2444_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; lean_object* v_unused_2495_; lean_object* v_unused_2496_; lean_object* v_unused_2497_; lean_object* v_unused_2498_; 
v_unused_2494_ = lean_ctor_get(v_l_2444_, 4);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_l_2444_, 3);
lean_dec(v_unused_2495_);
v_unused_2496_ = lean_ctor_get(v_l_2444_, 2);
lean_dec(v_unused_2496_);
v_unused_2497_ = lean_ctor_get(v_l_2444_, 1);
lean_dec(v_unused_2497_);
v_unused_2498_ = lean_ctor_get(v_l_2444_, 0);
lean_dec(v_unused_2498_);
v___x_2467_ = v_l_2444_;
v_isShared_2468_ = v_isSharedCheck_2493_;
goto v_resetjp_2466_;
}
else
{
lean_dec(v_l_2444_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2493_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2483_; 
v___x_2469_ = lean_nat_add(v___x_2439_, v_size_2440_);
v___x_2470_ = lean_nat_add(v___x_2469_, v_size_2441_);
lean_dec(v_size_2441_);
if (lean_obj_tag(v_l_2460_) == 0)
{
lean_object* v_size_2491_; 
v_size_2491_ = lean_ctor_get(v_l_2460_, 0);
lean_inc(v_size_2491_);
v___y_2483_ = v_size_2491_;
goto v___jp_2482_;
}
else
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_unsigned_to_nat(0u);
v___y_2483_ = v___x_2492_;
goto v___jp_2482_;
}
v___jp_2471_:
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = lean_nat_add(v___y_2472_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec(v___y_2472_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 4, v_r_2445_);
lean_ctor_set(v___x_2467_, 3, v_r_2461_);
lean_ctor_set(v___x_2467_, 2, v_v_2443_);
lean_ctor_set(v___x_2467_, 1, v_k_2442_);
lean_ctor_set(v___x_2467_, 0, v___x_2475_);
v___x_2477_ = v___x_2467_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_k_2442_);
lean_ctor_set(v_reuseFailAlloc_2481_, 2, v_v_2443_);
lean_ctor_set(v_reuseFailAlloc_2481_, 3, v_r_2461_);
lean_ctor_set(v_reuseFailAlloc_2481_, 4, v_r_2445_);
v___x_2477_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2479_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 4, v___x_2477_);
lean_ctor_set(v___x_2455_, 3, v___y_2473_);
lean_ctor_set(v___x_2455_, 2, v_v_2459_);
lean_ctor_set(v___x_2455_, 1, v_k_2458_);
lean_ctor_set(v___x_2455_, 0, v___x_2470_);
v___x_2479_ = v___x_2455_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v___y_2473_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
v___jp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2484_ = lean_nat_add(v___x_2469_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec(v___x_2469_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 4, v_l_2460_);
lean_ctor_set(v___x_2295_, 0, v___x_2484_);
v___x_2486_ = v___x_2295_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_l_2292_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v_l_2460_);
v___x_2486_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_nat_add(v___x_2439_, v_size_2462_);
if (lean_obj_tag(v_r_2461_) == 0)
{
lean_object* v_size_2488_; 
v_size_2488_ = lean_ctor_get(v_r_2461_, 0);
lean_inc(v_size_2488_);
v___y_2472_ = v___x_2487_;
v___y_2473_ = v___x_2486_;
v___y_2474_ = v_size_2488_;
goto v___jp_2471_;
}
else
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_unsigned_to_nat(0u);
v___y_2472_ = v___x_2487_;
v___y_2473_ = v___x_2486_;
v___y_2474_ = v___x_2489_;
goto v___jp_2471_;
}
}
}
}
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
lean_del_object(v___x_2295_);
v___x_2499_ = lean_nat_add(v___x_2439_, v_size_2440_);
v___x_2500_ = lean_nat_add(v___x_2499_, v_size_2441_);
lean_dec(v_size_2441_);
v___x_2501_ = lean_nat_add(v___x_2499_, v_size_2457_);
lean_dec(v___x_2499_);
lean_inc_ref(v_l_2292_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 4, v_l_2444_);
lean_ctor_set(v___x_2455_, 3, v_l_2292_);
lean_ctor_set(v___x_2455_, 2, v_v_2291_);
lean_ctor_set(v___x_2455_, 1, v_k_2290_);
lean_ctor_set(v___x_2455_, 0, v___x_2501_);
v___x_2503_ = v___x_2455_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v_l_2292_);
lean_ctor_set(v_reuseFailAlloc_2516_, 4, v_l_2444_);
v___x_2503_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
v_isSharedCheck_2510_ = !lean_is_exclusive(v_l_2292_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; lean_object* v_unused_2512_; lean_object* v_unused_2513_; lean_object* v_unused_2514_; lean_object* v_unused_2515_; 
v_unused_2511_ = lean_ctor_get(v_l_2292_, 4);
lean_dec(v_unused_2511_);
v_unused_2512_ = lean_ctor_get(v_l_2292_, 3);
lean_dec(v_unused_2512_);
v_unused_2513_ = lean_ctor_get(v_l_2292_, 2);
lean_dec(v_unused_2513_);
v_unused_2514_ = lean_ctor_get(v_l_2292_, 1);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v_l_2292_, 0);
lean_dec(v_unused_2515_);
v___x_2505_ = v_l_2292_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_dec(v_l_2292_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 4, v_r_2445_);
lean_ctor_set(v___x_2505_, 3, v___x_2503_);
lean_ctor_set(v___x_2505_, 2, v_v_2443_);
lean_ctor_set(v___x_2505_, 1, v_k_2442_);
lean_ctor_set(v___x_2505_, 0, v___x_2500_);
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_k_2442_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_v_2443_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_r_2445_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2523_; 
v_l_2523_ = lean_ctor_get(v_impl_2438_, 3);
lean_inc(v_l_2523_);
if (lean_obj_tag(v_l_2523_) == 0)
{
lean_object* v_r_2524_; lean_object* v_k_2525_; lean_object* v_v_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2549_; 
v_r_2524_ = lean_ctor_get(v_impl_2438_, 4);
v_k_2525_ = lean_ctor_get(v_impl_2438_, 1);
v_v_2526_ = lean_ctor_get(v_impl_2438_, 2);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_impl_2438_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; lean_object* v_unused_2551_; 
v_unused_2550_ = lean_ctor_get(v_impl_2438_, 3);
lean_dec(v_unused_2550_);
v_unused_2551_ = lean_ctor_get(v_impl_2438_, 0);
lean_dec(v_unused_2551_);
v___x_2528_ = v_impl_2438_;
v_isShared_2529_ = v_isSharedCheck_2549_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_r_2524_);
lean_inc(v_v_2526_);
lean_inc(v_k_2525_);
lean_dec(v_impl_2438_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2549_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_k_2530_; lean_object* v_v_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2545_; 
v_k_2530_ = lean_ctor_get(v_l_2523_, 1);
v_v_2531_ = lean_ctor_get(v_l_2523_, 2);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_l_2523_);
if (v_isSharedCheck_2545_ == 0)
{
lean_object* v_unused_2546_; lean_object* v_unused_2547_; lean_object* v_unused_2548_; 
v_unused_2546_ = lean_ctor_get(v_l_2523_, 4);
lean_dec(v_unused_2546_);
v_unused_2547_ = lean_ctor_get(v_l_2523_, 3);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v_l_2523_, 0);
lean_dec(v_unused_2548_);
v___x_2533_ = v_l_2523_;
v_isShared_2534_ = v_isSharedCheck_2545_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_v_2531_);
lean_inc(v_k_2530_);
lean_dec(v_l_2523_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2545_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2524_, 2);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 4, v_r_2524_);
lean_ctor_set(v___x_2533_, 3, v_r_2524_);
lean_ctor_set(v___x_2533_, 2, v_v_2291_);
lean_ctor_set(v___x_2533_, 1, v_k_2290_);
lean_ctor_set(v___x_2533_, 0, v___x_2439_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v_r_2524_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v_r_2524_);
v___x_2537_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
lean_inc(v_r_2524_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 3, v_r_2524_);
lean_ctor_set(v___x_2528_, 0, v___x_2439_);
v___x_2539_ = v___x_2528_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_k_2525_);
lean_ctor_set(v_reuseFailAlloc_2543_, 2, v_v_2526_);
lean_ctor_set(v_reuseFailAlloc_2543_, 3, v_r_2524_);
lean_ctor_set(v_reuseFailAlloc_2543_, 4, v_r_2524_);
v___x_2539_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2541_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 4, v___x_2539_);
lean_ctor_set(v___x_2295_, 3, v___x_2537_);
lean_ctor_set(v___x_2295_, 2, v_v_2531_);
lean_ctor_set(v___x_2295_, 1, v_k_2530_);
lean_ctor_set(v___x_2295_, 0, v___x_2535_);
v___x_2541_ = v___x_2295_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_k_2530_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_v_2531_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
}
else
{
lean_object* v_r_2552_; 
v_r_2552_ = lean_ctor_get(v_impl_2438_, 4);
lean_inc(v_r_2552_);
if (lean_obj_tag(v_r_2552_) == 0)
{
lean_object* v_k_2553_; lean_object* v_v_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2565_; 
v_k_2553_ = lean_ctor_get(v_impl_2438_, 1);
v_v_2554_ = lean_ctor_get(v_impl_2438_, 2);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_impl_2438_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; lean_object* v_unused_2567_; lean_object* v_unused_2568_; 
v_unused_2566_ = lean_ctor_get(v_impl_2438_, 4);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_impl_2438_, 3);
lean_dec(v_unused_2567_);
v_unused_2568_ = lean_ctor_get(v_impl_2438_, 0);
lean_dec(v_unused_2568_);
v___x_2556_ = v_impl_2438_;
v_isShared_2557_ = v_isSharedCheck_2565_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_v_2554_);
lean_inc(v_k_2553_);
lean_dec(v_impl_2438_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2565_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2558_ = lean_unsigned_to_nat(3u);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 4, v_l_2523_);
lean_ctor_set(v___x_2556_, 2, v_v_2291_);
lean_ctor_set(v___x_2556_, 1, v_k_2290_);
lean_ctor_set(v___x_2556_, 0, v___x_2439_);
v___x_2560_ = v___x_2556_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v_l_2523_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v_l_2523_);
v___x_2560_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2562_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 4, v_r_2552_);
lean_ctor_set(v___x_2295_, 3, v___x_2560_);
lean_ctor_set(v___x_2295_, 2, v_v_2554_);
lean_ctor_set(v___x_2295_, 1, v_k_2553_);
lean_ctor_set(v___x_2295_, 0, v___x_2558_);
v___x_2562_ = v___x_2295_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_k_2553_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_v_2554_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_r_2552_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_unsigned_to_nat(2u);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 4, v_impl_2438_);
lean_ctor_set(v___x_2295_, 3, v_r_2552_);
lean_ctor_set(v___x_2295_, 0, v___x_2569_);
v___x_2571_ = v___x_2295_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_r_2552_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_impl_2438_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
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
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_unsigned_to_nat(1u);
v___x_2575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v_k_2286_);
lean_ctor_set(v___x_2575_, 2, v_v_2287_);
lean_ctor_set(v___x_2575_, 3, v_t_2288_);
lean_ctor_set(v___x_2575_, 4, v_t_2288_);
return v___x_2575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t v_sz_2576_, size_t v_i_2577_, lean_object* v_bs_2578_){
_start:
{
uint8_t v___x_2579_; 
v___x_2579_ = lean_usize_dec_lt(v_i_2577_, v_sz_2576_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_bs_2578_);
return v___x_2580_;
}
else
{
lean_object* v_v_2581_; lean_object* v___x_2582_; lean_object* v_bs_x27_2583_; lean_object* v_a_2585_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2656_; 
v_v_2581_ = lean_array_uget(v_bs_2578_, v_i_2577_);
v___x_2582_ = lean_unsigned_to_nat(0u);
v_bs_x27_2583_ = lean_array_uset(v_bs_2578_, v_i_2577_, v___x_2582_);
v___x_2590_ = lean_array_get_size(v_v_2581_);
v___x_2591_ = lean_unsigned_to_nat(4u);
v___x_2656_ = lean_nat_dec_eq(v___x_2590_, v___x_2591_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = lean_unsigned_to_nat(5u);
v___x_2658_ = lean_nat_dec_eq(v___x_2590_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_dec_ref(v_bs_x27_2583_);
lean_dec(v_v_2581_);
v___x_2659_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2660_ = l_Nat_reprFast(v___x_2590_);
v___x_2661_ = lean_string_append(v___x_2659_, v___x_2660_);
lean_dec_ref(v___x_2660_);
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
return v___x_2662_;
}
else
{
goto v___jp_2592_;
}
}
else
{
goto v___jp_2592_;
}
v___jp_2584_:
{
size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = ((size_t)1ULL);
v___x_2587_ = lean_usize_add(v_i_2577_, v___x_2586_);
v___x_2588_ = lean_array_uset(v_bs_x27_2583_, v_i_2577_, v_a_2585_);
v_i_2577_ = v___x_2587_;
v_bs_2578_ = v___x_2588_;
goto _start;
}
v___jp_2592_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_array_fget_borrowed(v_v_2581_, v___x_2582_);
lean_inc(v___x_2593_);
v___x_2594_ = l_Lean_Json_getNat_x3f(v___x_2593_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v_bs_x27_2583_);
lean_dec(v_v_2581_);
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_a_2603_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2604_ = lean_unsigned_to_nat(1u);
v___x_2605_ = lean_array_fget_borrowed(v_v_2581_, v___x_2604_);
lean_inc(v___x_2605_);
v___x_2606_ = l_Lean_Json_getNat_x3f(v___x_2605_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_a_2603_);
lean_dec_ref(v_bs_x27_2583_);
lean_dec(v_v_2581_);
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_a_2615_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2616_ = lean_unsigned_to_nat(2u);
v___x_2617_ = lean_array_fget_borrowed(v_v_2581_, v___x_2616_);
lean_inc(v___x_2617_);
v___x_2618_ = l_Lean_Json_getNat_x3f(v___x_2617_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_a_2615_);
lean_dec(v_a_2603_);
lean_dec_ref(v_bs_x27_2583_);
lean_dec(v_v_2581_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_a_2627_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2628_ = lean_unsigned_to_nat(3u);
v___x_2629_ = lean_array_fget_borrowed(v_v_2581_, v___x_2628_);
lean_inc(v___x_2629_);
v___x_2630_ = l_Lean_Json_getNat_x3f(v___x_2629_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec(v_a_2627_);
lean_dec(v_a_2615_);
lean_dec(v_a_2603_);
lean_dec_ref(v_bs_x27_2583_);
lean_dec(v_v_2581_);
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v_a_2639_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2630_, 1);
v___x_2640_ = lean_unsigned_to_nat(5u);
v___x_2641_ = lean_nat_dec_eq(v___x_2590_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
lean_dec(v_v_2581_);
v___x_2642_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2643_, 0, v_a_2603_);
lean_ctor_set(v___x_2643_, 1, v_a_2615_);
lean_ctor_set(v___x_2643_, 2, v_a_2627_);
lean_ctor_set(v___x_2643_, 3, v_a_2639_);
lean_ctor_set(v___x_2643_, 4, v___x_2642_);
v_a_2585_ = v___x_2643_;
goto v___jp_2584_;
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = lean_array_fget(v_v_2581_, v___x_2591_);
lean_dec(v_v_2581_);
v___x_2645_ = l_Lean_Json_getStr_x3f(v___x_2644_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_a_2639_);
lean_dec(v_a_2627_);
lean_dec(v_a_2615_);
lean_dec(v_a_2603_);
lean_dec_ref(v_bs_x27_2583_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2645_, 1);
v___x_2655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2655_, 0, v_a_2603_);
lean_ctor_set(v___x_2655_, 1, v_a_2615_);
lean_ctor_set(v___x_2655_, 2, v_a_2627_);
lean_ctor_set(v___x_2655_, 3, v_a_2639_);
lean_ctor_set(v___x_2655_, 4, v_a_2654_);
v_a_2585_ = v___x_2655_;
goto v___jp_2584_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2663_, lean_object* v_i_2664_, lean_object* v_bs_2665_){
_start:
{
size_t v_sz_boxed_2666_; size_t v_i_boxed_2667_; lean_object* v_res_2668_; 
v_sz_boxed_2666_ = lean_unbox_usize(v_sz_2663_);
lean_dec(v_sz_2663_);
v_i_boxed_2667_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_res_2668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2666_, v_i_boxed_2667_, v_bs_2665_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2669_, size_t v_i_2670_, lean_object* v_bs_2671_){
_start:
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_lt(v_i_2670_, v_sz_2669_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_bs_2671_);
return v___x_2673_;
}
else
{
lean_object* v_v_2674_; lean_object* v___x_2675_; 
v_v_2674_ = lean_array_uget_borrowed(v_bs_2671_, v_i_2670_);
lean_inc(v_v_2674_);
v___x_2675_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2674_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref(v_bs_2671_);
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2685_; lean_object* v_bs_x27_2686_; size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
v_a_2684_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2685_ = lean_unsigned_to_nat(0u);
v_bs_x27_2686_ = lean_array_uset(v_bs_2671_, v_i_2670_, v___x_2685_);
v___x_2687_ = ((size_t)1ULL);
v___x_2688_ = lean_usize_add(v_i_2670_, v___x_2687_);
v___x_2689_ = lean_array_uset(v_bs_x27_2686_, v_i_2670_, v_a_2684_);
v_i_2670_ = v___x_2688_;
v_bs_2671_ = v___x_2689_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2691_, lean_object* v_i_2692_, lean_object* v_bs_2693_){
_start:
{
size_t v_sz_boxed_2694_; size_t v_i_boxed_2695_; lean_object* v_res_2696_; 
v_sz_boxed_2694_ = lean_unbox_usize(v_sz_2691_);
lean_dec(v_sz_2691_);
v_i_boxed_2695_ = lean_unbox_usize(v_i_2692_);
lean_dec(v_i_2692_);
v_res_2696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2694_, v_i_boxed_2695_, v_bs_2693_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2697_){
_start:
{
if (lean_obj_tag(v_x_2697_) == 4)
{
lean_object* v_elems_2698_; size_t v_sz_2699_; size_t v___x_2700_; lean_object* v___x_2701_; 
v_elems_2698_ = lean_ctor_get(v_x_2697_, 0);
lean_inc_ref(v_elems_2698_);
lean_dec_ref_known(v_x_2697_, 1);
v_sz_2699_ = lean_array_size(v_elems_2698_);
v___x_2700_ = ((size_t)0ULL);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2699_, v___x_2700_, v_elems_2698_);
return v___x_2701_;
}
else
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2702_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2703_ = lean_unsigned_to_nat(80u);
v___x_2704_ = l_Lean_Json_pretty(v_x_2697_, v___x_2703_);
v___x_2705_ = lean_string_append(v___x_2702_, v___x_2704_);
lean_dec_ref(v___x_2704_);
v___x_2706_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_2707_ = lean_string_append(v___x_2705_, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2709_, lean_object* v_k_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = l_Lean_Json_getObjValD(v_j_2709_, v_k_2710_);
v___x_2712_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2713_, lean_object* v_k_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2713_, v_k_2714_);
lean_dec_ref(v_k_2714_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4___redArg(lean_object* v_upperBound_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_b_2719_){
_start:
{
uint8_t v___x_2720_; 
v___x_2720_ = lean_nat_dec_lt(v_a_2718_, v_upperBound_2716_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; 
lean_dec(v_a_2718_);
v___x_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_b_2719_);
return v___x_2721_;
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2722_ = lean_unsigned_to_nat(2u);
v___x_2723_ = lean_nat_mul(v___x_2722_, v_a_2718_);
v___x_2724_ = lean_array_fget_borrowed(v_a_2717_, v___x_2723_);
lean_inc(v___x_2724_);
v___x_2725_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v___x_2724_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v___x_2723_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v_definition_x3f_2739_; lean_object* v_a_2768_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2734_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2735_ = lean_unsigned_to_nat(1u);
v___x_2736_ = lean_nat_add(v___x_2723_, v___x_2735_);
lean_dec(v___x_2723_);
v___x_2737_ = lean_array_fget_borrowed(v_a_2717_, v___x_2736_);
lean_dec(v___x_2736_);
v___x_2770_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v___x_2737_);
v___x_2771_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v___x_2737_, v___x_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_a_2734_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2860_; 
v_a_2780_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2782_ = v___x_2771_;
v_isShared_2783_ = v_isSharedCheck_2860_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2771_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2860_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
if (lean_obj_tag(v_a_2780_) == 0)
{
lean_object* v___x_2784_; 
lean_del_object(v___x_2782_);
v___x_2784_ = lean_box(0);
v_definition_x3f_2739_ = v___x_2784_;
goto v___jp_2738_;
}
else
{
lean_object* v_val_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2851_; 
v_val_2785_ = lean_ctor_get(v_a_2780_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v_a_2780_, 1);
v___x_2786_ = lean_unsigned_to_nat(0u);
v___x_2787_ = lean_array_get_size(v_val_2785_);
v___x_2788_ = lean_unsigned_to_nat(4u);
v___x_2851_ = lean_nat_dec_eq(v___x_2787_, v___x_2788_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2852_ = lean_unsigned_to_nat(5u);
v___x_2853_ = lean_nat_dec_eq(v___x_2787_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2858_; 
lean_dec(v_val_2785_);
lean_dec(v_a_2734_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v___x_2854_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2855_ = l_Nat_reprFast(v___x_2787_);
v___x_2856_ = lean_string_append(v___x_2854_, v___x_2855_);
lean_dec_ref(v___x_2855_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2856_);
v___x_2858_ = v___x_2782_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
else
{
lean_del_object(v___x_2782_);
goto v___jp_2789_;
}
}
else
{
lean_del_object(v___x_2782_);
goto v___jp_2789_;
}
v___jp_2789_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_array_fget_borrowed(v_val_2785_, v___x_2786_);
lean_inc(v___x_2790_);
v___x_2791_ = l_Lean_Json_getNat_x3f(v___x_2790_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_val_2785_);
lean_dec(v_a_2734_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_a_2800_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2801_ = lean_array_fget_borrowed(v_val_2785_, v___x_2735_);
lean_inc(v___x_2801_);
v___x_2802_ = l_Lean_Json_getNat_x3f(v___x_2801_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_a_2800_);
lean_dec(v_val_2785_);
lean_dec(v_a_2734_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_a_2811_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2812_ = lean_array_fget_borrowed(v_val_2785_, v___x_2722_);
lean_inc(v___x_2812_);
v___x_2813_ = l_Lean_Json_getNat_x3f(v___x_2812_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec(v_a_2811_);
lean_dec(v_a_2800_);
lean_dec(v_val_2785_);
lean_dec(v_a_2734_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2813_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2813_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_a_2822_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2823_ = lean_unsigned_to_nat(3u);
v___x_2824_ = lean_array_fget_borrowed(v_val_2785_, v___x_2823_);
lean_inc(v___x_2824_);
v___x_2825_ = l_Lean_Json_getNat_x3f(v___x_2824_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_a_2822_);
lean_dec(v_a_2811_);
lean_dec(v_a_2800_);
lean_dec(v_val_2785_);
lean_dec(v_a_2734_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v_a_2834_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2835_ = lean_unsigned_to_nat(5u);
v___x_2836_ = lean_nat_dec_eq(v___x_2787_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
lean_dec(v_val_2785_);
v___x_2837_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2838_, 0, v_a_2800_);
lean_ctor_set(v___x_2838_, 1, v_a_2811_);
lean_ctor_set(v___x_2838_, 2, v_a_2822_);
lean_ctor_set(v___x_2838_, 3, v_a_2834_);
lean_ctor_set(v___x_2838_, 4, v___x_2837_);
v_a_2768_ = v___x_2838_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_array_fget(v_val_2785_, v___x_2788_);
lean_dec(v_val_2785_);
v___x_2840_ = l_Lean_Json_getStr_x3f(v___x_2839_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v_a_2834_);
lean_dec(v_a_2822_);
lean_dec(v_a_2811_);
lean_dec(v_a_2800_);
lean_dec(v_a_2734_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2840_, 1);
v___x_2850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2850_, 0, v_a_2800_);
lean_ctor_set(v___x_2850_, 1, v_a_2811_);
lean_ctor_set(v___x_2850_, 2, v_a_2822_);
lean_ctor_set(v___x_2850_, 3, v_a_2834_);
lean_ctor_set(v___x_2850_, 4, v_a_2849_);
v_a_2768_ = v___x_2850_;
goto v___jp_2767_;
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
v___jp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
lean_inc(v___x_2737_);
v___x_2741_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v___x_2737_, v___x_2740_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_definition_x3f_2739_);
lean_dec(v_a_2734_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
else
{
lean_object* v_a_2750_; size_t v_sz_2751_; size_t v___x_2752_; lean_object* v___x_2753_; 
v_a_2750_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2741_, 1);
v_sz_2751_ = lean_array_size(v_a_2750_);
v___x_2752_ = ((size_t)0ULL);
v___x_2753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2751_, v___x_2752_, v_a_2750_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_definition_x3f_2739_);
lean_dec(v_a_2734_);
lean_dec(v_b_2719_);
lean_dec(v_a_2718_);
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v_a_2762_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2753_, 1);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_definition_x3f_2739_);
lean_ctor_set(v___x_2763_, 1, v_a_2762_);
v___x_2764_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2734_, v___x_2763_, v_b_2719_);
v___x_2765_ = lean_nat_add(v_a_2718_, v___x_2735_);
lean_dec(v_a_2718_);
v_a_2718_ = v___x_2765_;
v_b_2719_ = v___x_2764_;
goto _start;
}
}
}
v___jp_2767_:
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_a_2768_);
v_definition_x3f_2739_ = v___x_2769_;
goto v___jp_2738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4___redArg___boxed(lean_object* v_upperBound_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_b_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4___redArg(v_upperBound_2861_, v_a_2862_, v_a_2863_, v_b_2864_);
lean_dec_ref(v_a_2862_);
lean_dec(v_upperBound_2861_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_2866_, lean_object* v_k_2867_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = l_Lean_Json_getObjValD(v_j_2866_, v_k_2867_);
v___x_2869_ = l_Lean_Json_getArr_x3f(v___x_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v_a_2878_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2879_ = lean_array_get_size(v_a_2878_);
v___x_2880_ = lean_unsigned_to_nat(2u);
v___x_2881_ = lean_nat_mod(v___x_2879_, v___x_2880_);
v___x_2882_ = lean_unsigned_to_nat(0u);
v___x_2883_ = lean_nat_dec_eq(v___x_2881_, v___x_2882_);
lean_dec(v___x_2881_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; 
lean_dec(v_a_2878_);
v___x_2884_ = ((lean_object*)(l_Lean_Lsp_instFromJsonModuleRefs___lam__0___closed__1));
return v___x_2884_;
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2885_ = lean_box(1);
v___x_2886_ = lean_unsigned_to_nat(1u);
v___x_2887_ = lean_nat_shiftr(v___x_2879_, v___x_2886_);
v___x_2888_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4___redArg(v___x_2887_, v_a_2878_, v___x_2882_, v___x_2885_);
lean_dec(v_a_2878_);
lean_dec(v___x_2887_);
return v___x_2888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_2889_, lean_object* v_k_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_2889_, v_k_2890_);
lean_dec_ref(v_k_2890_);
return v_res_2891_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = 1;
v___x_2898_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_2899_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2898_, v___x_2897_);
return v___x_2899_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_2901_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_2902_ = lean_string_append(v___x_2901_, v___x_2900_);
return v___x_2902_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_2904_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_2905_ = lean_string_append(v___x_2904_, v___x_2903_);
return v___x_2905_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2906_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_2907_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_2908_ = lean_string_append(v___x_2907_, v___x_2906_);
return v___x_2908_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = 1;
v___x_2913_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_2914_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2913_, v___x_2912_);
return v___x_2914_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_2916_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_2917_ = lean_string_append(v___x_2916_, v___x_2915_);
return v___x_2917_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2918_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_2919_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_2920_ = lean_string_append(v___x_2919_, v___x_2918_);
return v___x_2920_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = 1;
v___x_2925_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_2926_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2925_, v___x_2924_);
return v___x_2926_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_2928_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_2929_ = lean_string_append(v___x_2928_, v___x_2927_);
return v___x_2929_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_2931_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_2932_ = lean_string_append(v___x_2931_, v___x_2930_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_2933_){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_2933_);
v___x_2935_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_2933_, v___x_2934_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_json_2933_);
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2945_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2945_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2940_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_2941_ = lean_string_append(v___x_2940_, v_a_2936_);
lean_dec(v_a_2936_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2941_);
v___x_2943_ = v___x_2938_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_a_2946_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2947_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_2933_);
v___x_2948_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_2933_, v___x_2947_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2958_; 
lean_dec(v_a_2946_);
lean_dec(v_json_2933_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2958_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2958_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2953_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
v___x_2954_ = lean_string_append(v___x_2953_, v_a_2949_);
lean_dec(v_a_2949_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2954_);
v___x_2956_ = v___x_2951_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_a_2959_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2960_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_2961_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_2933_, v___x_2960_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v_a_2959_);
lean_dec(v_a_2946_);
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2971_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2971_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2966_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
v___x_2967_ = lean_string_append(v___x_2966_, v_a_2962_);
lean_dec(v_a_2962_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2967_);
v___x_2969_ = v___x_2964_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2980_; 
v_a_2972_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2974_ = v___x_2961_;
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2961_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2976_, 0, v_a_2946_);
lean_ctor_set(v___x_2976_, 1, v_a_2959_);
lean_ctor_set(v___x_2976_, 2, v_a_2972_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_2981_, lean_object* v_k_2982_, lean_object* v_v_2983_, lean_object* v_t_2984_, lean_object* v_hl_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2982_, v_v_2983_, v_t_2984_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_upperBound_2987_, lean_object* v_a_2988_, lean_object* v_inst_2989_, lean_object* v_R_2990_, lean_object* v_a_2991_, lean_object* v_b_2992_, lean_object* v_c_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4___redArg(v_upperBound_2987_, v_a_2988_, v_a_2991_, v_b_2992_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4___boxed(lean_object* v_upperBound_2995_, lean_object* v_a_2996_, lean_object* v_inst_2997_, lean_object* v_R_2998_, lean_object* v_a_2999_, lean_object* v_b_3000_, lean_object* v_c_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_upperBound_2995_, v_a_2996_, v_inst_2997_, v_R_2998_, v_a_2999_, v_b_3000_, v_c_3001_);
lean_dec_ref(v_a_2996_);
lean_dec(v_upperBound_2995_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3003_, lean_object* v_k_3004_, lean_object* v_v_3005_, lean_object* v_t_3006_, lean_object* v_hl_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3004_, v_v_3005_, v_t_3006_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__8(size_t v_sz_3011_, size_t v_i_3012_, lean_object* v_bs_3013_){
_start:
{
uint8_t v___x_3014_; 
v___x_3014_ = lean_usize_dec_lt(v_i_3012_, v_sz_3011_);
if (v___x_3014_ == 0)
{
return v_bs_3013_;
}
else
{
lean_object* v_v_3015_; lean_object* v___x_3016_; lean_object* v_bs_x27_3017_; size_t v___x_3018_; size_t v___x_3019_; lean_object* v___x_3020_; 
v_v_3015_ = lean_array_uget(v_bs_3013_, v_i_3012_);
v___x_3016_ = lean_unsigned_to_nat(0u);
v_bs_x27_3017_ = lean_array_uset(v_bs_3013_, v_i_3012_, v___x_3016_);
v___x_3018_ = ((size_t)1ULL);
v___x_3019_ = lean_usize_add(v_i_3012_, v___x_3018_);
v___x_3020_ = lean_array_uset(v_bs_x27_3017_, v_i_3012_, v_v_3015_);
v_i_3012_ = v___x_3019_;
v_bs_3013_ = v___x_3020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__8___boxed(lean_object* v_sz_3022_, lean_object* v_i_3023_, lean_object* v_bs_3024_){
_start:
{
size_t v_sz_boxed_3025_; size_t v_i_boxed_3026_; lean_object* v_res_3027_; 
v_sz_boxed_3025_ = lean_unbox_usize(v_sz_3022_);
lean_dec(v_sz_3022_);
v_i_boxed_3026_ = lean_unbox_usize(v_i_3023_);
lean_dec(v_i_3023_);
v_res_3027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__8(v_sz_boxed_3025_, v_i_boxed_3026_, v_bs_3024_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3028_){
_start:
{
size_t v_sz_3029_; size_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_sz_3029_ = lean_array_size(v_a_3028_);
v___x_3030_ = ((size_t)0ULL);
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__8(v_sz_3029_, v___x_3030_, v_a_3028_);
v___x_3032_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3033_){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_array_mk(v_a_3033_);
v___x_3035_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3036_){
_start:
{
if (lean_obj_tag(v_x_3036_) == 0)
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_box(0);
return v___x_3037_;
}
else
{
lean_object* v_val_3038_; lean_object* v___x_3039_; 
v_val_3038_ = lean_ctor_get(v_x_3036_, 0);
lean_inc(v_val_3038_);
lean_dec_ref_known(v_x_3036_, 1);
v___x_3039_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3038_);
return v___x_3039_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
if (lean_obj_tag(v_a_3040_) == 0)
{
lean_object* v___x_3042_; 
v___x_3042_ = l_List_reverse___redArg(v_a_3041_);
return v___x_3042_;
}
else
{
lean_object* v_head_3043_; lean_object* v_tail_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3054_; 
v_head_3043_ = lean_ctor_get(v_a_3040_, 0);
v_tail_3044_ = lean_ctor_get(v_a_3040_, 1);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_a_3040_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3046_ = v_a_3040_;
v_isShared_3047_ = v_isSharedCheck_3054_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_tail_3044_);
lean_inc(v_head_3043_);
lean_dec(v_a_3040_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3054_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3048_ = l_Lean_JsonNumber_fromNat(v_head_3043_);
v___x_3049_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 1, v_a_3041_);
lean_ctor_set(v___x_3046_, 0, v___x_3049_);
v___x_3051_ = v___x_3046_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_a_3041_);
v___x_3051_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
v_a_3040_ = v_tail_3044_;
v_a_3041_ = v___x_3051_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3055_, size_t v_i_3056_, lean_object* v_bs_3057_){
_start:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_usize_dec_lt(v_i_3056_, v_sz_3055_);
if (v___x_3058_ == 0)
{
return v_bs_3057_;
}
else
{
lean_object* v_v_3059_; lean_object* v_startPosLine_3060_; lean_object* v_startPosCharacter_3061_; lean_object* v_endPosLine_3062_; lean_object* v_endPosCharacter_3063_; lean_object* v___x_3064_; lean_object* v_bs_x27_3065_; lean_object* v___y_3067_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v_range_3077_; lean_object* v___x_3078_; 
v_v_3059_ = lean_array_uget(v_bs_3057_, v_i_3056_);
v_startPosLine_3060_ = lean_ctor_get(v_v_3059_, 0);
v_startPosCharacter_3061_ = lean_ctor_get(v_v_3059_, 1);
v_endPosLine_3062_ = lean_ctor_get(v_v_3059_, 2);
v_endPosCharacter_3063_ = lean_ctor_get(v_v_3059_, 3);
v___x_3064_ = lean_unsigned_to_nat(0u);
v_bs_x27_3065_ = lean_array_uset(v_bs_3057_, v_i_3056_, v___x_3064_);
v___x_3072_ = lean_box(0);
lean_inc(v_endPosCharacter_3063_);
v___x_3073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3073_, 0, v_endPosCharacter_3063_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
lean_inc(v_endPosLine_3062_);
v___x_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_endPosLine_3062_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
lean_inc(v_startPosCharacter_3061_);
v___x_3075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3075_, 0, v_startPosCharacter_3061_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
lean_inc(v_startPosLine_3060_);
v___x_3076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3076_, 0, v_startPosLine_3060_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v_range_3077_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3076_, v___x_3072_);
v___x_3078_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3059_);
lean_dec(v_v_3059_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v___x_3079_; 
v___x_3079_ = l_List_appendTR___redArg(v_range_3077_, v___x_3072_);
v___y_3067_ = v___x_3079_;
goto v___jp_3066_;
}
else
{
lean_object* v_val_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3089_; 
v_val_3080_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3082_ = v___x_3078_;
v_isShared_3083_ = v_isSharedCheck_3089_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_val_3080_);
lean_dec(v___x_3078_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3089_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set_tag(v___x_3082_, 3);
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_val_3080_);
v___x_3085_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
lean_ctor_set(v___x_3086_, 1, v___x_3072_);
v___x_3087_ = l_List_appendTR___redArg(v_range_3077_, v___x_3086_);
v___y_3067_ = v___x_3087_;
goto v___jp_3066_;
}
}
}
v___jp_3066_:
{
size_t v___x_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((size_t)1ULL);
v___x_3069_ = lean_usize_add(v_i_3056_, v___x_3068_);
v___x_3070_ = lean_array_uset(v_bs_x27_3065_, v_i_3056_, v___y_3067_);
v_i_3056_ = v___x_3069_;
v_bs_3057_ = v___x_3070_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3090_, lean_object* v_i_3091_, lean_object* v_bs_3092_){
_start:
{
size_t v_sz_boxed_3093_; size_t v_i_boxed_3094_; lean_object* v_res_3095_; 
v_sz_boxed_3093_ = lean_unbox_usize(v_sz_3090_);
lean_dec(v_sz_3090_);
v_i_boxed_3094_ = lean_unbox_usize(v_i_3091_);
lean_dec(v_i_3091_);
v_res_3095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3093_, v_i_boxed_3094_, v_bs_3092_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3096_, size_t v_i_3097_, lean_object* v_bs_3098_){
_start:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_usize_dec_lt(v_i_3097_, v_sz_3096_);
if (v___x_3099_ == 0)
{
return v_bs_3098_;
}
else
{
lean_object* v_v_3100_; lean_object* v___x_3101_; lean_object* v_bs_x27_3102_; lean_object* v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; lean_object* v___x_3106_; 
v_v_3100_ = lean_array_uget(v_bs_3098_, v_i_3097_);
v___x_3101_ = lean_unsigned_to_nat(0u);
v_bs_x27_3102_ = lean_array_uset(v_bs_3098_, v_i_3097_, v___x_3101_);
v___x_3103_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3100_);
v___x_3104_ = ((size_t)1ULL);
v___x_3105_ = lean_usize_add(v_i_3097_, v___x_3104_);
v___x_3106_ = lean_array_uset(v_bs_x27_3102_, v_i_3097_, v___x_3103_);
v_i_3097_ = v___x_3105_;
v_bs_3098_ = v___x_3106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3108_, lean_object* v_i_3109_, lean_object* v_bs_3110_){
_start:
{
size_t v_sz_boxed_3111_; size_t v_i_boxed_3112_; lean_object* v_res_3113_; 
v_sz_boxed_3111_ = lean_unbox_usize(v_sz_3108_);
lean_dec(v_sz_3108_);
v_i_boxed_3112_ = lean_unbox_usize(v_i_3109_);
lean_dec(v_i_3109_);
v_res_3113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3111_, v_i_boxed_3112_, v_bs_3110_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3114_){
_start:
{
size_t v_sz_3115_; size_t v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_sz_3115_ = lean_array_size(v_a_3114_);
v___x_3116_ = ((size_t)0ULL);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3115_, v___x_3116_, v_a_3114_);
v___x_3118_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3119_, lean_object* v_x_3120_){
_start:
{
if (lean_obj_tag(v_x_3120_) == 0)
{
lean_object* v_k_3121_; lean_object* v_v_3122_; lean_object* v_l_3123_; lean_object* v_r_3124_; lean_object* v___x_3125_; lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3186_; 
v_k_3121_ = lean_ctor_get(v_x_3120_, 1);
lean_inc(v_k_3121_);
v_v_3122_ = lean_ctor_get(v_x_3120_, 2);
lean_inc(v_v_3122_);
v_l_3123_ = lean_ctor_get(v_x_3120_, 3);
lean_inc(v_l_3123_);
v_r_3124_ = lean_ctor_get(v_x_3120_, 4);
lean_inc(v_r_3124_);
lean_dec_ref_known(v_x_3120_, 5);
v___x_3125_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3119_, v_l_3123_);
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3186_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3186_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v_definition_x3f_3130_; lean_object* v_usages_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3185_; 
v_definition_x3f_3130_ = lean_ctor_get(v_v_3122_, 0);
v_usages_3131_ = lean_ctor_get(v_v_3122_, 1);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_v_3122_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3133_ = v_v_3122_;
v_isShared_3134_ = v_isSharedCheck_3185_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_usages_3131_);
lean_inc(v_definition_x3f_3130_);
lean_dec(v_v_3122_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3185_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___y_3139_; lean_object* v___y_3157_; 
v___x_3135_ = l_Lean_Lsp_RefIdent_toJson(v_k_3121_);
lean_dec(v_k_3121_);
v___x_3136_ = lean_array_push(v_a_3126_, v___x_3135_);
v___x_3137_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3130_) == 0)
{
lean_object* v___x_3161_; 
lean_del_object(v___x_3128_);
v___x_3161_ = lean_box(0);
v___y_3139_ = v___x_3161_;
goto v___jp_3138_;
}
else
{
lean_object* v_val_3162_; lean_object* v_startPosLine_3163_; lean_object* v_startPosCharacter_3164_; lean_object* v_endPosLine_3165_; lean_object* v_endPosCharacter_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v_range_3172_; lean_object* v___x_3173_; 
v_val_3162_ = lean_ctor_get(v_definition_x3f_3130_, 0);
lean_inc(v_val_3162_);
lean_dec_ref_known(v_definition_x3f_3130_, 1);
v_startPosLine_3163_ = lean_ctor_get(v_val_3162_, 0);
v_startPosCharacter_3164_ = lean_ctor_get(v_val_3162_, 1);
v_endPosLine_3165_ = lean_ctor_get(v_val_3162_, 2);
v_endPosCharacter_3166_ = lean_ctor_get(v_val_3162_, 3);
v___x_3167_ = lean_box(0);
lean_inc(v_endPosCharacter_3166_);
v___x_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3168_, 0, v_endPosCharacter_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
lean_inc(v_endPosLine_3165_);
v___x_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3169_, 0, v_endPosLine_3165_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
lean_inc(v_startPosCharacter_3164_);
v___x_3170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3170_, 0, v_startPosCharacter_3164_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
lean_inc(v_startPosLine_3163_);
v___x_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3171_, 0, v_startPosLine_3163_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v_range_3172_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3171_, v___x_3167_);
v___x_3173_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3162_);
lean_dec(v_val_3162_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v___x_3174_; 
v___x_3174_ = l_List_appendTR___redArg(v_range_3172_, v___x_3167_);
v___y_3157_ = v___x_3174_;
goto v___jp_3156_;
}
else
{
lean_object* v_val_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3184_; 
v_val_3175_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3177_ = v___x_3173_;
v_isShared_3178_ = v_isSharedCheck_3184_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_val_3175_);
lean_dec(v___x_3173_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3184_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
lean_ctor_set_tag(v___x_3177_, 3);
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_val_3175_);
v___x_3180_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v___x_3167_);
v___x_3182_ = l_List_appendTR___redArg(v_range_3172_, v___x_3181_);
v___y_3157_ = v___x_3182_;
goto v___jp_3156_;
}
}
}
}
v___jp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3139_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 1, v___x_3140_);
lean_ctor_set(v___x_3133_, 0, v___x_3137_);
v___x_3142_ = v___x_3133_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3143_; size_t v_sz_3144_; size_t v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3143_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3144_ = lean_array_size(v_usages_3131_);
v___x_3145_ = ((size_t)0ULL);
v___x_3146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3144_, v___x_3145_, v_usages_3131_);
v___x_3147_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3146_);
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3143_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3142_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = l_Lean_Json_mkObj(v___x_3151_);
lean_dec_ref_known(v___x_3151_, 2);
v___x_3153_ = lean_array_push(v___x_3136_, v___x_3152_);
v_init_3119_ = v___x_3153_;
v_x_3120_ = v_r_3124_;
goto _start;
}
}
v___jp_3156_:
{
lean_object* v___x_3159_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___y_3157_);
v___x_3159_ = v___x_3128_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___y_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
v___y_3139_ = v___x_3159_;
goto v___jp_3138_;
}
}
}
}
}
else
{
lean_object* v___x_3187_; 
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_init_3119_);
return v___x_3187_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
if (lean_obj_tag(v_a_3188_) == 0)
{
lean_object* v___x_3190_; 
v___x_3190_ = l_List_reverse___redArg(v_a_3189_);
return v___x_3190_;
}
else
{
lean_object* v_head_3191_; lean_object* v_snd_3192_; lean_object* v_tail_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3245_; 
v_head_3191_ = lean_ctor_get(v_a_3188_, 0);
lean_inc(v_head_3191_);
v_snd_3192_ = lean_ctor_get(v_head_3191_, 1);
lean_inc(v_snd_3192_);
v_tail_3193_ = lean_ctor_get(v_a_3188_, 1);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_a_3188_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v_a_3188_, 0);
lean_dec(v_unused_3246_);
v___x_3195_ = v_a_3188_;
v_isShared_3196_ = v_isSharedCheck_3245_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_tail_3193_);
lean_dec(v_a_3188_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3245_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_fst_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3243_; 
v_fst_3197_ = lean_ctor_get(v_head_3191_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_head_3191_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v_head_3191_, 1);
lean_dec(v_unused_3244_);
v___x_3199_ = v_head_3191_;
v_isShared_3200_ = v_isSharedCheck_3243_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_fst_3197_);
lean_dec(v_head_3191_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3243_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_rangeStartPosLine_3201_; lean_object* v_rangeStartPosCharacter_3202_; lean_object* v_rangeEndPosLine_3203_; lean_object* v_rangeEndPosCharacter_3204_; lean_object* v_selectionRangeStartPosLine_3205_; lean_object* v_selectionRangeStartPosCharacter_3206_; lean_object* v_selectionRangeEndPosLine_3207_; lean_object* v_selectionRangeEndPosCharacter_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v_rangeStartPosLine_3201_ = lean_ctor_get(v_snd_3192_, 0);
lean_inc(v_rangeStartPosLine_3201_);
v_rangeStartPosCharacter_3202_ = lean_ctor_get(v_snd_3192_, 1);
lean_inc(v_rangeStartPosCharacter_3202_);
v_rangeEndPosLine_3203_ = lean_ctor_get(v_snd_3192_, 2);
lean_inc(v_rangeEndPosLine_3203_);
v_rangeEndPosCharacter_3204_ = lean_ctor_get(v_snd_3192_, 3);
lean_inc(v_rangeEndPosCharacter_3204_);
v_selectionRangeStartPosLine_3205_ = lean_ctor_get(v_snd_3192_, 4);
lean_inc(v_selectionRangeStartPosLine_3205_);
v_selectionRangeStartPosCharacter_3206_ = lean_ctor_get(v_snd_3192_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3206_);
v_selectionRangeEndPosLine_3207_ = lean_ctor_get(v_snd_3192_, 6);
lean_inc(v_selectionRangeEndPosLine_3207_);
v_selectionRangeEndPosCharacter_3208_ = lean_ctor_get(v_snd_3192_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3208_);
lean_dec(v_snd_3192_);
v___x_3209_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3201_);
v___x_3210_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
v___x_3211_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3202_);
v___x_3212_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
v___x_3213_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3203_);
v___x_3214_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
v___x_3215_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3204_);
v___x_3216_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
v___x_3217_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3205_);
v___x_3218_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
v___x_3219_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3206_);
v___x_3220_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
v___x_3221_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3207_);
v___x_3222_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
v___x_3223_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3208_);
v___x_3224_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
v___x_3225_ = lean_unsigned_to_nat(8u);
v___x_3226_ = lean_mk_empty_array_with_capacity(v___x_3225_);
v___x_3227_ = lean_array_push(v___x_3226_, v___x_3210_);
v___x_3228_ = lean_array_push(v___x_3227_, v___x_3212_);
v___x_3229_ = lean_array_push(v___x_3228_, v___x_3214_);
v___x_3230_ = lean_array_push(v___x_3229_, v___x_3216_);
v___x_3231_ = lean_array_push(v___x_3230_, v___x_3218_);
v___x_3232_ = lean_array_push(v___x_3231_, v___x_3220_);
v___x_3233_ = lean_array_push(v___x_3232_, v___x_3222_);
v___x_3234_ = lean_array_push(v___x_3233_, v___x_3224_);
v___x_3235_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3234_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 1, v___x_3235_);
v___x_3237_ = v___x_3199_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_fst_3197_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3239_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 1, v_a_3189_);
lean_ctor_set(v___x_3195_, 0, v___x_3237_);
v___x_3239_ = v___x_3195_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_a_3189_);
v___x_3239_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
v_a_3188_ = v_tail_3193_;
v_a_3189_ = v___x_3239_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3247_, lean_object* v_x_3248_){
_start:
{
if (lean_obj_tag(v_x_3248_) == 0)
{
lean_object* v_k_3249_; lean_object* v_v_3250_; lean_object* v_l_3251_; lean_object* v_r_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v_k_3249_ = lean_ctor_get(v_x_3248_, 1);
v_v_3250_ = lean_ctor_get(v_x_3248_, 2);
v_l_3251_ = lean_ctor_get(v_x_3248_, 3);
v_r_3252_ = lean_ctor_get(v_x_3248_, 4);
v___x_3253_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3247_, v_r_3252_);
lean_inc(v_v_3250_);
lean_inc(v_k_3249_);
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v_k_3249_);
lean_ctor_set(v___x_3254_, 1, v_v_3250_);
v___x_3255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v___x_3253_);
v_init_3247_ = v___x_3255_;
v_x_3248_ = v_l_3251_;
goto _start;
}
else
{
return v_init_3247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3257_, lean_object* v_x_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3257_, v_x_3258_);
lean_dec(v_x_3258_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3260_){
_start:
{
lean_object* v_version_3261_; lean_object* v_references_3262_; lean_object* v_decls_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___y_3272_; lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
v_version_3261_ = lean_ctor_get(v_x_3260_, 0);
lean_inc(v_version_3261_);
v_references_3262_ = lean_ctor_get(v_x_3260_, 1);
lean_inc(v_references_3262_);
v_decls_3263_ = lean_ctor_get(v_x_3260_, 2);
lean_inc(v_decls_3263_);
lean_dec_ref(v_x_3260_);
v___x_3264_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3265_ = l_Lean_JsonNumber_fromNat(v_version_3261_);
v___x_3266_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3264_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v_a_3287_ = ((lean_object*)(l_Lean_Lsp_instToJsonModuleRefs___lam__2___closed__0));
v___x_3288_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_a_3287_, v_references_3262_);
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v___jp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3270_);
lean_ctor_set(v___x_3273_, 1, v___y_3272_);
v___x_3274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
lean_ctor_set(v___x_3274_, 1, v___x_3268_);
v___x_3275_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3276_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3268_, v_decls_3263_);
lean_dec(v_decls_3263_);
v___x_3277_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3276_, v___x_3268_);
v___x_3278_ = l_Lean_Json_mkObj(v___x_3277_);
lean_dec(v___x_3277_);
v___x_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3275_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
lean_ctor_set(v___x_3280_, 1, v___x_3268_);
v___x_3281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v___x_3268_);
v___x_3282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3274_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3269_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3285_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3283_, v___x_3284_);
v___x_3286_ = l_Lean_Json_mkObj(v___x_3285_);
lean_dec(v___x_3285_);
return v___x_3286_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 4);
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
v___y_3272_ = v___x_3294_;
goto v___jp_3271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3299_, size_t v_i_3300_, lean_object* v_bs_3301_){
_start:
{
uint8_t v___x_3302_; 
v___x_3302_ = lean_usize_dec_lt(v_i_3300_, v_sz_3299_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; 
v___x_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3303_, 0, v_bs_3301_);
return v___x_3303_;
}
else
{
lean_object* v_v_3304_; lean_object* v___x_3305_; 
v_v_3304_ = lean_array_uget_borrowed(v_bs_3301_, v_i_3300_);
lean_inc(v_v_3304_);
v___x_3305_ = l_Lean_Json_getStr_x3f(v_v_3304_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref(v_bs_3301_);
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3315_; lean_object* v_bs_x27_3316_; size_t v___x_3317_; size_t v___x_3318_; lean_object* v___x_3319_; 
v_a_3314_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3315_ = lean_unsigned_to_nat(0u);
v_bs_x27_3316_ = lean_array_uset(v_bs_3301_, v_i_3300_, v___x_3315_);
v___x_3317_ = ((size_t)1ULL);
v___x_3318_ = lean_usize_add(v_i_3300_, v___x_3317_);
v___x_3319_ = lean_array_uset(v_bs_x27_3316_, v_i_3300_, v_a_3314_);
v_i_3300_ = v___x_3318_;
v_bs_3301_ = v___x_3319_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3321_, lean_object* v_i_3322_, lean_object* v_bs_3323_){
_start:
{
size_t v_sz_boxed_3324_; size_t v_i_boxed_3325_; lean_object* v_res_3326_; 
v_sz_boxed_3324_ = lean_unbox_usize(v_sz_3321_);
lean_dec(v_sz_3321_);
v_i_boxed_3325_ = lean_unbox_usize(v_i_3322_);
lean_dec(v_i_3322_);
v_res_3326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3324_, v_i_boxed_3325_, v_bs_3323_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3327_){
_start:
{
if (lean_obj_tag(v_x_3327_) == 4)
{
lean_object* v_elems_3328_; size_t v_sz_3329_; size_t v___x_3330_; lean_object* v___x_3331_; 
v_elems_3328_ = lean_ctor_get(v_x_3327_, 0);
lean_inc_ref(v_elems_3328_);
lean_dec_ref_known(v_x_3327_, 1);
v_sz_3329_ = lean_array_size(v_elems_3328_);
v___x_3330_ = ((size_t)0ULL);
v___x_3331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3329_, v___x_3330_, v_elems_3328_);
return v___x_3331_;
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3332_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3333_ = lean_unsigned_to_nat(80u);
v___x_3334_ = l_Lean_Json_pretty(v_x_3327_, v___x_3333_);
v___x_3335_ = lean_string_append(v___x_3332_, v___x_3334_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_3337_ = lean_string_append(v___x_3335_, v___x_3336_);
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3339_, lean_object* v_k_3340_){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = l_Lean_Json_getObjValD(v_j_3339_, v_k_3340_);
v___x_3342_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3343_, lean_object* v_k_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3343_, v_k_3344_);
lean_dec_ref(v_k_3344_);
return v_res_3345_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = 1;
v___x_3353_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3354_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3353_, v___x_3352_);
return v___x_3354_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3356_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3357_ = lean_string_append(v___x_3356_, v___x_3355_);
return v___x_3357_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3360_ = 1;
v___x_3361_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3361_, v___x_3360_);
return v___x_3362_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3364_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3365_ = lean_string_append(v___x_3364_, v___x_3363_);
return v___x_3365_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3367_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3368_ = lean_string_append(v___x_3367_, v___x_3366_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3369_){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3371_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3369_, v___x_3370_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3381_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3381_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3381_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
v___x_3376_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3377_ = lean_string_append(v___x_3376_, v_a_3372_);
lean_dec(v_a_3372_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3377_);
v___x_3379_ = v___x_3374_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
v_a_3382_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3371_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3371_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3392_, size_t v_i_3393_, lean_object* v_bs_3394_){
_start:
{
uint8_t v___x_3395_; 
v___x_3395_ = lean_usize_dec_lt(v_i_3393_, v_sz_3392_);
if (v___x_3395_ == 0)
{
return v_bs_3394_;
}
else
{
lean_object* v_v_3396_; lean_object* v___x_3397_; lean_object* v_bs_x27_3398_; lean_object* v___x_3399_; size_t v___x_3400_; size_t v___x_3401_; lean_object* v___x_3402_; 
v_v_3396_ = lean_array_uget(v_bs_3394_, v_i_3393_);
v___x_3397_ = lean_unsigned_to_nat(0u);
v_bs_x27_3398_ = lean_array_uset(v_bs_3394_, v_i_3393_, v___x_3397_);
v___x_3399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3399_, 0, v_v_3396_);
v___x_3400_ = ((size_t)1ULL);
v___x_3401_ = lean_usize_add(v_i_3393_, v___x_3400_);
v___x_3402_ = lean_array_uset(v_bs_x27_3398_, v_i_3393_, v___x_3399_);
v_i_3393_ = v___x_3401_;
v_bs_3394_ = v___x_3402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3404_, lean_object* v_i_3405_, lean_object* v_bs_3406_){
_start:
{
size_t v_sz_boxed_3407_; size_t v_i_boxed_3408_; lean_object* v_res_3409_; 
v_sz_boxed_3407_ = lean_unbox_usize(v_sz_3404_);
lean_dec(v_sz_3404_);
v_i_boxed_3408_ = lean_unbox_usize(v_i_3405_);
lean_dec(v_i_3405_);
v_res_3409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3407_, v_i_boxed_3408_, v_bs_3406_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3410_){
_start:
{
size_t v_sz_3411_; size_t v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_sz_3411_ = lean_array_size(v_a_3410_);
v___x_3412_ = ((size_t)0ULL);
v___x_3413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3411_, v___x_3412_, v_a_3410_);
v___x_3414_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3415_){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3416_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3417_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3415_);
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
lean_ctor_set(v___x_3421_, 1, v___x_3419_);
v___x_3422_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3423_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3421_, v___x_3422_);
v___x_3424_ = l_Lean_Json_mkObj(v___x_3423_);
lean_dec(v___x_3423_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3427_, lean_object* v_k_3428_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = l_Lean_Json_getObjValD(v_j_3427_, v_k_3428_);
v___x_3430_ = l_Lean_Json_getStr_x3f(v___x_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3431_, lean_object* v_k_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3431_, v_k_3432_);
lean_dec_ref(v_k_3432_);
return v_res_3433_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = 1;
v___x_3441_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3442_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3441_, v___x_3440_);
return v___x_3442_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3444_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3445_ = lean_string_append(v___x_3444_, v___x_3443_);
return v___x_3445_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = 1;
v___x_3449_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3450_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3449_, v___x_3448_);
return v___x_3450_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3452_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3453_ = lean_string_append(v___x_3452_, v___x_3451_);
return v___x_3453_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3454_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3455_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3456_ = lean_string_append(v___x_3455_, v___x_3454_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3457_){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3459_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3457_, v___x_3458_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3469_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3462_ = v___x_3459_;
v_isShared_3463_ = v_isSharedCheck_3469_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3469_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3464_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
v___x_3465_ = lean_string_append(v___x_3464_, v_a_3460_);
lean_dec(v_a_3460_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 0, v___x_3465_);
v___x_3467_ = v___x_3462_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
v_a_3470_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3459_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3459_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3480_){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3481_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3482_, 0, v_x_3480_);
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_box(0);
v___x_3485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v___x_3484_);
v___x_3487_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3488_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3486_, v___x_3487_);
v___x_3489_ = l_Lean_Json_mkObj(v___x_3488_);
lean_dec(v___x_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl(lean_object* v_x_3492_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_obj_tag_nat(v_x_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl___boxed(lean_object* v_x_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Lsp_OpenNamespace_ctorIdx___impl(v_x_3494_);
lean_dec_ref(v_x_3494_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3496_, lean_object* v_k_3497_){
_start:
{
if (lean_obj_tag(v_t_3496_) == 0)
{
lean_object* v_namespace_3498_; lean_object* v_exceptions_3499_; lean_object* v___x_3500_; 
v_namespace_3498_ = lean_ctor_get(v_t_3496_, 0);
lean_inc(v_namespace_3498_);
v_exceptions_3499_ = lean_ctor_get(v_t_3496_, 1);
lean_inc_ref(v_exceptions_3499_);
lean_dec_ref_known(v_t_3496_, 2);
v___x_3500_ = lean_apply_2(v_k_3497_, v_namespace_3498_, v_exceptions_3499_);
return v___x_3500_;
}
else
{
lean_object* v_from_3501_; lean_object* v_to_3502_; lean_object* v___x_3503_; 
v_from_3501_ = lean_ctor_get(v_t_3496_, 0);
lean_inc(v_from_3501_);
v_to_3502_ = lean_ctor_get(v_t_3496_, 1);
lean_inc(v_to_3502_);
lean_dec_ref_known(v_t_3496_, 2);
v___x_3503_ = lean_apply_2(v_k_3497_, v_from_3501_, v_to_3502_);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3504_, lean_object* v_ctorIdx_3505_, lean_object* v_t_3506_, lean_object* v_h_3507_, lean_object* v_k_3508_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3506_, v_k_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3510_, lean_object* v_ctorIdx_3511_, lean_object* v_t_3512_, lean_object* v_h_3513_, lean_object* v_k_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3510_, v_ctorIdx_3511_, v_t_3512_, v_h_3513_, v_k_3514_);
lean_dec(v_ctorIdx_3511_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3516_, lean_object* v_allExcept_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3516_, v_allExcept_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3519_, lean_object* v_t_3520_, lean_object* v_h_3521_, lean_object* v_allExcept_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3520_, v_allExcept_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3524_, lean_object* v_renamed_3525_){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3524_, v_renamed_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3527_, lean_object* v_t_3528_, lean_object* v_h_3529_, lean_object* v_renamed_3530_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3528_, v_renamed_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3532_, size_t v_i_3533_, lean_object* v_bs_3534_){
_start:
{
uint8_t v___x_3535_; 
v___x_3535_ = lean_usize_dec_lt(v_i_3533_, v_sz_3532_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; 
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v_bs_3534_);
return v___x_3536_;
}
else
{
lean_object* v_v_3537_; lean_object* v___x_3538_; 
v_v_3537_ = lean_array_uget_borrowed(v_bs_3534_, v_i_3533_);
lean_inc(v_v_3537_);
v___x_3538_ = l_Lean_Name_fromJson_x3f(v_v_3537_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref(v_bs_3534_);
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3548_; lean_object* v_bs_x27_3549_; size_t v___x_3550_; size_t v___x_3551_; lean_object* v___x_3552_; 
v_a_3547_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3538_, 1);
v___x_3548_ = lean_unsigned_to_nat(0u);
v_bs_x27_3549_ = lean_array_uset(v_bs_3534_, v_i_3533_, v___x_3548_);
v___x_3550_ = ((size_t)1ULL);
v___x_3551_ = lean_usize_add(v_i_3533_, v___x_3550_);
v___x_3552_ = lean_array_uset(v_bs_x27_3549_, v_i_3533_, v_a_3547_);
v_i_3533_ = v___x_3551_;
v_bs_3534_ = v___x_3552_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3554_, lean_object* v_i_3555_, lean_object* v_bs_3556_){
_start:
{
size_t v_sz_boxed_3557_; size_t v_i_boxed_3558_; lean_object* v_res_3559_; 
v_sz_boxed_3557_ = lean_unbox_usize(v_sz_3554_);
lean_dec(v_sz_3554_);
v_i_boxed_3558_ = lean_unbox_usize(v_i_3555_);
lean_dec(v_i_3555_);
v_res_3559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3557_, v_i_boxed_3558_, v_bs_3556_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3560_){
_start:
{
if (lean_obj_tag(v_x_3560_) == 4)
{
lean_object* v_elems_3561_; size_t v_sz_3562_; size_t v___x_3563_; lean_object* v___x_3564_; 
v_elems_3561_ = lean_ctor_get(v_x_3560_, 0);
lean_inc_ref(v_elems_3561_);
lean_dec_ref_known(v_x_3560_, 1);
v_sz_3562_ = lean_array_size(v_elems_3561_);
v___x_3563_ = ((size_t)0ULL);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3562_, v___x_3563_, v_elems_3561_);
return v___x_3564_;
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3565_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3566_ = lean_unsigned_to_nat(80u);
v___x_3567_ = l_Lean_Json_pretty(v_x_3560_, v___x_3566_);
v___x_3568_ = lean_string_append(v___x_3565_, v___x_3567_);
lean_dec_ref(v___x_3567_);
v___x_3569_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_3570_ = lean_string_append(v___x_3568_, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
return v___x_3571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3608_){
_start:
{
lean_object* v___x_3609_; 
lean_inc(v_json_3608_);
v___x_3609_ = l_Lean_Json_getTag_x3f(v_json_3608_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v___x_3610_; 
lean_dec(v_json_3608_);
v___x_3610_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
return v___x_3610_;
}
else
{
lean_object* v_val_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v_val_3611_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_val_3611_);
lean_dec_ref_known(v___x_3609_, 1);
v___x_3612_ = lean_box(0);
v___x_3613_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3614_ = lean_string_dec_eq(v_val_3611_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; uint8_t v___x_3616_; 
v___x_3615_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
v___x_3616_ = lean_string_dec_eq(v_val_3611_, v___x_3615_);
lean_dec(v_val_3611_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
lean_dec(v_json_3608_);
v___x_3617_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__5));
return v___x_3617_;
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = lean_unsigned_to_nat(2u);
v___x_3619_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__11));
v___x_3620_ = l_Lean_Json_parseCtorFields(v_json_3608_, v___x_3615_, v___x_3618_, v___x_3619_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3620_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v_a_3629_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3630_ = lean_unsigned_to_nat(0u);
v___x_3631_ = lean_array_get_borrowed(v___x_3612_, v_a_3629_, v___x_3630_);
lean_inc(v___x_3631_);
v___x_3632_ = l_Lean_Name_fromJson_x3f(v___x_3631_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v_a_3629_);
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v_a_3641_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3641_);
lean_dec_ref_known(v___x_3632_, 1);
v___x_3642_ = lean_unsigned_to_nat(1u);
v___x_3643_ = lean_array_get(v___x_3612_, v_a_3629_, v___x_3642_);
lean_dec(v_a_3629_);
v___x_3644_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3643_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_a_3641_);
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3661_; 
v_a_3653_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3655_ = v___x_3644_;
v_isShared_3656_ = v_isSharedCheck_3661_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3644_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3661_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
v___x_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3657_, 0, v_a_3641_);
lean_ctor_set(v___x_3657_, 1, v_a_3653_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v___x_3657_);
v___x_3659_ = v___x_3655_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_dec(v_val_3611_);
v___x_3662_ = lean_unsigned_to_nat(2u);
v___x_3663_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__17));
v___x_3664_ = l_Lean_Json_parseCtorFields(v_json_3608_, v___x_3613_, v___x_3662_, v___x_3663_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_a_3673_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3664_, 1);
v___x_3674_ = lean_unsigned_to_nat(0u);
v___x_3675_ = lean_array_get_borrowed(v___x_3612_, v_a_3673_, v___x_3674_);
lean_inc(v___x_3675_);
v___x_3676_ = l_Lean_Name_fromJson_x3f(v___x_3675_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v_a_3673_);
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v_a_3685_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___x_3676_, 1);
v___x_3686_ = lean_unsigned_to_nat(1u);
v___x_3687_ = lean_array_get(v___x_3612_, v_a_3673_, v___x_3686_);
lean_dec(v_a_3673_);
v___x_3688_ = l_Lean_Name_fromJson_x3f(v___x_3687_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v_a_3685_);
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3688_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
else
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3705_; 
v_a_3697_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3699_ = v___x_3688_;
v_isShared_3700_ = v_isSharedCheck_3705_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3688_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3705_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3701_, 0, v_a_3685_);
lean_ctor_set(v___x_3701_, 1, v_a_3697_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3701_);
v___x_3703_ = v___x_3699_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3708_, size_t v_i_3709_, lean_object* v_bs_3710_){
_start:
{
uint8_t v___x_3711_; 
v___x_3711_ = lean_usize_dec_lt(v_i_3709_, v_sz_3708_);
if (v___x_3711_ == 0)
{
return v_bs_3710_;
}
else
{
lean_object* v_v_3712_; lean_object* v___x_3713_; lean_object* v_bs_x27_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; size_t v___x_3717_; size_t v___x_3718_; lean_object* v___x_3719_; 
v_v_3712_ = lean_array_uget(v_bs_3710_, v_i_3709_);
v___x_3713_ = lean_unsigned_to_nat(0u);
v_bs_x27_3714_ = lean_array_uset(v_bs_3710_, v_i_3709_, v___x_3713_);
v___x_3715_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3712_, v___x_3711_);
v___x_3716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
v___x_3717_ = ((size_t)1ULL);
v___x_3718_ = lean_usize_add(v_i_3709_, v___x_3717_);
v___x_3719_ = lean_array_uset(v_bs_x27_3714_, v_i_3709_, v___x_3716_);
v_i_3709_ = v___x_3718_;
v_bs_3710_ = v___x_3719_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3721_, lean_object* v_i_3722_, lean_object* v_bs_3723_){
_start:
{
size_t v_sz_boxed_3724_; size_t v_i_boxed_3725_; lean_object* v_res_3726_; 
v_sz_boxed_3724_ = lean_unbox_usize(v_sz_3721_);
lean_dec(v_sz_3721_);
v_i_boxed_3725_ = lean_unbox_usize(v_i_3722_);
lean_dec(v_i_3722_);
v_res_3726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3724_, v_i_boxed_3725_, v_bs_3723_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3727_){
_start:
{
size_t v_sz_3728_; size_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_sz_3728_ = lean_array_size(v_a_3727_);
v___x_3729_ = ((size_t)0ULL);
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3728_, v___x_3729_, v_a_3727_);
v___x_3731_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3732_){
_start:
{
if (lean_obj_tag(v_x_3732_) == 0)
{
lean_object* v_namespace_3733_; lean_object* v_exceptions_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3756_; 
v_namespace_3733_ = lean_ctor_get(v_x_3732_, 0);
v_exceptions_3734_ = lean_ctor_get(v_x_3732_, 1);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_x_3732_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3736_ = v_x_3732_;
v_isShared_3737_ = v_isSharedCheck_3756_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_exceptions_3734_);
lean_inc(v_namespace_3733_);
lean_dec(v_x_3732_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3756_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3744_; 
v___x_3738_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
v___x_3739_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3740_ = 1;
v___x_3741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3733_, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 1, v___x_3742_);
lean_ctor_set(v___x_3736_, 0, v___x_3739_);
v___x_3744_ = v___x_3736_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3745_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__8));
v___x_3746_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3734_);
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = lean_box(0);
v___x_3749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3744_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = l_Lean_Json_mkObj(v___x_3750_);
lean_dec_ref_known(v___x_3750_, 2);
v___x_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3738_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
lean_ctor_set(v___x_3753_, 1, v___x_3748_);
v___x_3754_ = l_Lean_Json_mkObj(v___x_3753_);
lean_dec_ref_known(v___x_3753_, 2);
return v___x_3754_;
}
}
}
else
{
lean_object* v_from_3757_; lean_object* v_to_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3781_; 
v_from_3757_ = lean_ctor_get(v_x_3732_, 0);
v_to_3758_ = lean_ctor_get(v_x_3732_, 1);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_x_3732_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3760_ = v_x_3732_;
v_isShared_3761_ = v_isSharedCheck_3781_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_to_3758_);
lean_inc(v_from_3757_);
lean_dec(v_x_3732_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3781_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3762_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3763_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_3764_ = 1;
v___x_3765_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_3757_, v___x_3764_);
v___x_3766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set_tag(v___x_3760_, 0);
lean_ctor_set(v___x_3760_, 1, v___x_3766_);
lean_ctor_set(v___x_3760_, 0, v___x_3763_);
v___x_3768_ = v___x_3760_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3763_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3769_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__14));
v___x_3770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_3758_, v___x_3764_);
v___x_3771_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3769_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = lean_box(0);
v___x_3774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3768_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = l_Lean_Json_mkObj(v___x_3775_);
lean_dec_ref_known(v___x_3775_, 2);
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3762_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
lean_ctor_set(v___x_3778_, 1, v___x_3773_);
v___x_3779_ = l_Lean_Json_mkObj(v___x_3778_);
lean_dec_ref_known(v___x_3778_, 2);
return v___x_3779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3784_, size_t v_i_3785_, lean_object* v_bs_3786_){
_start:
{
uint8_t v___x_3787_; 
v___x_3787_ = lean_usize_dec_lt(v_i_3785_, v_sz_3784_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; 
v___x_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3788_, 0, v_bs_3786_);
return v___x_3788_;
}
else
{
lean_object* v_v_3789_; lean_object* v___x_3790_; 
v_v_3789_ = lean_array_uget_borrowed(v_bs_3786_, v_i_3785_);
lean_inc(v_v_3789_);
v___x_3790_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_3789_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec_ref(v_bs_3786_);
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3790_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3790_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3800_; lean_object* v_bs_x27_3801_; size_t v___x_3802_; size_t v___x_3803_; lean_object* v___x_3804_; 
v_a_3799_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3790_, 1);
v___x_3800_ = lean_unsigned_to_nat(0u);
v_bs_x27_3801_ = lean_array_uset(v_bs_3786_, v_i_3785_, v___x_3800_);
v___x_3802_ = ((size_t)1ULL);
v___x_3803_ = lean_usize_add(v_i_3785_, v___x_3802_);
v___x_3804_ = lean_array_uset(v_bs_x27_3801_, v_i_3785_, v_a_3799_);
v_i_3785_ = v___x_3803_;
v_bs_3786_ = v___x_3804_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3806_, lean_object* v_i_3807_, lean_object* v_bs_3808_){
_start:
{
size_t v_sz_boxed_3809_; size_t v_i_boxed_3810_; lean_object* v_res_3811_; 
v_sz_boxed_3809_ = lean_unbox_usize(v_sz_3806_);
lean_dec(v_sz_3806_);
v_i_boxed_3810_ = lean_unbox_usize(v_i_3807_);
lean_dec(v_i_3807_);
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3809_, v_i_boxed_3810_, v_bs_3808_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_3812_){
_start:
{
if (lean_obj_tag(v_x_3812_) == 4)
{
lean_object* v_elems_3813_; size_t v_sz_3814_; size_t v___x_3815_; lean_object* v___x_3816_; 
v_elems_3813_ = lean_ctor_get(v_x_3812_, 0);
lean_inc_ref(v_elems_3813_);
lean_dec_ref_known(v_x_3812_, 1);
v_sz_3814_ = lean_array_size(v_elems_3813_);
v___x_3815_ = ((size_t)0ULL);
v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_3814_, v___x_3815_, v_elems_3813_);
return v___x_3816_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3817_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3818_ = lean_unsigned_to_nat(80u);
v___x_3819_ = l_Lean_Json_pretty(v_x_3812_, v___x_3818_);
v___x_3820_ = lean_string_append(v___x_3817_, v___x_3819_);
lean_dec_ref(v___x_3819_);
v___x_3821_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_3822_ = lean_string_append(v___x_3820_, v___x_3821_);
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
return v___x_3823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_3824_, lean_object* v_k_3825_){
_start:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = l_Lean_Json_getObjValD(v_j_3824_, v_k_3825_);
v___x_3827_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_3826_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_3828_, lean_object* v_k_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_3828_, v_k_3829_);
lean_dec_ref(v_k_3829_);
return v_res_3830_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = 1;
v___x_3838_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_3839_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3838_, v___x_3837_);
return v___x_3839_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3840_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3841_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_3842_ = lean_string_append(v___x_3841_, v___x_3840_);
return v___x_3842_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3845_ = 1;
v___x_3846_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_3847_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3846_, v___x_3845_);
return v___x_3847_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3848_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_3849_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_3850_ = lean_string_append(v___x_3849_, v___x_3848_);
return v___x_3850_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3851_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3852_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_3853_ = lean_string_append(v___x_3852_, v___x_3851_);
return v___x_3853_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3857_ = 1;
v___x_3858_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_3859_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3858_, v___x_3857_);
return v___x_3859_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3860_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_3861_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_3862_ = lean_string_append(v___x_3861_, v___x_3860_);
return v___x_3862_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3863_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3864_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_3865_ = lean_string_append(v___x_3864_, v___x_3863_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_3866_){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_3866_);
v___x_3868_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3866_, v___x_3867_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3878_; 
lean_dec(v_json_3866_);
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3871_ = v___x_3868_;
v_isShared_3872_ = v_isSharedCheck_3878_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3868_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3878_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3873_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
v___x_3874_ = lean_string_append(v___x_3873_, v_a_3869_);
lean_dec(v_a_3869_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v___x_3874_);
v___x_3876_ = v___x_3871_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_a_3879_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3868_, 1);
v___x_3880_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_3881_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_3866_, v___x_3880_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v_a_3879_);
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3886_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
v___x_3887_ = lean_string_append(v___x_3886_, v_a_3882_);
lean_dec(v_a_3882_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3887_);
v___x_3889_ = v___x_3884_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3900_; 
v_a_3892_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3894_ = v___x_3881_;
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3881_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3896_, 0, v_a_3879_);
lean_ctor_set(v___x_3896_, 1, v_a_3892_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_3896_);
v___x_3898_ = v___x_3894_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_3903_, size_t v_i_3904_, lean_object* v_bs_3905_){
_start:
{
uint8_t v___x_3906_; 
v___x_3906_ = lean_usize_dec_lt(v_i_3904_, v_sz_3903_);
if (v___x_3906_ == 0)
{
return v_bs_3905_;
}
else
{
lean_object* v_v_3907_; lean_object* v___x_3908_; lean_object* v_bs_x27_3909_; lean_object* v___x_3910_; size_t v___x_3911_; size_t v___x_3912_; lean_object* v___x_3913_; 
v_v_3907_ = lean_array_uget(v_bs_3905_, v_i_3904_);
v___x_3908_ = lean_unsigned_to_nat(0u);
v_bs_x27_3909_ = lean_array_uset(v_bs_3905_, v_i_3904_, v___x_3908_);
v___x_3910_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_3907_);
v___x_3911_ = ((size_t)1ULL);
v___x_3912_ = lean_usize_add(v_i_3904_, v___x_3911_);
v___x_3913_ = lean_array_uset(v_bs_x27_3909_, v_i_3904_, v___x_3910_);
v_i_3904_ = v___x_3912_;
v_bs_3905_ = v___x_3913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3915_, lean_object* v_i_3916_, lean_object* v_bs_3917_){
_start:
{
size_t v_sz_boxed_3918_; size_t v_i_boxed_3919_; lean_object* v_res_3920_; 
v_sz_boxed_3918_ = lean_unbox_usize(v_sz_3915_);
lean_dec(v_sz_3915_);
v_i_boxed_3919_ = lean_unbox_usize(v_i_3916_);
lean_dec(v_i_3916_);
v_res_3920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_3918_, v_i_boxed_3919_, v_bs_3917_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_3921_){
_start:
{
size_t v_sz_3922_; size_t v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v_sz_3922_ = lean_array_size(v_a_3921_);
v___x_3923_ = ((size_t)0ULL);
v___x_3924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_3922_, v___x_3923_, v_a_3921_);
v___x_3925_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_3926_){
_start:
{
lean_object* v_identifier_3927_; lean_object* v_openNamespaces_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3948_; 
v_identifier_3927_ = lean_ctor_get(v_x_3926_, 0);
v_openNamespaces_3928_ = lean_ctor_get(v_x_3926_, 1);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_x_3926_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3930_ = v_x_3926_;
v_isShared_3931_ = v_isSharedCheck_3948_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_openNamespaces_3928_);
lean_inc(v_identifier_3927_);
lean_dec(v_x_3926_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3948_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3932_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_3933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3933_, 0, v_identifier_3927_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 1, v___x_3933_);
lean_ctor_set(v___x_3930_, 0, v___x_3932_);
v___x_3935_ = v___x_3930_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3936_ = lean_box(0);
v___x_3937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3935_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_3939_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_3928_);
v___x_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3938_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
v___x_3941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
lean_ctor_set(v___x_3941_, 1, v___x_3936_);
v___x_3942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
lean_ctor_set(v___x_3942_, 1, v___x_3936_);
v___x_3943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3937_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3945_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3943_, v___x_3944_);
v___x_3946_ = l_Lean_Json_mkObj(v___x_3945_);
lean_dec(v___x_3945_);
return v___x_3946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_3954_, lean_object* v_k_3955_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_Json_getObjValD(v_j_3954_, v_k_3955_);
switch(lean_obj_tag(v___x_3956_))
{
case 3:
{
lean_object* v_s_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3965_; 
v_s_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_s_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
lean_ctor_set_tag(v___x_3959_, 0);
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_s_3957_);
v___x_3962_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
}
}
case 2:
{
lean_object* v_n_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3974_; 
v_n_3966_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3968_ = v___x_3956_;
v_isShared_3969_ = v_isSharedCheck_3974_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_n_3966_);
lean_dec(v___x_3956_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3974_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
lean_ctor_set_tag(v___x_3968_, 1);
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_n_3966_);
v___x_3971_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
return v___x_3972_;
}
}
}
default: 
{
lean_object* v___x_3975_; 
lean_dec(v___x_3956_);
v___x_3975_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_3975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_3976_, lean_object* v_k_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_3976_, v_k_3977_);
lean_dec_ref(v_k_3977_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_3979_, size_t v_i_3980_, lean_object* v_bs_3981_){
_start:
{
uint8_t v___x_3982_; 
v___x_3982_ = lean_usize_dec_lt(v_i_3980_, v_sz_3979_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
v___x_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3983_, 0, v_bs_3981_);
return v___x_3983_;
}
else
{
lean_object* v_v_3984_; lean_object* v___x_3985_; 
v_v_3984_ = lean_array_uget_borrowed(v_bs_3981_, v_i_3980_);
lean_inc(v_v_3984_);
v___x_3985_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_3984_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec_ref(v_bs_3981_);
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3985_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3985_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3995_; lean_object* v_bs_x27_3996_; size_t v___x_3997_; size_t v___x_3998_; lean_object* v___x_3999_; 
v_a_3994_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3994_);
lean_dec_ref_known(v___x_3985_, 1);
v___x_3995_ = lean_unsigned_to_nat(0u);
v_bs_x27_3996_ = lean_array_uset(v_bs_3981_, v_i_3980_, v___x_3995_);
v___x_3997_ = ((size_t)1ULL);
v___x_3998_ = lean_usize_add(v_i_3980_, v___x_3997_);
v___x_3999_ = lean_array_uset(v_bs_x27_3996_, v_i_3980_, v_a_3994_);
v_i_3980_ = v___x_3998_;
v_bs_3981_ = v___x_3999_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4001_, lean_object* v_i_4002_, lean_object* v_bs_4003_){
_start:
{
size_t v_sz_boxed_4004_; size_t v_i_boxed_4005_; lean_object* v_res_4006_; 
v_sz_boxed_4004_ = lean_unbox_usize(v_sz_4001_);
lean_dec(v_sz_4001_);
v_i_boxed_4005_ = lean_unbox_usize(v_i_4002_);
lean_dec(v_i_4002_);
v_res_4006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4004_, v_i_boxed_4005_, v_bs_4003_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4007_){
_start:
{
if (lean_obj_tag(v_x_4007_) == 4)
{
lean_object* v_elems_4008_; size_t v_sz_4009_; size_t v___x_4010_; lean_object* v___x_4011_; 
v_elems_4008_ = lean_ctor_get(v_x_4007_, 0);
lean_inc_ref(v_elems_4008_);
lean_dec_ref_known(v_x_4007_, 1);
v_sz_4009_ = lean_array_size(v_elems_4008_);
v___x_4010_ = ((size_t)0ULL);
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4009_, v___x_4010_, v_elems_4008_);
return v___x_4011_;
}
else
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4012_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4013_ = lean_unsigned_to_nat(80u);
v___x_4014_ = l_Lean_Json_pretty(v_x_4007_, v___x_4013_);
v___x_4015_ = lean_string_append(v___x_4012_, v___x_4014_);
lean_dec_ref(v___x_4014_);
v___x_4016_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_4017_ = lean_string_append(v___x_4015_, v___x_4016_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4019_, lean_object* v_k_4020_){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4021_ = l_Lean_Json_getObjValD(v_j_4019_, v_k_4020_);
v___x_4022_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4021_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4023_, lean_object* v_k_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4023_, v_k_4024_);
lean_dec_ref(v_k_4024_);
return v_res_4025_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4032_ = 1;
v___x_4033_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4034_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4033_, v___x_4032_);
return v___x_4034_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4036_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4037_ = lean_string_append(v___x_4036_, v___x_4035_);
return v___x_4037_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4040_ = 1;
v___x_4041_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4042_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4041_, v___x_4040_);
return v___x_4042_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4043_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4044_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4045_ = lean_string_append(v___x_4044_, v___x_4043_);
return v___x_4045_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4046_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4047_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4048_ = lean_string_append(v___x_4047_, v___x_4046_);
return v___x_4048_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = 1;
v___x_4053_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4054_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4053_, v___x_4052_);
return v___x_4054_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4056_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4057_ = lean_string_append(v___x_4056_, v___x_4055_);
return v___x_4057_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4058_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4059_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4060_ = lean_string_append(v___x_4059_, v___x_4058_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4061_){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4062_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4061_);
v___x_4063_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4061_, v___x_4062_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4073_; 
lean_dec(v_json_4061_);
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4066_ = v___x_4063_;
v_isShared_4067_ = v_isSharedCheck_4073_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4073_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4071_; 
v___x_4068_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4069_ = lean_string_append(v___x_4068_, v_a_4064_);
lean_dec(v_a_4064_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4069_);
v___x_4071_ = v___x_4066_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4069_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_a_4074_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4075_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4076_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4061_, v___x_4075_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4086_; 
lean_dec(v_a_4074_);
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4086_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4086_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4084_; 
v___x_4081_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
v___x_4082_ = lean_string_append(v___x_4081_, v_a_4077_);
lean_dec(v_a_4077_);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v___x_4082_);
v___x_4084_ = v___x_4079_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4095_; 
v_a_4087_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4089_ = v___x_4076_;
v_isShared_4090_ = v_isSharedCheck_4095_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4076_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4095_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v_a_4074_);
lean_ctor_set(v___x_4091_, 1, v_a_4087_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4091_);
v___x_4093_ = v___x_4089_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4091_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4098_, size_t v_i_4099_, lean_object* v_bs_4100_){
_start:
{
uint8_t v___x_4101_; 
v___x_4101_ = lean_usize_dec_lt(v_i_4099_, v_sz_4098_);
if (v___x_4101_ == 0)
{
return v_bs_4100_;
}
else
{
lean_object* v_v_4102_; lean_object* v___x_4103_; lean_object* v_bs_x27_4104_; lean_object* v___x_4105_; size_t v___x_4106_; size_t v___x_4107_; lean_object* v___x_4108_; 
v_v_4102_ = lean_array_uget(v_bs_4100_, v_i_4099_);
v___x_4103_ = lean_unsigned_to_nat(0u);
v_bs_x27_4104_ = lean_array_uset(v_bs_4100_, v_i_4099_, v___x_4103_);
v___x_4105_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4102_);
v___x_4106_ = ((size_t)1ULL);
v___x_4107_ = lean_usize_add(v_i_4099_, v___x_4106_);
v___x_4108_ = lean_array_uset(v_bs_x27_4104_, v_i_4099_, v___x_4105_);
v_i_4099_ = v___x_4107_;
v_bs_4100_ = v___x_4108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4110_, lean_object* v_i_4111_, lean_object* v_bs_4112_){
_start:
{
size_t v_sz_boxed_4113_; size_t v_i_boxed_4114_; lean_object* v_res_4115_; 
v_sz_boxed_4113_ = lean_unbox_usize(v_sz_4110_);
lean_dec(v_sz_4110_);
v_i_boxed_4114_ = lean_unbox_usize(v_i_4111_);
lean_dec(v_i_4111_);
v_res_4115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4113_, v_i_boxed_4114_, v_bs_4112_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4116_){
_start:
{
size_t v_sz_4117_; size_t v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v_sz_4117_ = lean_array_size(v_a_4116_);
v___x_4118_ = ((size_t)0ULL);
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4117_, v___x_4118_, v_a_4116_);
v___x_4120_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4121_){
_start:
{
lean_object* v_sourceRequestID_4122_; lean_object* v_queries_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4161_; 
v_sourceRequestID_4122_ = lean_ctor_get(v_x_4121_, 0);
v_queries_4123_ = lean_ctor_get(v_x_4121_, 1);
v_isSharedCheck_4161_ = !lean_is_exclusive(v_x_4121_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4125_ = v_x_4121_;
v_isShared_4126_ = v_isSharedCheck_4161_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_queries_4123_);
lean_inc(v_sourceRequestID_4122_);
lean_dec(v_x_4121_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4161_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___y_4129_; 
v___x_4127_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4122_))
{
case 0:
{
lean_object* v_s_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
v_s_4144_ = lean_ctor_get(v_sourceRequestID_4122_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_sourceRequestID_4122_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v_sourceRequestID_4122_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_s_4144_);
lean_dec(v_sourceRequestID_4122_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set_tag(v___x_4146_, 3);
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_s_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
v___y_4129_ = v___x_4149_;
goto v___jp_4128_;
}
}
}
case 1:
{
lean_object* v_n_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
v_n_4152_ = lean_ctor_get(v_sourceRequestID_4122_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v_sourceRequestID_4122_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v_sourceRequestID_4122_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_n_4152_);
lean_dec(v_sourceRequestID_4122_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
lean_ctor_set_tag(v___x_4154_, 2);
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_n_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
v___y_4129_ = v___x_4157_;
goto v___jp_4128_;
}
}
}
default: 
{
lean_object* v___x_4160_; 
v___x_4160_ = lean_box(0);
v___y_4129_ = v___x_4160_;
goto v___jp_4128_;
}
}
v___jp_4128_:
{
lean_object* v___x_4131_; 
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 1, v___y_4129_);
lean_ctor_set(v___x_4125_, 0, v___x_4127_);
v___x_4131_ = v___x_4125_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4127_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v___y_4129_);
v___x_4131_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4132_ = lean_box(0);
v___x_4133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4131_);
lean_ctor_set(v___x_4133_, 1, v___x_4132_);
v___x_4134_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4135_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4123_);
v___x_4136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4134_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
v___x_4137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
lean_ctor_set(v___x_4137_, 1, v___x_4132_);
v___x_4138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
lean_ctor_set(v___x_4138_, 1, v___x_4132_);
v___x_4139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4133_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4141_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4139_, v___x_4140_);
v___x_4142_ = l_Lean_Json_mkObj(v___x_4141_);
lean_dec(v___x_4141_);
return v___x_4142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4164_, lean_object* v_k_4165_){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = l_Lean_Json_getObjValD(v_j_4164_, v_k_4165_);
v___x_4167_ = l_Lean_Name_fromJson_x3f(v___x_4166_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4168_, lean_object* v_k_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4168_, v_k_4169_);
lean_dec_ref(v_k_4169_);
return v_res_4170_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = 1;
v___x_4178_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4179_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4178_, v___x_4177_);
return v___x_4179_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4180_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4181_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4182_ = lean_string_append(v___x_4181_, v___x_4180_);
return v___x_4182_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4185_ = 1;
v___x_4186_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4187_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4186_, v___x_4185_);
return v___x_4187_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4188_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4189_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4190_ = lean_string_append(v___x_4189_, v___x_4188_);
return v___x_4190_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4191_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4192_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4193_ = lean_string_append(v___x_4192_, v___x_4191_);
return v___x_4193_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4197_ = 1;
v___x_4198_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4199_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4198_, v___x_4197_);
return v___x_4199_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4200_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4201_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4202_ = lean_string_append(v___x_4201_, v___x_4200_);
return v___x_4202_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4203_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4204_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4205_ = lean_string_append(v___x_4204_, v___x_4203_);
return v___x_4205_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = 1;
v___x_4210_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4211_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4210_, v___x_4209_);
return v___x_4211_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4213_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4214_ = lean_string_append(v___x_4213_, v___x_4212_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4215_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4216_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4217_ = lean_string_append(v___x_4216_, v___x_4215_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4218_){
_start:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4218_);
v___x_4220_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4218_, v___x_4219_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_json_4218_);
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4230_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4230_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4228_; 
v___x_4225_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4226_ = lean_string_append(v___x_4225_, v_a_4221_);
lean_dec(v_a_4221_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v___x_4226_);
v___x_4228_ = v___x_4223_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4226_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v_a_4231_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4231_);
lean_dec_ref_known(v___x_4220_, 1);
v___x_4232_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4218_);
v___x_4233_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4218_, v___x_4232_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4243_; 
lean_dec(v_a_4231_);
lean_dec(v_json_4218_);
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4236_ = v___x_4233_;
v_isShared_4237_ = v_isSharedCheck_4243_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4233_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4243_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4241_; 
v___x_4238_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
v___x_4239_ = lean_string_append(v___x_4238_, v_a_4234_);
lean_dec(v_a_4234_);
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 0, v___x_4239_);
v___x_4241_ = v___x_4236_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v_a_4244_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4233_, 1);
v___x_4245_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4246_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4218_, v___x_4245_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4256_; 
lean_dec(v_a_4244_);
lean_dec(v_a_4231_);
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4249_ = v___x_4246_;
v_isShared_4250_ = v_isSharedCheck_4256_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4246_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4256_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4254_; 
v___x_4251_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
v___x_4252_ = lean_string_append(v___x_4251_, v_a_4247_);
lean_dec(v_a_4247_);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 0, v___x_4252_);
v___x_4254_ = v___x_4249_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4252_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4266_; 
v_a_4257_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4259_ = v___x_4246_;
v_isShared_4260_ = v_isSharedCheck_4266_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4246_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4266_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4261_; uint8_t v___x_4262_; lean_object* v___x_4264_; 
v___x_4261_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4261_, 0, v_a_4231_);
lean_ctor_set(v___x_4261_, 1, v_a_4244_);
v___x_4262_ = lean_unbox(v_a_4257_);
lean_dec(v_a_4257_);
lean_ctor_set_uint8(v___x_4261_, sizeof(void*)*2, v___x_4262_);
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 0, v___x_4261_);
v___x_4264_ = v___x_4259_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4261_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4269_){
_start:
{
lean_object* v_module_4270_; lean_object* v_decl_4271_; uint8_t v_isExactMatch_4272_; lean_object* v___x_4273_; uint8_t v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v_module_4270_ = lean_ctor_get(v_x_4269_, 0);
lean_inc(v_module_4270_);
v_decl_4271_ = lean_ctor_get(v_x_4269_, 1);
lean_inc(v_decl_4271_);
v_isExactMatch_4272_ = lean_ctor_get_uint8(v_x_4269_, sizeof(void*)*2);
lean_dec_ref(v_x_4269_);
v___x_4273_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4274_ = 1;
v___x_4275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4270_, v___x_4274_);
v___x_4276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
v___x_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4273_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = lean_box(0);
v___x_4279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4271_, v___x_4274_);
v___x_4282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
v___x_4283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4280_);
lean_ctor_set(v___x_4283_, 1, v___x_4282_);
v___x_4284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4283_);
lean_ctor_set(v___x_4284_, 1, v___x_4278_);
v___x_4285_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4286_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4286_, 0, v_isExactMatch_4272_);
v___x_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4285_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___x_4288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4287_);
lean_ctor_set(v___x_4288_, 1, v___x_4278_);
v___x_4289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
lean_ctor_set(v___x_4289_, 1, v___x_4278_);
v___x_4290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4284_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
v___x_4291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4279_);
lean_ctor_set(v___x_4291_, 1, v___x_4290_);
v___x_4292_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4293_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4291_, v___x_4292_);
v___x_4294_ = l_Lean_Json_mkObj(v___x_4293_);
lean_dec(v___x_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4297_, size_t v_i_4298_, lean_object* v_bs_4299_){
_start:
{
uint8_t v___x_4300_; 
v___x_4300_ = lean_usize_dec_lt(v_i_4298_, v_sz_4297_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; 
v___x_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4301_, 0, v_bs_4299_);
return v___x_4301_;
}
else
{
lean_object* v_v_4302_; lean_object* v___x_4303_; 
v_v_4302_ = lean_array_uget_borrowed(v_bs_4299_, v_i_4298_);
lean_inc(v_v_4302_);
v___x_4303_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4302_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec_ref(v_bs_4299_);
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4303_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4303_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4313_; lean_object* v_bs_x27_4314_; size_t v___x_4315_; size_t v___x_4316_; lean_object* v___x_4317_; 
v_a_4312_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4303_, 1);
v___x_4313_ = lean_unsigned_to_nat(0u);
v_bs_x27_4314_ = lean_array_uset(v_bs_4299_, v_i_4298_, v___x_4313_);
v___x_4315_ = ((size_t)1ULL);
v___x_4316_ = lean_usize_add(v_i_4298_, v___x_4315_);
v___x_4317_ = lean_array_uset(v_bs_x27_4314_, v_i_4298_, v_a_4312_);
v_i_4298_ = v___x_4316_;
v_bs_4299_ = v___x_4317_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4319_, lean_object* v_i_4320_, lean_object* v_bs_4321_){
_start:
{
size_t v_sz_boxed_4322_; size_t v_i_boxed_4323_; lean_object* v_res_4324_; 
v_sz_boxed_4322_ = lean_unbox_usize(v_sz_4319_);
lean_dec(v_sz_4319_);
v_i_boxed_4323_ = lean_unbox_usize(v_i_4320_);
lean_dec(v_i_4320_);
v_res_4324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4322_, v_i_boxed_4323_, v_bs_4321_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4325_){
_start:
{
if (lean_obj_tag(v_x_4325_) == 4)
{
lean_object* v_elems_4326_; size_t v_sz_4327_; size_t v___x_4328_; lean_object* v___x_4329_; 
v_elems_4326_ = lean_ctor_get(v_x_4325_, 0);
lean_inc_ref(v_elems_4326_);
lean_dec_ref_known(v_x_4325_, 1);
v_sz_4327_ = lean_array_size(v_elems_4326_);
v___x_4328_ = ((size_t)0ULL);
v___x_4329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4327_, v___x_4328_, v_elems_4326_);
return v___x_4329_;
}
else
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4330_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4331_ = lean_unsigned_to_nat(80u);
v___x_4332_ = l_Lean_Json_pretty(v_x_4325_, v___x_4331_);
v___x_4333_ = lean_string_append(v___x_4330_, v___x_4332_);
lean_dec_ref(v___x_4332_);
v___x_4334_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_4335_ = lean_string_append(v___x_4333_, v___x_4334_);
v___x_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
return v___x_4336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4337_, size_t v_i_4338_, lean_object* v_bs_4339_){
_start:
{
uint8_t v___x_4340_; 
v___x_4340_ = lean_usize_dec_lt(v_i_4338_, v_sz_4337_);
if (v___x_4340_ == 0)
{
lean_object* v___x_4341_; 
v___x_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4341_, 0, v_bs_4339_);
return v___x_4341_;
}
else
{
lean_object* v_v_4342_; lean_object* v___x_4343_; 
v_v_4342_ = lean_array_uget_borrowed(v_bs_4339_, v_i_4338_);
lean_inc(v_v_4342_);
v___x_4343_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4342_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec_ref(v_bs_4339_);
v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4343_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4343_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4353_; lean_object* v_bs_x27_4354_; size_t v___x_4355_; size_t v___x_4356_; lean_object* v___x_4357_; 
v_a_4352_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4343_, 1);
v___x_4353_ = lean_unsigned_to_nat(0u);
v_bs_x27_4354_ = lean_array_uset(v_bs_4339_, v_i_4338_, v___x_4353_);
v___x_4355_ = ((size_t)1ULL);
v___x_4356_ = lean_usize_add(v_i_4338_, v___x_4355_);
v___x_4357_ = lean_array_uset(v_bs_x27_4354_, v_i_4338_, v_a_4352_);
v_i_4338_ = v___x_4356_;
v_bs_4339_ = v___x_4357_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4359_, lean_object* v_i_4360_, lean_object* v_bs_4361_){
_start:
{
size_t v_sz_boxed_4362_; size_t v_i_boxed_4363_; lean_object* v_res_4364_; 
v_sz_boxed_4362_ = lean_unbox_usize(v_sz_4359_);
lean_dec(v_sz_4359_);
v_i_boxed_4363_ = lean_unbox_usize(v_i_4360_);
lean_dec(v_i_4360_);
v_res_4364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4362_, v_i_boxed_4363_, v_bs_4361_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4365_){
_start:
{
if (lean_obj_tag(v_x_4365_) == 4)
{
lean_object* v_elems_4366_; size_t v_sz_4367_; size_t v___x_4368_; lean_object* v___x_4369_; 
v_elems_4366_ = lean_ctor_get(v_x_4365_, 0);
lean_inc_ref(v_elems_4366_);
lean_dec_ref_known(v_x_4365_, 1);
v_sz_4367_ = lean_array_size(v_elems_4366_);
v___x_4368_ = ((size_t)0ULL);
v___x_4369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4367_, v___x_4368_, v_elems_4366_);
return v___x_4369_;
}
else
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4370_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4371_ = lean_unsigned_to_nat(80u);
v___x_4372_ = l_Lean_Json_pretty(v_x_4365_, v___x_4371_);
v___x_4373_ = lean_string_append(v___x_4370_, v___x_4372_);
lean_dec_ref(v___x_4372_);
v___x_4374_ = ((lean_object*)(l_Lean_Lsp_RefIdent_fromJson_x3f___closed__1));
v___x_4375_ = lean_string_append(v___x_4373_, v___x_4374_);
v___x_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
return v___x_4376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4377_, lean_object* v_k_4378_){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = l_Lean_Json_getObjValD(v_j_4377_, v_k_4378_);
v___x_4380_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4381_, lean_object* v_k_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4381_, v_k_4382_);
lean_dec_ref(v_k_4382_);
return v_res_4383_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4390_ = 1;
v___x_4391_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4392_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4391_, v___x_4390_);
return v___x_4392_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4393_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4394_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4395_ = lean_string_append(v___x_4394_, v___x_4393_);
return v___x_4395_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = 1;
v___x_4399_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4400_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4399_, v___x_4398_);
return v___x_4400_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4401_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4402_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4403_ = lean_string_append(v___x_4402_, v___x_4401_);
return v___x_4403_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4405_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4406_ = lean_string_append(v___x_4405_, v___x_4404_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4407_){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4409_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4407_, v___x_4408_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4419_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4412_ = v___x_4409_;
v_isShared_4413_ = v_isSharedCheck_4419_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4409_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4419_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4417_; 
v___x_4414_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4415_ = lean_string_append(v___x_4414_, v_a_4410_);
lean_dec(v_a_4410_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4415_);
v___x_4417_ = v___x_4412_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
v_a_4420_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4409_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4409_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4430_, size_t v_i_4431_, lean_object* v_bs_4432_){
_start:
{
uint8_t v___x_4433_; 
v___x_4433_ = lean_usize_dec_lt(v_i_4431_, v_sz_4430_);
if (v___x_4433_ == 0)
{
return v_bs_4432_;
}
else
{
lean_object* v_v_4434_; lean_object* v___x_4435_; lean_object* v_bs_x27_4436_; lean_object* v___x_4437_; size_t v___x_4438_; size_t v___x_4439_; lean_object* v___x_4440_; 
v_v_4434_ = lean_array_uget(v_bs_4432_, v_i_4431_);
v___x_4435_ = lean_unsigned_to_nat(0u);
v_bs_x27_4436_ = lean_array_uset(v_bs_4432_, v_i_4431_, v___x_4435_);
v___x_4437_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4434_);
v___x_4438_ = ((size_t)1ULL);
v___x_4439_ = lean_usize_add(v_i_4431_, v___x_4438_);
v___x_4440_ = lean_array_uset(v_bs_x27_4436_, v_i_4431_, v___x_4437_);
v_i_4431_ = v___x_4439_;
v_bs_4432_ = v___x_4440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4442_, lean_object* v_i_4443_, lean_object* v_bs_4444_){
_start:
{
size_t v_sz_boxed_4445_; size_t v_i_boxed_4446_; lean_object* v_res_4447_; 
v_sz_boxed_4445_ = lean_unbox_usize(v_sz_4442_);
lean_dec(v_sz_4442_);
v_i_boxed_4446_ = lean_unbox_usize(v_i_4443_);
lean_dec(v_i_4443_);
v_res_4447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4445_, v_i_boxed_4446_, v_bs_4444_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4448_){
_start:
{
size_t v_sz_4449_; size_t v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v_sz_4449_ = lean_array_size(v_a_4448_);
v___x_4450_ = ((size_t)0ULL);
v___x_4451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4449_, v___x_4450_, v_a_4448_);
v___x_4452_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4453_, size_t v_i_4454_, lean_object* v_bs_4455_){
_start:
{
uint8_t v___x_4456_; 
v___x_4456_ = lean_usize_dec_lt(v_i_4454_, v_sz_4453_);
if (v___x_4456_ == 0)
{
return v_bs_4455_;
}
else
{
lean_object* v_v_4457_; lean_object* v___x_4458_; lean_object* v_bs_x27_4459_; lean_object* v___x_4460_; size_t v___x_4461_; size_t v___x_4462_; lean_object* v___x_4463_; 
v_v_4457_ = lean_array_uget(v_bs_4455_, v_i_4454_);
v___x_4458_ = lean_unsigned_to_nat(0u);
v_bs_x27_4459_ = lean_array_uset(v_bs_4455_, v_i_4454_, v___x_4458_);
v___x_4460_ = l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4457_);
v___x_4461_ = ((size_t)1ULL);
v___x_4462_ = lean_usize_add(v_i_4454_, v___x_4461_);
v___x_4463_ = lean_array_uset(v_bs_x27_4459_, v_i_4454_, v___x_4460_);
v_i_4454_ = v___x_4462_;
v_bs_4455_ = v___x_4463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4465_, lean_object* v_i_4466_, lean_object* v_bs_4467_){
_start:
{
size_t v_sz_boxed_4468_; size_t v_i_boxed_4469_; lean_object* v_res_4470_; 
v_sz_boxed_4468_ = lean_unbox_usize(v_sz_4465_);
lean_dec(v_sz_4465_);
v_i_boxed_4469_ = lean_unbox_usize(v_i_4466_);
lean_dec(v_i_4466_);
v_res_4470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4468_, v_i_boxed_4469_, v_bs_4467_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4471_){
_start:
{
size_t v_sz_4472_; size_t v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v_sz_4472_ = lean_array_size(v_a_4471_);
v___x_4473_ = ((size_t)0ULL);
v___x_4474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4472_, v___x_4473_, v_a_4471_);
v___x_4475_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object* v_x_4476_){
_start:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4477_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4478_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4476_);
v___x_4479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4477_);
lean_ctor_set(v___x_4479_, 1, v___x_4478_);
v___x_4480_ = lean_box(0);
v___x_4481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4479_);
lean_ctor_set(v___x_4481_, 1, v___x_4480_);
v___x_4482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
lean_ctor_set(v___x_4482_, 1, v___x_4480_);
v___x_4483_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4484_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4482_, v___x_4483_);
v___x_4485_ = l_Lean_Json_mkObj(v___x_4484_);
lean_dec(v___x_4484_);
return v___x_4485_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4497_ = 1;
v___x_4498_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1));
v___x_4499_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4498_, v___x_4497_);
return v___x_4499_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4500_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4501_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2);
v___x_4502_ = lean_string_append(v___x_4501_, v___x_4500_);
return v___x_4502_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4504_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4505_ = lean_string_append(v___x_4504_, v___x_4503_);
return v___x_4505_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4506_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4507_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4);
v___x_4508_ = lean_string_append(v___x_4507_, v___x_4506_);
return v___x_4508_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4509_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4510_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4511_ = lean_string_append(v___x_4510_, v___x_4509_);
return v___x_4511_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4512_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4513_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6);
v___x_4514_ = lean_string_append(v___x_4513_, v___x_4512_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object* v_json_4515_){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4515_);
v___x_4517_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4515_, v___x_4516_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4527_; 
lean_dec(v_json_4515_);
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4520_ = v___x_4517_;
v_isShared_4521_ = v_isSharedCheck_4527_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4517_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4527_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4525_; 
v___x_4522_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5);
v___x_4523_ = lean_string_append(v___x_4522_, v_a_4518_);
lean_dec(v_a_4518_);
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 0, v___x_4523_);
v___x_4525_ = v___x_4520_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4523_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
else
{
lean_object* v_a_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v_a_4528_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4528_);
lean_dec_ref_known(v___x_4517_, 1);
v___x_4529_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4530_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4515_, v___x_4529_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4540_; 
lean_dec(v_a_4528_);
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4533_ = v___x_4530_;
v_isShared_4534_ = v_isSharedCheck_4540_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4530_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4540_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4538_; 
v___x_4535_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7);
v___x_4536_ = lean_string_append(v___x_4535_, v_a_4531_);
lean_dec(v_a_4531_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 0, v___x_4536_);
v___x_4538_ = v___x_4533_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4549_; 
v_a_4541_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4543_ = v___x_4530_;
v_isShared_4544_ = v_isSharedCheck_4549_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4530_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4549_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4545_; lean_object* v___x_4547_; 
v___x_4545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4545_, 0, v_a_4528_);
lean_ctor_set(v___x_4545_, 1, v_a_4541_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v___x_4545_);
v___x_4547_ = v___x_4543_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4545_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object* v_x_4552_){
_start:
{
lean_object* v_module_4553_; lean_object* v_decl_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4577_; 
v_module_4553_ = lean_ctor_get(v_x_4552_, 0);
v_decl_4554_ = lean_ctor_get(v_x_4552_, 1);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_x_4552_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4556_ = v_x_4552_;
v_isShared_4557_ = v_isSharedCheck_4577_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_decl_4554_);
lean_inc(v_module_4553_);
lean_dec(v_x_4552_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4577_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4558_; uint8_t v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4563_; 
v___x_4558_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4559_ = 1;
v___x_4560_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4553_, v___x_4559_);
v___x_4561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 1, v___x_4561_);
lean_ctor_set(v___x_4556_, 0, v___x_4558_);
v___x_4563_ = v___x_4556_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4558_);
lean_ctor_set(v_reuseFailAlloc_4576_, 1, v___x_4561_);
v___x_4563_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4564_ = lean_box(0);
v___x_4565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4563_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
v___x_4566_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4567_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4554_, v___x_4559_);
v___x_4568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
v___x_4569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4566_);
lean_ctor_set(v___x_4569_, 1, v___x_4568_);
v___x_4570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
lean_ctor_set(v___x_4570_, 1, v___x_4564_);
v___x_4571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4570_);
lean_ctor_set(v___x_4571_, 1, v___x_4564_);
v___x_4572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4565_);
lean_ctor_set(v___x_4572_, 1, v___x_4571_);
v___x_4573_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4574_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4572_, v___x_4573_);
v___x_4575_ = l_Lean_Json_mkObj(v___x_4574_);
lean_dec(v___x_4574_);
return v___x_4575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object* v_j_4580_, lean_object* v_k_4581_){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = l_Lean_Json_getObjValD(v_j_4580_, v_k_4581_);
v___x_4583_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4582_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object* v_j_4584_, lean_object* v_k_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_j_4584_, v_k_4585_);
lean_dec_ref(v_k_4585_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4589_){
_start:
{
if (lean_obj_tag(v_x_4589_) == 0)
{
lean_object* v___x_4590_; 
v___x_4590_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
return v___x_4590_;
}
else
{
lean_object* v___x_4591_; 
v___x_4591_ = l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(v_x_4589_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___x_4591_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4591_);
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
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4608_; 
v_a_4600_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4602_ = v___x_4591_;
v_isShared_4603_ = v_isSharedCheck_4608_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4591_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4608_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4604_; lean_object* v___x_4606_; 
v___x_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4604_, 0, v_a_4600_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4604_);
v___x_4606_ = v___x_4602_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object* v_j_4609_, lean_object* v_k_4610_){
_start:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4611_ = l_Lean_Json_getObjValD(v_j_4609_, v_k_4610_);
v___x_4612_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4611_);
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object* v_j_4613_, lean_object* v_k_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_j_4613_, v_k_4614_);
lean_dec_ref(v_k_4614_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4618_){
_start:
{
if (lean_obj_tag(v_x_4618_) == 0)
{
lean_object* v___x_4619_; 
v___x_4619_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_4619_;
}
else
{
lean_object* v___x_4620_; 
v___x_4620_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_4618_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4620_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4620_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4637_; 
v_a_4629_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4631_ = v___x_4620_;
v_isShared_4632_ = v_isSharedCheck_4637_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4620_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4637_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4633_; lean_object* v___x_4635_; 
v___x_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4633_, 0, v_a_4629_);
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 0, v___x_4633_);
v___x_4635_ = v___x_4631_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object* v_j_4638_, lean_object* v_k_4639_){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4640_ = l_Lean_Json_getObjValD(v_j_4638_, v_k_4639_);
v___x_4641_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4640_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object* v_j_4642_, lean_object* v_k_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_j_4642_, v_k_4643_);
lean_dec_ref(v_k_4643_);
return v_res_4644_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4651_ = 1;
v___x_4652_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2));
v___x_4653_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4652_, v___x_4651_);
return v___x_4653_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4654_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4655_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3);
v___x_4656_ = lean_string_append(v___x_4655_, v___x_4654_);
return v___x_4656_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7(void){
_start:
{
uint8_t v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4660_ = 1;
v___x_4661_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6));
v___x_4662_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4661_, v___x_4660_);
return v___x_4662_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4663_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7);
v___x_4664_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4665_ = lean_string_append(v___x_4664_, v___x_4663_);
return v___x_4665_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4666_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4667_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8);
v___x_4668_ = lean_string_append(v___x_4667_, v___x_4666_);
return v___x_4668_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12(void){
_start:
{
uint8_t v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = 1;
v___x_4673_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11));
v___x_4674_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4673_, v___x_4672_);
return v___x_4674_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12);
v___x_4676_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4677_ = lean_string_append(v___x_4676_, v___x_4675_);
return v___x_4677_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14(void){
_start:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4678_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4679_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13);
v___x_4680_ = lean_string_append(v___x_4679_, v___x_4678_);
return v___x_4680_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17(void){
_start:
{
uint8_t v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4684_ = 1;
v___x_4685_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16));
v___x_4686_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4685_, v___x_4684_);
return v___x_4686_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4687_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17);
v___x_4688_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4689_ = lean_string_append(v___x_4688_, v___x_4687_);
return v___x_4689_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4690_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4691_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18);
v___x_4692_ = lean_string_append(v___x_4691_, v___x_4690_);
return v___x_4692_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22(void){
_start:
{
uint8_t v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4696_ = 1;
v___x_4697_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21));
v___x_4698_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4697_, v___x_4696_);
return v___x_4698_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23(void){
_start:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4699_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22);
v___x_4700_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4701_ = lean_string_append(v___x_4700_, v___x_4699_);
return v___x_4701_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24(void){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4703_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23);
v___x_4704_ = lean_string_append(v___x_4703_, v___x_4702_);
return v___x_4704_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28(void){
_start:
{
uint8_t v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4709_ = 1;
v___x_4710_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27));
v___x_4711_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4710_, v___x_4709_);
return v___x_4711_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29(void){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4712_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28);
v___x_4713_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4714_ = lean_string_append(v___x_4713_, v___x_4712_);
return v___x_4714_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30(void){
_start:
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4715_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4716_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29);
v___x_4717_ = lean_string_append(v___x_4716_, v___x_4715_);
return v___x_4717_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33(void){
_start:
{
uint8_t v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4721_ = 1;
v___x_4722_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32));
v___x_4723_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4722_, v___x_4721_);
return v___x_4723_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34(void){
_start:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4724_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33);
v___x_4725_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4726_ = lean_string_append(v___x_4725_, v___x_4724_);
return v___x_4726_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35(void){
_start:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4727_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4728_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34);
v___x_4729_ = lean_string_append(v___x_4728_, v___x_4727_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object* v_json_4730_){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
lean_inc(v_json_4730_);
v___x_4732_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_json_4730_, v___x_4731_);
if (lean_obj_tag(v___x_4732_) == 0)
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4742_; 
lean_dec(v_json_4730_);
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4735_ = v___x_4732_;
v_isShared_4736_ = v_isSharedCheck_4742_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4732_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4742_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4740_; 
v___x_4737_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9);
v___x_4738_ = lean_string_append(v___x_4737_, v_a_4733_);
lean_dec(v_a_4733_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 0, v___x_4738_);
v___x_4740_ = v___x_4735_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4738_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v_a_4743_ = lean_ctor_get(v___x_4732_, 0);
lean_inc(v_a_4743_);
lean_dec_ref_known(v___x_4732_, 1);
v___x_4744_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
lean_inc(v_json_4730_);
v___x_4745_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4730_, v___x_4744_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4755_; 
lean_dec(v_a_4743_);
lean_dec(v_json_4730_);
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4748_ = v___x_4745_;
v_isShared_4749_ = v_isSharedCheck_4755_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4745_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4755_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4753_; 
v___x_4750_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14);
v___x_4751_ = lean_string_append(v___x_4750_, v_a_4746_);
lean_dec(v_a_4746_);
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v___x_4751_);
v___x_4753_ = v___x_4748_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4751_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v_a_4756_ = lean_ctor_get(v___x_4745_, 0);
lean_inc(v_a_4756_);
lean_dec_ref_known(v___x_4745_, 1);
v___x_4757_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
lean_inc(v_json_4730_);
v___x_4758_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_4730_, v___x_4757_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4768_; 
lean_dec(v_a_4756_);
lean_dec(v_a_4743_);
lean_dec(v_json_4730_);
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4761_ = v___x_4758_;
v_isShared_4762_ = v_isSharedCheck_4768_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4758_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4768_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4766_; 
v___x_4763_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19);
v___x_4764_ = lean_string_append(v___x_4763_, v_a_4759_);
lean_dec(v_a_4759_);
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 0, v___x_4764_);
v___x_4766_ = v___x_4761_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4764_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
else
{
lean_object* v_a_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v_a_4769_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4769_);
lean_dec_ref_known(v___x_4758_, 1);
v___x_4770_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
lean_inc(v_json_4730_);
v___x_4771_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_4730_, v___x_4770_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4781_; 
lean_dec(v_a_4769_);
lean_dec(v_a_4756_);
lean_dec(v_a_4743_);
lean_dec(v_json_4730_);
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4774_ = v___x_4771_;
v_isShared_4775_ = v_isSharedCheck_4781_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_dec(v___x_4771_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4781_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4779_; 
v___x_4776_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24);
v___x_4777_ = lean_string_append(v___x_4776_, v_a_4772_);
lean_dec(v_a_4772_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v___x_4777_);
v___x_4779_ = v___x_4774_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4777_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v_a_4782_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_a_4782_);
lean_dec_ref_known(v___x_4771_, 1);
v___x_4783_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
lean_inc(v_json_4730_);
v___x_4784_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_json_4730_, v___x_4783_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4794_; 
lean_dec(v_a_4782_);
lean_dec(v_a_4769_);
lean_dec(v_a_4756_);
lean_dec(v_a_4743_);
lean_dec(v_json_4730_);
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4787_ = v___x_4784_;
v_isShared_4788_ = v_isSharedCheck_4794_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4784_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4794_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4792_; 
v___x_4789_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30);
v___x_4790_ = lean_string_append(v___x_4789_, v_a_4785_);
lean_dec(v_a_4785_);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v___x_4790_);
v___x_4792_ = v___x_4787_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v_a_4795_ = lean_ctor_get(v___x_4784_, 0);
lean_inc(v_a_4795_);
lean_dec_ref_known(v___x_4784_, 1);
v___x_4796_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_4797_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4730_, v___x_4796_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4807_; 
lean_dec(v_a_4795_);
lean_dec(v_a_4782_);
lean_dec(v_a_4769_);
lean_dec(v_a_4756_);
lean_dec(v_a_4743_);
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4800_ = v___x_4797_;
v_isShared_4801_ = v_isSharedCheck_4807_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4797_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4807_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4805_; 
v___x_4802_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35);
v___x_4803_ = lean_string_append(v___x_4802_, v_a_4798_);
lean_dec(v_a_4798_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v___x_4803_);
v___x_4805_ = v___x_4800_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4803_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4818_; 
v_a_4808_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4810_ = v___x_4797_;
v_isShared_4811_ = v_isSharedCheck_4818_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4797_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4818_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; lean_object* v___x_4816_; 
v___x_4812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4812_, 0, v_a_4743_);
lean_ctor_set(v___x_4812_, 1, v_a_4756_);
lean_ctor_set(v___x_4812_, 2, v_a_4769_);
lean_ctor_set(v___x_4812_, 3, v_a_4782_);
v___x_4813_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4813_, 0, v___x_4812_);
lean_ctor_set(v___x_4813_, 1, v_a_4795_);
v___x_4814_ = lean_unbox(v_a_4808_);
lean_dec(v_a_4808_);
lean_ctor_set_uint8(v___x_4813_, sizeof(void*)*2, v___x_4814_);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 0, v___x_4813_);
v___x_4816_ = v___x_4810_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4813_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object* v_k_4821_, lean_object* v_x_4822_){
_start:
{
if (lean_obj_tag(v_x_4822_) == 0)
{
lean_object* v___x_4823_; 
lean_dec_ref(v_k_4821_);
v___x_4823_ = lean_box(0);
return v___x_4823_;
}
else
{
lean_object* v_val_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
v_val_4824_ = lean_ctor_get(v_x_4822_, 0);
lean_inc(v_val_4824_);
lean_dec_ref_known(v_x_4822_, 1);
v___x_4825_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_4824_);
v___x_4826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4826_, 0, v_k_4821_);
lean_ctor_set(v___x_4826_, 1, v___x_4825_);
v___x_4827_ = lean_box(0);
v___x_4828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4826_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
return v___x_4828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object* v_k_4829_, lean_object* v_x_4830_){
_start:
{
if (lean_obj_tag(v_x_4830_) == 0)
{
lean_object* v___x_4831_; 
lean_dec_ref(v_k_4829_);
v___x_4831_ = lean_box(0);
return v___x_4831_;
}
else
{
lean_object* v_val_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
v_val_4832_ = lean_ctor_get(v_x_4830_, 0);
lean_inc(v_val_4832_);
lean_dec_ref_known(v_x_4830_, 1);
v___x_4833_ = l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(v_val_4832_);
v___x_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4834_, 0, v_k_4829_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
v___x_4835_ = lean_box(0);
v___x_4836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4834_);
lean_ctor_set(v___x_4836_, 1, v___x_4835_);
return v___x_4836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object* v_x_4837_){
_start:
{
lean_object* v_toLocationLink_4838_; lean_object* v_ident_x3f_4839_; uint8_t v_isDefault_4840_; lean_object* v_originSelectionRange_x3f_4841_; lean_object* v_targetUri_4842_; lean_object* v_targetRange_4843_; lean_object* v_targetSelectionRange_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v_toLocationLink_4838_ = lean_ctor_get(v_x_4837_, 0);
lean_inc_ref(v_toLocationLink_4838_);
v_ident_x3f_4839_ = lean_ctor_get(v_x_4837_, 1);
lean_inc(v_ident_x3f_4839_);
v_isDefault_4840_ = lean_ctor_get_uint8(v_x_4837_, sizeof(void*)*2);
lean_dec_ref(v_x_4837_);
v_originSelectionRange_x3f_4841_ = lean_ctor_get(v_toLocationLink_4838_, 0);
lean_inc(v_originSelectionRange_x3f_4841_);
v_targetUri_4842_ = lean_ctor_get(v_toLocationLink_4838_, 1);
lean_inc_ref(v_targetUri_4842_);
v_targetRange_4843_ = lean_ctor_get(v_toLocationLink_4838_, 2);
lean_inc_ref(v_targetRange_4843_);
v_targetSelectionRange_4844_ = lean_ctor_get(v_toLocationLink_4838_, 3);
lean_inc_ref(v_targetSelectionRange_4844_);
lean_dec_ref(v_toLocationLink_4838_);
v___x_4845_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
v___x_4846_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(v___x_4845_, v_originSelectionRange_x3f_4841_);
v___x_4847_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
v___x_4848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4848_, 0, v_targetUri_4842_);
v___x_4849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4847_);
lean_ctor_set(v___x_4849_, 1, v___x_4848_);
v___x_4850_ = lean_box(0);
v___x_4851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4851_, 0, v___x_4849_);
lean_ctor_set(v___x_4851_, 1, v___x_4850_);
v___x_4852_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
v___x_4853_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_4843_);
v___x_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4852_);
lean_ctor_set(v___x_4854_, 1, v___x_4853_);
v___x_4855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
lean_ctor_set(v___x_4855_, 1, v___x_4850_);
v___x_4856_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
v___x_4857_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_4844_);
v___x_4858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4856_);
lean_ctor_set(v___x_4858_, 1, v___x_4857_);
v___x_4859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
lean_ctor_set(v___x_4859_, 1, v___x_4850_);
v___x_4860_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
v___x_4861_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(v___x_4860_, v_ident_x3f_4839_);
v___x_4862_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_4863_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4863_, 0, v_isDefault_4840_);
v___x_4864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4862_);
lean_ctor_set(v___x_4864_, 1, v___x_4863_);
v___x_4865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
lean_ctor_set(v___x_4865_, 1, v___x_4850_);
v___x_4866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
lean_ctor_set(v___x_4866_, 1, v___x_4850_);
v___x_4867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4861_);
lean_ctor_set(v___x_4867_, 1, v___x_4866_);
v___x_4868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4859_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
v___x_4869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4855_);
lean_ctor_set(v___x_4869_, 1, v___x_4868_);
v___x_4870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4851_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
v___x_4871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4846_);
lean_ctor_set(v___x_4871_, 1, v___x_4870_);
v___x_4872_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4873_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4871_, v___x_4872_);
v___x_4874_ = l_Lean_Json_mkObj(v___x_4873_);
lean_dec(v___x_4873_);
return v___x_4874_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Internal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instEmptyCollectionDecls___aux__1 = _init_l_Lean_Lsp_instEmptyCollectionDecls___aux__1();
lean_mark_persistent(l_Lean_Lsp_instEmptyCollectionDecls___aux__1);
l_Lean_Lsp_instEmptyCollectionDecls = _init_l_Lean_Lsp_instEmptyCollectionDecls();
lean_mark_persistent(l_Lean_Lsp_instEmptyCollectionDecls);
l_Lean_Lsp_instEmptyCollectionModuleRefs___aux__1 = _init_l_Lean_Lsp_instEmptyCollectionModuleRefs___aux__1();
lean_mark_persistent(l_Lean_Lsp_instEmptyCollectionModuleRefs___aux__1);
l_Lean_Lsp_instEmptyCollectionModuleRefs = _init_l_Lean_Lsp_instEmptyCollectionModuleRefs();
lean_mark_persistent(l_Lean_Lsp_instEmptyCollectionModuleRefs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Internal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* initialize_Lean_Data_DeclarationRange(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Internal(builtin);
}
#ifdef __cplusplus
}
#endif
